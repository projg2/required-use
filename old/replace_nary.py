#!/usr/bin/env python

import itertools
import sys

from parser import (parse_string, Flag, Implication, NaryOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator,
        AllOfOperator)

def negate(expr):
    if isinstance(expr, Flag):
        return expr.negated()
    elif isinstance(expr, AllOfOperator):
        return AnyOfOperator([negate(x) for x in expr.constraint])
    elif isinstance(expr, AnyOfOperator):
        return AllOfOperator([negate(x) for x in expr.constraint])
    else:
        raise ValueError('Invalid expr for negate: %s' % expr)

def replace_nary(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            yield Implication(expr.condition, list(replace_nary(expr.constraint)))
        elif isinstance(expr, AtMostOneOfOperator):
            # ?? ( a b c ... ) -> a? ( !b !c ... ) b? ( !c ... ) ...
            # -> && ( || ( ( !b !c ... ) !a ) || ( ( !c ... ) !b ) ... )
            constraint = [ negate(x) for x in replace_nary(expr.constraint) ]
            result = []
            while len(constraint) > 0:
                r = constraint.pop(0)
                l = AllOfOperator([ x for x in constraint ])
                result.append(AnyOfOperator([l,r]))
            yield AllOfOperator(result)
        elif isinstance(expr, ExactlyOneOfOperator):
            # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
            constraint = list(replace_nary(expr.constraint))
            m = list(replace_nary([AtMostOneOfOperator(constraint)]))
            yield AllOfOperator([AnyOfOperator(constraint)]+ m)
        elif isinstance(expr, AllOfOperator):
            yield AllOfOperator(list(replace_nary(expr.constraint)))
        elif isinstance(expr, AnyOfOperator):
            yield AnyOfOperator(list(replace_nary(expr.constraint)))
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


def expand_conditions(expr):
    for subexpr in expr:
        if isinstance(subexpr, Flag):
            yield [subexpr]
        elif isinstance(subexpr, AllOfOperator):
            yield (x.negated() for x in subexpr.constraint)
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


def replace_allof(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            condition = expr.condition
            constraint = list(replace_allof(expr.constraint))

            if any(isinstance(x, AllOfOperator) for x in condition):
                if all(x.enabled for x in condition):
                    yield Implication(list(replace_nary(condition)), constraint)
                else:
                    if any(x.enabled for x in condition):
                        raise NotImplementedError(
                                'Only pure negative or pure positive implication conditions supported')

                    # we need to replace !(a && b && c) -> !a || !b || !c
                    # per de Morgan's law, then convert to CNF
                    # (!a || !b) && (!c || !d) -> (!a && !c) || (!a && !d) || ...
                    for cset in itertools.product(*expand_conditions(condition)):
                        yield Implication(list(cset), list(constraint))
            else:
                yield Implication(condition, constraint)
        elif isinstance(expr, NaryOperator):
            raise ValueError('Flat n-ary operators should be replaced already')
        else:
            raise ValueError('Unknown AST expr: %s' % expr)

def merge_and_expand_implications(ast):
    for expr in ast:
        if isinstance(expr, Implication):
            for i in expr.constraint:
                if isinstance(i, Implication):
                    for j in merge_and_expand_implications([i]):
                        yield Implication(expr.condition+j.condition,
                                j.constraint)
                elif isinstance(i, AllOfOperator):
                    for j in i.constraint:
                        yield Implication(expr.condition, [j], strict=True)
                else:
                    yield Implication(expr.condition, [i], strict=True)
        else:
            yield expr

def really_replace_nested_implications(ast):
    for expr in ast:
        if isinstance(expr, Implication):
            m = list(really_replace_nested_implications(expr.constraint))
            yield AllOfOperator(expr.condition+m)
        else:
            if hasattr(expr, "constraint"):
                m = list(really_replace_nested_implications(expr.constraint))
                expr.constraint = m
            yield expr

def replace_nested_implications(ast):
    for expr in ast:
        if hasattr(expr, "constraint"):
            n = list(really_replace_nested_implications(expr.constraint))
            expr.constraint = n
        yield expr

def simplify_with_immutables(ast, immutables):
    if type(ast) == list:
        r = []
        for x in ast:
            m = simplify_with_immutables(x,immutables)
            if m is True: continue
            if m is False: return False
            r.append(m)
        return r
    elif isinstance(ast, Flag):
        if ast.name in immutables:
            if ast.enabled: return immutables[ast.name]
            else: return not immutables[ast.name]
        else: return ast
    elif isinstance(ast, Implication):
        nc = []
        for c in ast.condition:
            if c.name in immutables:
                if not immutables[c.name]: return True
            else: nc.append(c)
        if len(nc) <= 0:
            return simplify_with_immutables(AllOfOperator(ast.constraint), immutables)
        ncons = []
        for c in ast.constraint:
            m = simplify_with_immutables(c, immutables)
            if m is True: continue
            if m is False: return False
            ncons.append(m)
        if len(ncons) <= 0: return True
        return Implication(nc, ncons)
    elif isinstance(ast, AllOfOperator):
        r = []
        for x in ast.constraint:
            m = simplify_with_immutables(x, immutables)
            if m is True: continue
            if m is False: return False
            r.append(m)
        if len(r) <= 0: return True
        if len(r) == 1: return r[0]
        return AllOfOperator(r)
    elif isinstance(ast, AnyOfOperator):
        r = []
        for x in ast.constraint:
            m = simplify_with_immutables(x, immutables)
            if m is True: return True
            if m is False: continue
            r.append(m)
        if len(r) <= 0: return False
        if len(r) == 1: return r[0]
        return AnyOfOperator(r)
    else:
        raise ValueError('Unknown AST expr: %s' % ast)


def normalize(ast, immutables={}, trace=False):
    if trace: print("Input: %s" % ast)
    # a? b? c --> [a,b]?c
    merged = list(merge_and_expand_implications(ast))
    if trace: print("After 1st merge: %s" % merged)
    # || ( a? ( b ) c ) -> || ( ( a b ) c )
    unnested = list(replace_nested_implications(merged))
    if trace: print("After removing nested implications: %s"%unnested)
    # kill ^^ and ??
    boolean = list(replace_nary(unnested))
    if trace: print("Converted to boolean algebra: %s"%boolean)
    # || () -> False, && () -> True, || ( immutable_true bar ) -> True, etc.
    simplified_ast = simplify_with_immutables(boolean, immutables)
    if trace: print("Simplified ast: %s"%simplified_ast)
    # reduce again
    # a? b? c --> [a,b]?c
    reduced = list(merge_and_expand_implications(simplified_ast))
    if trace: print("End result after merging: %s"%reduced)
    return reduced


if __name__ == '__main__':
    normalize(list(parse_string(sys.argv[1])), trace=True)
