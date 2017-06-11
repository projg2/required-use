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
            # ?? ( a b c ... ) -> || ( ( a !b !c ... ) ( !a b !c ... ) ... ( !a !b !c ... !last ) )
            constraint = list(replace_nary(expr.constraint))
            result = []
            begin = []
            while len(constraint)>0:
                cur = constraint.pop(0)
                result.append(AllOfOperator(begin + [cur] + [negate(x) for x in constraint]))
                begin.append(negate(cur))
            # dont forget all disabled is ok
            result.append(AllOfOperator(begin))
            yield AnyOfOperator(result)
        elif isinstance(expr, ExactlyOneOfOperator):
            # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
            constraint = list(replace_nary(expr.constraint))
            m = list(replace_nary([AtMostOneOfOperator(constraint)]))
            yield AllOfOperator([AnyOfOperator(constraint), m])
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

def normalize(ast, trace=False):
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
    # reduce again
    # a? b? c --> [a,b]?c
    reduced = list(merge_and_expand_implications(boolean))
    print("End result after merging: %s"%reduced)
    return reduced

def sort_nary(ast, sort_key):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            yield Implication(expr.condition, list(sort_nary(expr.constraint, sort_key)))
        elif isinstance(expr, AllOfOperator):
            # no point in sorting all-of
            yield expr
        elif isinstance(expr, NaryOperator):
            # sort subexpressions first, if any
            constraint = list(sort_nary(expr.constraint, sort_key))
            constraint.sort(key=sort_key)
            yield expr.__class__(constraint)
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


if __name__ == '__main__':
    normalize(list(parse_string(sys.argv[1])), trace=True)
