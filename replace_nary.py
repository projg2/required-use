#!/usr/bin/env python

import itertools
import sys

from parser import (parse_string, Flag, Implication, NaryOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator,
        AllOfOperator)


def replace_nary(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            yield Implication(expr.condition, list(replace_nary(expr.constraint)))
        elif isinstance(expr, AllOfOperator):
            if expr.enabled:
                for x in expr.constraint:
                    yield x
            else:
                # !&& [a b..] -> [a b..]? => [!a !b..]
                yield Implication(expr.constraint,
                        [x.negated() for x in expr.constraint])
        elif isinstance(expr, NaryOperator):
            # replace subexpressions first, if any
            constraint = list(expr.constraint)
            for subexpr in constraint:
                if not isinstance(subexpr, Flag) and not isinstance(subexpr, AllOfOperator):
                    raise NotImplementedError('Nested operators not supported')
            # then replace the expression itself
            if isinstance(expr, AnyOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # || ( a b c ... ) -> [!a !b !c !...]? ( a )
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                if len(constraint) == 1:
                    if isinstance(constraint[0], AllOfOperator):
                        for x in constraint[0].constraint:
                            yield x
                    else:
                        yield constraint[0]
                else:
                    yield Implication([v.negated() for v in constraint], constraint[0:1])
            if isinstance(expr, AtMostOneOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # ?? ( a b c ... ) -> a? ( !b !c ... ) b? ( !c ... ) ...
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                while len(constraint) > 1:
                    k = constraint.pop(0)
                    yield Implication([k], [f.negated() for f in constraint])
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
                        yield Implication(expr.condition, [j])
                else:
                    yield Implication(expr.condition, [i])
        else:
            yield expr

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
    print(repr(list(replace_allof(replace_nary(parse_string(sys.argv[1]))))))
