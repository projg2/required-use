#!/usr/bin/env python

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
            for x in expr.constraint:
                yield x
        elif isinstance(expr, NaryOperator):
            # replace subexpressions first, if any
            constraint = list(expr.constraint)
            for subexpr in constraint:
                if not isinstance(subexpr, Flag):
                    raise NotImplementedError('Nested operators not supported')
            # then replace the expression itself
            if isinstance(expr, AnyOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # || ( a b c ... ) -> [!b !c !...]? ( a )
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                if len(constraint) == 1:
                    yield constraint[0]
                else:
                    yield Implication([v.negated() for v in constraint[1:]], constraint[0:1])
            if isinstance(expr, AtMostOneOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # ?? ( a b c ... ) -> a? ( !b !c ... ) b? ( !c ... ) ...
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                while len(constraint) > 1:
                    k = constraint.pop(0)
                    yield Implication([k], [f.negated() for f in constraint])
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


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
    print(repr(list(replace_nary(parse_string(sys.argv[1])))))
