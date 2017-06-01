#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, NaryOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator)


def nested_negations(constraint, final_constraint):
    val = final_constraint
    for v in reversed(constraint):
        val = Implication(v.negated(), [val])
    return val


def replace_nary(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            yield Implication(expr.condition, list(replace_nary(expr.constraint)))
        elif isinstance(expr, NaryOperator):
            # replace subexpressions first, if any
            constraint = list(replace_nary(expr.constraint))
            for subexpr in constraint:
                if not isinstance(subexpr, Flag):
                    raise NotImplementedError('Nested operators not supported')
            # then replace the expression itself
            if isinstance(expr, AnyOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # || ( a b c ... ) -> !b? ( !c? ( ...? ( a ) ) )
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                yield nested_negations(constraint[1:], constraint[0])
            if isinstance(expr, AtMostOneOfOperator) or isinstance(expr, ExactlyOneOfOperator):
                # ?? ( a b c ... ) -> a? ( !b !c ... ) b? ( !c ... ) ...
                # ^^ ( a b c ... ) -> || ( a b c ... ) ?? ( a b c ... )
                while len(constraint) > 1:
                    k = constraint.pop(0)
                    yield Implication(k, [f.negated() for f in constraint])


def sort_nary(ast, sort_key):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
        elif isinstance(expr, Implication):
            yield Implication(expr.condition, list(sort_nary(expr.constraint, sort_key)))
        elif isinstance(expr, NaryOperator):
            # sort subexpressions first, if any
            constraint = list(sort_nary(expr.constraint, sort_key))
            constraint.sort(key=sort_key)
            yield expr.__class__(constraint)


if __name__ == '__main__':
    print(repr(list(replace_nary(parse_string(sys.argv[1])))))
