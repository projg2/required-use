#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, NaryOperator)
from replace_nary import replace_nary


def nested_implications(conditions, final_constraint):
    val = final_constraint
    for v in reversed(conditions):
        val = Implication(v, [val])
    return val


def flatten_implications(ast, current_implications=[]):
    for expr in ast:
        if isinstance(expr, Flag):
            yield nested_implications(current_implications, expr)
        elif isinstance(expr, Implication):
            for x in flatten_implications(expr.constraint,
                    current_implications + [expr.condition]):
                yield x
        elif isinstance(expr, NaryOperator):
            raise ValueError('N-ary operators should be replaced already')


if __name__ == '__main__':
    print(repr(list(flatten_implications(replace_nary(parse_string(sys.argv[1]))))))
