#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, NaryOperator,
        AllOfOperator)


def validate_ast(ast, in_nary=False):
    for expr in ast:
        if isinstance(expr, Flag):
            pass
        elif isinstance(expr, Implication):
            if in_nary:
                raise ValueError('Implication in n-ary operator')
            assert len(expr.condition) == 1
            assert isinstance(expr.condition[0], Flag)
            validate_ast(expr.constraint)
        elif isinstance(expr, AllOfOperator):
            raise ValueError('All-of operator forbidden')
        elif isinstance(expr, NaryOperator):
            if in_nary:
                raise ValueError('Nested n-ary operator!')
            validate_ast(expr.constraint, in_nary=expr.op)
        else:
            raise NotImplementedError('Unknown AST subexpr: %s' % expr)


if __name__ == '__main__':
    validate_ast(parse_string(sys.argv[1]))
