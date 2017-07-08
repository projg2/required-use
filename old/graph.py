#!/usr/bin/env python

import sys
sys.path.insert(0, '..')

from flatten_implications import flatten_implications
from parser import (parse_string, Flag, Implication, NaryOperator)
from replace_nary import replace_nary, replace_allof


def get_edges_from_flat_ast(ast):
    for expr in ast:
        # skip stand-alone flags
        if isinstance(expr, Flag):
            continue
        elif isinstance(expr, Implication):
            assert(len(expr.constraint) == 1)
            for x in expr.condition:
                assert(isinstance(x, Flag))
                yield (x, expr.constraint[0])
        elif isinstance(expr, NaryOperator):
            raise ValueError('N-ary operators should be replaced already')
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


def get_nodes_from_flat_ast(ast):
    for expr in ast:
        # skip stand-alone flags
        if isinstance(expr, Flag):
            continue
        elif isinstance(expr, Implication):
            for x in expr.condition:
                yield x
            for x in expr.constraint:
                yield x
        elif isinstance(expr, NaryOperator):
            raise ValueError('N-ary operators should be replaced already')
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


def print_graph(ast):
    ast = list(ast)

    print('digraph {')
    for e in get_edges_from_flat_ast(ast):
        # dependee -> dependency
        print('\t"%s" -> "%s";' % e)

    nodes = frozenset(get_nodes_from_flat_ast(ast))
    for n in nodes:
        # link nodes with their negations (if both present)
        if n.enabled and n.negated() in nodes:
            print('\t"%s" -> "%s" [color=red];' % (n.negated(), n))
            print('\t"%s" -> "%s" [color=red];' % (n, n.negated()))
    print('}')


if __name__ == '__main__':
    print_graph(flatten_implications(replace_allof(replace_nary(parse_string(sys.argv[1])))))
