#!/usr/bin/env python

import sys

from flatten_implications import flatten_implications
from parser import (parse_string, Flag, Implication, NaryOperator)
from replace_nary import replace_nary


def get_edges_for_nested_implications(impl):
    conditions = set()
    v = impl
    while isinstance(v, Implication):
        assert(len(v.constraint) == 1)
        assert(len(v.condition) == 1)
        conditions.add(v.condition[0])
        v = v.constraint[0]
    for c in conditions:
        yield (c, v)


def get_edges_from_flat_ast(ast):
    for expr in ast:
        # skip stand-alone flags
        if isinstance(expr, Flag):
            continue
        elif isinstance(expr, Implication):
            for e in get_edges_for_nested_implications(expr):
                yield e
        elif isinstance(expr, NaryOperator):
            raise ValueError('N-ary operators should be replaced already')


def get_nodes_for_nested_implications(impl):
    v = impl
    while isinstance(v, Implication):
        assert(len(v.constraint) == 1)
        assert(len(v.condition) == 1)
        yield v.condition[0]
        v = v.constraint[0]
    yield v


def get_nodes_from_flat_ast(ast):
    for expr in ast:
        # skip stand-alone flags
        if isinstance(expr, Flag):
            continue
        elif isinstance(expr, Implication):
            for n in get_nodes_for_nested_implications(expr):
                yield n
        elif isinstance(expr, NaryOperator):
            raise ValueError('N-ary operators should be replaced already')


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
    print_graph(flatten_implications(replace_nary(parse_string(sys.argv[1]))))
