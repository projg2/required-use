#!/usr/bin/env python

import sys

from parser import parse_string, Implication
#from to_impl import convert_to_implications
from to_flat3 import flatten3
from toposort import toposort, toposort_flatten
from validate_ast import validate_ast_passthrough


class Cyclic(Exception):
    pass


class NeedTopoSort(Exception):
    pass


def solve(constraint_str, immutable_flag_str='', print_status=False):
    #flat = convert_to_implications(constraint_str,immutable_flag_str)
    flat = []
    ast = validate_ast_passthrough(parse_string(constraint_str))
    for x, y in flatten3(ast):
        flat.append(Implication(x, [y]))
    for i in flat:
        i.fill_can_break(flat)
    try:
        x = toposort_flatten({ str(x) : {str(e) for e in x.edges} for x in flat })
    except:
        if print_status:
            print("'%s' is cyclic" % constraint_str)
            return
        else:
            raise Cyclic()

    for i in range(len(flat)):
        for j in range(i+1,len(flat)):
            cb = flat[j].can_break(flat[i])
            if cb:
                if print_status:
                    print("'%s' needs sorting" % constraint_str)
                    return
                else:
                    raise NeedTopoSort()

    if print_status:
        print("'%s' is all good"%constraint_str)


def basic_test():
    solve("a? ( b ) b? ( a )")
    solve("a? ( !b ) b? ( a )")
    try:
        solve("a? ( b ) c? ( a )")
    except NeedTopoSort:
        pass
    else:
        raise AssertionError("'a? ( b ) c? ( a )' did not raise NeedTopoSort")


def test():
    basic_test()


if __name__ == '__main__':
    if(len(sys.argv)<=1): test()
    else: solve(*sys.argv[1:], print_status=True)
