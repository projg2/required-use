#!/usr/bin/env python

import sys

from parser import parse_string
from replace_nary import sort_nary, replace_nary, replace_allof, merge_and_expand_implications, replace_nested_implications
from replace_nary import normalize
from to_impl import to_implication


from flatten_implications import flatten_implications
from toposort import toposort, toposort_flatten


def parse_immutables(s):
    ret = {}
    for x in s.split():
        if x.startswith('!'):
            ret[x[1:]] = False
        else:
            ret[x] = True
    return ret


def solve(constraint_str, immutable_flag_str='', pkg='', parse_error={},
        good={}, need_topo_sort={}, cyclic={}, reraise=True, print_status=False):
    cons = list(parse_string(constraint_str))
    immutable_flags = parse_immutables(immutable_flag_str)
    n = normalize(cons, immutable_flags)
    try:
        flat = []
        for e in n:
            flat+=to_implication(e)
    except:
        parse_error[pkg]=constraint_str
        if reraise: raise
        return
    for i in flat:
        i.fill_can_break(flat)
    try:
        x = toposort_flatten({ str(x) : {str(e) for e in x.edges} for x in flat })
    except:
        cyclic[pkg]=constraint_str
        if(print_status): print("'%s' is cyclic"%constraint_str)
        if reraise: raise
        return

    for i in range(len(flat)):
        for j in range(i+1,len(flat)):
            cb = flat[j].can_break(flat[i])
            if cb:
                need_topo_sort[pkg] = constraint_str
                if(print_status): print("'%s' needs sorting"%constraint_str)
                return
    if(print_status): print("'%s' is all good"%constraint_str)
    good[pkg]=constraint_str


def basic_test():
    m={}
    solve("a? ( b ) b? ( a )", good=m, reraise=False)
    assert(len(m)>0)
    m={}
    solve("a? ( !b ) b? ( a )", good=m, reraise=False)
    assert(len(m)>0)
    m={}
    solve("a? ( b ) c? ( a )", need_topo_sort=m, reraise=False)
    assert(len(m)>0)

def test():
    basic_test()

if __name__ == '__main__':
    if(len(sys.argv)<=1): test()
    else: solve(*sys.argv[1:], print_status=True)
