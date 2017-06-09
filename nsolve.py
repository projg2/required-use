#!/usr/bin/env python

import sys

from parser import parse_string
from replace_nary import sort_nary, replace_nary, replace_allof
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
        good={}, need_topo_sort={}, cyclic={}, reraise=True):
    cons = parse_string(constraint_str)
    nary = replace_allof(replace_nary(cons))
    immutable_flags = parse_immutables(immutable_flag_str)
    if immutable_flags:
        raise NotImplementedError('Immutables are not implemented yet')
    try:
        flat = list(flatten_implications(nary))
    except:
        parse_error[pkg]=constraint_str
        if reraise: raise
        return
    for i in flat:
        i.fill_can_break(flat)
    try:
        x = toposort_flatten({ x : set(x.edges) for x in flat })
    except:
        cyclic[pkg]=constraint_str
        if reraise: raise
        return

    for i in range(len(flat)):
        for j in range(i+1,len(flat)):
            cb = flat[j].can_break(flat[i])
            if cb:
                need_topo_sort[pkg] = constraint_str
                return
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
    else: solve(*sys.argv[1:])
