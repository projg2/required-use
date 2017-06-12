#!/usr/bin/env python

import sys
from nsolve import solve

def main(filename):
    f = open(filename, "r")
    parse_error={}
    good={}
    need_topo_sort={}
    cyclic={}

    for l in f.readlines():
        pkg,cons = l.split(' ', 1)
        solve(cons, pkg=pkg, parse_error=parse_error, good=good,
                need_topo_sort=need_topo_sort, cyclic=cyclic, reraise=False)

    print("Stats:")
    print("\tParse error: %i"%(len(parse_error)))
    print("\tGood: %i"%(len(good)))
    print("\tNeed topo sort: %i"%(len(need_topo_sort)))
    print("\tCyclic: %i"%(len(cyclic)))

    tp = parse_error
    for k in tp:
        print("%s: %s"%(k,tp[k]))

if __name__ == '__main__':
    main(*sys.argv[1:])
