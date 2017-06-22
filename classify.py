#!/usr/bin/env python

import sys
from nsolve import solve, Cyclic, NeedTopoSort


def main(filename):
    f = open(filename, "r")
    parse_error=[]
    good=[]
    need_topo_sort=[]
    cyclic=[]

    for l in f.readlines():
        pkg,cons = l.split(' ', 1)
        try:
            solve(cons)
        except Cyclic:
            cyclic.append((pkg, cons))
        except NeedTopoSort:
            need_topo_sort.append((pkg, cons))
        except Exception:
            parse_error.append((pkg, cons))
        else:
            good.append((pkg, cons))

    print("Stats:")
    print("\tParse error: %i"%(len(parse_error)))
    print("\tGood: %i"%(len(good)))
    print("\tNeed topo sort: %i"%(len(need_topo_sort)))
    print("\tCyclic: %i"%(len(cyclic)))

    tp = cyclic
    for v in tp:
        print("%s: %s" % v)


if __name__ == '__main__':
    main(*sys.argv[1:])
