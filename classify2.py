#!/usr/bin/env python
# classify variant that works on deduped entries (i.e. doesn't care about
# pkg) and is intended to print diffable output

import sys
from nsolve import solve, Cyclic, NeedTopoSort


def main(f):
    issues=[]

    for l in f.readlines():
        l = l.strip()
        try:
            solve(l)
        except Cyclic:
            issues.append('cyclic\t%s' % l)
        except NeedTopoSort:
            issues.append('need_topo_sort\t%s' % l)
        except Exception:
            issues.append('parse_error\t%s' % l)

    for x in sorted(issues):
        print(x)


if __name__ == '__main__':
    main(sys.stdin)
