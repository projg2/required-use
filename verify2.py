#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, NaryOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator)
from replace_nary import sort_nary
from solve import immutability_sort, parse_immutables
from to_flat3 import flatten3
from validate_ast import validate_ast_passthrough


class ImmutabilityVerifyError(Exception):
    def __init__(self, conditions, effect, expected):
        super(ImmutabilityVerifyError, self).__init__(
            "Expression (%s => %s) can alter immutable flag (expected: %s)"
            % (conditions, effect, expected))


def verify_immutability(flats, immutables):
    # for every path, if C can be true, E must not alter immutables
    for c, e in flats:
        for ci in c:
            # if Ci is in immutables, and it evaluates to false,
            # the rule will never apply; if it is not in immutables,
            # we assume it can apply
            if immutables.get(ci.name, ci.enabled) != ci.enabled:
                break
        else:
            if immutables.get(e.name, e.enabled) != e.enabled:
                raise ImmutabilityVerifyError(c, e, e.enabled)


def conditions_can_coexist(c1, c2):
    # C1 and C2 can occur simultaneously unless C2 contains a negation
    # of any member of C1 (the condition is symmetric)
    for ci in c1:
        if ci.negated() in c2:
            return False
    return True


class ConflictVerifyError(Exception):
    def __init__(self, c1, c2, e1):
        super(ConflictVerifyError, self).__init__(
            "Expression (%s => %s) can conflict with (%s => %s)"
            % (c1, e1, c2, e1.negated()))


def verify_conflicts(flats):
    # for every unique pair of paths, conflicts occurs if both:
    # 1. E1 = !E2,
    # 2. C1 can occur simultaneously with C2.
    for i in range(len(flats)):
        c1, e1 = flats[i]
        for j in range(i+1, len(flats)):
            c2, e2 = flats[j]
            if e1 == e2.negated() and conditions_can_coexist(c1, c2):
                raise ConflictVerifyError(c1, c2, e1)


def main(constraint_str, immutable_str=''):
    immutables = parse_immutables(immutable_str)
    ast = sort_nary(validate_ast_passthrough(parse_string(constraint_str)),
            immutability_sort(immutables))
    flats = list(flatten3(ast))

    print('Flat items:')
    for i, v in enumerate(flats):
        print('%02d. %s' % (i+1, v))
    print()

    verify_immutability(flats, immutables)
    print('Immutability ok.')
    verify_conflicts(flats)
    print('Conflicts ok.')


if __name__ == '__main__':
    main(*sys.argv[1:])
