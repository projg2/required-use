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


def split_common_prefix(c1, c2):
    # if two paths have common prefix (using node-wise comparison),
    # split it into a separate list
    pfx = []
    c1 = list(c1)
    c2 = list(c2)
    while c1 and c2 and c1[0] is c2[0]:
        pfx.append(c1.pop(0))
        del c2[0]
    return (pfx, c1, c2)


def conditions_can_coexist(c1, c2):
    # ignore common prefix as it will never conflict (the solver does
    # not backtrace to the top node)
    pfx, c1, c2 = split_common_prefix(c1, c2)
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


class BackAlterationVerifyError(Exception):
    def __init__(self, cj, ej, ci, ei):
        super(BackAlterationVerifyError, self).__init__(
            "Expression (%s => %s) may enable the condition of (%s => %s)"
            % (cj, ej, ci, ei))


def verify_back_alteration(flats):
    # for every pair of paths (Pi, Pj) so that i < j,
    # back alteration occurs if both:
    # 1. Ej is in the non-common part of Ci,
    # 2. Ci can occur simultaneously with Cj.
    for i in range(len(flats)):
        ci, ei = flats[i]
        for j in range(i+1, len(flats)):
            cj, ej = flats[j]
            pfx, cis, cjs = split_common_prefix(ci, cj)
            if ej in cis and conditions_can_coexist(cis, cjs):
                raise BackAlterationVerifyError(cj, ej, ci, ei)


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
    verify_back_alteration(flats)
    print('Back alteration ok.')


if __name__ == '__main__':
    main(*sys.argv[1:])
