#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator)
from replace_nary import sort_nary, replace_nary
from flatten_implications import flatten_implications


def validate_constraint(flags, constraint):
    for expr in constraint:
        if isinstance(expr, Flag):
            if flags[expr.name] != expr.enabled:
                return False
        elif isinstance(expr, Implication):
            if flags[expr.condition.name] == expr.condition.enabled:
                if not validate_constraint(flags, expr.constraint):
                    return False
        elif isinstance(expr, AnyOfOperator):
            if not any(validate_constraint(flags, [x]) for x in expr.constraint):
                return False
        elif isinstance(expr, ExactlyOneOfOperator):
            if list(validate_constraint(flags, [x]) for x in expr.constraint).count(True) != 1:
                return False
        elif isinstance(expr, AtMostOneOfOperator):
            if list(validate_constraint(flags, [x]) for x in expr.constraint).count(True) > 1:
                return False

    return True


class ImmutabilityError(Exception):
    def __init__(self, flag_name):
        super(ImmutabilityError, self).__init__('Immutability error: value of %s mismatches' % flag_name)
        self.flag_name = flag_name


class InfiniteLoopError(Exception):
    def __init__(self):
        super(InfiniteLoopError, self).__init__('Constraints cause infinite loop')


def apply_solving(flags, constraint, immutable_flags, negate=False):
    for expr in constraint:
        if isinstance(expr, Flag):
            want = expr.enabled
            if negate:
                want = not want
            if immutable_flags.get(expr.name, want) != want:
                raise ImmutabilityError(expr.name)
            flags[expr.name] = want
        elif isinstance(expr, Implication):
            if flags[expr.condition.name] == expr.condition.enabled:
                apply_solving(flags, expr.constraint, immutable_flags, negate)
        elif isinstance(expr, AnyOfOperator):
            if not validate_constraint(flags, [expr]):
                apply_solving(flags, expr.constraint[0:1], immutable_flags, negate)
        elif isinstance(expr, ExactlyOneOfOperator):
            apply_solving(flags, [AnyOfOperator(expr.constraint)], immutable_flags, negate)
            apply_solving(flags, [AtMostOneOfOperator(expr.constraint)], immutable_flags, negate)
        elif isinstance(expr, AtMostOneOfOperator):
            if not validate_constraint(flags, [expr]):
                past_first = False
                for x in expr.constraint:
                    if validate_constraint(flags, [x]):
                        if past_first:
                            apply_solving(flags, [x], immutable_flags, not negate)
                        else:
                            past_first = True


def get_all_flags(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
            continue
        if isinstance(expr, Implication):
            yield expr.condition
        for x in get_all_flags(expr.constraint):
            yield x


class immutability_sort(object):
    def __init__(self, immutable_flags):
        self.immutable_flags = immutable_flags

    def __call__(self, key):
        # forced = 0 [go first]
        # normal = 1
        # masked = 2 [go last]
        if key.name not in self.immutable_flags:
            return 1
        if self.immutable_flags[key.name]:
            return 0
        else:
            return 2


def do_solving(sorted_flags, inp_flags, ast, immutable_flags, verbose=True):
    prev_states = [inp_flags]
    out_flags = dict(inp_flags)
    while True:
        try:
            try:
                apply_solving(out_flags, ast, immutable_flags)
            except ImmutabilityError as e:
                if verbose:
                    print('\033[31m [unsolvable: immutable %s mismatched]' % e.flag_name, end='')
                raise
            else:
                valid_now = validate_constraint(out_flags, ast)
                if verbose:
                    if valid_now:
                        print('\033[32m', end='')
                    else:
                        print('\033[33m', end='')
                    for f in sorted_flags:
                        if out_flags[f] != prev_states[-1][f]:
                            print(' \033[1m%d\033[22m' % out_flags[f], end='')
                        else:
                            print(' %d' % out_flags[f], end='')

                if not valid_now:
                    # compare with previous states
                    for x in prev_states:
                        if out_flags == x:
                            if verbose:
                                print('\033[31m [unsolvable due to loop]', end='')
                            raise InfiniteLoopError()
        finally:
            if verbose:
                print('\033[0m')

        if valid_now:
            return out_flags

        prev_states.append(dict(out_flags))
        if verbose:
            print('%*s |' % (len(sorted_flags) * 2, ''), end='')


def print_solutions(ast, immutable_flags):
    # sort n-ary expressions
    ast = sort_nary(ast, immutability_sort(immutable_flags))
    ast = list(ast)
    print(ast)
    print()

    all_flags = frozenset(x.name for x in get_all_flags(ast))

    # print flag names, vertically
    sorted_flags = sorted(all_flags)
    no_flags = len(sorted_flags)
    y_max = max(len(x) for x in sorted_flags)
    for y in range(0, y_max):
        for f in sorted_flags + ['|'] + sorted_flags:
            print(' %s' % (f[len(f)-y_max+y] if y >= y_max - len(f) else ' '), end='')
        print('')

    # solve for input = 000... to 111...
    for inpv in range(0, 2**no_flags):
        inp_flags = {}
        for x in range(0, no_flags):
            inp_flags[sorted_flags[no_flags-x-1]] = bool(inpv & (2**x))

        skip = False
        for k, v in immutable_flags.items():
            # skip mismatches for immutables
            if inp_flags[k] != v:
                skip = True
                break
        if skip:
            continue

        for f in sorted_flags:
            if f in immutable_flags:
                print('\033[33m', end='')
            print(' %d' % inp_flags[f], end='')
            if f in immutable_flags:
                print('\033[0m', end='')
        print(' |', end='')

        if validate_constraint(inp_flags, ast):
            print('\033[32m', end='')
            for f in sorted_flags:
                print(' %d' % inp_flags[f], end='')
            print(' (==)\033[0m')
        else:
            try:
                ret = do_solving(sorted_flags, inp_flags, ast, immutable_flags)
            except (ImmutabilityError, InfiniteLoopError):
                pass


def parse_immutables(s):
    ret = {}
    for x in s.split():
        if x.startswith('!'):
            ret[x[1:]] = False
        else:
            ret[x] = True
    return ret


def main(constraint_str, immutable_flag_str=''):
    cons = parse_string(constraint_str)
    nary = replace_nary(cons)
    flat = list(flatten_implications(nary))
    print(flat)
    for i in range(len(flat)):
        for j in range(i+1,len(flat)):
            cb = flat[j].can_break(flat[i])
            if cb:
                print("[%s] can break [%s]"%(flat[j],flat[i]))


if __name__ == '__main__':
    main(*sys.argv[1:])
