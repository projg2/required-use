#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, NaryOperator)
from replace_nary import (replace_nary, sort_nary)


def validate_constraint(flags, constraint):
    for expr in constraint:
        if isinstance(expr, Flag):
            if flags[expr.name] != expr.enabled:
                return False
        elif isinstance(expr, Implication):
            if flags[expr.condition.name] == expr.condition.enabled:
                if not validate_constraint(flags, expr.constraint):
                    return False
        elif isinstance(expr, NaryOperator):
            raise NotImplementedError('N-ary operators not implemented')

    return True


class ConvergenceError(Exception):
    def __init__(self, flag_name):
        super(ConvergenceError, self).__init__('Convergence error: conflicting values for %s' % flag_name)
        self.flag_name = flag_name


class ImmutabilityError(Exception):
    def __init__(self, flag_name):
        super(ImmutabilityError, self).__init__('Immutability error: value of %s mismatches' % flag_name)
        self.flag_name = flag_name


def apply_solving(flags, constraint, conflict_dict, immutable_flags):
    for expr in constraint:
        if isinstance(expr, Flag):
            if immutable_flags.get(expr.name, expr.enabled) != expr.enabled:
                raise ImmutabilityError(expr.name)
            if conflict_dict.setdefault(expr.name, expr.enabled) != expr.enabled:
                raise ConvergenceError(expr.name)
            flags[expr.name] = expr.enabled
        elif isinstance(expr, Implication):
            if flags[expr.condition.name] == expr.condition.enabled:
                apply_solving(flags, expr.constraint, conflict_dict, immutable_flags)
        elif isinstance(expr, NaryOperator):
            raise NotImplementedError('N-ary operators not implemented')


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


def print_solutions(ast, immutable_flags):
    # sort n-ary expressions
    ast = sort_nary(ast, immutability_sort(immutable_flags))
    # convert to implication form
    ast = replace_nary(ast)
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
            prev_states = [inp_flags]
            out_flags = dict(inp_flags)
            conflict_dict = {}
            while True:
                try:
                    apply_solving(out_flags, ast, conflict_dict, immutable_flags)
                except ConvergenceError as e:
                    print('\033[31m [unsolvable: convergence error on %s]' % e.flag_name, end='')
                    valid_now = True
                except ImmutabilityError as e:
                    print('\033[31m [unsolvable: immutable %s mismatched]' % e.flag_name, end='')
                    valid_now = True
                else:
                    valid_now = validate_constraint(out_flags, ast)
                    if valid_now:
                        print('\033[32m', end='')
                    else:
                        print('\033[33m', end='')
                    for f in sorted_flags:
                        print(' %d' % out_flags[f], end='')

                    if not valid_now:
                        # compare with previous states
                        for x in prev_states:
                            if out_flags == x:
                                print('\033[31m [unsolvable due to loop]', end='')
                                # abort
                                valid_now = True
                                break

                print('\033[0m')

                if valid_now:
                    break

                prev_states.append(dict(out_flags))
                print('%*s |' % (no_flags * 2, ''), end='')


def parse_immutables(s):
    ret = {}
    for x in s.split():
        if x.startswith('!'):
            ret[x[1:]] = False
        else:
            ret[x] = True
    return ret


def main(constraint_str, immutable_flag_str=''):
    print_solutions(parse_string(constraint_str),
            parse_immutables(immutable_flag_str))


if __name__ == '__main__':
    main(*sys.argv[1:])
