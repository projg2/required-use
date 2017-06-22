#!/usr/bin/env python

import sys

from parser import (parse_string, Flag, Implication, AllOfOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator,
        NaryOperator)
from replace_nary import sort_nary
from to_impl import convert_to_implications


def validate_constraint(flags, constraint):
    for expr in constraint:
        if isinstance(expr, Flag):
            if flags[expr.name] != expr.enabled:
                return False
        elif isinstance(expr, Implication):
            if validate_constraint(flags, expr.condition):
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
        elif isinstance(expr, AllOfOperator):
            if not all(validate_constraint(flags, [x]) for x in expr.constraint):
                return False
        else:
            raise ValueError('Unknown AST expr: %s' % expr)

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
            if validate_constraint(flags, expr.condition):
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
        elif isinstance(expr, AllOfOperator):
            if not negate:
                apply_solving(flags, expr.constraint, immutable_flags, negate)
            else:
                apply_solving(flags, expr.constraint[0:1], immutable_flags, negate)
        else:
            raise ValueError('Unknown AST expr: %s' % expr)


def get_all_flags(ast):
    for expr in ast:
        if isinstance(expr, Flag):
            yield expr
            continue
        if isinstance(expr, Implication):
            for x in get_all_flags(expr.condition):
                yield x
        for x in get_all_flags(expr.constraint):
            yield x


class immutability_sort(object):
    def __init__(self, immutable_flags):
        self.immutable_flags = immutable_flags

    def __call__(self, key):
        # support recurrence into n-ary operators
        if isinstance(key, NaryOperator):
            for x in key.constraint:
                if self(x) != 1:
                    return self(x)
            else:
                return 1

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


def add_subcond(impl, out):
    if len(impl.condition) > 1:
        out.append(Implication(impl.condition[1:], impl.constraint))
    else:
        out.extend(impl.constraint)


def combine_common_prefixes(ast):
    assert(isinstance(ast, list))
    ast = list(ast)
    out = []

    while ast:
        first = ast.pop(0)
        if isinstance(first, Flag):
            out.append(first)
        elif isinstance(first, Implication):
            assert(first.condition)

            # last one? no way to combine it
            if not ast:
                out.append(first)
                continue

            # do they have a common prefix? if not, do not even start
            # merging
            assert(ast[0].condition)
            if not ast[0].condition[0] is first.condition[0]:
                out.append(first)
                continue

            # merge on condition[0]
            repl = Implication(first.condition[0:1], [])
            add_subcond(first, repl.constraint)

            while ast:
                assert(ast[0].condition)
                if ast[0].condition[0] is first.condition[0]:
                    add_subcond(ast.pop(0), repl.constraint)
                else:
                    break

            # since we were able to successfully merge on cond[0],
            # attempt cond[1]... recursively
            repl.constraint = combine_common_prefixes(repl.constraint)
            out.append(repl)
        else:
            raise AssertionError('Unexpected AST node: %s' % first)

    return out


def print_solutions(constraint_str, immutable_str):
    # sort n-ary expressions
    immutable_flags = parse_immutables(immutable_str)
    ast = sort_nary(parse_string(constraint_str),
            immutability_sort(immutable_flags))
    ast = list(ast)
    print(ast)
    print()

    # implication variant
    # we need to combine common prefixes to get equivalent results
    impl_ast = combine_common_prefixes(
            convert_to_implications(constraint_str, immutable_str))

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
            else:
                ret_impl = do_solving(sorted_flags, inp_flags,
                        impl_ast, immutable_flags, verbose=False)
                if ret != ret_impl:
                    print('%*s |\033[31m' % (len(sorted_flags) * 2, ''), end='')
                    for f in sorted_flags:
                        if ret_impl[f] != ret[f]:
                            print(' \033[1m%d\033[22m' % ret_impl[f], end='')
                        else:
                            print(' %d' % ret_impl[f], end='')
                    print(' [mismatch between implication and basic form]\033[0m')



def parse_immutables(s):
    ret = {}
    for x in s.split():
        if x.startswith('!'):
            ret[x[1:]] = False
        else:
            ret[x] = True
    return ret


def main(constraint_str, immutable_flag_str=''):
    print_solutions(constraint_str, immutable_flag_str)


if __name__ == '__main__':
    main(*sys.argv[1:])
