#!/usr/bin/env python

import re
import sys


flag_re = re.compile(r'^[A-Za-z0-9][A-Za-z0-9+_@-]*$')

def object_in_allowed_set(allowed, o):
    for i in allowed:
        if isinstance(o, i): return True
    return False

def all_object_in_allowed_set(allowed, l):
    all_good=True
    for i in l:
        if not object_in_allowed_set(allowed, i):
            return False
    return True

class Flag(object):
    def __init__(self, name, enabled=True):
        if not flag_re.match(name):
            raise ValueError('Invalid flag name: %s' % name)
        self.name = name
        self.enabled = enabled

    def __repr__(self):
        return '%s%s' % ('' if self.enabled else '!', self.name)

    def __hash__(self):
        return hash(repr(self))

    def __eq__(self, other):
        return (self.name == other.name and self.enabled == other.enabled)

    def __ne__(self, other):
        return not self.__eq__(other)

    def negated(self):
        return Flag(self.name, not self.enabled)


class Implication(object):
    _allowed_nest = [ Flag ]

    def __init__(self, condition, constraint, strict=False, stricter=False):
        assert(isinstance(condition, list))
        assert(isinstance(constraint, list))
        if strict:
            assert(len(constraint)==1)
        if stricter:
            assert(all_object_in_allowed_set(self._allowed_nest, condition))
            assert(all_object_in_allowed_set(self._allowed_nest, constraint))
            ncons = []
            for i in constraint:
                if i not in condition and i not in ncons:
                    ncons.append(i)
            constraint = ncons
            nc = []
            for c in condition:
                if c not in nc:
                    nc.append(c)
            condition = nc

            for i in constraint:
                if i.negated() in constraint:
                    raise ValueError('Constraint %s is impossible'%constraint)

            for i in condition:
                if i.negated() in condition:
                    condition = []
                    constraint = []

        self.condition = condition
        self.constraint = constraint

    def __repr__(self):
        if len(self.constraint)>1:
            return '%s? => %s' % (self.condition, self.constraint)
        else:
            return '%s? => %s' % (self.condition, self.constraint[0])

    def can_break(self, other):
        # "p_1? p_2? ... p_n? ( q_1 ... q_m )" and "p'_1? p'_2? ... p'_{n'}?
        # ( q'_1 ... q'_{m'} )", assuming the first is satisfied, when can solving
        # the 2nd break the 1st?

        # Symbols used for sanity:
        # c1 -- self.condition; c2 -- other.condition
        # r1 -- self.constraint; r2 -- other.constraint

        # trivially true == condition does not match => constraint is not applied

        # 1.The conditions are compatible: No p_i is the negation of a p'_j.
        for c2 in other.condition:
            for c1 in self.condition:
                if c2 == c1.negated(): return False
        # 2.Solving the 1st does not make the 2nd trivially true: No q_i is
        # the negation of a p'_j.
        for r2 in other.constraint:
            for c1 in self.condition:
                if r2 == c1.negated(): return False
        # 3.Solving the 2nd does not make the 1st trivially true afterwards: No
        # p_i is the negation of a q'_j.
        for c2 in other.condition:
            for r1 in self.constraint:
                if c2 == r1.negated(): return False
        # 4.Solving the 2nd does break the 1st assumption: (A q_i is
        # the negation of a q_'j) or (a q'_j is some p_i and one of q_1 ... q_m
        #  might be false).
        for r1 in self.constraint:
            for r2 in other.constraint:
                if r1 == r2.negated(): return True
            for c2 in other.condition:
                if c2 == r1:
                    # If {q_i} is a subset of {p'_i}U{q'_i} then the 1st is trivially
                    # true if we apply the 2nd, so it does not break it.
                    trivial=True
                    for r2 in other.constraint:
                        if r2 not in self.condition and r2 not in self.constraint:
                            trivial=False
                    return not trivial
        return False

    def fill_can_break(self, list_impl):
        self.edges = []
        for i in list_impl:
            if i == self: continue
            if self.can_break(i): self.edges.append(i)

    def __lt__(self, other): return str(self) < str(other)

    def __eq__(self, other):
        if not isinstance(other, Implication): return False
        if len(self.constraint) != len(other.constraint): return False
        if len(self.condition) != len(other.condition): return False
        for i in range(len(self.constraint)):
            if self.constraint[i] != other.constraint[i]: return False
        for i in range(len(self.condition)):
            if self.condition[i] != other.condition[i]: return False
        return True

class NaryOperator(object):
    def __init__(self, op, constraint):
        assert op in ('||', '??', '^^', '&&')
        self.op = op
        self.constraint = constraint

    def __repr__(self):
        return '%s %s' % (self.op, self.constraint)

def flatten_operator(l, operator):
    r = []
    for c in l:
        if isinstance(c, operator):
            r += flatten_operator(c.constraint, operator)
        else:
            r.append(c)
    return r

class AnyOfOperator(NaryOperator):
    def __init__(self, constraint):
        rc = flatten_operator(list(constraint), AnyOfOperator)
        super(AnyOfOperator, self).__init__('||', rc)

    def __eq__(self, other):
        if not isinstance(other, AnyOfOperator): return False
        if len(self.constraint) != len(other.constraint): return False
        for i in range(len(self.constraint)):
            if self.constraint[i] != other.constraint[i]: return False
        return True

class ExactlyOneOfOperator(NaryOperator):
    def __init__(self, constraint):
        super(ExactlyOneOfOperator, self).__init__('^^', constraint)


class AtMostOneOfOperator(NaryOperator):
    def __init__(self, constraint):
        super(AtMostOneOfOperator, self).__init__('??', constraint)


class AllOfOperator(NaryOperator):
    def __init__(self, constraint, enabled=True):
        rc = flatten_operator(list(constraint), AllOfOperator)
        super(AllOfOperator, self).__init__('&&', rc)
        self.enabled = enabled

    def __repr__(self):
        return '%s%s' % ('' if self.enabled else '!',
                super(AllOfOperator, self).__repr__())

    def __eq__(self, other):
        if not isinstance(other, AllOfOperator): return False
        if len(self.constraint) != len(other.constraint): return False
        for i in range(len(self.constraint)):
            if self.constraint[i] != other.constraint[i]: return False
        return True

    def negated(self):
        return AllOfOperator(self.constraint, not self.enabled)


def parse_tokens(l, nested=False):
    while l:
        # implication or n-ary operator
        if l[0] in ('||', '??', '^^', '(') or l[0].endswith('?'):
            if '(' not in l[0:2]:
                raise ValueError('"%s" must be followed by "("' % l[0])
            k = l.pop(0)
            if k != '(':
                l.pop(0)

            if k == '||':
                yield AnyOfOperator(list(parse_tokens(l, True)))
            elif k == '??':
                yield AtMostOneOfOperator(list(parse_tokens(l, True)))
            elif k == '^^':
                yield ExactlyOneOfOperator(list(parse_tokens(l, True)))
            elif k == '(':
                yield AllOfOperator(list(parse_tokens(l, True)))
            else:
                # strip ?
                assert k.endswith('?')
                k = k[:-1]
                if k.startswith('!'):
                    kf = Flag(k[1:], False)
                else:
                    kf = Flag(k)
                yield Implication([kf], list(parse_tokens(l, True)))
                
        # end of group
        elif l[0] == ')':
            if not nested:
                raise ValueError('Stray ")" at top level')
            l.pop(0)
            return
        # plain flag
        else:
            if l[0].startswith('!'):
                yield Flag(l[0][1:], False)
            else:
                yield Flag(l[0])
            l.pop(0)

    if nested:
        raise ValueError('Missing terminating ")"')


def parse_string(s):
    # tokenize & parse
    return parse_tokens(s.split())


if __name__ == '__main__':
    print(repr(list(parse_string(sys.argv[1]))))
