#!/usr/bin/env python

from parser import (Flag, Implication, NaryOperator,
        AnyOfOperator, ExactlyOneOfOperator, AtMostOneOfOperator,
        AllOfOperator)

from replace_nary import negate, merge_and_expand_implications

def merge(cond, cons):
    if isinstance(cond, Flag):
        return [ Implication([cond]+c.condition, c.constraint, strict=True, stricter=True) for c in cons ]
    elif isinstance(cond, AnyOfOperator):
        r = []
        for c in cond.constraint:
            r+=merge(c,cons)
        return list(merge_and_expand_implications(r))
    elif isinstance(cond, AllOfOperator):
        if len(cond.constraint)<=0: return cons
        return list(merge_and_expand_implications(merge(cond.constraint[0],
            merge(AllOfOperator(cond.constraint[1:]),cons))))
    else:
        raise ValueError('Invalid operator in %s'%cond)

def to_implication(expr):
    if isinstance(expr, Flag):
        return [ Implication([],[expr], strict=True, stricter=True) ]
    elif isinstance(expr, Implication):
        l = []
        for x in expr.constraint:
            l+=to_implication(x)
        return [ Implication(expr.condition + c.condition, c.constraint,
            strict=True, stricter=True) for c in l ]
    elif isinstance(expr, AnyOfOperator):
        f = expr.constraint.pop(0)
        if len(expr.constraint) > 0:
            return list(merge_and_expand_implications(merge(negate(AnyOfOperator(expr.constraint)), to_implication(f))))
        else: return list(merge_and_expand_implications(to_implication(f)))
    elif isinstance(expr, AllOfOperator):
        r = []
        for i in expr.constraint:
            r+=to_implication(i)
        return list(merge_and_expand_implications(r))
    else:
         raise ValueError('Invalid operator in %s'%expr)

def check_equal(s, expected):
    from replace_nary import normalize
    from parser import parse_string
    m = list(normalize(list(parse_string(s))))
    r = []
    for e in m:
        r+=to_implication(e)
    assert len(r) == len(expected)
    for i in range(len(r)):
        assert r[i] == expected[i]

def selftest():
    check_equal('|| ( a b )', [ Implication([Flag('b').negated()],[Flag('a')])])
    check_equal('?? ( a b )',
        [ Implication([Flag('a')],[Flag('b').negated()]) ])
    check_equal('|| ( a b c? ( d ) )',
        [ Implication([Flag('b').negated(), Flag('c').negated()],[Flag('a')]),
          Implication([Flag('b').negated(), Flag('d').negated()],[Flag('a')])])
    check_equal('a b? ( c )',
        [ Implication([],[Flag('a')]),
          Implication([Flag('b')],[Flag('c')])])
    check_equal('^^ ( a b )',
        [ Implication([Flag('b').negated()],[Flag('a')]),
          Implication([Flag('a')], [Flag('b').negated()])])

if __name__ == '__main__':
    from replace_nary import normalize
    from parser import parse_string
    import sys
    if len(sys.argv) <= 1:
        selftest()
        exit(0)
    m = normalize(list(parse_string(sys.argv[1])))
    print("Normalized: %s"%m)
    print("List of implications:")
    for i in m:
        print("  %s"%(to_implication(i)))

