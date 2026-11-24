#!/usr/bin/env python3
"""A minimal interpreter for Max's MLISP (postfix, stack-parsed, lazily evaluated).
Atoms: 0. Lists: pairs. Numbers in unary: 0, 1={0,0}, n+1={0,n}. Truth: 0 false, nonzero (a list) true.
Base symbols: a (first part), b (second part), c (combine i,j -> {i,j}), d (decide: j if i is a list else k, lazy),
e (equal: {0,0} if i==j else 0), f (recursive call of the function being defined), i j k (arguments), 0.
A program is a postfix string; defined symbols expand to their own programs with their own i,j,k."""
import sys
sys.setrecursionlimit(1000000)
BASE = {'a': 1, 'b': 1, 'c': 2, 'd': 3, '0': 0, 'i': 0, 'j': 0, 'k': 0}
class Undefined(Exception): pass
class Lang:
    def __init__(self): self.defs = {}; self.arity = dict(BASE)
    def define(self, sym, arity, prog):
        self.defs[sym] = self.parse(prog, arity); self.arity[sym] = arity
    def parse(self, prog, farity):
        stack = []
        for ch in prog:
            n = farity if ch == 'f' else self.arity[ch]
            args = stack[-n:] if n else []
            if n: del stack[-n:]
            stack.append((ch, args))
        assert len(stack) == 1, 'ill-formed program %r (stack %d)' % (prog, len(stack))
        return stack[0]
    def ev(self, node, env, fname, fdef):
        ch, args = node
        if ch == '0': return 0
        if ch in 'ijk': return env['ijk'.index(ch)]
        if ch == 'd':
            cond = self.ev(args[0], env, fname, fdef)
            return self.ev(args[1] if cond != 0 else args[2], env, fname, fdef)
        vals = [self.ev(x, env, fname, fdef) for x in args]
        if ch == 'a':
            if vals[0] == 0: raise Undefined('a of 0')
            return vals[0][0]
        if ch == 'b':
            if vals[0] == 0: raise Undefined('b of 0')
            return vals[0][1]
        if ch == 'c': return (vals[0], vals[1])
        if ch == 'f': return self.ev(fdef, vals, fname, fdef)
        d = self.defs[ch]
        return self.ev(d, vals, ch, d)
    def call(self, sym, *args):
        d = self.defs[sym]; return self.ev(d, list(args), sym, d)
def num(n):
    v = 0
    for _ in range(n): v = (0, v)
    return v
def val(v):
    n = 0
    while v != 0: v = v[1]; n += 1
    return n
L = Lang()
TABLE = [('1', 0, '00c'), ('2', 0, '01c'), ('s', 1, '0ic'), ('-', 2, 'jibjbfid'), ('+', 2, 'iib0jcfjd'), ('*', 2, 'iibjfj+0d'),
         ('^', 2, 'jijbfi*1d'), ('!', 1, 'iiibf*1d'), ('n', 1, 'i01d'), ('&', 2, 'ij10d0d'), ('v', 2, 'i1j10dd'),
         ('<', 2, 'jiibjbf1d0d'), ('D', 2, 'iij<0ij-jfd1d'), ('P', 2, 'jbijDnijbf&1d'), ('p', 1, 'iibP')]
for sym, ar, prog in TABLE: L.define(sym, ar, prog)
if __name__ == '__main__':
    print('1 =', val(L.call('1')), ' 2 =', val(L.call('2')), ' s(4) =', val(L.call('s', num(4))))
    ok = True
    for x in range(0, 6):
        for y in range(0, 6):
            checks = {'+': x + y, '*': x * y, '<': int(x < y)}
            if x >= y: checks['-'] = x - y
            if y <= 3 and x <= 4: checks['^'] = x ** y
            if y > 0: checks['D'] = int(x % y == 0)
            for sym, want in checks.items():
                try: got = val(L.call(sym, num(x), num(y)))
                except Undefined as u: got = 'undefined (%s)' % u
                if got != want: ok = False; print('MISMATCH', sym, x, y, 'got', got, 'want', want)
    for x in range(0, 6):
        if val(L.call('!', num(x))) != __import__('math').factorial(x): ok = False; print('MISMATCH ! at', x)
    for x in range(0, 2):
        for y in range(0, 2):
            if val(L.call('&', num(x), num(y))) != (x and y): ok = False; print('MISMATCH &', x, y)
            if val(L.call('v', num(x), num(y))) != (x or y): ok = False; print('MISMATCH v', x, y)
        if val(L.call('n', num(x))) != (1 - x): ok = False; print('MISMATCH n', x)
    primes = [val(L.call('p', num(x))) for x in range(2, 14)]
    print('prime(2..13) =', primes, ' expected', [int(x in (2,3,5,7,11,13)) for x in range(2,14)]); print('prime(0), prime(1): undefined (b of 0)')
    try: L.call('-', num(1), num(2))
    except Undefined as u: print('1-2 is', 'undefined:', u)
    print('all arithmetic/logic checks passed' if ok else 'some checks FAILED')
