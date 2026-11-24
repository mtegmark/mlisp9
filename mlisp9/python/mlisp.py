#!/usr/bin/env python3
"""MLISP in Python.

Values are binary trees over a single atom: 0 is the atom, (x, y) a pair.
A value is written as a raw string in reverse Polish over 0 and c: 0 pushes
the atom, c pairs the two most recent entries, so 0000ccc is {0,{0,{0,0}}},
the natural number 3. The raw string is the program that builds the value.

A program is a postfix string of one-character symbols:
  a  first part of a pair          b  second part of a pair
  c  combine two values into a pair
  d  decide: j if i is a pair, else k (only the chosen branch is evaluated)
  f  the function being defined (recursion)
  i j k  the arguments            0  the atom
plus symbols defined by writing  X<program>#  before the program. A program's
arity is 3, 2, 1 or 0 according to whether it mentions k, j, i or none of them.

Usage:  python3 mlisp.py [-t] '<definitions...program>' [i] [j] [k]
with the inputs as raw strings; -t loads Table 1 first. Example:
  python3 mlisp.py -t 'ij+' 0000ccc 00000cccc      ->  00000000ccccccc  (3 + 4 = 7)
"""
import sys
sys.setrecursionlimit(1000000)
BASE = {'a': 1, 'b': 1, 'c': 2, 'd': 3, '0': 0, 'i': 0, 'j': 0, 'k': 0}   # number of arguments
TABLE = ('100c#eijiajafibjbf0d0dj01dd#201c#↑0ic#-jibjbfid#+iib0jcfjd#*iibjfj+0d#^jijbfi*1d#!iiibf*1d#'
         '¬i01d#&ij10d0d#∨i1j10dd#<jiibjbf1d0d#%ij<iij-jfd#Δij%¬#PjbijΔ¬ijbf&1d#ΠiibP#')
defs = {}                                   # symbol -> (arity, parsed program)
class Undefined(Exception): pass

def arity(prog): return max([0] + [1 + 'ijk'.index(ch) for ch in prog if ch in 'ijk'])

def parse(prog, farity):                    # postfix string -> tree (symbol, arguments)
    stack = []
    for ch in prog:
        n = farity if ch == 'f' else BASE[ch] if ch in BASE else defs[ch][0]
        assert len(stack) >= n, 'symbol %s needs %d arguments in %r' % (ch, n, prog)
        args = stack[len(stack) - n:] if n else []
        del stack[len(stack) - n:]
        stack.append((ch, args))
    assert len(stack) == 1, 'ill-formed program %r' % prog
    return stack[0]

def ev(node, env, fdef):                    # evaluate with arguments env = [i, j, k]
    ch, args = node
    if ch == '0': return 0
    if ch in 'ijk': return env['ijk'.index(ch)]
    if ch == 'd': return ev(args[1] if ev(args[0], env, fdef) != 0 else args[2], env, fdef)
    v = [ev(x, env, fdef) for x in args]
    if ch in 'ab':
        if v[0] == 0: raise Undefined(ch + ' of 0')
        return v[0]['ab'.index(ch)]
    if ch == 'c': return (v[0], v[1])
    if ch == 'f': return ev(fdef, v, fdef)
    return ev(defs[ch][1], v, defs[ch][1])

def run(text, inputs=()):                   # definitions "X...#", then an optional program
    *ds, prog = text.replace(' ', '').replace('\n', '').split('#')
    for d in ds: defs[d[0]] = (arity(d[1:]), parse(d[1:], arity(d[1:])))
    if not prog: return None
    for pre in ['', 'i', 'ij', 'ijk'][:len(inputs) + 1]:    # a bare + is run as ij+
        try: tree = parse(pre + prog, arity(pre + prog)); break
        except AssertionError as e:
            if pre == 'ijk' or len(inputs) == len(pre): raise
    return ev(tree, list(inputs) + [0, 0, 0], tree)

def value(s):                               # raw string -> value
    stack = []
    for ch in s:
        assert ch == '0' or len(stack) >= 2, 'ill-formed value %r' % s
        stack.append(0 if ch == '0' else (stack.pop(-2), stack.pop()))
    assert len(stack) == 1, 'ill-formed value %r' % s
    return stack[0]

def raw(v): return '0' if v == 0 else raw(v[0]) + raw(v[1]) + 'c'   # value -> raw string

if __name__ == '__main__':
    a = sys.argv[1:]
    if a and a[0] == '-t': run(TABLE); a = a[1:]
    if not a: print(__doc__); sys.exit()
    try:
        r = run(a[0], [value(s) for s in a[1:]])
        print(raw(r) if r is not None else 'defined: ' + ' '.join(sorted(defs)))
    except Undefined as u: print('undefined:', u)
    except (AssertionError, KeyError) as e: print('error:', e)
