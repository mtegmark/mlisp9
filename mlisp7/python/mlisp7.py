#!/usr/bin/env python3
"""mLISP in Python: the seven-symbol language 0 a b c d e f.

Values are binary trees over a single atom: 0 is the atom, (x, y) a pair.
A value is written as a raw string in reverse Polish over 0 and c: 0 pushes
the atom, c pairs the two most recent entries, so 0000ccc is {0,{0,{0,0}}},
the natural number 3. The raw string is the program that builds the value.

A program is a postfix string over seven one-character symbols:
  0  the atom                       e  the argument of the function being evaluated
  a  first part of a pair           b  second part of a pair
  c  combine two values into a pair
  d  decide: the 2nd of three if the 1st is a pair, else the 3rd (lazy)
  f  the function being defined, applied to one popped value (recursion)
plus symbols defined by writing  X<program>#  before the program. A defined
symbol pops one value (the e of its body) if its body mentions e or f, else none.

Notation, not language: a binary function takes the pair {x,y}, a ternary one
{x,{y,z}}; the accessor macros i j k stand for the parts of that tuple (in a
text mentioning k: i = ea, j = eba, k = ebb; in one mentioning i or j: i = ea,
j = eb) and are expanded textually before anything is parsed.

Usage:  python3 mlisp7.py [-t] '<definitions...program>' [x] [y] [z]
with the inputs as raw strings, packed into the one argument e = x, {x,y} or
{x,{y,z}}; -t loads Table 1 first. Example:
  python3 mlisp7.py -t 'ijc+' 0000ccc 00000cccc      ->  00000000ccccccc  (3 + 4 = 7)
"""
import sys
sys.setrecursionlimit(1000000)
BASE = {'a': 1, 'b': 1, 'c': 2, 'd': 3, '0': 0, 'e': 0, 'f': 1}   # number of values popped
TABLE = ('100c#=ijiajacfibjbcf0d0dj01dd#201c#↑0ec#-jibjbcfid#+iib0jccfjd#*iibjcfjc+0d#^jijbcfic*1d#!eeebfc*1d#'
         '¬e01d#&ij10d0d#∨i1j10dd#<jiibjbcf1d0d#%ijc<iijc-jcfd#Δijc%¬#PjbijcΔ¬ijbcfc&1d#ΠeebcP#')
defs = {}                                   # symbol -> (values popped, parsed program)
class Undefined(Exception): pass

def tuple_arity(src):                       # the macro notation: k ternary, i or j binary, e or f unary, else a constant
    n = 3 if 'k' in src else 2 if 'i' in src or 'j' in src else 1 if 'e' in src or 'f' in src else 0
    assert not (n >= 2 and 'e' in src), 'mixes e with the macros i j k: %r' % src
    return n

def expand(src):                            # macro notation -> pure mLISP
    n = tuple_arity(src)
    if n == 3: return src.replace('j', 'eba').replace('k', 'ebb').replace('i', 'ea')
    if n == 2: return src.replace('j', 'eb').replace('i', 'ea')
    return src

def parse(prog):                            # postfix string -> tree (symbol, arguments)
    stack = []
    for ch in prog:
        n = BASE[ch] if ch in BASE else defs[ch][0]
        assert len(stack) >= n, 'symbol %s needs %d argument%s in %r' % (ch, n, 's' if n > 1 else '', prog)
        args = stack[len(stack) - n:] if n else []
        del stack[len(stack) - n:]
        stack.append((ch, args))
    assert len(stack) == 1, 'ill-formed program %r' % prog
    return stack[0]

def ev(node, arg, fdef):                    # evaluate with the argument e = arg; f stands for fdef
    ch, args = node
    if ch == '0': return 0
    if ch == 'e':
        if arg is None: raise Undefined('no argument e was supplied')
        return arg
    if ch == 'd': return ev(args[1] if ev(args[0], arg, fdef) != 0 else args[2], arg, fdef)
    v = [ev(x, arg, fdef) for x in args]
    if ch in 'ab':
        if v[0] == 0: raise Undefined(ch + ' of 0')
        return v[0]['ab'.index(ch)]
    if ch == 'c': return (v[0], v[1])
    if ch == 'f': return ev(fdef, v[0], fdef)
    body = defs[ch][1]
    return ev(body, v[0] if v else None, body)

def pack(vals):                             # the inputs x, y, z as the one argument: x, {x,y} or {x,{y,z}}
    vals = list(vals)
    if len(vals) <= 1: return vals[0] if vals else None
    if len(vals) == 2: return (vals[0], vals[1])
    return (vals[0], (vals[1], vals[2]))

def run(text, inputs=()):                   # definitions "X...#", then an optional program
    *ds, prog = text.replace(' ', '').replace('\n', '').split('#')
    for d in ds:
        p = expand(d[1:]); defs[d[0]] = (1 if 'e' in p or 'f' in p else 0, parse(p))
    if not prog: return None
    prog = expand(prog)
    for pre in ['', 'e'][:len(inputs) + 1]:  # a bare + is run as e+
        try: tree = parse(pre + prog); break
        except AssertionError:
            if pre == 'e' or not inputs: raise
    return ev(tree, pack(inputs), tree)

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
