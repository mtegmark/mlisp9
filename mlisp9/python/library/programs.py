"""MLISP programs for the functions of the countable models, in the calculator's syntax (definitions "X<prog>#", then the program).
Naturals: the nested pairs of the language. Integers: pairs {a,b} of naturals standing for a-b, kept in the canonical form
{n,0} or {0,n}, so that equal integers are equal pairs. Rationals: pairs {p,q} of canonical integers, q > 0, in lowest terms."""
from mlisp import Lang, num, val, Undefined
# ---- naturals (Table 1)
ONE   = "100c#";  SUCC = "↑0ic#";  NOT = ONE + "¬i01d#";  EQ = ONE + "eijiajafibjbf0d0dj01dd#"   # equality is a program, not a primitive
PLUS  = "+iib0jcfjd#"                               # if i then (i-1)+(j+1) else j
TIMES = PLUS + "*iibjfj+0d#";  MINUS = "-jibjbfid#";  LESS = ONE + "<jiibjbf1d0d#"
DIV   = LESS + MINUS + NOT + "%ij<iij-jfd#" + "Δij%¬#"
EVEN  = NOT + "Eiibf¬1d#"                                  # E(i): if i then not E(i-1) else 1
# ---- integers as pairs {a,b}
ZN = "Nibiac#"                                             # negation: swap
ZA = PLUS + "Aiaja+ibjb+c#"                                # {a+c, b+d}
ZS = PLUS + "Siajb+ibja+c#"                                # (a-b)-(c-d) = (a+d)-(b+c)
ZM = TIMES + "Miaja*ibjb*+iajb*ibja*+c#"                   # (ac+bd) - (ad+bc)
ZR = LESS + MINUS + "Riaib<0ibia-ciaib-0cd#"               # canonical form: {0,b-a} if a<b else {a-b,0}
ZL = PLUS + LESS + NOT + "Ljaib+iajb+<¬#"                  # a-b <= c-d  iff  not (c+b < a+d)
ZV = PLUS + DIV + "Viaib+jajb+iaib+Δjajb+01dd#"            # x | y: if |x| then Δ(|y|,|x|) else (y = 0)
ZBASE = ZA + ZR
# ---- rationals as pairs {p,q}: p a canonical integer, q a natural number >= 1, in lowest terms
MOD  = LESS + MINUS + "%ij<iij-jfd#"                       # i mod j
GCD  = MOD + "Gjjij%fid#"                                  # gcd(i,j): if j then gcd(j, i mod j) else i
QUO  = LESS + MINUS + "Qij<00ij-jfcd#"               # floor(i/j)
ZE_  = ZM + "⊙ij0cM#"                                      # integer i times natural j
QG   = PLUS + GCD + "giaaiab+ibG#"                         # gcd(|p|, q), with |{a,b}| = a + b
QY   = QUO + QG + "YiaaigQiabigQcibigQc#"                   # divide numerator parts and denominator by the gcd
QRED = QY                                         # reduce to lowest terms (the denominator is positive already)
QADD = ZE_ + ZA + ZR + TIMES + QRED + "⊕iajb⊙jaib⊙ARibjb*cY#"
QSUB = ZE_ + ZS + ZR + TIMES + QRED + "⊖iajb⊙jaib⊙SRibjb*cY#"
QMUL = ZM + TIMES + QRED + "⊗iajaMibjb*cY#"
QDIV = ZE_ + ZN + PLUS + TIMES + QRED + "⊘jabiajb⊙Niajb⊙dibjaajab+*cY#"   # x/y = p1 q2 / (q1 |p2|), negated when p2 < 0
QNEG = ZN + "⊝iaNibc#"
QLE  = ZE_ + ZL + "≼iajb⊙jaib⊙L#"
NLE  = LESS + NOT + "≤ji<¬#"
NDIV = DIV + "|jiΔ#"                                       # i divides j, on the positive integers
NMOD = EVEN + EQ + "~iEjEe#"
ZADD = ZA + ZR + "⊞ijAR#";  ZSUB = ZS + ZR + "⊟ijSR#";  ZMUL = ZM + ZR + "⊠ijMR#"
P = {
 ('N', '0'): "0",  ('N', "x'"): "0ic",  ('N', 'x+y'): PLUS + "ij+",  ('N', 'x\\cdot y'): TIMES + "ij*",
 ('nle', 'x\\le y'): NLE + "ij≤",
 ('divn', 'x\\mid y'): NDIV + "ij|",
 ('mod2', 'x\\sim y'): NMOD + "ij~",
 ('Z', '0'): "00c",  ('Z', 'x+y'): ZADD + "ij⊞",  ('Z', 'x-y'): ZSUB + "ij⊟",  ('Z', 'x\\cdot y'): ZMUL + "ij⊠",
 ('zs', '0'): "00c",  ('zs', "x'"): ZADD + "i00c0c⊞",  ('zs', '-x'): ZN + "iN",  ('zs', 'x+y'): ZADD + "ij⊞",  ('zs', 'x\\cdot y'): ZMUL + "ij⊠",
 ('zsub', 'x-y'): ZSUB + "ij⊟",
 ('zle', 'x\\le y'): ZL + "ijL",
 ('divz', 'x\\lesssim y'): ZV + "ijV",
 ('Q', '0'): ONE + "00c1c",  ('Q', '1'): ONE + "10c1c",  ('Q', '-x'): QNEG + "i⊝",
 ('Q', 'x+y'): QADD + "ij⊕",  ('Q', 'x\\cdot y'): QMUL + "ij⊗",  ('qle', 'x\\le y'): QLE + "ij≼",
}
RATIONAL = {'+': QADD + "ij⊕", '-': QSUB + "ij⊖", '*': QMUL + "ij⊗", '/': QDIV + "ij⊘", 'neg': QNEG + "i⊝", '<=': QLE + "ij≼"}
# what every symbol means (shown by the calculator and under the tableaus)
COMMENTS = {
 '1': ('one', 0), '2': ('two', 0), 'e': ('equal ({0,0} if i = j, else 0)', 2), '↑': ('successor', 1), '+': ('plus', 2), '*': ('times', 2), '-': ('minus (defined only for i ≥ j)', 2), '<': ('less than (i<j)', 2),
 '^': ('power', 2), '!': ('factorial', 1), '¬': ('not', 1), '&': ('and', 2), '∨': ('or', 2), 'Δ': ('i divisible by j', 2), 'P': ('i indivisible by all of 2..j', 2), 'Π': ('prime, for i >= 2', 1),
 'E': ('even', 1), '≤': ('less or equal', 2), '|': ('i divides j', 2), '~': ('same parity', 2),
 'N': ('integer negation: swap the parts', 1), 'A': ('integer addition partwise', 2), 'S': ('integer subtraction', 2), 'M': ('integer multiplication', 2),
 'R': ('reduce integer to canonical form (n,0) or (0,n)', 1), 'L': ('integer less or equal', 2), 'V': ('integer i divides j', 2), '⊞': ('integer addition, canonical', 2), '⊟': ('integer subtraction, canonical', 2), '⊠': ('integer multiplication, canonical', 2),
 '%': ('remainder of i by j', 2), 'G': ('greatest common divisor', 2), 'Q': ('quotient of i by j, rounded down', 2), '⊙': ('integer times natural', 2), 'g': ('gcd of |numerator| and denominator', 1),
 'Y': ('divide numerator and denominator by their gcd', 1),
 '⊕': ('addition of rationals', 2), '⊖': ('subtraction of rationals', 2), '⊗': ('multiplication of rationals', 2), '⊘': ('division of rationals', 2), '⊝': ('negation of a rational', 1), '≼': ('rational less or equal', 2),
}
def dedupe(prog):
    """Keep the first definition of each symbol (the pieces above repeat their prerequisites)."""
    parts = prog.split('#'); seen = set(); out = []
    for p in parts[:-1]:
        if p[0] in seen: continue
        seen.add(p[0]); out.append(p)
    return '#'.join(out + [parts[-1]])
P = {k: dedupe(v) for k, v in P.items()}; RATIONAL = {k: dedupe(v) for k, v in RATIONAL.items()}
NAT = ('N', 'aux', ["0"], [('N', "0ic")])
RULES = {
 'N':    [('S1', 'sort', ["0"], [('S1', "0ic")])],
 'nle':  [('S1', 'sort', ["0"], [('S1', "0ic")]), ('S2', 'sort', ["0", "00c"], [])],
 'mod2': [('S1', 'sort', ["0"], [('S1', "0ic")]), ('S2', 'sort', ["0", "00c"], [])],
 'divn': [('S1', 'sort', ["00c"], [('S1', "0ic")]), ('S2', 'sort', ["0", "00c"], [])],
 'Z':    [NAT, ('S1', 'sort', [], [('N', "i0c"), ('N', "0ic")])],
 'zs':   [NAT, ('S1', 'sort', [], [('N', "i0c"), ('N', "0ic")])],
 'zsub': [NAT, ('S1', 'sort', [], [('N', "i0c"), ('N', "0ic")])],
 'zle':  [NAT, ('S1', 'sort', [], [('N', "i0c"), ('N', "0ic")]), ('S2', 'sort', ["0", "00c"], [])],
 'divz': [NAT, ('S1', 'sort', [], [('N', "i0c"), ('N', "0ic")]), ('S2', 'sort', ["0", "00c"], [])],
 'Q':    [('Q+', 'aux', [ONE + "10c1c"], [('Q+', ZA + "iaiaib0cAac"), ('Q+', ZA + "iaib0cAibc")]), ('S1', 'sort', [ONE + "00c1c"], [('Q+', "i"), ('Q+', QNEG + "i⊝")])],
 'qle':  [('Q+', 'aux', [ONE + "10c1c"], [('Q+', ZA + "iaiaib0cAac"), ('Q+', ZA + "iaib0cAibc")]), ('S1', 'sort', [ONE + "00c1c"], [('Q+', "i"), ('Q+', QNEG + "i⊝")]), ('S2', 'sort', ["0", "00c"], [])],
}
def generate(mid, count):
    """The first `count` strings of every set of a countable model, in generation order: base strings in the order listed,
    then the rules applied in the order listed to the source set's elements in their generation order (breadth-first for
    a set that feeds itself); a string already produced is not produced again."""
    sets = {name: (kind, bases, rules) for name, kind, bases, rules in RULES[mid]}; out = {}
    def strings(name):
        if name in out: return out[name]
        kind, bases, rules = sets[name]; vals = []
        def add(v):
            if v not in vals: vals.append(v)
        for b in bases: add(run(b))
        selfrules = [(src, pr) for src, pr in rules if src == name]; others = [(src, pr) for src, pr in rules if src != name]
        if others:
            for src, _ in others: strings(src)
            n = 0
            while len(vals) < count and n < count * 4:
                for src, pr in others:
                    srcvals = out[src]
                    if n < len(srcvals): add(run(pr, srcvals[n]))
                n += 1
        if selfrules:
            k = 0
            while len(vals) < count and k < len(vals):
                for _, pr in selfrules: add(run(pr, vals[k]))
                k += 1
        out[name] = vals[:count]; return out[name]
    for name in sets: strings(name)
    return out
def factor(progs):
    """Lines for a tableau: each table as f_k = "sym" ≡ "def" (or f_k = "body"), every definition written once.
    Returns [(label, sym, text)]: label is 'f_k' or '' for a helper, sym the symbol or '', text the program text."""
    out = []; printed = set()
    for k, prog in enumerate(progs, 1):
        parts = prog.split('#'); defs, body = parts[:-1], parts[-1]
        sym = defs[-1][0] if defs else None
        named = sym is not None and body in (sym, 'i' + sym, 'ij' + sym, 'ijk' + sym)
        helpers = defs[:-1] if named else defs
        for d in helpers:
            if d[0] not in printed: out.append(('', d[0], d[1:])); printed.add(d[0])
        later = ''.join(progs[k:])
        if named and sym in later: out.append(('f_%d' % k, sym, defs[-1][1:])); printed.add(sym)
        elif named: out.append(('f_%d' % k, '', defs[-1][1:]))
        else: out.append(('f_%d' % k, '', body))
    return out
def run(prog, *args):
    """Evaluate a program with definitions; integer arguments are naturals, tuples are values of the language."""
    lang = Lang(); parts = prog.split('#'); body = parts[-1]
    ar = lambda pr: max([0] + [{'i': 1, 'j': 2, 'k': 3}[ch] for ch in pr if ch in 'ijk'])
    for p in parts[:-1]: lang.define(p[0], ar(p[1:]), p[1:])
    lang.define('@', ar(body), body)
    return lang.call('@', *[num(a) if isinstance(a, int) else a for a in args])
# encodings
def zpair(k): return (num(k), 0) if k >= 0 else (0, num(-k))
def zval(v): return val(v[0]) - val(v[1])
def qpair(p, q):
    from math import gcd
    g = gcd(abs(p), q); return (zpair(p // g), num(q // g))
def qval(v): return (zval(v[0]), val(v[1]))
from fractions import Fraction
def _fusc(n):
    a, b = 1, 0
    while n: 
        if n & 1: b += a
        else: a += b
        n >>= 1
    return b
CW = [Fraction(_fusc(n), _fusc(n + 1)) for n in range(1, 400)]           # positive rationals in Calkin-Wilf order
def qidx(r):
    r = Fraction(r)
    if r == 0: return 0
    n = CW.index(abs(r)) + 1; return 2*n - 1 if r > 0 else 2*n
def qofidx(n):
    if n == 0: return Fraction(0)
    r = CW[(n + 1)//2 - 1]; return r if n % 2 else -r
zidx = lambda k: 0 if k == 0 else (2*k - 1 if k > 0 else -2*k)      # tableau label of the integer k
zofidx = lambda n: 0 if n == 0 else ((n + 1)//2 if n % 2 else -(n//2))
if __name__ == '__main__':
    from fractions import Fraction
    ok = True
    def chk(name, prog, args, want):
        global ok
        try: got = run(prog, *args)
        except Undefined: got = 'undefined'
        if got != want: ok = False; print('MISMATCH', name, args, 'got', got, 'want', want)
    R = range(6)
    for x in R:
        chk("N x'", P[('N',"x'")], [x], num(x + 1))
        for y in R:
            chk('N +', P[('N','x+y')], [x, y], num(x + y)); chk('N *', P[('N','x\\cdot y')], [x, y], num(x * y))
            chk('nle', P[('nle','x\\le y')], [x, y], num(int(x <= y))); chk('mod2', P[('mod2','x\\sim y')], [x, y], num(int((x - y) % 2 == 0)))
            chk('divn', P[('divn','x\\mid y')], [x + 1, y + 1], num(int((y + 1) % (x + 1) == 0)))
    Z = range(-4, 5)
    chk('Z 0', P[('Z','0')], [], zpair(0))
    chk('zs 0', P[('zs','0')], [], zpair(0))
    for a in range(-3, 4): chk('zs succ', P[('zs',"x'")], [zpair(a)], zpair(a + 1)); chk('zs neg', P[('zs','-x')], [zpair(a)], zpair(-a))
    for a in Z:
        for b in Z:
            chk('Z +', P[('Z','x+y')], [zpair(a), zpair(b)], zpair(a + b)); chk('Z *', P[('Z','x\\cdot y')], [zpair(a), zpair(b)], zpair(a * b)); chk('Z -', P[('Z','x-y')], [zpair(a), zpair(b)], zpair(a - b))
            chk('zsub', P[('zsub','x-y')], [zpair(a), zpair(b)], zpair(a - b)); chk('zle', P[('zle','x\\le y')], [zpair(a), zpair(b)], num(int(a <= b)))
            chk('divz', P[('divz','x\\lesssim y')], [zpair(a), zpair(b)], num(int(b % a == 0 if a else b == 0)))
    for r in (Fraction(1), Fraction(1,2), Fraction(-1,2), Fraction(2), Fraction(1,3), Fraction(-3,2)): assert qofidx(qidx(r)) == r
    chk('Q 0', P[('Q','0')], [], qpair(0, 1)); chk('Q 1', P[('Q','1')], [], qpair(1, 1))
    Qs = [(p, q) for p in range(-3, 4) for q in range(1, 4)]
    for p1, q1 in Qs:
        r1 = Fraction(p1, q1); chk('Q neg', RATIONAL['neg'], [qpair(p1, q1)], qpair(-r1.numerator, r1.denominator))
        for p2, q2 in Qs:
            r2 = Fraction(p2, q2)
            for op, f in (('+', r1 + r2), ('-', r1 - r2), ('*', r1 * r2)):
                chk('Q ' + op, RATIONAL[op], [qpair(p1, q1), qpair(p2, q2)], qpair(f.numerator, f.denominator))
            if r2 != 0: f = r1 / r2; chk('Q /', RATIONAL['/'], [qpair(p1, q1), qpair(p2, q2)], qpair(f.numerator, f.denominator))
            chk('Q <=', RATIONAL['<='], [qpair(p1, q1), qpair(p2, q2)], num(int(r1 <= r2)))
    print('ALL PROGRAMS CORRECT' if ok else 'FAILURES')
    for k, v in list(P.items()) + [(('Q', k), v) for k, v in RATIONAL.items()]: print(k, len(v), v)
