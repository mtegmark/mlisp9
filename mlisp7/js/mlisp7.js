// mLISP: the seven-symbol language 0 a b c d e f of mlisp_lean.pdf, Section 2 (the arity-<=1 fragment of MLISP with the argument spelled e).
// Values are binary trees over the single atom 0. A program is a postfix string: 0 pushes the atom, e the argument of the function being
// evaluated; a, b take the first and second part of a pair; c pairs two values; d decides (the 2nd of three if the 1st is a pair, else the
// 3rd; only the chosen branch is evaluated); f calls the function being defined on one popped value (recursion).
// A definition "X<program>#" names a program; the symbol X pops one value (which becomes the e of its body) if the body mentions e or f, else none.
// Numbers are unary nested pairs: 0, 1 = {0,0}, 2 = {0,{0,0}}, n+1 = {0,n}. Truth: 0 is false, any pair is true.
// Notation (not language): a binary function takes the flat pair {x,y}, a ternary one {x,{y,z}}. The accessor macros i j k abbreviate the
// parts of that tuple and are expanded textually before anything is parsed: a text mentioning k is ternary (i = ea, j = eba, k = ebb), one
// mentioning i or j binary (i = ea, j = eb). The stored definitions are pure mLISP.
window.MLISP7 = (function(){
  const BASE = {a:1, b:1, c:2, d:3, '0':0, e:0, f:1};   // how many values each symbol pops
  const MACROS = 'ijk';
  const defs = {};            // symbol -> {src (as written, macros included), prog (pure mLISP), arity (0 or 1: what it pops), tuple (0..3: the shape of its argument), tree, comment}
  const STEP_LIMIT = 20000000;
  class Undefined extends Error {}
  const norm = s => s.replace(/∗/g, '*').replace(/−/g, '-');
  // the macro notation: k makes a ternary body, i or j a binary one, e or f a unary one, anything else a constant
  function tupleArity(src){ const n = src.includes('k') ? 3 : (src.includes('i') || src.includes('j')) ? 2 : (src.includes('e') || src.includes('f')) ? 1 : 0;
    if (n >= 2 && src.includes('e')) throw new Error('"' + src + '" mixes e with the macros i j k: write the argument either as e or through i, j, k');
    return n; }
  function expand(src, n){ if (n === undefined) n = tupleArity(src);
    if (n >= 3) return src.replace(/j/g, 'eba').replace(/k/g, 'ebb').replace(/i/g, 'ea');
    if (n === 2) return src.replace(/j/g, 'eb').replace(/i/g, 'ea');
    return src; }
  function arityOf(sym){ if (sym in BASE) return BASE[sym]; if (sym in defs) return defs[sym].arity; throw new Error('unknown symbol "' + sym + '"'); }
  function parse(prog){
    const stack = []; parse.ignored = [];
    for (const ch of prog){
      if (ch === ' ') continue;
      if (!(ch in BASE || ch in defs)){ if (!parse.ignored.includes(ch)) parse.ignored.push(ch); continue; }   // undefined symbols are ignored, but reported
      const n = arityOf(ch);
      if (stack.length < n) throw new Error('symbol "' + ch + '" needs ' + n + ' argument' + (n>1?'s':'') + ' but only ' + stack.length + ' available in "' + prog + '"');
      const args = n ? stack.splice(stack.length - n, n) : [];
      stack.push({ch, args});
    }
    if (stack.length === 0 && parse.ignored.length) throw new Error('nothing to run: the symbol' + (parse.ignored.length>1?'s ':' ') + parse.ignored.join(', ') + ' ' + (parse.ignored.length>1?'are':'is') + ' not defined (load the table\'s definitions, or define ' + (parse.ignored.length>1?'them':'it') + ' with "X<program>#")');
    if (stack.length !== 1) throw new Error('program "' + prog + '" leaves ' + stack.length + ' values on the stack (it should leave one)');
    return stack[0];
  }
  let steps = 0;
  function ev(node, arg, fdef){           // arg: the value of e; fdef: the tree f stands for
    if (++steps > STEP_LIMIT) throw new Error('stopped after ' + STEP_LIMIT + ' steps (not terminating?)');
    const ch = node.ch, args = node.args;
    if (ch === '0') return 0;
    if (ch === 'e'){ if (arg === undefined) throw new Undefined('argument e not supplied'); return arg; }
    if (ch === 'd'){ const cond = ev(args[0], arg, fdef); return ev(cond !== 0 ? args[1] : args[2], arg, fdef); }
    const vals = args.map(x => ev(x, arg, fdef));
    if (ch === 'a'){ if (vals[0] === 0) throw new Undefined('a of 0'); return vals[0][0]; }
    if (ch === 'b'){ if (vals[0] === 0) throw new Undefined('b of 0'); return vals[0][1]; }
    if (ch === 'c') return [vals[0], vals[1]];
    if (ch === 'f') return ev(fdef, vals[0], fdef);
    const d = defs[ch]; return ev(d.tree, vals.length ? vals[0] : undefined, d.tree);
  }
  function equal(x, y){ if (x === 0 || y === 0) return x === y; return equal(x[0], y[0]) && equal(x[1], y[1]); }
  function define(sym, src, comment){ sym = norm(sym); src = norm(src);
    if (sym in BASE) throw new Error('"' + sym + '" cannot be redefined: 0 a b c d e f are the symbols of the language');
    if (MACROS.includes(sym)) throw new Error('"' + sym + '" cannot be defined: i j k are the accessor macros (i = ea, j = eb or eba, k = ebb)');
    const tuple = tupleArity(src), prog = expand(src, tuple); const tree = parse(prog); const arity = /[ef]/.test(prog) ? 1 : 0;
    defs[sym] = {src, prog, arity, tuple, tree, comment: comment || ''}; return defs[sym]; }
  // A program that starts by needing its argument, such as "Π" or "+", is run on the supplied input: "eΠ", "e+".
  function complete(prog, haveArg){
    let err = null;
    for (const pre of haveArg ? ['', 'e'] : ['']){ try { parse(pre + prog); return pre + prog; } catch (e){ if (!err) err = e; if (!/needs .* argument/.test(e.message)) throw e; } }
    throw err;
  }
  function run(prog, arg){
    prog = norm(prog); const pure = expand(prog); const full = complete(pure, arg !== undefined); const tree = parse(full); steps = 0;
    const result = ev(tree, arg, tree); run.last = full; run.ignored = parse.ignored.slice(); return result;
  }
  // the inputs x, y, z as the one argument e: x, {x,y} or {x,{y,z}} (a missing component is 0)
  function pack(vals, n){ const v = k => vals[k] === undefined ? 0 : vals[k];
    if (n <= 0) return undefined; if (n === 1) return vals[0]; if (n === 2) return [v(0), v(1)]; return [v(0), [v(1), v(2)]]; }
  // how many inputs a program takes: the macros decide (k: three, i or j: two); a program written with e takes the filled inputs as they are;
  // a bare defined symbol takes the tuple its definition expects; a closed program that parses on its own takes none
  function packCount(prog, filled){ prog = norm(prog); const n = tupleArity(prog); if (n >= 2) return n; if (n === 1) return filled;
    try { parse(prog); return 0; } catch (e){ if (!/needs .* argument/.test(e.message)) return filled; }
    for (const ch of prog){ if (ch in defs){ if (defs[ch].arity) return defs[ch].tuple; continue; } if (ch in BASE && BASE[ch]) return filled; }
    return filled; }
  // values <-> text
  function num(n){ let v = 0; for (let t = 0; t < n; t++) v = [0, v]; return v; }
  function asNumber(v){ let n = 0; while (v !== 0){ if (!(v instanceof Array) || v[0] !== 0) return null; v = v[1]; n++; } return n; }
  function show(v){ return v === 0 ? '0' : '{' + show(v[0]) + ',' + show(v[1]) + '}'; }
  function showRaw(v){ return v === 0 ? '0' : showRaw(v[0]) + showRaw(v[1]) + 'c'; } // the value as the program that builds it
  function showList(v){ if (v === 0) return '[]'; const items = []; while (v !== 0){ items.push(v[0] === 0 ? '0' : showList(v[0])); v = v[1]; } return '[' + items.join(',') + ']'; }
  function parseValue(s){
    s = s.replace(/\s+/g, '');
    if (s === '') return undefined;
    if (/^\d+$/.test(s)) return num(parseInt(s, 10));
    if (/^[{}]+$/.test(s)){ // a bare bracket string is read as a Dyck word: the atom is the empty string and the pair {x,y} is '{' x '}' y, so {}{}{} is 3
      let pos = 0; function dyck(){ const items = []; while (pos < s.length && s[pos] === '{'){ pos++; items.push(dyck()); if (s[pos] !== '}') throw new Error('unbalanced brackets in the input'); pos++; } let v = 0; for (let i = items.length - 1; i >= 0; i--) v = [items[i], v]; return v; }
      const v = dyck(); if (pos !== s.length) throw new Error('unbalanced brackets in the input'); return v; }
    if (/^[0c|]+$/.test(s) && s.length > 1){ // raw form: reverse Polish over 0 and c, i.e. the program that builds the value (| is accepted for c)
      const st = []; for (const ch of s){ if (ch === '0') st.push(0); else { if (st.length < 2) throw new Error('c needs two entries on the stack'); const y = st.pop(), x = st.pop(); st.push([x, y]); } }
      if (st.length !== 1) throw new Error('a raw string must leave exactly one value on the stack'); return st[0]; }
    if (/^[\[\]0,]+$/.test(s)){ // list form: [x1,...,xn] = {x1,{x2,...{xn,0}}}, with 0 or [] for the atom
      let pos = 0; function item(){ if (s[pos] === '0'){ pos++; return 0; } if (s[pos] !== '[') throw new Error('bad list syntax'); pos++; const items = []; while (pos < s.length && s[pos] !== ']'){ items.push(item()); if (s[pos] === ',') pos++; else if (s[pos] !== ']') throw new Error('bad list syntax'); } if (s[pos] !== ']') throw new Error('unbalanced [ ] in the input'); pos++; let v = 0; for (let i = items.length - 1; i >= 0; i--) v = [items[i], v]; return v; }
      const v = item(); if (pos !== s.length) throw new Error('bad list syntax'); return v; }
    let pos = 0;
    function val(){
      if (s[pos] === '0'){ pos++; return 0; }
      if (s[pos] === '{'){ pos++; const x = val(); if (s[pos] !== ',') throw new Error('expected "," at position ' + pos + ' of the input'); pos++; const y = val(); if (s[pos] !== '}') throw new Error('expected "}" at position ' + pos + ' of the input'); pos++; return [x, y]; }
      if (/\d/.test(s[pos])){ let m = ''; while (pos < s.length && /\d/.test(s[pos])) m += s[pos++]; return num(parseInt(m, 10)); }
      throw new Error('cannot read the input at position ' + pos + ': "' + s.slice(pos, pos + 8) + '"');
    }
    const v = val(); if (pos !== s.length) throw new Error('unexpected text after the input value: "' + s.slice(pos) + '"'); return v;
  }
  // "X<prog>#" definitions followed by an optional program to run on the argument arg
  function submit(text, arg){
    const out = {defined: [], result: undefined};
    let rest = norm(text.replace(/\s+/g, ''));
    while (rest.includes('#')){
      const cut = rest.indexOf('#'); const chunk = rest.slice(0, cut); rest = rest.slice(cut + 1);
      if ([...chunk].length < 2) throw new Error('a definition needs a symbol and a program before "#"');
      const sym = [...chunk][0]; define(sym, chunk.slice(sym.length)); out.defined.push(sym);
    }
    if (rest.length) out.result = run(rest, arg);
    return out;
  }
  // Table 1 in mLISP (Table 5 of mlisp_lean.pdf; every row verified against its MLISP original by gen_mlisp7.py). Equality is = since e is the argument.
  const TABLE = [['1','00c','one, true'],['=','ijiajacfibjbcf0d0dj01dd','equal: {0,0} if i = j, else 0'],['2','01c','two'],['↑','0ec','successor'],['-','jibjbcfid','minus, undefined for i < j'],['+','iib0jccfjd','plus'],['*','iibjcfjc+0d','times'],['^','jijbcfic*1d','power'],['!','eeebfc*1d','factorial'],['¬','e01d','not'],['&','ij10d0d','and'],['∨','i1j10dd','or'],['<','jiibjbcf1d0d','less than (i<j)'],['%','ijc<iijc-jcfd','remainder of i by j'],['Δ','ijc%¬','i divisible by j'],['P','jbijcΔ¬ijbcfc&1d','i indivisible by all of 2..j'],['Π','eebcP','prime, for i >= 2']];
  function loadTable(){ for (const [s, p, c] of TABLE) define(s, p, c); }
  function loadLibrary(lib, comments){ submit(lib, undefined); for (const k of Object.keys(defs)) if (comments[k] && !defs[k].comment) defs[k].comment = comments[k]; }
  function clear(){ for (const k of Object.keys(defs)) delete defs[k]; }
  return {defs, define, run, submit, parse, expand, tupleArity, pack, packCount, loadLibrary, num, asNumber, show, showRaw, showList, parseValue, loadTable, clear, TABLE, Undefined, BASE, MACROS};
})();
