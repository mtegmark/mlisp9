// MLISP: Max Tegmark's minimal postfix language. Programs are strings of single-character symbols in reverse Polish order.
// Base symbols: a, b (first and second part of a pair), c (combine into a pair), d (decide: j if i is a list, else k; lazy),
// f (the function being defined, recursion), i j k (arguments), 0 (the only atom).
// Numbers are unary nested pairs: 0, 1 = {0,0}, 2 = {0,{0,0}}, n+1 = {0,n}. Truth: 0 is false, any list is true.
// A definition "X<program>#" binds the symbol X to the program; its arity is the highest argument letter it uses.
window.MLISP = (function(){
  const BASE = {a:1, b:1, c:2, d:3, '0':0, i:0, j:0, k:0};
  const defs = {};            // symbol -> {prog, arity, tree}
  const STEP_LIMIT = 20000000;
  class Undefined extends Error {}
  function arityOf(sym, farity){ if (sym === 'f') return farity; if (sym in BASE) return BASE[sym]; if (sym in defs) return defs[sym].arity; throw new Error('unknown symbol "' + sym + '"'); }
  function inferArity(prog){ let a = 0; for (const ch of prog){ if (ch === 'i') a = Math.max(a, 1); if (ch === 'j') a = Math.max(a, 2); if (ch === 'k') a = Math.max(a, 3); } return a; }
  function parse(prog, farity){
    const stack = []; parse.ignored = [];
    for (const ch of prog){
      if (ch === ' ') continue;
      if (!(ch === 'f' || ch in BASE || ch in defs)){ if (!parse.ignored.includes(ch)) parse.ignored.push(ch); continue; }   // undefined symbols are ignored, but reported
      const n = arityOf(ch, farity);
      if (stack.length < n) throw new Error('symbol "' + ch + '" needs ' + n + ' argument' + (n>1?'s':'') + ' but only ' + stack.length + ' available in "' + prog + '"');
      const args = n ? stack.splice(stack.length - n, n) : [];
      stack.push({ch, args});
    }
    if (stack.length === 0 && parse.ignored.length) throw new Error('nothing to run: the symbol' + (parse.ignored.length>1?'s ':' ') + parse.ignored.join(', ') + ' ' + (parse.ignored.length>1?'are':'is') + ' not defined (load the table\'s definitions, or define ' + (parse.ignored.length>1?'them':'it') + ' with "X<program>#")');
    if (stack.length !== 1) throw new Error('program "' + prog + '" leaves ' + stack.length + ' values on the stack (it should leave one)');
    return stack[0];
  }
  let steps = 0;
  function ev(node, env, fdef){
    if (++steps > STEP_LIMIT) throw new Error('stopped after ' + STEP_LIMIT + ' steps (not terminating?)');
    const ch = node.ch, args = node.args;
    if (ch === '0') return 0;
    if (ch === 'i' || ch === 'j' || ch === 'k'){ const v = env['ijk'.indexOf(ch)]; if (v === undefined) throw new Undefined('argument ' + ch + ' not supplied'); return v; }
    if (ch === 'd'){ const cond = ev(args[0], env, fdef); return ev(cond !== 0 ? args[1] : args[2], env, fdef); }
    const vals = args.map(x => ev(x, env, fdef));
    if (ch === 'a'){ if (vals[0] === 0) throw new Undefined('a of 0'); return vals[0][0]; }
    if (ch === 'b'){ if (vals[0] === 0) throw new Undefined('b of 0'); return vals[0][1]; }
    if (ch === 'c') return [vals[0], vals[1]];
    if (ch === 'f') return ev(fdef, vals, fdef);
    const d = defs[ch]; return ev(d.tree, vals, d.tree);
  }
  function equal(x, y){ if (x === 0 || y === 0) return x === y; return equal(x[0], y[0]) && equal(x[1], y[1]); }
  function define(sym, prog, comment){ sym = sym.replace(/∗/g, '*').replace(/−/g, '-'); prog = prog.replace(/∗/g, '*').replace(/−/g, '-'); const arity = inferArity(prog); const tree = parse(prog, arity); defs[sym] = {prog, arity, tree, comment: comment || ''}; return defs[sym]; }
  // A program that starts by needing arguments, such as "Π" or "+", is run on the supplied inputs: "iΠ", "ij+".
  function complete(prog, inputs){
    const given = inputs.filter(v => v !== undefined).length;
    const tries = ['', 'i', 'ij', 'ijk'].slice(0, given + 1);
    let err = null;
    for (const pre of tries){ try { parse(pre + prog, inferArity(pre + prog)); return pre + prog; } catch (e){ if (!err) err = e; if (!/needs .* argument/.test(e.message)) throw e; } }
    throw err;
  }
  function run(prog, inputs){
    prog = prog.replace(/∗/g, '*').replace(/−/g, '-'); const full = complete(prog, inputs); const tree = parse(full, inferArity(full)); steps = 0;
    const result = ev(tree, inputs, tree); run.last = full; run.ignored = parse.ignored.slice(); return result;
  }
  // values <-> text
  function num(n){ let v = 0; for (let t = 0; t < n; t++) v = [0, v]; return v; }
  function asNumber(v){ let n = 0; while (v !== 0){ if (!(v instanceof Array) || v[0] !== 0) return null; v = v[1]; n++; } return n; }
  function show(v){ return v === 0 ? '0' : '{' + show(v[0]) + ',' + show(v[1]) + '}'; }
  function showRaw(v){ return v === 0 ? '0' : showRaw(v[0]) + showRaw(v[1]) + 'c'; } // the value as the program that builds it
  function showList(v){ if (v === 0) return '[]'; const items = []; while (v !== 0){ items.push(v[0] === 0 ? '0' : showList(v[0])); v = v[1]; } return '[' + items.join(',') + ']'; } // the value as a nested list: the empty list is [], elements that are atoms are written 0, so 3 is [0,0,0] and {{0,0},0} is [[0]]
  function parseValue(s){
    s = s.replace(/\s+/g, '');
    if (s === '') return undefined;
    if (/^\d+$/.test(s)) return num(parseInt(s, 10));
    if (/^[{}]+$/.test(s)){ // a bare bracket string is read as a Dyck word: the atom is the empty string and the pair {x,y} is '{' x '}' y, so {}{}{} is 3 and {{}}{} is {{0,0},{0,0}}
      let pos = 0; function dyck(){ const items = []; while (pos < s.length && s[pos] === '{'){ pos++; items.push(dyck()); if (s[pos] !== '}') throw new Error('unbalanced brackets in the input'); pos++; } let v = 0; for (let i = items.length - 1; i >= 0; i--) v = [items[i], v]; return v; }
      const v = dyck(); if (pos !== s.length) throw new Error('unbalanced brackets in the input'); return v; }
    if (/^[0c|]+$/.test(s) && s.length > 1){ // raw form: reverse Polish over 0 and c, i.e. the program that builds the value: 0 pushes the atom, c pairs the two most recent entries, so 0000ccc is 3 (| is accepted for c)
      const st = []; for (const ch of s){ if (ch === '0') st.push(0); else { if (st.length < 2) throw new Error('c needs two entries on the stack'); const y = st.pop(), x = st.pop(); st.push([x, y]); } }
      if (st.length !== 1) throw new Error('a raw string must leave exactly one value on the stack'); return st[0]; }
    if (/^[\[\]0,]+$/.test(s)){ // list form: [x1,...,xn] = {x1,{x2,...{xn,0}}}, with 0 or [] for the atom, so [0,0,0] is 3 and [[0]] is {{0,0},0}
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
  // "X<prog>#" definitions followed by an optional program to run
  function submit(text, inputs){
    const out = {defined: [], result: undefined};
    let rest = text.replace(/\s+/g, '').replace(/∗/g, '*').replace(/−/g, '-');
    while (rest.includes('#')){
      const cut = rest.indexOf('#'); const chunk = rest.slice(0, cut); rest = rest.slice(cut + 1);
      if (chunk.length < 2) throw new Error('a definition needs a symbol and a program before "#"');
      define(chunk[0], chunk.slice(1)); out.defined.push(chunk[0]);
    }
    if (rest.length) out.result = run(rest, inputs);
    return out;
  }
  const TABLE = [['1','00c','one, true'],['e','ijiajafibjbf0d0dj01dd','equal: {0,0} if i = j, else 0'],['2','01c','two'],['↑','0ic','successor'],['-','jibjbfid','minus, undefined for i < j'],['+','iib0jcfjd','plus'],['*','iibjfj+0d','times'],['^','jijbfi*1d','power'],['!','iiibf*1d','factorial'],['¬','i01d','not'],['&','ij10d0d','and'],['∨','i1j10dd','or'],['<','jiibjbf1d0d','less than (i<j)'],['%','ij<iij-jfd','remainder of i by j'],['Δ','ij%¬','i divisible by j'],['P','jbijΔ¬ijbf&1d','i indivisible by all of 2..j'],['Π','iibP','prime, for i >= 2']];
  function loadTable(){ for (const [s, p, c] of TABLE) define(s, p, c); }
  function loadLibrary(lib, comments){ submit(lib, []); for (const k of Object.keys(defs)) if (comments[k] && !defs[k].comment) defs[k].comment = comments[k]; }
  function clear(){ for (const k of Object.keys(defs)) delete defs[k]; }
  return {defs, define, run, submit, parse, loadLibrary, num, asNumber, show, showRaw, showList, parseValue, loadTable, clear, TABLE, Undefined, BASE};
})();
