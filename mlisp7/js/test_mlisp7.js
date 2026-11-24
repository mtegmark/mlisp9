// node test_mlisp7.js: run every case of mlisp7_cases.json (written by gen_mlisp7.py, verified against the MLISP originals) on the page's JS engine mlisp7.js
const fs = require('fs'), vm = require('vm');
const ctx = {window: {}}; vm.createContext(ctx);
vm.runInContext(fs.readFileSync(__dirname + '/mlisp7.js', 'utf8'), ctx);
const M = ctx.window.MLISP7;
const cases = JSON.parse(fs.readFileSync(__dirname + '/mlisp7_cases.json', 'utf8'));
let ok = 0, bad = 0;
for (const [defs, prog, inputs, expected] of cases){
  M.clear(); let got;
  try { M.submit(defs, undefined); const vals = inputs.map(M.parseValue); const r = M.submit(prog, M.pack(vals, vals.length)); got = r.result === undefined ? null : M.showRaw(r.result); }
  catch (e){ got = e instanceof M.Undefined ? 'undefined' : 'ERROR ' + e.message; }
  if (got === expected) ok++; else { bad++; console.log('MISMATCH', prog, inputs, 'expected', expected, 'got', got); }
}
// the packing heuristic of the page: a bare binary symbol takes {i,j}, a unary one i, a program with macros the macros' shape, a constant nothing
M.clear(); M.loadTable();
const pc = [['+', 2, 2], ['+', 3, 2], ['Π', 2, 1], ['ijc+', 1, 2], ['ijkcc+', 1, 3], ['1', 2, 0], ['0ec', 1, 1], ['a', 1, 1], ['a', 2, 2]];
for (const [p, filled, want] of pc){ const n = M.packCount(p, filled); if (n === want) ok++; else { bad++; console.log('PACK MISMATCH', p, filled, 'expected', want, 'got', n); } }
console.log(ok + ' cases agree, ' + bad + ' mismatches');
process.exit(bad ? 1 : 0);
