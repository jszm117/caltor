// Human-readable program text <-> calculator token IDs.
// The Studio deliberately uses the calculator's own symbols so copied programs
// remain useful outside this page and can be pasted back without a private format.

import { K, TOK, tok, bytesOf, registerConstants, unavailableCoordinateFunction } from './tokens.js';
import { CONSTANTS } from './consts.js';

// Text import must recognize scientific constants before a Machine is created.
registerConstants(CONSTANTS);

const ASCII_ALIASES = [
  ['whileend', 'pWhileEnd'], ['whlend', 'pWhileEnd'],
  ['clrmemory', 'pClrMemory'], ['clrmem', 'pClrMemory'], ['clrstat', 'pClrStat'],
  ['freqoff', 'pFreqOff'], ['freqon', 'pFreqOn'], ['ifend', 'pIfEnd'],
  ['npr', 'nPr'], ['ncr', 'nCr'],
  ['sinh^-1(', 'asinh'], ['cosh^-1(', 'acosh'], ['tanh^-1(', 'atanh'],
  ['sin^-1(', 'asin'], ['cos^-1(', 'acos'], ['tan^-1(', 'atan'],
  ['sqrt(', 'sqrt'], ['cbrt(', 'cbrt'], ['pi', 'pi'],
  ['->', 'pAsg'], ['=>', 'pJump'], ['M−', 'pMminus'],
  ['[a b/c]', 'frac'], ['(-)', 'neg'], ['EXP', 'EXP'],
  ['−', 'sub'], ['°', 'dms'], ['ᵈ', 'degU']
];

const AMBIGUOUS_IDS = new Set([
  'neg', 'sub', 'mul', 'div', 'pow', 'EXP',
  'hexA', 'hexB', 'hexC', 'hexD', 'hexE', 'hexF',
  'varA', 'varB', 'varC', 'varD', 'varX', 'varY', 'varM',
  'regA', 'regB', 'regC', 'regR', 'Sn', 'dms', 'degU'
]);

function aliases() {
  const out = ASCII_ALIASES.map(([label, id]) => ({ label, id }));
  for (const name of 'ABCDXYM') out.push({ label: `ALPHA(${name})`, id: `var${name}` });
  for (const [id, spec] of Object.entries(TOK)) {
    if (spec.sci) out.push({ label: `CONST(${spec.s})`, id, caseSensitive:true });
  }
  for (const [id, spec] of Object.entries(TOK)) {
    const label = spec.s.trim();
    if (AMBIGUOUS_IDS.has(id) || label.length < 2) continue;
    // Lowercase x/y in sum labels belong to the native statistics token.
    // Uppercase Y is a separate variable: ΣxY means Σx × Y, not Σxy.
    out.push({ label, id, caseSensitive:Boolean(spec.sci) || label.startsWith('Σ') });
  }
  const seen = new Set();
  return out
    .sort((a, b) => b.label.length - a.label.length)
    .filter(({ label, caseSensitive }) => {
      const key = caseSensitive ? `exact:${label}` : label.toLocaleLowerCase();
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
}

function singleToken(ch, mode, previous) {
  if (ch >= '0' && ch <= '9') return ch;
  if (ch === '.') return '.';
  if (ch === '+') return 'add';
  if (ch === '×' || ch === '*') return 'mul';
  if (ch === '÷' || ch === '/') return 'div';
  if (ch === '^') return 'pow';
  if (ch === '(' || ch === ')' || ch === ',' || ch === ';' || ch === ':') return ch;
  if (ch === '→') return 'pAsg';
  if (ch === '⇒') return 'pJump';
  if (ch === '?' || ch === '◢') return ch === '?' ? 'pIn' : 'pOut';
  if (ch === 'π') return 'pi';
  if (ch === '⌐' || ch === '┘') return 'frac';
  if (ch === '²') return 'sqr';
  if (ch === '³') return 'cube';
  if (ch === '%') return 'pct';
  if (ch === '=') return 'eq';
  if (ch === '≠') return 'ne';
  if (ch === '>') return 'gt';
  if (ch === '<') return 'lt';
  if (ch === '≥') return 'ge';
  if (ch === '≤') return 'le';
  if (ch === 'E') return mode === 'BASE' ? 'hexE' : 'EXP';

  if ('ABCDXYM'.includes(ch)) {
    if (mode === 'BASE' && 'ABCDEF'.includes(ch)) return 'hex' + ch;
    return 'var' + ch;
  }
  if (mode === 'BASE' && 'F'.includes(ch)) return 'hexF';
  if (mode === 'REG' && 'abcr'.includes(ch)) return 'reg' + ch.toUpperCase();
  if ((mode === 'SD' || mode === 'REG') && ch === 'n') return 'Sn';
  if (mode === 'BASE' && 'dhbo'.includes(ch)) return 'base' + ch.toUpperCase();
  // Outside BASE, CONST h must not collide with the hexadecimal prefix h.
  if (ch === 'h' && TOK.CONST_h) return 'CONST_h';
  if (ch === 'e') return 'napier';
  if (ch === 'i') return 'imag';

  if (ch === '-') {
    const unary = !previous || [K.OPEN, K.SEP, K.INFIX, K.POW, K.FN, K.PRE, K.PROG].includes(previous.k);
    return unary ? 'neg' : 'sub';
  }

  const exact = Object.entries(TOK).find(([id, spec]) =>
    !AMBIGUOUS_IDS.has(id) && spec.s === ch);
  return exact?.[0] || null;
}

// The statistics modes use the physical M+/SHIFT M+ keys for statistics.
// Text import must not silently add unavailable memory instructions. Keep the
// token stream intact so an existing draft can still be displayed and repaired.
export function programModeTokenError(id, mode) {
  if (id === 'pct' && mode === 'CMPLX') {
    return 'CMPLX 程式不能輸入百分號 %；請改用小數或一般除法。';
  }
  if (unavailableCoordinateFunction(id, mode)) {
    return `${mode} 程式不能輸入 ${id}(；座標變換函數適用於 COMP、SD、REG。`;
  }
  if ((mode === 'SD' || mode === 'REG') && (id === 'pMplus' || id === 'pMminus')) {
    return `${mode} 程式不能輸入原生 M+／M−；請用一般加減及 →M 賦值。`;
  }
  return null;
}

/** Parse a copyable Program Studio string into calculator tokens. */
export function parseProgramText(source, mode = 'COMP', { includeRanges = false } = {}) {
  const raw = String(source || '');
  const text = raw.replace(/\r\n?/g, '\n');
  const tokenIds = [];
  const ranges = [];
  // Only editor callers need source ranges. Map CRLF boundaries back to the
  // original text without changing the parser's existing normalized behavior.
  let offsets = null;
  if (includeRanges && raw !== text) {
    offsets = [0];
    for (let p = 0; p < raw.length;) {
      p += raw[p] === '\r' && raw[p + 1] === '\n' ? 2 : 1;
      offsets.push(p);
    }
  }
  const errors = [];
  const words = aliases();
  let i = 0;

  const push = (id, end = i + 1) => {
    const message = programModeTokenError(id, mode);
    if (message) errors.push({ index:offsets ? offsets[i] : i, character:text.slice(i,end), code:'mode-token', message });
    if (includeRanges) ranges.push({ id, start:offsets ? offsets[i] : i, end:offsets ? offsets[end] : end });
    tokenIds.push(id);
  };

  while (i < text.length) {
    const ch = text[i];
    if (ch === '\n') {
      // Blank lines are formatting. Explicit colons, including empty
      // statements and a final colon, are native tokens and consume bytes.
      let next = i + 1;
      while (next < text.length && /\s/u.test(text[next])) next++;
      if (next < text.length && text[next] !== ':' && tokenIds.length &&
          ![':', 'pOut', 'pThen', 'pElse'].includes(tokenIds[tokenIds.length - 1])) push(':');
      i = next;
      continue;
    }
    if (/\s/u.test(ch)) { i++; continue; }

    let matched = false;
    for (const entry of words) {
      const candidate = text.slice(i, i + entry.label.length);
      if (entry.caseSensitive ? candidate !== entry.label : candidate.toLocaleLowerCase() !== entry.label.toLocaleLowerCase()) continue;
      const next = text[i + entry.label.length] || '';
      const followsConditional = text.startsWith('⇒', i + entry.label.length) ||
        text.startsWith('=>', i + entry.label.length);
      if ((entry.id === 'pMplus' || entry.id === 'pMminus') &&
          next && !/[\s:◢→]/u.test(next) && !followsConditional) continue;
      // Calculator tokens need no word spaces: Ans², 3⁻¹arg(M and Norm2
      // are valid concatenations, including output from formatProgramText.
      push(entry.id, i + entry.label.length);
      i += entry.label.length;
      matched = true;
      break;
    }
    if (matched) continue;

    const previous = tokenIds.length ? tok(tokenIds[tokenIds.length - 1]) : null;
    const id = singleToken(ch, mode, previous);
    if (id) {
      const width = ch === '^' && text[i + 1] === '(' ? 2 : 1;
      push(id, i + width);
      i += width;
      continue;
    }

    errors.push({ index: i, character: ch });
    i++;
  }

  let tokens = [];
  try { tokens = tokenIds.map(tok); }
  catch (error) { errors.push({ index: -1, character: '', message: error.message }); }
  return { tokenIds, tokens, bytes: bytesOf(tokens), errors, ...(includeRanges ? { ranges } : {}) };
}

/** One calculator statement per line, with native symbols retained. */
export function programTokenSource(tokenOrId, mode = 'COMP') {
  const token = typeof tokenOrId === 'string' ? tok(tokenOrId) : tokenOrId;
  if (token.id === 'frac') return '┘';
  if (token.id === 'neg') return '(-)';
  if (token.id === 'sub') return ' − ';
  // Spaces distinguish variable M + addition from the native M+ command.
  if (token.id === 'add') return ' + ';
  if (token.id === 'nPr' || token.id === 'nCr') return ` ${token.id} `;
  if (token.id === 'degU') return 'ᵈ';
  if (token.id === 'EXP' && mode === 'BASE') return 'EXP';
  if (token.v && mode === 'BASE' && 'ABCD'.includes(token.v)) return `ALPHA(${token.v})`;
  if (token.sci) {
    const parsed = parseProgramText(token.s, mode);
    if (parsed.errors.length || parsed.tokenIds.length !== 1 || parsed.tokenIds[0] !== token.id) return `CONST(${token.s})`;
  }
  if (token.id === 'pMplus' || token.id === 'pMminus') return ` ${token.s} `;
  return token.s;
}

export function formatProgramText(tokens, mode = 'COMP') {
  return (tokens || [])
    .map((token, index, list) => token.id === ':' ?
      (index === 0 || index === list.length - 1 || list[index + 1]?.id === ':' ||
        [':', 'pOut', 'pThen', 'pElse'].includes(list[index - 1]?.id) ? ':\n' : '\n') :
      token.id === 'pOut' && index < list.length - 1 && list[index + 1].id !== ':'
        ? token.s + '\n' : programTokenSource(token, mode))
    .join('')
    .split('\n')
    .map((line) => line.trim())
    .join('\n');
}
