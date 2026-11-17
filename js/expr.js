// expr.js — number model, parser and evaluator.
//
// The parser is recursive descent laid out in exactly the priority order the
// fx-50F II guide prints (CN-103/104; 1 = tightest):
//   1 parenthetical functions   2 postfix / ^( / xroot( / %   3 fractions
//   4 prefix (-) and base tags  5 statistical estimated values
//   6 omitted ×                7 nPr nCr ∠                    8 explicit × ÷
//   9 + -                     10 relational                  11 and
//  12 or xor xnor

import { K, unavailableModeToken } from './tokens.js';
import { numeric, decimalParts, decimalAdd } from './numeric-backend.js';

export class CalcError extends Error {
  constructor(kind, at = -1) {
    super(kind + ' ERROR');
    this.kind = kind;
    this.at = at;
  }
}
const err = (kind, at) => { throw new CalcError(kind, at); };

// ---------------------------------------------------------------------------
// Values are always complex; the imaginary part is 0 for real results.
export const C = (re, im = 0) => ({ re, im });
export const isReal = (z) => Math.abs(z.im) < 1e-300;
export const asComplex = (value) => {
  const z = typeof value === 'number' ? C(value) : C(value.re, value.im);
  if (value?.complexFraction && (value.complexFraction.re || value.complexFraction.im)) {
    z.complexFraction = { ...value.complexFraction };
  }
  copyNativeFraction(value, z);
  return z;
};

/** Working precision through the active backend (historical function name). */
export function r15(x) {
  return numeric.roundWorking(x);
}
// Keep real memories as Numbers for existing modes, and retain both parts in CMPLX.
export function storedValue(value) {
  const z = asComplex(value);
  const guard = quotientGuards.get(value);
  const re = storedCoordinate(z.re, guard?.complex && guard.re);
  const im = storedCoordinate(z.im, guard?.complex && guard.im);
  if (im === 0) return re;
  const result = C(re, im);
  if (z.complexFraction) result.complexFraction = { ...z.complexFraction };
  return result;
}
// Variable memory keeps the calibrated 15-digit decimal. A live COMP memory
// can retain a bounded real quotient origin separately, while Ans retains its
// working origin. No guard is serialized or used by equality/Rnd.
// Before ending it, commit eligible complex quotient coordinates from their
// working rational origin. Otherwise a squared quotient's arithmetic tail
// becomes permanent when rounded to memory, and later integer scaling fails.
// Real and complex quotients retain their origin through working arithmetic.
// An exactly integral product may correct a small arithmetic tail, including
// real quotient squares; nonintegral targets and exact comparisons stay intact.
const quotientGuards = new WeakMap();
function boundedStoredOrigin(origin) {
  return origin && origin.d <= 1000000n &&
    (origin.n < 0n ? -origin.n : origin.n) <= BigInt(Number.MAX_SAFE_INTEGER);
}
function storedCoordinate(value, origin) {
  let commit = value;
  // Same short-rational bounds as read-side recovery below. Do not promote
  // arbitrary decimals, widen all memories, or round genuinely nonintegral
  // values to integers. Comparisons and Rnd still see ordinary stored numbers.
  if (boundedStoredOrigin(origin)) {
    const exact = Number(origin.n) / Number(origin.d);
    if (exact !== 0 && Math.abs(value - exact) <= Math.abs(exact) * 1e-12) commit = exact;
  }
  return numeric.roundSignificant(commit);
}
export function workingValue(value) {
  const z = asComplex(value), guard = quotientGuards.get(value);
  if (guard) quotientGuards.set(z, guard);
  return z;
}
const gcd = (a,b) => { a=a<0n?-a:a; b=b<0n?-b:b; while(b)[a,b]=[b,a%b]; return a; };
function rational(n,d=1n){
  if(!d)return null;
  if(d<0n){n=-n;d=-d;}
  const g=gcd(n,d);n/=g;d/=g;
  return n.toString().length+d.toString().length>256?null:{n,d};
}
function scalarRational(x){
  if(!Number.isFinite(x))return null;
  const {coefficient:n,scale}=decimalParts(x);
  if(Math.abs(scale)>128)return null;
  return scale<0?rational(n*10n**BigInt(-scale)):rational(n,10n**BigInt(scale));
}
const qadd=(a,b)=>a&&b?rational(a.n*b.d+b.n*a.d,a.d*b.d):null;
const qneg=a=>a?{n:-a.n,d:a.d}:null;
const qsub=(a,b)=>qadd(a,qneg(b));
const qmul=(a,b)=>a&&b?rational(a.n*b.n,a.d*b.d):null;
const qdiv=(a,b)=>a&&b?rational(a.n*b.d,a.d*b.n):null;
// W15/W16: native real fractions retain bounded rational origin in COMP.
// Decimal memory is not reconstructed from proximity to a short fraction.
const nativeFractions = new WeakMap(), realMemoryOrigins = new WeakMap();
function copyNativeFraction(from, to) {
  const q = from && typeof from === 'object' && nativeFractions.get(from);
  if (q) nativeFractions.set(to, q);
  return to;
}
function nativeFractionValue(z, q) {
  // Keep the model bounded to short fractions. Larger results use the existing
  // decimal path; this guard is not a claim about the firmware's exact limit.
  if (!q || z.im !== 0 || (q.n < 0n ? -q.n : q.n).toString().length + q.d.toString().length > 10) return z;
  z.re = r15(numeric.div(Number(q.n), Number(q.d)));
  if (q.d !== 1n) nativeFractions.set(z, q);
  return z;
}
function nativeFractionOperand(z) {
  if (z.im !== 0) return null;
  return nativeFractions.get(z) || (Number.isSafeInteger(z.re) ? rational(BigInt(z.re)) : null);
}
function nativeFractionOperation(z, a, b, op, introduce = false) {
  if (!introduce && !nativeFractions.has(a) && !nativeFractions.has(b)) return z;
  const p = nativeFractionOperand(a), q = nativeFractionOperand(b);
  return nativeFractionValue(z, ({ add:qadd, sub:qsub, mul:qmul, div:qdiv })[op](p, q));
}
export function storeVariable(vars, name, value, round = true) {
  const stored = round ? storedValue(value) : value;
  vars[name] = stored;
  let entries = realMemoryOrigins.get(vars);
  const q = nativeFractions.get(value);
  // G6: retain a bounded real quotient origin across COMP variable writes,
  // without changing the decimal stored value or inferring origin on reload.
  const origin = quotientGuards.get(value);
  const guard = round && stored !== 0 && origin && !origin.complex &&
    origin.re.d > 1n && boundedStoredOrigin(origin.re) ? origin : null;
  if ((q || guard) && typeof stored === 'number') {
    if (!entries) realMemoryOrigins.set(vars, entries = new Map());
    entries.set(name, { stored, q, guard });
  } else entries?.delete(name);
  return stored;
}
export function variableValue(vars, name, mode = 'COMP') {
  const value = vars[name] || 0, z = asComplex(value);
  const entry = mode === 'COMP' && realMemoryOrigins.get(vars)?.get(name);
  if (entry && entry.stored === value) {
    if (entry.q) nativeFractions.set(z, entry.q);
    if (entry.guard) quotientGuards.set(z, entry.guard);
  }
  return z;
}
const rationalPair=z=>quotientGuards.get(z)||{re:scalarRational(z.re),im:scalarRational(z.im)};

export function quotientCounterAdvance(start, step) {
  const increment = quotientGuards.get(step)?.re;
  if (!boundedStoredOrigin(increment) || increment.d === 1n) return null;
  let exact = quotientGuards.get(start)?.re || scalarRational(start.re);
  let previous = start.re;
  return (current) => {
    if (!Number.isFinite(current)) return undefined;
    if (current !== previous) exact = scalarRational(current);
    exact = qadd(exact, increment);
    if (!exact) return undefined;
    previous = Number(exact.n) / Number(exact.d);
    return previous;
  };
}
// Nov03: stored 4/3 then 9(X+i)^2 is integral. Nov05 W22/W23:
// stored complex quotients also recover integral scaled squares/cubes.
// Recover a short rational only when its calibrated quotient or rounded stored
// spelling is IDENTICAL to the memory value. This is a bounded model, not
// fuzzy equality or unlimited exact arithmetic. No history metadata is stored.
function shortStoredRational(value) {
  if (!Number.isFinite(value)) return null;
  if (Number.isSafeInteger(value)) return rational(BigInt(value));
  const source = scalarRational(Math.abs(value));
  if (!source) return null;
  let n=source.n,d=source.d,h0=0n,h1=1n,k0=1n,k1=0n;
  for (let i=0; i<32 && d; i++) {
    const a=n/d,h=a*h1+h0,k=a*k1+k0;
    if (k>1000000n || h>BigInt(Number.MAX_SAFE_INTEGER)) break;
    const numerator=Math.sign(value)*Number(h),denominator=Number(k);
    if (k>1n && (numeric.div(numerator,denominator)===value ||
        numeric.roundSignificant(numerator/denominator)===value)) {
      return rational(BigInt(Math.sign(value))*h,k);
    }
    [h0,h1,k0,k1]=[h1,h,k1,k];[n,d]=[d,n%d];
  }
  return null;
}
function storedNumericOperand(value, mode) {
  const z = asComplex(value);
  if (mode !== 'CMPLX' || (Number.isInteger(z.re) && Number.isInteger(z.im))) return z;
  const re=shortStoredRational(z.re),im=shortStoredRational(z.im);
  // Both coordinates must match the bounded reconstruction exactly. Reads
  // never alter memory, comparisons, Rnd, or serialized decimal values.
  if (re && im) quotientGuards.set(z,{re,im,complex:z.im!==0});
  return z;
}
function guardQuotient(z,a,b,op){
  const active=quotientGuards.has(a)||quotientGuards.has(b);
  if(!active&&op!=='div')return z;
  const p=rationalPair(a),q=rationalPair(b);let result;
  if(op==='add'||op==='sub'){
    const combine=op==='add'?qadd:qsub;result={re:combine(p.re,q.re),im:combine(p.im,q.im)};
  }else if(op==='mul'){
    result={re:qsub(qmul(p.re,q.re),qmul(p.im,q.im)),im:qadd(qmul(p.re,q.im),qmul(p.im,q.re))};
  }else{
    const d=qadd(qmul(q.re,q.re),qmul(q.im,q.im));
    result={re:qdiv(qadd(qmul(p.re,q.re),qmul(p.im,q.im)),d),im:qdiv(qsub(qmul(p.im,q.re),qmul(p.re,q.im)),d)};
  }
  if(!result.re||!result.im)return z;
  result.complex=Boolean(p.complex||q.complex||a.im!==0||b.im!==0);
  quotientGuards.set(z,result);
  if(op==='mul')for(const part of ['re','im']){
    const value=result[part];if(value.d!==1n)continue;
    const target=Number(value.n);
    if(target!==0&&Number.isSafeInteger(target)&&Math.abs(z[part]-target)<=Math.abs(target)*1e-12)z[part]=target;
  }
  return z;
}
const rz = (z) => {
  const value=C(r15(z.re),r15(z.im)),guard=quotientGuards.get(z);
  if(guard)quotientGuards.set(value,guard);
  return copyNativeFraction(z, value);
};

const cadd = (a, b, mode) => guardQuotient(C(numeric.expressionAdd(a.re, b.re, mode), numeric.expressionAdd(a.im, b.im, mode)),a,b,'add');
const csub = (a, b, mode) => guardQuotient(C(numeric.expressionSub(a.re, b.re, mode), numeric.expressionSub(a.im, b.im, mode)),a,b,'sub');
const cmul = (a, b) => guardQuotient(C(
  numeric.sub(numeric.mul(a.re, b.re), numeric.mul(a.im, b.im)),
  numeric.add(numeric.mul(a.re, b.im), numeric.mul(a.im, b.re))
),a,b,'mul');
function cdiv(a, b) {
  // Axis denominators use direct division. Squaring them in the general
  // formula changes calibrated guard digits and can introduce extra overflow.
  if (b.im === 0) {
    if (b.re === 0) err('Math');
    return guardQuotient(C(numeric.div(a.re, b.re), numeric.div(a.im, b.re)),a,b,'div');
  }
  if (b.re === 0) return guardQuotient(C(numeric.div(a.im, b.im), -numeric.div(a.re, b.im)),a,b,'div');
  // Physical extreme complex quotients reject an overflowing/underflowing
  // squared denominator even when the mathematical final quotient is finite.
  const product = (x, y) => checkedScalar(numeric.mul(x, y));
  const d = checkedScalar(numeric.add(product(b.re, b.re), product(b.im, b.im)));
  if (d === 0) err('Math');
  return guardQuotient(C(
    numeric.div(checkedScalar(numeric.add(product(a.re, b.re), product(a.im, b.im))), d),
    numeric.div(checkedScalar(numeric.sub(product(a.im, b.re), product(a.re, b.im))), d)
  ),a,b,'div');
}
const cabs = (z) => Math.hypot(z.re, z.im);
const carg = (z) => Math.atan2(z.im, z.re);

// ---------------------------------------------------------------------------
// Angle handling
const ANG = { Deg: Math.PI / 180, Rad: 1, Gra: Math.PI / 200 };
const toRad = (x, unit) => x * ANG[unit];
const fromRad = (x, unit) => {
  const q = x / (Math.PI / 2);
  // arg(i), Pol and inverse-function axes must use the same quarter turns as
  // the native pi token. Otherwise removing a false tangent exclusion zone
  // exposes a binary-pi endpoint as a finite angle beside the real pole.
  return Number.isInteger(q) ? numeric.mul(quarterTurn(unit),q) : x / ANG[unit];
};
// Recognise exact quarter turns in the calculator's own input units. Its pi
// constant has measured decimal guard digits, unlike JavaScript's Math.PI.
const CALCULATOR_PI = 3.14159265358980;
const quarterTurn = (unit) => unit === 'Deg' ? 90 : unit === 'Gra' ? 100 : CALCULATOR_PI / 2;
function convertAngle(x, from, to) {
  if (from === to) return x;
  return numeric.div(numeric.mul(x, quarterTurn(to)), quarterTurn(from));
}
function requireTrigAngle(x, unit) {
  const limit = unit === 'Deg' ? 9e9 : unit === 'Gra' ? 1e10 : 157079632.7;
  if (Math.abs(x) >= limit) err('Math');
}
function reducedRadians(x, unit) {
  if (unit === 'Rad') return x;
  const cycle = unit === 'Deg' ? 360 : 400, half = cycle / 2;
  let reduced = x % cycle;
  if (reduced > half) reduced -= cycle;
  if (reduced < -half) reduced += cycle;
  return toRad(reduced, unit);
}
// W13: 36*pi radians / 3 is an exact turn despite intermediate working
// rounding. Read only simple angle arithmetic; never evaluate an AST twice,
// propagate identities through stored angles, or snap nearby numerical values.
function angleOrigin(node, ctx) {
  if (!node) return null;
  const scalar = value => value && { value, unit: null };
  if (node.t === 'num') return scalar(scalarRational(Number(node.s + (node.exp == null ? '' : 'e' + node.exp))));
  if (node.t === 'val') {
    if (node.tok.id === 'pi') return { value: rational(2n), unit: 'Rad' };
    // Integer counters are exact scalar multipliers, not stored angle origins.
    if (node.tok.v) {
      const z = asComplex(ctx.vars[node.tok.v] || 0);
      return z.im === 0 && Number.isSafeInteger(z.re) ? scalar(scalarRational(z.re)) : null;
    }
    return null;
  }
  const a = angleOrigin(node.a ?? node.parts?.[0], ctx);
  if (!a) return null;
  if (node.t === 'neg') return { ...a, value: qneg(a.value) };
  if (node.t === 'post') {
    const from = { toDeg: 'Deg', toRad: 'Rad', toGra: 'Gra' }[node.f];
    if (!from || (a.unit && a.unit !== from)) return null;
    const value = a.unit ? a.value : from === 'Rad' ? null
      : qdiv(a.value, rational(from === 'Deg' ? 90n : 100n));
    return value && { value, unit: ctx.angle };
  }
  if (node.t !== 'bin' && !(node.t === 'frac' && node.parts.length === 2)) return null;
  const b = angleOrigin(node.b ?? node.parts?.[1], ctx);
  if (!b) return null;
  const f = node.t === 'frac' ? 'div' : node.f;
  let value, unit;
  if (f === 'mul' && !(a.unit && b.unit)) {
    value = qmul(a.value, b.value); unit = a.unit || b.unit;
  } else if (f === 'div' && !b.unit) {
    value = qdiv(a.value, b.value); unit = a.unit;
  } else if ((f === 'add' || f === 'sub') && a.unit === b.unit) {
    value = (f === 'add' ? qadd : qsub)(a.value, b.value); unit = a.unit;
  }
  return value ? { value, unit } : null;
}
function originAxis(f, node, ctx) {
  const a = angleOrigin(node, ctx);
  if (!a || a.unit !== ctx.angle || a.value.n % a.value.d !== 0n) return undefined;
  const quadrant = Number(((a.value.n / a.value.d) % 4n + 4n) % 4n);
  if (f === 'tan' && quadrant % 2) err('Math');
  return f === 'sin' ? [0, 1, 0, -1][quadrant]
    : f === 'cos' ? [1, 0, -1, 0][quadrant] : 0;
}
function exactAxis(f, x, unit) {
  const quarter = quarterTurn(unit);
  const ratio = x / quarter;
  const q = unit === 'Rad' ? Math.round(ratio) : ratio;
  // Multiples such as 3*pi/2 have already passed through decimal working
  // precision. Compare that reconstructed value exactly, not with an epsilon.
  if (!Number.isInteger(q) || (unit === 'Rad' && x !== numeric.mul(quarter, q))) return undefined;
  const quadrant = ((q % 4) + 4) % 4;
  if (f === 'tan' && quadrant % 2) err('Math');
  return f === 'sin' ? [0, 1, 0, -1][quadrant]
    : f === 'cos' ? [1, 0, -1, 0][quadrant] : 0;
}
function rectangularParts(r, angle, unit) {
  const radians = reducedRadians(angle, unit);
  return C(r * (exactAxis('cos', angle, unit) ?? Math.cos(radians)),
    r * (exactAxis('sin', angle, unit) ?? Math.sin(radians)));
}

// ---------------------------------------------------------------------------
// Base-n word sizes.  The guide gives 10 binary digits, 10 octal digits and a
// 32-bit signed decimal/hex range, so each base has its own word width.
export const WORD_BITS = { 2: 10, 8: 30, 10: 32, 16: 32 };

export function wrapWord(n, base) {
  const bits = WORD_BITS[base] || 32;
  const m = 2 ** bits;
  let v = ((Math.trunc(n) % m) + m) % m;
  if (v >= m / 2) v -= m;
  return v;
}
export function toWord(n, base) {
  const bits = WORD_BITS[base] || 32;
  const m = 2 ** bits;
  return ((Math.trunc(n) % m) + m) % m;
}

// ---------------------------------------------------------------------------
// Parser
class Parser {
  constructor(tokens, ctx) {
    this.ts = tokens;
    this.i = 0;
    this.ctx = ctx;
    this.depth = 0;
  }
  peek(o = 0) { return this.ts[this.i + o]; }
  next() { return this.ts[this.i++]; }
  at(kind) { const t = this.peek(); return t && t.k === kind; }
  isId(...ids) { const t = this.peek(); return t && ids.includes(t.id); }

  parse() {
    if (!this.ts.length) err('Syntax', 0);
    const v = this.pOr();
    if (this.i < this.ts.length) {
      const t = this.peek();
      if (t.k === K.CONV) {
        this.next();
        if (this.i !== this.ts.length) err('Syntax',this.i);
        return { t: 'conv', conv: t.conv, a: v };
      }
      err('Syntax', this.i);
    }
    return v;
  }

  binaryLevel(nextFn, prio) {
    let left = nextFn.call(this);
    for (;;) {
      const t = this.peek();
      if (!t || t.k !== K.INFIX || t.p !== prio) return left;
      this.next();
      const right = nextFn.call(this);
      left = { t: 'bin', f: t.f, a: left, b: right, at: this.i };
    }
  }

  pOr() { return this.binaryLevel(this.pAnd, 11); }
  pAnd() { return this.binaryLevel(this.pRel, 10); }
  pRel() { return this.binaryLevel(this.pAdd, 9); }
  pAdd() { return this.binaryLevel(this.pMul, 8); }

  // Explicit multiplication/division stay left-associative. Juxtaposed
  // factors bind within each operand before explicit multiplication/division.
  pMul() { return this.binaryLevel(this.pPerm, 7); }

  pImplicit() {
    let left = this.pEst();
    while (this.startsImplicitFactor()) {
      left = { t: 'bin', f: 'mul', a: left, b: this.pEst(), at: this.i };
    }
    return left;
  }

  // The multiplication sign may be dropped before a parenthesis, a
  // parenthetical function, a variable, a constant or a base tag.
  startsImplicitFactor() {
    const t = this.peek();
    if (!t) return false;
    if (t.k === K.OPEN || t.k === K.FN) return true;
    if (t.k === K.CONST) return true;
    if (t.k === K.PRE && t.base) return true;
    return false;
  }

  // Implied factors belong to each operand: 2∠3⁻¹arg(M) means
  // 2∠((1/3) arg(M)), not (2∠(1/3)) arg(M).
  pPerm() { return this.binaryLevel(this.pImplicit, 6); }

  pEst() {
    let v = this.pUnary();
    while (this.at(K.EST)) {
      const t = this.next();
      v = { t: 'est', est: t.est, a: v };
    }
    return v;
  }

  pUnary() {
    const t = this.peek();
    // Measured: SUB can negate a number, function or another negative operand
    // after ADD as well as SUB: 3+-2 = 1, 3+-sqrt(4) = 1, 3+-[NEG]2 = 5.
    // Keep unary priority below squaring.
    // Measured: 3++2 = 5 and 3-+2 = 1.
    if (t && t.id === 'add') {
      this.next();
      return this.pUnary();
    }
    if (t && t.id === 'sub') {
      this.next();
      return { t: 'neg', a: this.pUnary() };
    }
    if (t && t.k === K.PRE) {
      this.next();
      if (t.base) return { t: 'based', base: t.base, a: this.pUnary() };
      return { t: 'neg', a: this.pUnary() };
    }
    return this.pFrac();
  }

  pFrac() {
    const parts = [this.pPower()];
    while (this.at(K.FRAC)) { this.next(); parts.push(this.pSignedFractionPart()); }
    if (parts.length === 1) return parts[0];
    if (parts.length > 3) err('Syntax', this.i);
    return { t: 'frac', parts };
  }

  pSignedFractionPart() {
    // Physical R7: both NEG and SUB are legal immediately after a b/c.
    // Do not call pUnary here: it would swallow the next fraction separator
    // and turn a three-part mixed fraction into a nested division.
    const t = this.peek();
    if (t && (t.id === 'sub' || t.id === 'neg')) {
      this.next();
      return { t: 'neg', a: this.pSignedFractionPart() };
    }
    return this.pPower();
  }

  pPower() {
    let v = this.pAtom();
    for (;;) {
      const t = this.peek();
      if (t && t.id === 'dms') {
        // {degrees}°{minutes}°{seconds}° — each element is its own atom
        this.next();
        const parts = [v];
        while (parts.length < 3 && this.at(K.DIGIT)) {
          parts.push(this.pAtom());
          if (this.isId('dms')) this.next();
          else break;
        }
        v = { t: 'dmsval', parts };
      } else if (t && t.k === K.POST) {
        if (unavailableModeToken(t.id, this.ctx.mode)) err('Syntax', this.i);
        this.next();
        v = { t: 'post', f: t.f, a: v };
      } else if (t && t.k === K.POW) {
        this.next();
        const arg = this.parenBody(1)[0];
        v = { t: 'bin', f: t.f, a: v, b: arg };
      } else {
        return v;
      }
    }
  }

  // Reads arguments up to the matching ')'.  A closing parenthesis at the very
  // end of the input may be omitted, as on the real machine.
  parenBody(minArgs, maxArgs = minArgs, deferExtra = false) {
    const args = [];
    const frames = this.parenFrames ??= [];
    const frame = {args, maxArgs};
    frames.push(frame);
    try {
    if (this.i >= this.ts.length) err('Syntax', this.i);
    for (;;) {
      args.push(this.pOr());
      const t = this.peek();
      if (t && t.k === K.SEP && t.s === ',') {
        // W5: a full inner Pol returns the next comma to the enclosing Rec.
        // A root function with too many arguments still raises Argument.
        if (args.length === maxArgs && (this.fieldSeparators ||
            frames.slice(0,-1).some(f => f.args.length < f.maxArgs - 1))) break;
        this.next(); continue;
      }
      break;
    }
    const t = this.peek();
    if (t && t.k === K.CLOSE) this.next();
    // W10: a final display conversion also ends every omitted right bracket.
    // Leave it for parse(), so it formats the whole expression. A conversion
    // within an unfinished expression is still invalid.
    else if (this.i < this.ts.length && !(t?.k === K.CONV && this.i === this.ts.length - 1) &&
      !(args.length === maxArgs && t?.k === K.SEP &&
      ((t.s === ',' && (this.fieldSeparators || frames.slice(0,-1).some(f => f.args.length < f.maxArgs - 1))) ||
       (t.s === ';' && this.fieldSeparators)))) err('Syntax', this.i);
    if (args.length < minArgs || args.length > maxArgs + Number(deferExtra)) err('Arg', this.i);
    return args;
    } finally { frames.pop(); }
  }

  pAtom() {
    const t = this.peek();
    if (!t) err('Syntax', this.i);

    if (t.k === K.DIGIT) return this.number();

    if (t.k === K.OPEN) {
      this.next();
      const v = this.parenBody(1, 1)[0];
      return v;
    }

    if (t.k === K.FN) {
      if (unavailableModeToken(t.id, this.ctx.mode)) err('Syntax', this.i);
      this.next();
      let args;
      if (t.f === 'log') args = this.parenBody(1, 2);
      else if (t.f === 'Pol' || t.f === 'Rec') args = this.parenBody(2, 2);
      else args = this.parenBody(1, 1, t.f === 'ln');
      return { t: 'call', f: t.f, args };
    }

    if (t.k === K.CONST) {
      this.next();
      return { t: 'val', tok: t };
    }

    err('Syntax', this.i);
    return null;
  }

  number() {
    let s = '';
    let expPart = null;
    while (this.at(K.DIGIT)) {
      const t = this.next();
      if (t.id === 'EXP') {
        if (expPart !== null) err('Syntax', this.i);
        expPart = '';
        // EXP accepts the subtraction key too; consecutive negative signs
        // cancel (measured 1 EXP [NEG] [NEG] 2 = 100).
        let negative = false;
        while (this.isId('neg') || this.isId('sub') || this.isId('add')) {
          if (this.next().id !== 'add') negative = !negative;
        }
        expPart = negative ? '-' : '';
        continue;
      }
      if (t.id === '.' && (expPart !== null || s.includes('.'))) err('Syntax', this.i - 1);
      if (expPart !== null) expPart += t.s;
      else s += t.s;
    }
    if (s === '' && expPart === null) err('Syntax', this.i);
    // EXP requires exponent digits, including when a negative sign was entered.
    if (expPart !== null && !/^-?\d{1,2}$/.test(expPart)) err('Syntax', this.i);
    // A bare decimal point is a zero mantissa on the physical calculator.
    return { t: 'num', s: s === '.' ? '0' : (s || '1'), exp: expPart };
  }
}

export function parse(tokens, ctx) {
  const ast = new Parser(tokens, ctx).parse();
  // fx-50FH II physical probes: six nested i values succeed; seven produce
  // Stack ERROR. Related-model five-value limits do not match this device.
  const numericLimit = ctx.mode === 'CMPLX' ? 6 : 10;
  if (numericStackNeed(ast) > numericLimit || commandStackPeak(tokens) > 24) err('Stack');
  return ast;
}

// W6: a DT separator may implicitly finish the preceding parenthesized field.
// Use the expression grammar so commas required by Pol/Rec remain arguments.
// This only locates fields; evaluation (and its side effects) still occurs once.
export function splitExpressionFields(tokens, ctx) {
  const parser = new Parser(tokens, ctx);
  parser.fieldSeparators = true;
  const groups = [], seps = [];
  for (;;) {
    const start = parser.i, first = parser.peek();
    if (first && !(first.k === K.SEP && [',',';'].includes(first.s))) parser.pOr();
    groups.push(tokens.slice(start, parser.i));
    const next = parser.peek();
    if (!next) return {groups, seps};
    if (next.k !== K.SEP || ![',',';'].includes(next.s)) err('Syntax', parser.i);
    seps.push(next.s); parser.next();
  }
}

// Values are evaluated left-to-right. While the right operand is evaluated,
// the completed left value remains on the numeric stack. This reproduces the
// five occupied numeric slots in the guide's stack illustration.
function numericStackNeed(node) {
  if (!node) return 0;
  if (node.t === 'num' || node.t === 'val') return 1;
  if (node.t === 'bin') {
    return Math.max(numericStackNeed(node.a), 1 + numericStackNeed(node.b));
  }
  const children = node.args || node.parts || (node.a ? [node.a] : []);
  let peak = 1;
  children.forEach((child, i) => { peak = Math.max(peak, i + numericStackNeed(child)); });
  return peak;
}

// Priority-aware operator scan for the calculator's 24-level command stack.
// Parenthetical function tokens include their opening parenthesis and occupy a
// single command slot, matching the key-operation storage model.
function commandStackPeak(tokens) {
  const stack = [];
  let peak = 0;
  const note = () => { peak = Math.max(peak, stack.length); };
  const pushOp = (p) => {
    while (stack.length && !stack[stack.length - 1].open && stack[stack.length - 1].p <= p) stack.pop();
    stack.push({ p });
    note();
  };
  for (const t of tokens) {
    if (t.k === K.OPEN || t.k === K.FN || t.k === K.POW) {
      stack.push({ open: true });
      note();
    } else if (t.k === K.CLOSE) {
      while (stack.length && !stack[stack.length - 1].open) stack.pop();
      if (stack.length) stack.pop();
    } else if (t.k === K.SEP) {
      while (stack.length && !stack[stack.length - 1].open) stack.pop();
    } else if (t.k === K.INFIX) {
      pushOp(t.p);
    } else if (t.k === K.FRAC) {
      pushOp(3);
    } else if (t.k === K.PRE) {
      stack.push({ p: 4 });
      note();
    } else if (t.k === K.POST || t.k === K.EST || t.k === K.CONV) {
      peak = Math.max(peak, stack.length + 1);
    }
  }
  return peak;
}

// ---------------------------------------------------------------------------
// Evaluator
//
// ctx supplies:
//   mode 'COMP'|'CMPLX'|'BASE'|'SD'|'REG'|'PRGM'
//   angle 'Deg'|'Rad'|'Gra'
//   base  (BASE mode only)
//   vars  {A,B,C,D,X,Y,M}
//   ans   value
//   sci(key), stat(name), est(kind, value)
//   fvars {a,b,c,r,t,v,ρ,θ}
//   fixDigits / sciDigits / dispMode  (for Rnd)

const FACT_MAX = 69;

export function evaluate(node, ctx) {
  return checkedEvaluate(node, ctx, true);
}

function checkedScalar(value) {
  if (!Number.isFinite(value) || Math.abs(value) >= 1e100) err('Math');
  return Math.abs(value) < 1e-99 ? 0 : value;
}

function checkedEvaluate(node, ctx, final) {
  const z = evaluateNode(node, ctx);
  if (!z) err('Math');
  const re = checkedScalar(z.re), im = checkedScalar(z.im);
  if (final && ctx.mode === 'BASE') {
    const bits = WORD_BITS[ctx.base] || 32;
    if (!Number.isInteger(z.re) || z.re < -(2 ** (bits - 1)) || z.re > 2 ** (bits - 1) - 1) err('Math');
  }
  // Measured: (1E-99 / 10) * 10 and (1E-99 / 10) * 1E99 both
  // return zero. Flush underflow at each evaluated step, before its parent
  // operation can amplify it. Copy rather than mutate a referenced value.
  const result={ ...z, re, im };
  const guard=quotientGuards.get(z);
  if(guard&&re===z.re&&im===z.im)quotientGuards.set(result,guard);
  if (re === z.re && im === z.im) copyNativeFraction(z, result);
  return result;
}

function coordinateResult(x, y, ctx) {
  // Validate both outputs before committing either memory. Apply the same
  // range/underflow policy as the returned value, preserving working digits.
  // Otherwise Pol overflow leaves an invalid X after Math ERROR, and tiny
  // Rec components can disagree with the zero returned in Ans.
  const checkedX = checkedScalar(x), checkedY = checkedScalar(y);
  ctx.setVar('X', checkedX); ctx.setVar('Y', checkedY);
  return C(checkedX);
}

function evaluateNode(node, ctx) {
  const E = (n) => checkedEvaluate(n, ctx, false);
  const real = (n) => {
    const z = E(n);
    if (!isReal(z)) err('Math');
    return z.re;
  };

  switch (node.t) {
    case 'num': {
      if (ctx.mode === 'BASE') return C(parseBaseDigits(node.s, ctx.base));
      let x = Number(node.s === '' ? '0' : node.s);
      if (node.exp !== null && node.exp !== undefined && node.exp !== '') {
        x = Number(node.s + 'e' + node.exp);
      } else if (node.exp === '') {
        x = Number(node.s);
      }
      if (!isFinite(x)) err('Math');
      return C(x);
    }

    case 'based':
      return C(parseBaseDigits(collectDigits(node.a), node.base));

    case 'val': return valueOf(node.tok, ctx);

    case 'neg': {
      const z = E(node.a), result = C(-z.re, -z.im);
      const guard=quotientGuards.get(z);
      if(guard)quotientGuards.set(result,{...guard,re:qneg(guard.re),im:qneg(guard.im)});
      const fraction = nativeFractions.get(z);
      if (fraction) nativeFractions.set(result, qneg(fraction));
      if (z.complexFraction) result.complexFraction = { ...z.complexFraction };
      return result;
    }

    case 'frac': {
      const values = node.parts.length === 2 ? node.parts.map(E) : null;
      // Physical CMPLX probe: (3+6i) [a b/c] 3 = 1+2i. A two-part
      // fraction with complex operands follows ordinary complex division.
      // Three-part mixed fractions still require real elements; their
      // complex sign convention has not been physically established.
      if (values && values.some((z) => !isReal(z))) {
        const [a, b] = values;
        if (b.re === 0 && b.im === 0) err('Math');
        return complexOperationResult(cdiv(a, b), [a, b]);
      }
      const p = values ? values.map((z) => z.re) : node.parts.map(real);
      if (p.some((x) => !Number.isInteger(x))) {
        // non-integer elements degrade to a plain division, as documented
        const result=C(p.length === 2 ? p[0] / p[1] : p[0] + p[1] / p[2]);
        if (values) {
          const guarded = guardQuotient(result, values[0], values[1], 'div');
          return ctx.mode === 'COMP' ? nativeFractionOperation(guarded, values[0], values[1], 'div', true) : guarded;
        }
        const part=guardQuotient(C(p[1]/p[2]),C(p[1]),C(p[2]),'div');
        return guardQuotient(result,C(p[0]),part,'add');
      }
      if (p.length === 2) {
        if (p[1] === 0) err('Math');
        const result = guardQuotient(C(r15(p[0] / p[1])),values[0],values[1],'div');
        return ctx.mode === 'COMP' ? nativeFractionOperation(result, values[0], values[1], 'div', true) : result;
      }
      if (p[2] === 0) err('Math');
      const sign = p[0] < 0 ? -1 : 1;
      const part=guardQuotient(C(sign*p[1]/p[2]),C(sign*p[1]),C(p[2]),'div');
      const result = guardQuotient(C(r15(sign * (Math.abs(p[0]) + p[1] / p[2]))),C(p[0]),part,'add');
      return ctx.mode === 'COMP' && p.every(Number.isSafeInteger)
        ? nativeFractionValue(result, rational(BigInt(p[0]) * BigInt(p[2]) + BigInt(sign * p[1]), BigInt(p[2]))) : result;
    }

    case 'dmsval': {
      const p = node.parts.map((x) => real(x));
      const d = p[0], m = p[1] || 0, s = p[2] || 0;
      if (m < 0 || s < 0) err('Math');
      return C(r15(dmsToDecimal(d, m, s)));
    }

    case 'post': return postfix(node.f, node, ctx, E, real);

    case 'bin': return binary(node.f, node, ctx, E, real);

    case 'call': return callFn(node.f, node.args, ctx, E, real);

    case 'est': {
      const x = real(node.a);
      return C(ctx.est(node.est, x));
    }

    case 'conv': {
      const z = E(node.a);
      z.forceFormat = node.conv;
      return z;
    }
  }
  err('Syntax');
  return null;
}

function collectDigits(node) {
  if (node.t === 'num') return node.s;
  err('Syntax');
  return '';
}

export function parseBaseDigits(s, base) {
  if (!s.length) err('Syntax');
  const digits = '0123456789ABCDEF'.slice(0, base);
  let v = 0;
  for (const ch of s) {
    const d = digits.indexOf(ch.toUpperCase());
    if (d < 0) err('Syntax');
    v = v * base + d;
  }
  if (base === 10) {
    if (v > 2 ** 31 - 1) err('Math');
    return v;
  }
  if (v >= 2 ** WORD_BITS[base]) err('Math');
  return wrapWord(v, base);
}

function valueOf(t, ctx) {
  if (t.id === 'pi') return C(CALCULATOR_PI);
  if (t.id === 'napier') return C(2.71828182845904);
  if (t.id === 'Ans') {
    const z = ctx.ans ? storedNumericOperand(ctx.ans, ctx.mode) : C(0);
    const guard = ctx.ans && quotientGuards.get(ctx.ans);
    if (guard) quotientGuards.set(z, guard);
    if (ctx.ans?.complexFraction) z.complexFraction = { ...ctx.ans.complexFraction };
    return z;
  }
  if (t.id === 'Ran') return C(Math.floor(Math.random() * 1000) / 1000);
  if (t.id === 'imag') {
    if (ctx.mode !== 'CMPLX') err('Syntax');
    return C(0, 1);
  }
  if (t.v) {
    if (ctx.mode === 'COMP') return variableValue(ctx.vars, t.v, ctx.mode);
    return storedNumericOperand(ctx.vars[t.v] || 0, ctx.mode);
  }
  if (t.sci) return C(ctx.sci(t.sci));
  if (t.fv) return C(ctx.fvars ? (ctx.fvars[t.fv] || 0) : 0);
  // W19: reading a statistic crosses the same working-value boundary as
  // storing it. Preserve raw statistical accumulators internally; do not
  // let an extra binary guard digit defeat exact comparison or convergence.
  if (t.stat) return C(numeric.roundSignificant(ctx.stat(t.stat)));
  err('Syntax');
  return null;
}

function axisAwareCube(z) {
  // Dedicated cube on a pure axis bypasses the separately normalized square.
  // Explicit z²×z still follows the two-operation path, as measured on hardware.
  if (z.im === 0) return C(numeric.pow(z.re, 3));
  if (z.re === 0) return C(0, -numeric.pow(z.im, 3));
  return cmul(cmul(z, z), z);
}
function complexCubeResult(z) {
  const result = rz(axisAwareCube(z));
  if (z.complexFraction) {
    result.complexFraction = complexProductResult(complexProductResult(z, z), z).complexFraction;
  }
  return result;
}

function postfix(f, node, ctx, E, real) {
  if (f === 'sqr') { const z = E(node.a); return complexProductResult(z, z); }
  if (f === 'cube') return complexCubeResult(E(node.a));
  if (f === 'recip') {
    const z = E(node.a);
    if (z.re === 0 && z.im === 0) err('Math');
    return complexOperationResult(cdiv(C(1), z), [z]);
  }
  if (f === 'fact') {
    const x = real(node.a);
    if (!Number.isInteger(x) || x < 0 || x > FACT_MAX) err('Math');
    let r = 1;
    for (let i = 2; i <= x; i++) r *= i;
    return C(r15(r));
  }
  if (f === 'pct') return C(r15(real(node.a) / 100));
  if (f === 'toDeg') return C(r15(convertAngle(real(node.a), 'Deg', ctx.angle)));
  if (f === 'toRad') return C(r15(convertAngle(real(node.a), 'Rad', ctx.angle)));
  if (f === 'toGra') return C(r15(convertAngle(real(node.a), 'Gra', ctx.angle)));
  if (f === 'dms') return E(node.a);
  err('Syntax');
  return null;
}

// Presentation hint only: measured complex division/reciprocal results use
// fractions even when the imaginary component cancels. Literal a+bi entry
// does not. Extension to other complex powers is an inferred display model.
// Measured Ans and non-real variable storage retain this presentation hint.
function complexOperationResult(value, operands, introduceFraction = true) {
  const z = rz(value);
  const introduce = introduceFraction && operands.some((operand) => !isReal(operand));
  z.complexFraction = Object.fromEntries(['re', 'im'].map((part) =>
    [part, introduce || operands.some((operand) => operand.complexFraction?.[part])]));
  return z;
}

function complexSumResult(value, a, b) {
  const z = rz(value);
  // Measured: adding real 0.1 changes only the real component to decimal;
  // adding integer 0 preserves both fractions. Other sums/differences use
  // this inferred per-component rule until further physical calibration.
  z.complexFraction = Object.fromEntries(['re', 'im'].map((part) => [part,
    Boolean(a.complexFraction?.[part] || b.complexFraction?.[part]) &&
    [a, b].every((operand) => operand.complexFraction?.[part] || Number.isInteger(operand[part]))
  ]));
  return z;
}

function complexProductResult(a, b) {
  const z = rz(cmul(a, b));
  // Follow ac-bd and ad+bc so presentation moves with the contributing
  // components. Multiplication by i is physically measured; the general
  // mixed-product propagation remains an inferred presentation model.
  const term = (p, q) => ({
    value: numeric.mul(a[p], b[q]),
    fraction: a[p] !== 0 && b[q] !== 0 &&
      Boolean(a.complexFraction?.[p] || b.complexFraction?.[q]) &&
      (a.complexFraction?.[p] || Number.isInteger(a[p])) &&
      (b.complexFraction?.[q] || Number.isInteger(b[q]))
  });
  const combine = (terms) => terms.some((t) => t.fraction) &&
    terms.every((t) => t.fraction || Number.isInteger(t.value));
  z.complexFraction = {
    re: combine([term('re', 're'), term('im', 'im')]),
    im: combine([term('re', 'im'), term('im', 're')])
  };
  return z;
}

function binary(f, node, ctx, E, real) {
  if (f === 'add' || f === 'sub' || f === 'mul' || f === 'div') {
    const a = E(node.a), b = E(node.b);
    if (ctx.mode === 'BASE') {
      const x = a.re, y = b.re;
      let v;
      if (f === 'add') v = x + y;
      else if (f === 'sub') v = x - y;
      else if (f === 'mul') v = x * y;
      else { if (y === 0) err('Math', node.at); v = Math.trunc(x / y); }
      const bits = WORD_BITS[ctx.base] || 32;
      const min = -(2 ** (bits - 1));
      const max = 2 ** (bits - 1) - 1;
      if (v < min || v > max) err('Math');
      return C(Math.trunc(v));
    }
    if (f === 'div' && b.re === 0 && b.im === 0) err('Math', node.at);
    const z = f === 'add' ? complexSumResult(cadd(a, b, ctx.mode), a, b)
      : f === 'sub' ? complexSumResult(csub(a, b, ctx.mode), a, b)
      : f === 'mul' ? complexProductResult(a, b) : complexOperationResult(cdiv(a, b), [a, b]);
    return ctx.mode === 'COMP' ? nativeFractionOperation(z, a, b, f) : z;
  }
  if (f === 'pow') {
    const a = E(node.a), b = E(node.b);
    if (a.re === 0 && a.im === 0 && b.re === 0 && b.im === 0) err('Math');
    if (!isReal(b)) err('Math');
    if (isReal(a)) {
      if (a.re < 0 && !Number.isInteger(b.re)) {
        // A reduced odd denominator admits a real result. The numerator's
        // parity determines its sign; 2/5 must give a positive result.
        const fraction = toFraction(b.re, 15);
        if (!fraction || fraction.d % 2 === 0 ||
            Math.abs(fraction.sign * fraction.n / fraction.d - b.re) > 1e-12) err('Math');
        const sign = fraction.n % 2 === 0 ? 1 : -1;
        const value = sign * numeric.pow(-a.re, b.re);
        if (!Number.isFinite(value)) err('Math');
        return C(r15(value));
      }
      const v = numeric.pow(a.re, b.re);
      if (!isFinite(v)) err('Math');
      return C(r15(v));
    }
    // Physical generic-power probes accept 2, 3 and -1, but reject 0, 1,
    // 4 and -2. A domain limited to the three supported operations is the
    // current INFERRED model; other exponents still need physical measurements.
    // Algebraic operations avoid log/exp introducing a false real/imaginary
    // component for a purely imaginary base. Do not clamp small components.
    // Physical decimal ^(2) displays the same decimal components as native ²;
    // it does not introduce a fraction hint, but retains one from its operands.
    if (b.re === 2) return complexProductResult(a, a);
    if (b.re === 3) return complexCubeResult(a);
    if (b.re === -1) return complexOperationResult(cdiv(C(1), a), [a]);
    err('Math');
  }
  if (f === 'xroot') {
    const m = real(node.a), n = E(node.b);
    if (m === 0) err('Math');
    if (!isReal(n)) err('Math');
    if (n.re < 0) {
      if (!Number.isInteger(m) || m % 2 === 0) err('Math');
      return C(r15(-numeric.pow(-n.re, 1 / m)));
    }
    return C(r15(numeric.pow(n.re, 1 / m)));
  }
  if (f === 'nPr' || f === 'nCr') {
    const n = real(node.a), r = real(node.b);
    if (!Number.isInteger(n) || !Number.isInteger(r) || n < 0 || n >= 1e10 || r < 0 || r > n) err('Math');
    if (f === 'nCr') {
      const k = Math.min(r, n - r);
      // The shorter falling factorial must itself fit, even when nCr fits.
      // With k <= n/2 each factor is >= k+1, so overflow also bounds the loop.
      const limit = 10n ** 100n;
      let numerator = 1n, denominator = 1n;
      for (let i = 1; i <= k; i++) {
        numerator *= BigInt(n - i + 1);
        if (numerator >= limit) err('Math');
        denominator *= BigInt(i);
      }
      return C(r15(Number(numerator / denominator)));
    }
    let v = 1;
    for (let i = 0; i < r; i++) {
      v *= (n - i);
      // All factors are positive integers. Once the product leaves the
      // calculator's range it cannot recover, so huge r cannot block the UI.
      if (!isFinite(v) || v >= 1e100) err('Math');
    }
    return C(r15(v));
  }
  if (f === 'angle') {
    if (ctx.mode !== 'CMPLX') err('Syntax');
    const r = real(node.a), angle = real(node.b);
    if (r < 0) err('Math');
    return rz(rectangularParts(r, angle, ctx.angle));
  }
  if (f === 'eq' || f === 'ne') {
    const a = E(node.a), b = E(node.b);
    let equal = a.re === b.re && a.im === b.im;
    if (!equal && ctx.mode === 'COMP' && isReal(a) && isReal(b)) {
      // ON5: cancellation can leave different working digits for the same
      // short rational. Require matching exact origins on both operands.
      const left = quotientGuards.get(a)?.re, right = quotientGuards.get(b)?.re;
      equal = Boolean(boundedStoredOrigin(left) && right && left.n === right.n && left.d === right.d);
    }
    return C((f === 'eq' ? equal : !equal) ? 1 : 0);
  }
  if (['gt', 'lt', 'ge', 'le'].includes(f)) {
    const a = real(node.a), b = real(node.b);
    const ok = { eq: a === b, ne: a !== b, gt: a > b, lt: a < b, ge: a >= b, le: a <= b }[f];
    return C(ok ? 1 : 0);
  }
  if (['and', 'or', 'xor', 'xnor'].includes(f)) {
    const base = ctx.mode === 'BASE' ? ctx.base : 10;
    const a = toWord(real(node.a), base), b = toWord(real(node.b), base);
    const bits = WORD_BITS[base] || 32;
    let v = 0;
    for (let i = 0; i < bits; i++) {
      const x = Math.floor(a / 2 ** i) % 2, y = Math.floor(b / 2 ** i) % 2;
      let r;
      if (f === 'and') r = x & y;
      else if (f === 'or') r = x | y;
      else if (f === 'xor') r = x ^ y;
      else r = 1 - (x ^ y);
      v += r * 2 ** i;
    }
    return C(wrapWord(v, base));
  }
  err('Syntax');
  return null;
}

const completedTranscendentals = new Set([
  'sin', 'cos', 'tan', 'asin', 'acos', 'atan',
  'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh',
  'log', 'ln', 'exp10', 'expe'
]);

function callFn(f, args, ctx, E, real) {
  const value = rawCallFn(f, args, ctx, E, real);
  // W9: sin/cos/ln evaluated at the same stored argument compare equal
  // before and after assignment. Finish the function value at the memory
  // precision boundary, without changing equality or arithmetic guard digits.
  // Other transcendental functions share this local completion policy; the
  // three measured functions do not establish a complete firmware model.
  return completedTranscendentals.has(f)
    ? C(numeric.roundSignificant(value.re), numeric.roundSignificant(value.im))
    : value;
}

function rawCallFn(f, args, ctx, E, real) {
  const one = () => E(args[0]);
  const oneR = () => real(args[0]);

  switch (f) {
    case 'sin': case 'cos': case 'tan': {
      const z = one();
      if (!isReal(z)) err('Math');
      requireTrigAngle(z.re, ctx.angle);
      // Recognize exact axis angles in their original units. Converting 180°
      // to binary radians first leaves a false sin/tan remainder. Do not use
      // a result epsilon: nearby angles must keep their nonzero values.
      const axis = originAxis(f, args[0], ctx) ?? exactAxis(f, z.re, ctx.angle);
      if (axis !== undefined) return C(axis);
      const x = reducedRadians(z.re, ctx.angle);
      if (f === 'cos' && ctx.mode === 'COMP') {
        const cosine = Math.cos(x);
        if (Math.abs(cosine) < 1 - 1e-13) return C(cosine);
        // NP4a confirmed the lower 15-digit magnitude near +1. Compute
        // 1-|cos(x)| without subtracting two nearly equal binary values.
        const gapInLastPlaces = Math.sin(x) ** 2 / (1 + Math.abs(cosine)) * 1e15;
        // Limit the measured rule to the existing 13-place cancellation
        // range. Preserve rounding below half a place and outside the range.
        if (gapInLastPlaces < 0.5 || gapInLastPlaces > 100) return C(cosine);
        const magnitude = (1e15 - Math.ceil(gapInLastPlaces)) / 1e15;
        return C(Math.sign(cosine) * magnitude);
      }
      if (f === 'tan' && ctx.angle === 'Rad') {
        const q = Math.round(z.re / quarterTurn('Rad'));
        const delta = decimalAdd(z.re, -numeric.mul(quarterTurn('Rad'), q));
        // Exact poles were rejected above. Near them, decimal subtraction
        // before the cotangent identity avoids binary-pi cancellation; never
        // turn a finite neighbouring angle into a domain error.
        if (q % 2 !== 0 && Math.abs(delta) < 1e-8) return C(r15(-1 / Math.tan(delta)));
      }
      return C(r15(Math[f](x)));
    }
    case 'asin': case 'acos': {
      const x = oneR();
      if (Math.abs(x) > 1) err('Math');
      // Inverse-function endpoints and explicit angle-unit suffixes must
      // produce the same exact quarter turns as the calculator pi token.
      if (f === 'asin' && Math.abs(x) === 1) return C(x * quarterTurn(ctx.angle));
      if (f === 'acos' && x === 0) return C(quarterTurn(ctx.angle));
      if (f === 'acos' && x === -1) return C(2 * quarterTurn(ctx.angle));
      // Near either endpoint work with its decimal distance before taking
      // the half-angle. Both inverse functions depend on that same distance.
      if (Math.abs(x) > 0.5) {
        const distance = decimalAdd(1, -Math.abs(x));
        const angle = 2 * Math.asin(Math.sqrt(distance / 2));
        if (f === 'asin') {
          return C(r15(Math.sign(x) * decimalAdd(quarterTurn(ctx.angle), -fromRad(angle, ctx.angle))));
        }
        return C(r15(fromRad(x < 0 ? Math.PI - angle : angle, ctx.angle)));
      }
      return C(r15(fromRad(Math[f](x), ctx.angle)));
    }
    case 'atan': return C(r15(fromRad(Math.atan(oneR()), ctx.angle)));
    case 'sinh': {
      const x = oneR();
      if (Math.abs(x) > 230.2585092) err('Math');
      return C(r15(Math.sinh(x)));
    }
    case 'cosh': {
      const x = oneR();
      if (Math.abs(x) > 230.2585092) err('Math');
      return C(r15(Math.cosh(x)));
    }
    case 'tanh': return C(r15(Math.tanh(oneR())));
    // Casio's function input ranges can be narrower than their mathematical domains.
    case 'asinh': {
      const x = oneR();
      if (Math.abs(x) > 4.999999999e99) err('Math');
      return C(r15(Math.asinh(x)));
    }
    case 'acosh': {
      const x = oneR();
      if (x < 1 || x > 4.999999999e99) err('Math');
      return C(r15(numeric.acosh(x)));
    }
    case 'atanh': { const x = oneR(); if (Math.abs(x) >= 1) err('Math'); return C(r15(numeric.atanh(x))); }
    case 'log': {
      if (args.length === 2) {
        const b = real(args[0]), x = real(args[1]);
        if (b <= 0 || b === 1 || x <= 0) err('Math');
        return C(r15(numeric.ln(x) / numeric.ln(b)));
      }
      const x = oneR();
      if (x <= 0) err('Math');
      return C(r15(numeric.log10(x)));
    }
    case 'ln': {
      const x = oneR();
      if (x <= 0) err('Math');
      if (args.length !== 1) err('Arg');
      return C(r15(numeric.ln(x)));
    }
    case 'exp10': {
      const x = oneR();
      if (x >= 100) err('Math');
      const v = numeric.pow(10, x);
      if (!isFinite(v)) err('Math');
      return C(r15(v));
    }
    case 'expe': {
      const x = oneR();
      if (x > 230.2585092) err('Math');
      const v = Math.exp(x);
      if (!isFinite(v)) err('Math');
      return C(r15(v));
    }
    case 'sqrt': {
      const z = one();
      if (isReal(z)) {
        if (z.re < 0) {
          if (ctx.mode !== 'CMPLX') err('Math');
          return C(0, r15(numeric.sqrt(-z.re)));
        }
        return C(r15(numeric.sqrt(z.re)));
      }
      err('Math');
      return null;
    }
    case 'cbrt': return C(r15(Math.cbrt(oneR())));
    case 'Abs': { const z = one(); return C(r15(cabs(z))); }
    case 'arg': {
      if (ctx.mode !== 'CMPLX') err('Syntax');
      const z = one();
      if (z.re === 0 && z.im === 0) err('Math');
      // Unary negation can produce -0i; the measured negative real axis is +180°.
      const angle = z.im === 0 && z.re < 0 ? Math.PI : carg(z);
      return C(r15(fromRad(angle, ctx.angle)));
    }
    case 'Conjg': {
      const z = one(), result = C(z.re, -z.im);
      const guard=quotientGuards.get(z);
      if(guard)quotientGuards.set(result,{...guard,re:guard.re,im:qneg(guard.im)});
      if (z.complexFraction) result.complexFraction = { ...z.complexFraction };
      return result;
    }
    case 'Pol': {
      const x = real(args[0]), y = real(args[1]);
      if (x === 0 && y === 0) err('Math');
      const r = r15(Math.hypot(x, y));
      const th = r15(fromRad(Math.atan2(y, x), ctx.angle));
      return coordinateResult(r, th, ctx);
    }
    case 'Rec': {
      const r = real(args[0]), angle = real(args[1]);
      if (r < 0) err('Math');
      // Rec uses the same input-angle range as sin (Casio E-74).
      requireTrigAngle(angle, ctx.angle);
      const z = rz(rectangularParts(r, angle, ctx.angle));
      return coordinateResult(z.re, z.im, ctx);
    }
    case 'Rnd': {
      const z = one();
      if (z.im !== 0 && ctx.mode !== 'CMPLX') err('Math');
      // CMPLX rounds each displayed component, not the complex magnitude.
      return C(ctx.roundToDisplay(z.re), ctx.roundToDisplay(z.im));
    }
    case 'Not': {
      const base = ctx.mode === 'BASE' ? ctx.base : 10;
      const bits = WORD_BITS[base] || 32;
      return C(wrapWord(2 ** bits - 1 - toWord(oneR(), base), base));
    }
    case 'Neg': {
      const base = ctx.mode === 'BASE' ? ctx.base : 10;
      const value = -oneR(), bits = WORD_BITS[base] || 32;
      // Physical BIN Neg(minimum) is Math ERROR: the positive counterpart
      // does not fit. Validate before a parent expression can hide overflow.
      if (value < -(2 ** (bits - 1)) || value > 2 ** (bits - 1) - 1) err('Math');
      return C(value);
    }
  }
  err('Syntax');
  return null;
}

// ---------------------------------------------------------------------------
// Sexagesimal helpers used by the °′″ key and the decimal/DMS toggle.
export function dmsToDecimal(d, m, s) {
  const sign = d < 0 ? -1 : 1;
  return sign * (Math.abs(d) + m / 60 + s / 3600);
}
export function decimalToDms(x) {
  const sign = x < 0 ? -1 : 1;
  if (!Number.isFinite(x)) return { d: x, m: NaN, s: NaN, sign };
  // Round the whole angle in hundredths of a second before splitting it.
  // Decimal arithmetic preserves ties such as 2.0013875 degrees.
  const { coefficient, scale } = decimalParts(Math.abs(x));
  const scaled = coefficient * 360000n;
  const divisor = 10n ** BigInt(Math.max(0, scale));
  const ticks = scale < 0
    ? scaled * 10n ** BigInt(-scale)
    : (scaled + divisor / 2n) / divisor;
  return {
    d: Number(ticks / 360000n) * sign,
    m: Number(ticks / 6000n % 60n),
    s: Number(ticks % 6000n) / 100,
    sign
  };
}

// Decimal -> fraction, used when toggling a result to fraction form.
export function toFraction(x, maxElems = 10) {
  if (!isFinite(x)) return null;
  const sign = x < 0 ? -1 : 1;
  let v = Math.abs(x);
  let bestN = 0, bestD = 1;
  let h1 = 1, h2 = 0, k1 = 0, k2 = 1, b = v;
  for (let i = 0; i < 32; i++) {
    const a = Math.floor(b);
    const h = a * h1 + h2, k = a * k1 + k2;
    if (k > 1e9) break;
    h2 = h1; h1 = h; k2 = k1; k1 = k;
    bestN = h; bestD = k;
    if (Math.abs(h / k - v) < 1e-11 * Math.max(1, v)) break;
    const f = b - a;
    if (f < 1e-12) break;
    b = 1 / f;
  }
  if (!bestD || Math.abs(bestN / bestD - v) > 1e-9 * Math.max(1, v)) return null;
  const int = Math.floor(bestN / bestD);
  const num = bestN - int * bestD;
  const elems = (int ? String(int).length + 1 : 0) + String(num || bestN).length +
    String(bestD).length + 1;
  if (elems > maxElems) return null;
  return { sign, n: bestN, d: bestD, int, num };
}
