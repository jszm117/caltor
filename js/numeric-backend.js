// Shared decimal arithmetic policy.
export class JsNumberBackend {
  // Literal loading does not normalize. Arithmetic methods, memory writes and
  // display formatting each apply their own measured precision boundary.
  roundWorking(x) { return x; }

  roundSignificant(x, digits = 15) {
    if (!Number.isFinite(x) || x === 0) return x;
    return Number(x.toPrecision(digits));
  }

  add(a, b) { return a + b; }
  sub(a, b) { return a - b; }
  expressionAdd(a, b) { return this.add(a, b); }
  expressionSub(a, b) { return this.sub(a, b); }
  mul(a, b) { return a * b; }
  div(a, b) { return a / b; }
  pow(a, b) { return Math.pow(a, b); }
  sqrt(a) { return Math.sqrt(a); }
  acosh(a) { return Math.acosh(a); }
  atanh(a) { return Math.atanh(a); }
  ln(a) { return Math.log(a); }
  log10(a) { return Math.log10(a); }

  displayRound(x, setup) {
    if (setup.disp === 'Fix') return decimalRoundFixed(x, setup.digits);
    if (setup.disp === 'Sci') return decimalRoundSignificant(x, setup.digits === 0 ? 10 : setup.digits);
    return decimalRoundSignificant(x, 10);
  }
}

// Use each stored Number's shortest decimal spelling for exact add/sub before
// rounding. This is a measured improvement, not a complete Casio BCD model.
export function decimalParts(value) {
  const [mantissa, exponent = '0'] = String(value).toLowerCase().split('e');
  const negative = mantissa.startsWith('-');
  const digits = negative ? mantissa.slice(1) : mantissa;
  const point = digits.indexOf('.');
  const fraction = point < 0 ? 0 : digits.length - point - 1;
  const coefficient = BigInt(digits.replace('.', '')) * (negative ? -1n : 1n);
  return { coefficient, scale: fraction - Number(exponent) };
}

export function decimalAdd(a, b) {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return a + b;
  const left = decimalParts(a), right = decimalParts(b);
  const scale = Math.max(left.scale, right.scale);
  if (scale - Math.min(left.scale, right.scale) > 1000) return a + b;
  const sum = left.coefficient * 10n ** BigInt(scale - left.scale) +
    right.coefficient * 10n ** BigInt(scale - right.scale);
  return Number(`${sum}e${-scale}`);
}

// Calibrated accumulator: align operands to 16 decimal positions relative to
// the larger operand, truncating each toward zero before addition. The result
// then passes through the existing 15-digit working-result boundary. Applying
// the same rule to explicit and internal sums avoids binary carry before the
// decimal cut. This is a measured approximation, not a firmware reconstruction.
function workingDecimalAdd(a, b) {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return a + b;
  const left = decimalParts(a), right = decimalParts(b);
  const scale = a === 0 || b === 0
    ? Math.max(left.scale, right.scale)
    : 15 - Math.max(decimalExponent(a), decimalExponent(b));
  const align = ({coefficient, scale: sourceScale}) => sourceScale <= scale
    ? coefficient * 10n ** BigInt(scale - sourceScale)
    : coefficient / 10n ** BigInt(sourceScale - scale);
  return truncateCoefficient(align(left) + align(right), scale);
}

// Measured cancellation probes lose differences 13 or more decimal positions
// below their operands. A zero after subtraction does not locate the loss at
// the earlier addition. REG Program evidence requires keeping operand guards
// until cancellation/normalization; ordinary REG probes still return zero.
// Keep the existing CMPLX operand policy: widening it produced extra outputs
// in a hardware-confirmed Program replay. This remains a bounded model.
export function alignedDecimalAdd(a, b, operandDigits = 13) {
  const add = workingDecimalAdd;
  if (!Number.isFinite(a) || !Number.isFinite(b) || a === 0 || b === 0) {
    return add(a, b);
  }
  const exponent = (value) => {
    const {coefficient, scale} = decimalParts(value);
    const magnitude = coefficient < 0n ? -coefficient : coefficient;
    return magnitude.toString().length - 1 - scale;
  };
  const leftExponent = exponent(a), rightExponent = exponent(b);
  if (Math.abs(leftExponent - rightExponent) >= operandDigits) {
    return leftExponent > rightExponent ? a : b;
  }
  const sum = add(a, b);
  if (sum !== 0 && Math.sign(a) !== Math.sign(b) &&
      Math.max(leftExponent, rightExponent) - exponent(sum) >= 13) {
    return 0;
  }
  return sum;
}

function decimalExponent(value) {
  const {coefficient, scale} = decimalParts(value);
  return (coefficient < 0n ? -coefficient : coefficient).toString().length - 1 - scale;
}

function truncateCoefficient(coefficient, scale) {
  const magnitude = coefficient < 0n ? -coefficient : coefficient;
  const drop = Math.max(0, magnitude.toString().length - 15);
  return Number(`${coefficient / 10n ** BigInt(drop)}e${drop - scale}`);
}

// Measured operation results retain 15 decimal digits, with normalization near
// an 11-digit target. The distance must be strictly below 1E-13 at magnitude 1;
// use decimal exponents so this scales correctly across powers of ten.
// This bounded calibration does not claim to reproduce the complete firmware.
function finishArithmetic(value) {
  if (!Number.isFinite(value) || value === 0) return value;
  const {coefficient, scale} = decimalParts(value);
  const cut = truncateCoefficient(coefficient, scale);
  const target = decimalRoundSignificant(cut, 11);
  const delta = decimalAdd(cut, -target);
  if (delta === 0) return cut;
  // Use the pre-normalization magnitude: crossing a power of ten must not
  // enlarge the normalization window. Confirmed by two-sided boundary probes.
  const exponent = decimalExponent(cut);
  // Carrying a final decimal unit into the next decade is a normalization
  // boundary, not a fuzzy equality rule. The 0.2.12 feedback 9(10000/3)^2
  // reaches the immediate 14-significant-digit predecessor of 1E8. Retain
  // the strict window elsewhere, including the measured two-unit neighbour.
  const powerOfTen = (value) => {
    const {coefficient} = decimalParts(value);
    return /^10*$/.test((coefficient < 0n ? -coefficient : coefficient).toString());
  };
  const decadeCarry = decimalExponent(target) === exponent + 1 &&
    powerOfTen(target) && powerOfTen(delta) && decimalExponent(delta) === exponent - 13;
  return exponent - decimalExponent(delta) >= 14 || decadeCarry
    ? target : cut;
}

function decimalProduct(a, b) {
  if (!Number.isFinite(a) || !Number.isFinite(b) || a === 0 || b === 0) return a * b;
  const left = decimalParts(a), right = decimalParts(b);
  // Cut the decimal product before converting it back to binary Number.
  return truncateCoefficient(left.coefficient * right.coefficient, left.scale + right.scale);
}

function decimalQuotient(a, b) {
  if (!Number.isFinite(a) || !Number.isFinite(b) || a === 0 || b === 0) return a / b;
  const left = decimalParts(a), right = decimalParts(b);
  // Number's shortest decimal coefficient has at most 17 digits. Forty extra
  // places leave enough quotient digits for the 15-digit cut, even at 1 / 1E16.
  const extra = 40;
  const quotient = left.coefficient * 10n ** BigInt(extra) / right.coefficient;
  return truncateCoefficient(quotient, left.scale - right.scale + extra);
}

export class DecimalCandidateBackend extends JsNumberBackend {
  expressionAdd(a, b, mode) {
    return mode === 'REG' ? finishArithmetic(alignedDecimalAdd(a, b, 16)) : this.add(a, b);
  }
  expressionSub(a, b, mode) {
    return mode === 'REG' ? finishArithmetic(alignedDecimalAdd(a, -b, 16)) : this.sub(a, b);
  }
  roundSignificant(x, digits = 15) { return super.roundSignificant(x, digits); }
  add(a, b) { return finishArithmetic(alignedDecimalAdd(a, b)); }
  sub(a, b) { return finishArithmetic(alignedDecimalAdd(a, -b)); }
  mul(a, b) { return finishArithmetic(decimalProduct(a, b)); }
  div(a, b) { return finishArithmetic(decimalQuotient(a, b)); }
  pow(a, b) {
    if (b === 0.5 && a >= 0) return this.sqrt(a);
    // Preserve the working precision of the root before taking its reciprocal.
    if (b === -0.5 && a > 0) return this.div(1, this.sqrt(a));
    if (a >= 0.5 && a <= 1.5) {
      const offset = decimalAdd(a, -1);
      // The relative error in a^b is about b times the relative base error.
      // Switch when the decimal-to-binary discrepancy can affect the product.
      if (Math.abs(b * (offset - (a - 1))) > a * Number.EPSILON) {
        return finishArithmetic(Math.exp(b * Math.log1p(offset)));
      }
    }
    return finishArithmetic(super.pow(a, b));
  }
  sqrt(a) {
    if (!(a > 0) || !Number.isFinite(a)) return Math.sqrt(a);
    // Scale the radicand so the integer root contains 15 significant digits.
    // A binary sqrt can land just above a decimal cut, e.g. sqrt(1+1E-10).
    const {coefficient, scale} = decimalParts(a);
    const exponent = coefficient.toString().length - 1 - scale;
    const places = 14 - Math.floor(exponent / 2);
    const scaled = coefficient * 10n ** BigInt(2 * places - scale);
    let root = BigInt(Math.floor(Math.sqrt(Number(scaled))));
    if (root * root > scaled) root--;
    else if ((root + 1n) ** 2n <= scaled) root++;
    return finishArithmetic(Number(`${root}e${-places}`));
  }
  acosh(a) {
    if (a < 1 || a > 1.5) return super.acosh(a);
    const d = decimalAdd(a, -1);
    return Math.log1p(d + Math.sqrt(d * (2 + d)));
  }
  atanh(a) {
    const x = Math.abs(a);
    if (x < 0.5 || x >= 1) return super.atanh(a);
    return Math.sign(a) * 0.5 * (Math.log1p(x) - Math.log(decimalAdd(1, -x)));
  }
  ln(a) {
    // Near 1, the binary representation error in a becomes a large relative
    // error in ln(a). Recover the offset from the stored decimal spelling,
    // before log1p, without applying arithmetic's cancellation/absorption rules.
    // This does not recover digits already lost by earlier arithmetic.
    return a >= 0.5 && a <= 1.5 ? Math.log1p(decimalAdd(a, -1)) : super.ln(a);
  }
  log10(a) {
    return a >= 0.5 && a <= 1.5 ? this.ln(a) / Math.LN10 : super.log10(a);
  }
}

export const numeric = new DecimalCandidateBackend();

// Round the stored decimal spelling to a fixed number of places. Half-way
// values round away from zero; avoid binary toFixed tie misclassification.
export function decimalRoundFixed(x, digits) {
  if (!Number.isFinite(x) || x === 0) return x;
  if (!Number.isInteger(digits) || digits < 0 || digits > 100) throw new RangeError('Invalid decimal places');
  const {coefficient, scale} = decimalParts(x);
  if (scale <= digits) return x;
  const divisor = 10n ** BigInt(scale - digits);
  const negative = coefficient < 0n;
  const magnitude = negative ? -coefficient : coefficient;
  let rounded = magnitude / divisor;
  if ((magnitude % divisor) * 2n >= divisor) rounded++;
  return Number((negative ? '-' : '') + rounded + 'e-' + digits);
}

// Display/Rnd rounding in decimal; internal arithmetic keeps its own precision.
export function decimalRoundSignificant(x, digits) {
  if (!Number.isFinite(x) || x === 0) return x;
  if (!Number.isInteger(digits) || digits < 1 || digits > 100) throw new RangeError('Invalid significant digits');
  const {coefficient, scale} = decimalParts(x);
  const negative = coefficient < 0n;
  const magnitude = negative ? -coefficient : coefficient;
  const drop = magnitude.toString().length - digits;
  if (drop <= 0) return x;
  const divisor = 10n ** BigInt(drop);
  let rounded = magnitude / divisor;
  if ((magnitude % divisor) * 2n >= divisor) rounded++;
  return Number((negative ? '-' : '') + rounded + 'e' + (drop - scale));
}
