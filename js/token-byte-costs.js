// Program token storage costs, independent of display spelling.
const LEGACY_ONE_BYTE_IDS = `
  0 1 2 3 4 5 6 7 8 9 . EXP hexA hexB hexC hexD hexE hexF
  pi napier imag varA varB varC varD varX varY varM
  ( ) , ; : sqr cube fact dms degU radU graU pct neg
  baseD baseH baseB baseO frac add sub mul div nPr nCr angle
  eq ne gt lt ge le Sn regA regB regC regR estY
  pIn pAsg pOut pJump
`.trim().split(/\s+/);

const LEGACY_TWO_BYTE_IDS = `
  Ans Ran sin cos tan asin acos atan sinh cosh tanh asinh acosh atanh
  log ln exp10 expe sqrt cbrt Abs arg Conjg Pol Rec Rnd Not Neg
  recip pow xroot and or xor xnor Sx2 Sx Sy2 Sy Sxy Sx2y Sx3 Sx4
  xbar xsn xsn1 ybar ysn ysn1 minX maxX minY maxY estX estX1 estX2
  toRect toPolar pGoto pLbl pIf pThen pElse pIfEnd pFor pTo pStep
  pNext pWhile pWhileEnd pBreak pDeg pRad pGra pFix pSci pNorm
  pFreqOn pFreqOff pClrMemory pClrStat pMplus pMminus pDec pHex
  pBin pOct pDT
`.trim().split(/\s+/);

export const LEGACY_BYTE_COST = Object.freeze(Object.fromEntries([
  ...LEGACY_ONE_BYTE_IDS.map((id) => [id, 1]),
  ...LEGACY_TWO_BYTE_IDS.map((id) => [id, 2])
]));


// User clarification, 2026-10-24: every native Program symbol occupies one
// storage byte, regardless of its printed name or source-text length.
// Keep ordinary expression/input accounting in its separate function below.
export function byteCost(id) {
  inputByteCost(id); // Reject unknown identities as before.
  return 1;
}
export function inputByteCost(id) {
  if (Object.hasOwn(LEGACY_BYTE_COST, id)) return LEGACY_BYTE_COST[id];
  if (id.startsWith("CONST_") || id.startsWith("fv_")) return id.startsWith("fv_") ? 1 : 2;
  throw new Error(`missing byte cost for token ${id}`);
}
