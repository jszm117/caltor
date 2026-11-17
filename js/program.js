// program.js — the BASIC-like program store and interpreter.
//
// Program memory holds 680 bytes shared by four areas.  A program runs as a
// resumable state machine so that "?" input prompts and "◢" output pauses can
// hand control back to the keyboard between steps.

import { parse, evaluate, CalcError, C, r15, asComplex, storeVariable, variableValue, quotientCounterAdvance } from './expr.js';
import { decimalAdd } from './numeric-backend.js';
import { K, textOf, bytesOf } from './tokens.js';

export const PROGRAM_MEMORY = 680;

export class Program {
  constructor(mode, tokens) {
    this.mode = mode;
    this.tokens = tokens;
  }
  get bytes() { return bytesOf(this.tokens); }
  start(machine, options = {}) { return new Run(machine, this.tokens, options); }
}

const err = (kind) => { throw new CalcError(kind); };
const parameterlessCommands = new Set(['Next','WhileEnd','Break','IfEnd',
  'Deg','Rad','Gra','FreqOn','FreqOff','ClrMemory','ClrStat','Dec','Hex','Bin','Oct']);

function splitStatements(tokens) {
  const stmts = [];
  let cur = [];
  let start = 0;
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.k === K.SEP && t.s === ':') { stmts.push({ toks: cur, pause: false, sourceStart: start, colonAt:i }); cur = []; start = i + 1; continue; }
    if (t.c === 'output') { stmts.push({ toks: cur, pause: true, sourceStart: start }); cur = []; start = i + 1; continue; }
    // Split control tokens for indexing: Then For/While needs its own loop
    // address, and a label after an invalid Break must remain visible to Goto.
    // Splitting is not permission to execute an unterminated command. Hardware
    // R8/R9 rejects Break WhileEnd / Next Else when reached, after earlier
    // displays. Preserve that boundary for runtime validation and REPLAY.
    const head = cur[0]?.c;
    const inlineControl = cur.length === 1 && (
      (['Then','Else'].includes(head) && ['If','For','While'].includes(t.c)) ||
      (['Next','WhileEnd','Break','IfEnd'].includes(head) &&
       ['Then','Else','IfEnd','For','Next','While','WhileEnd','Break','Lbl'].includes(t.c))
    );
    if (inlineControl) {
      // The physical 242B matrix program rejects the If immediately after Then.
      const invalidBoundary = parameterlessCommands.has(head) || (head === 'Then' && t.c === 'If');
      const boundaryErrorAt = invalidBoundary ? i : undefined;
      stmts.push({ toks: cur, pause: false, sourceStart: start, boundaryErrorAt });
      cur = []; start = i;
    }
    cur.push(t);
  }
  stmts.push({ toks: cur, pause: false, sourceStart: start });
  return stmts.filter((s, i) => s.toks.length || s.pause || i === 0);
}

export class Run {
  constructor(machine, tokens, options = {}) {
    this.m = machine;
    this.stmts = splitStatements(tokens);
    this.pc = 0;
    this.ifStack = [];
    this.loops = [];
    this.last = null;
    this.lastTokens = [];
    this.lastDisplayValue = null;
    this.waiting = null;
    this.labelEntry = null;
    this.completionStatement = null;
    this.index();
  }

  index() {
    this.labels = {};
    this.labelOffsets = {};
    this.ifMap = {};
    this.loopMap = {};
    const ifs = [], fors = [], whiles = [];
    this.stmts.forEach((s, i) => {
      const c = s.toks[0] && s.toks[0].c;
      // W21: Then Lbl is a native instruction boundary, even though the
      // wrapper and label share a statement. Jump directly to the label,
      // without executing a Then/Else branch wrapper a second time.
      const labelOffset = c === 'Then' || c === 'Else' ? 1 : 0;
      if (s.toks[labelOffset]?.c === 'Lbl') {
        const d = s.toks[labelOffset + 1];
        if (d && d.k === K.DIGIT) {
          this.labels[d.s] = i;
          this.labelOffsets[d.s] = labelOffset;
        }
      }
      if (c === 'If') ifs.push({ i, elseIdx: -1, hasThen: false });
      else if (c === 'Then') {
        if (!ifs.length || ifs[ifs.length - 1].hasThen) err('Syntax');
        ifs[ifs.length - 1].hasThen = true;
      }
      else if (c === 'Else') {
        if (!ifs.length || !ifs[ifs.length - 1].hasThen || ifs[ifs.length - 1].elseIdx >= 0) err('Syntax');
        ifs[ifs.length - 1].elseIdx = i;
      }
      else if (c === 'IfEnd') {
        const f = ifs.pop();
        if (!f || !f.hasThen) err('Syntax');
        this.ifMap[f.i] = { elseIdx: f.elseIdx, endIdx: i };
        if (f.elseIdx >= 0) this.ifMap[f.elseIdx] = { endIdx: i };
      } else if (c === 'For') fors.push(i);
      else if (c === 'Next') {
        const f = fors.pop();
        if (f === undefined) err('Syntax');
        this.loopMap[f] = i;
        this.loopMap[i] = f;
      } else if (c === 'While') whiles.push(i);
      else if (c === 'WhileEnd') {
        const w = whiles.pop();
        if (w === undefined) err('Syntax');
        this.loopMap[w] = i;
        this.loopMap[i] = w;
      }
    });
    // The guide explicitly permits a missing IfEnd (with a warning that it can
    // make everything after the If part of the branch). Close such frames at
    // end-of-program, but an If without Then is always a Syntax ERROR.
    while (ifs.length) {
      const f = ifs.pop();
      if (!f.hasThen) err('Syntax');
      this.ifMap[f.i] = { elseIdx: f.elseIdx, endIdx: this.stmts.length };
      if (f.elseIdx >= 0) this.ifMap[f.elseIdx] = { endIdx: this.stmts.length };
    }
    if (fors.length || whiles.length) err('Syntax');
  }

  ctx() { return this.m.ctx(); }

  evalTokens(toks) {
    if (!toks.length) err('Syntax');
    const ast = parse(toks, this.ctx());
    const value = evaluate(ast, this.ctx());
    return value;
  }

  evalCondition(toks) {
    const memory = toks[toks.length - 1];
    const memoryTail = memory?.c === 'M+' || memory?.c === 'M-';
    const value = this.evalTokens(memoryTail ? toks.slice(0, -1) : toks);
    // Complex equality yields a real boolean; an un-compared complex value
    // itself cannot be used as an If / While / conditional-jump condition.
    if (value.im !== 0) err('Math');
    // If/While with a native memory tail accumulates the tested value but
    // preserves arithmetic Ans (physical R3/R4: the first output is still 7).
    if (memoryTail) this.accumulateMemory(value, memory.c);
    return value;
  }

  accumulateMemory(value, command) {
    const current = asComplex(this.m.vars.M);
    const sign = command === 'M+' ? 1 : -1;
    const next = C(decimalAdd(current.re, sign * value.re), decimalAdd(current.im, sign * value.im));
    if (!Number.isFinite(next.re) || !Number.isFinite(next.im) ||
        Math.abs(next.re) >= 1e100 || Math.abs(next.im) >= 1e100) err('Math');
    storeVariable(this.m.vars, 'M', next);
  }

  /** Advance until the program finishes or needs the keyboard. */
  step() {
    let guard = 0;
    for (;;) {
      if (guard++ > 200000) err('Time');
      if (this.pc >= this.stmts.length) {
        const ending = this.completionStatement;
        return {
          done: true,
          value: this.last,
          expressionTokens: this.lastTokens,
          displayValue: this.lastDisplayValue,
          completionValuePending: !ending?.pause && !!ending?.toks.length && !ending.toks[0]?.c,
          completionPaused: !!ending?.pause,
          completionText: textOf(ending?.toks || [])
        };
      }
      const indexed = this.stmts[this.pc];
      const s = this.labelEntry?.pc === this.pc
        ? { ...indexed, toks: indexed.toks.slice(this.labelEntry.offset) } : indexed;
      this.labelEntry = null;
      const r = this.exec(s);
      // A jump can skip the rest of the source (e.g. Else with implicit
      // IfEnd). Only a statement that finished or paused can label the result.
      if (!r?.jumped) this.completionStatement = this.stmts[this.pc] ?? s;
      if (r && r.wait) return r;
      if (r && r.jumped) {
        // W18: Goto commits its target, then an explicit display pauses
        // before executing the destination. Resume at that target once.
        if (r.pauseAfterJump) {
          this.completionStatement = s;
          this.waiting = 'output';
          return { kind: 'output', value: this.last || C(0), text: textOf(s.toks).slice(0, 16),
            expressionTokens: this.lastTokens, displayValue: this.lastDisplayValue };
        }
        continue;
      }
      if (s.pause && !r?.skipPause) {
        this.pc++;
        this.waiting = 'output';
        return { kind: 'output', value: this.last || C(0), text: textOf(s.toks).slice(0, 16),
          expressionTokens: this.lastTokens, displayValue: this.lastDisplayValue };
      }
      this.pc++;
    }
  }

  rememberResult(value, tokens, displayValue = value) {
    this.last = value;
    this.lastTokens = tokens;
    this.lastDisplayValue = displayValue;
  }

  provide(value, tokens = []) {
    if (!this.waiting || this.waiting.kind !== 'input') err('Syntax');
    storeVariable(this.m.vars, this.waiting.varName, value);
    this.rememberResult(variableValue(this.m.vars, this.waiting.varName, this.m.mode), tokens, value);
    this.waiting = null;
    this.pc++;

  }

  resume() { this.waiting = null; }

  exec(s) {
    const toks = s.toks;
    if (!toks.length) return null;
    const head = toks[0];
    const c = head.c;
    // A command must consume its complete statement. Never silently discard
    // an expression/assignment after a parameterless command or label.
    // Validate at execution time so skipped branches keep their old lifetime.
    if (s.boundaryErrorAt !== undefined && c !== 'Next') {
      const error = new CalcError('Syntax');
      error.programSourceAt = s.boundaryErrorAt;
      throw error;
    }
    if (parameterlessCommands.has(c) && toks.length !== 1) err('Syntax');
    if ((c === 'Lbl' || c === 'Goto') &&
        (toks.length !== 2 || toks[1].k !== K.DIGIT)) err('Syntax');
    if (['Fix','Sci','Norm'].includes(c) &&
        (toks.length !== 2 || toks[1].k !== K.DIGIT ||
         (c === 'Norm' && !['1','2'].includes(toks[1].s)))) err('Syntax');

    // conditional jump:  cond ⇒ statement
    const jumpAt = toks.findIndex((t) => t.c === 'Jump');
    if (jumpAt >= 0 && !c) {
      if (toks[jumpAt + 1]?.c === 'While') err('Syntax');
      const cond = this.evalCondition(toks.slice(0, jumpAt));
      this.rememberResult(cond, toks.slice(0, jumpAt));
      this.m.ans = cond;
      if (cond.re !== 0) return this.exec({ toks: toks.slice(jumpAt + 1), pause: false,
        statPause: Boolean(s.pause || s.statPause), jumpPause: Boolean(s.pause || s.jumpPause) });
      return { skipPause: true };
    }

    switch (c) {
      case 'Lbl': return null;
      case 'Goto': {
        const d = toks[1];
        if (!d || this.labels[d.s] === undefined) err('Go');
        const target = this.labels[d.s];
        // A jump out of a loop releases its active frame. A label inside
        // its body keeps the counter and bounds for the subsequent Next.
        this.loops = this.loops.filter(frame => {
          const start = frame.kind === 'for' ? frame.body : frame.start;
          return target > start && target < frame.exit;
        });
        this.pc = target;
        this.labelEntry = this.labelOffsets[d.s] ? { pc: target, offset: this.labelOffsets[d.s] } : null;
        return { jumped: true, pauseAfterJump: Boolean(s.pause || s.jumpPause) };
      }
      case 'If': {
        const cond = this.evalCondition(toks.slice(1));
        // Testing a condition must preserve the previous arithmetic Ans.
        // Published programs branch on Ans and then use that same value.
        const map = this.ifMap[this.pc];
        if (!map) err('Syntax');
        // One frame is pushed on either path so that IfEnd always has exactly
        // its own frame to pop.
        if (cond.re !== 0) {
          this.ifStack.push({ endIdx: map.endIdx, branch: 'then' });
          return null;
        }
        this.ifStack.push({ endIdx: map.endIdx, branch: 'else' });
        this.pc = map.elseIdx >= 0 ? map.elseIdx : map.endIdx;
        return { jumped: true };
      }
      case 'Then':
        // R2 hardware: an explicit colon immediately after Then is invalid.
        // A native Then For boundary has no colon and remains valid (R1).
        if (toks.length === 1 && s.colonAt !== undefined) {
          const error = new CalcError('Syntax');
          error.programSourceAt = s.colonAt;
          throw error;
        }
        return toks.length > 1 ? this.exec({ toks: toks.slice(1), pause: false,
          statPause: Boolean(s.pause || s.statPause), jumpPause: Boolean(s.pause || s.jumpPause) }) : null;
      case 'Else': {
        const frame = this.ifStack[this.ifStack.length - 1];
        const map = this.ifMap[this.pc];
        // Falling into Else from the true branch means the work is done.
        if (frame && map && frame.branch === 'then' && frame.endIdx === map.endIdx) {
          this.pc = map.endIdx;
          return { jumped: true };
        }
        return toks.length > 1 ? this.exec({ toks: toks.slice(1), pause: false,
          statPause: Boolean(s.pause || s.statPause), jumpPause: Boolean(s.pause || s.jumpPause) }) : null;
      }
      case 'IfEnd':
        if (this.ifStack.length) this.ifStack.pop();
        return null;
      case 'For': return this.forStart(toks);
      case 'Next': {
        const nextPc = this.pc;
        const result = this.forNext();
        // Physical R10 repeats the body before inspecting a missing separator
        // after Next. Validate that boundary only when the loop falls through.
        if (this.pc === nextPc && s.boundaryErrorAt !== undefined) {
          const error = new CalcError('Syntax');
          error.programSourceAt = s.boundaryErrorAt;
          throw error;
        }
        return result;
      }
      case 'While': {
        // Physical mixed For/While nesting also fails: one loop at a time.
        // Runtime-only validation permits nested source in a skipped branch.
        if (this.loops.length) err('Syntax');
        const cond = this.evalCondition(toks.slice(1));
        // Like If, While tests control flow without replacing arithmetic Ans.
        // Otherwise While Abs(X):Rnd(Ans loses X's sign and imaginary part.
        // W14: an explicit pause on While displays its condition, not the
        // previous expression or DT input. Only the display lifetime changes.
        if (s.pause) this.rememberResult(cond, toks.slice(1));
        if (cond.re === 0) {
          // W11: a terminating While test displays 0 when the program ends
          // at WhileEnd, but arithmetic Ans still holds the body's result.
          this.rememberResult(cond, toks.slice(1));
          this.pc = this.loopMap[this.pc];
          return null;
        }
        this.loops.push({ kind: 'while', start: this.pc, exit: this.loopMap[this.pc] });
        return null;
      }
      case 'WhileEnd': {
        const start = this.loopMap[this.pc];
        while (this.loops.length && this.loops[this.loops.length - 1].start !== start) this.loops.pop();
        if (this.loops.length) this.loops.pop();
        this.pc = start - 1;
        return null;
      }
      case 'Break': {
        const f = this.loops.pop();
        if (!f) err('Syntax');
        this.pc = f.exit;
        return null;
      }
      case 'input': return this.inputPrompt(toks);
      case 'Deg': case 'Rad': case 'Gra':
        this.m.setup.angle = c; return null;
      case 'Fix': case 'Sci': {
        const d = toks[1];
        this.m.setup.disp = c;
        this.m.setup.digits = d ? Number(d.s) : 0;
        if (c === 'Sci' && this.m.setup.digits === 0) this.m.setup.digits = 10;
        return null;
      }
      case 'Norm': {
        const d = toks[1];
        this.m.setup.disp = 'Norm';
        this.m.setup.norm = d && d.s === '2' ? 2 : 1;
        return null;
      }
      case 'FreqOn': this.m.setStatFrequency(true); return null;
      case 'FreqOff': this.m.setStatFrequency(false); return null;
      case 'ClrMemory':
        for (const k of Object.keys(this.m.vars)) storeVariable(this.m.vars, k, 0);
        return null;
      case 'ClrStat': this.m.stat.clearSamples(); return null;
      case 'Dec': this.m.base = 10; return null;
      case 'Hex': this.m.base = 16; return null;
      case 'Bin': this.m.base = 2; return null;
      case 'Oct': this.m.base = 8; return null;
      default: break;
    }

    // assignment:  expr → VAR
    const arrow = toks.findIndex((t) => t.c === 'assign');
    if (arrow >= 0) {
      const target = toks[arrow + 1];
      // Assignment ends its statement. Following expressions need a separator.
      if (!target || !target.v || arrow + 2 !== toks.length) err('Syntax');
      const expression = toks.slice(0, arrow);
      const memory = expression[expression.length - 1];
      let v;
      if (memory?.c === 'M+' || memory?.c === 'M-') {
        this.exec({ toks: expression, pause: false });
        v = this.last;
      } else v = this.evalTokens(expression);
      storeVariable(this.m.vars, target.v, v);
      this.rememberResult(variableValue(this.m.vars, target.v, this.m.mode), expression, v);
      this.m.ans = this.last;
      return null;
    }

    // trailing memory / statistics commands
    const tail = toks[toks.length - 1];
    if (tail && (tail.c === 'M+' || tail.c === 'M-')) {
      const v = this.evalTokens(toks.slice(0, -1));
      this.accumulateMemory(v, tail.c);
      this.rememberResult(v, toks.slice(0, -1));
      this.m.ans = v;
      return null;
    }
    if (tail && tail.c === 'DT') {
      const saved = this.m.tokens;
      this.m.tokens = toks.slice(0, -1);
      try {
        this.m.statEnter();
      } catch (e) {
        if (e instanceof CalcError && e.at >= 0) {
          const statement = this.stmts[this.pc];
          const innerOffset = statement.toks.indexOf(toks[0]);
          e.programSourceAt = statement.sourceStart + Math.max(0, innerOffset) + e.at;
        }
        throw e;
      } finally {
        this.m.tokens = saved;
      }
      this.m.screen = 'prog';
      // W17: DT followed by a pause displays the data-line count (1,2),
      // not its x operand, previous result, or total frequency n (1,5).
      // statEnter already keeps arithmetic Ans as x; do not replace it.
      if (s.pause || s.statPause) this.rememberResult(C(this.m.stat.count), toks);
      return null;
    }

    const value = this.evalTokens(toks);
    this.rememberResult(value, toks);
    this.m.ans = value;
    return null;
  }

  inputPrompt(toks) {
    // syntax:  ? → VAR
    const arrow = toks.findIndex((t) => t.c === 'assign');
    const target = arrow >= 0 ? toks[arrow + 1] : null;
    if (arrow !== 1 || toks.length !== 3 || !target || !target.v) err('Syntax');
    this.waiting = { kind: 'input', varName: target.v, edit: [] };
    return { wait: true, kind: 'input', varName: target.v, edit: this.waiting.edit };
  }

  forStart(toks) {
    // For expr → VAR To expr [Step expr]
    // A second active loop is a Syntax ERROR on the fx-50FH II. Keep this
    // runtime check here so an unexecuted inner loop is not rejected early.
    if (this.loops.length) err('Syntax');
    const arrow = toks.findIndex((t) => t.c === 'assign');
    const toIdx = toks.findIndex((t) => t.c === 'To');
    const stepIdx = toks.findIndex((t) => t.c === 'Step');
    if (arrow < 2 || toIdx !== arrow + 2 ||
        (stepIdx >= 0 && stepIdx <= toIdx + 1)) err('Syntax');
    const target = toks[arrow + 1];
    if (!target || !target.v) err('Syntax');
    const realHeader = (tokens) => {
      const value = this.evalTokens(tokens);
      if (value.im !== 0) err('Math');
      return value;
    };
    const start = realHeader(toks.slice(1, arrow));
    const from = start.re;
    // The counter receives its start before To and Step are evaluated;
    // either expression may refer to this newly assigned value.
    storeVariable(this.m.vars, target.v, from, false);
    const to = realHeader(toks.slice(toIdx + 1, stepIdx > 0 ? stepIdx : undefined)).re;
    const stepValue = stepIdx > 0 ? realHeader(toks.slice(stepIdx + 1)) : C(1);
    const step = stepValue.re;
    if (step === 0) err('Argument');
    const exit = this.loopMap[this.pc];
    if ((step > 0 && from > to) || (step < 0 && from < to)) { this.pc = exit; return null; }
    const advance = quotientCounterAdvance(start, stepValue);
    this.loops.push({ kind: 'for', varName: target.v, to, step, advance, body: this.pc, exit });
    return null;
  }

  forNext() {
    const startIdx = this.loopMap[this.pc];
    while (this.loops.length && this.loops[this.loops.length - 1].body !== startIdx) this.loops.pop();
    const f = this.loops[this.loops.length - 1];
    if (!f) err('Syntax');
    // Counter addition must use decimal operands, like native memory updates.
    // Binary 0.2+0.1 exceeds the stored decimal To=0.3 and skips its body.
    const current = this.m.vars[f.varName];
    const v = f.advance?.(current) ?? decimalAdd(current, f.step);
    storeVariable(this.m.vars, f.varName, r15(v), false);
    if ((f.step > 0 && v <= f.to) || (f.step < 0 && v >= f.to)) {
      this.pc = f.body;
      return null;
    }
    this.loops.pop();
    return null;
  }
}
