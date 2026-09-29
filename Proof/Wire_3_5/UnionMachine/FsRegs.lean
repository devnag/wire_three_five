import Proof.Wire_3_5.UnionMachine.FsNums
import Proof.Wire_3_5.Primitive.Writers.SymLayout

/-! # C6, the FILTER setup, part 3: the setup's registers

From the regular filter's numbers (`fieldBits`, `labelBits`, `walkLen`, `prefixBits` on `410`, `409`, `411`, `408`,
`FsNums.gapX`) and the row's values (`L`, `r4`, `G`, `off` on `407`, `404`, `405`, `406`), one register program
(**`rAW` … `rDW`**, 61 steps of PA's unary kit) writes what `UnitReady.FiltReady` reads from registers and what the words
stage needs (**`rA_spec` … `rD_spec`**):
* C5's builder registers `6 … 10` (`fieldBits`, `labelBits`, `labelBits − 1`, `prefixBits`, `L`) and the trace mask's
  `RgT 4 = 223` (`fieldBits`);
* the FILTER numbers `FR 1 … 4` (`r4`, `G`, `off`, `L`), `FR 13 = 4L`, `FR 14 = 384·walkLen + 1` (the table's degree,
  `FiltRec.filtDeg_filterTable`), `FR 15 = (walkLen+1)/2` (the majority threshold), `FR 17 = walkLen·(256L+258) + 1`
  (`|tableWord|`, `FiltRec.tableWord_length`), `FR 16 = FR 17 + 2L + FR 15 + 41` (`cap37 + 1`);
* the words stage's widths: `n = walkLen − 1` (`440`), `r = 128·wOf fieldBits labelBits` (`442`), the index word's
  length `160n + 2r` (`443`), the rulers' `2r + 1` (`444`), `labelBits + (labelBits − 1)` (`446`).

Paper quantity: none (the setup's register values for `filt:gap`'s regular filter, P3:2019-2054, 2096-2100). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsRegs
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

variable {ns : ℕ} (cap : ℕ)

/-- The registers `rAW` writes. -/
def rAOut : List (Fin LNR) := [(440 : Fin LNR), (441 : Fin LNR), (442 : Fin LNR), (443 : Fin LNR), (444 : Fin LNR), (445 : Fin LNR), (446 : Fin LNR), (448 : Fin LNR)]

/-- rA: 26 steps of PA's unary kit. -/
def rAW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR 411 440 451) (.dec 440)) (StarNums.incN 448 2)) (UnaryArith.mulAddW (⟨![410, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (UnaryArith.mulAddW (⟨![409, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (FinalPass.Hash4.wcopyR 409 445 451)) (.dec 445)) (WM.clear 448)) (StarNums.incN 448 1)) (UnaryArith.mulAddW (⟨![445, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)) (StarNums.incN 448 128)) (UnaryArith.mulAddW (⟨![441, 448, 442, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)) (StarNums.incN 448 160)) (UnaryArith.mulAddW (⟨![440, 448, 443, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)) (StarNums.incN 448 2)) (UnaryArith.mulAddW (⟨![442, 448, 443, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (UnaryArith.mulAddW (⟨![442, 448, 444, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (StarNums.incN 444 1)) (WM.clear 448)) (StarNums.incN 448 1)) (UnaryArith.mulAddW (⟨![409, 448, 446, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (UnaryArith.mulAddW (⟨![445, 448, 446, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)

theorem rA_spec (σ : WState ns LNR) (fb lb wl : ℕ)
    (h409 : σ.val 409 = lb) (h410 : σ.val 410 = fb) (h411 : σ.val 411 = wl)
    (z440 : σ.val 440 = 0) (z441 : σ.val 441 = 0) (z442 : σ.val 442 = 0) (z443 : σ.val 443 = 0) (z444 : σ.val 444 = 0) (z445 : σ.val 445 = 0) (z446 : σ.val 446 = 0) (z448 : σ.val 448 = 0) (z449 : σ.val 449 = 0) (z450 : σ.val 450 = 0) (z451 : σ.val 451 = 0)
    (hc1 : 1 ≤ cap) (hlb : 1 ≤ lb) (hwl : 1 ≤ wl) (hcr : 256 * (2 * fb + 3 * lb) + 160 * wl + 1000 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap rAW σ τ (52 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ rAOut → τ.val r = σ.val r) ∧
      τ.val 440 = wl - 1 ∧
      τ.val 442 = 128 * (2 * fb + 2 * lb + (lb - 1)) ∧
      τ.val 443 = 160 * (wl - 1) + 2 * (128 * (2 * fb + 2 * lb + (lb - 1))) ∧
      τ.val 444 = 2 * (128 * (2 * fb + 2 * lb + (lb - 1))) + 1 ∧
      τ.val 445 = lb - 1 ∧
      τ.val 446 = lb + (lb - 1) ∧
      τ.val 448 = 0 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := copy1 cap (411 : Fin LNR) (440 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (wl) σ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega)
  have c2 := WExec.seq c1 (dec1 cap (440 : Fin LNR) (wl) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c3 := WExec.seq c2 (incN0 cap (448 : Fin LNR) 2 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c4 := WExec.seq c3 (mulAdd1 cap (⟨![410, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (fb) (2) (0) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c5 := WExec.seq c4 (mulAdd1 cap (⟨![409, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (lb) (2) ((0) + (fb) * (2)) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c6 := WExec.seq c5 (copy1 cap (409 : Fin LNR) (445 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (lb) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c7 := WExec.seq c6 (dec1 cap (445 : Fin LNR) (lb) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c8 := WExec.seq c7 (clear1 cap (448 : Fin LNR) (2) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c9 := WExec.seq c8 (incN0 cap (448 : Fin LNR) 1 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c10 := WExec.seq c9 (mulAdd1 cap (⟨![445, 448, 441, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((lb) - 1) (1) (((0) + (fb) * (2)) + (lb) * (2)) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c11 := WExec.seq c10 (clear1 cap (448 : Fin LNR) (1) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c12 := WExec.seq c11 (incN0 cap (448 : Fin LNR) 128 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c13 := WExec.seq c12 (mulAdd1 cap (⟨![441, 448, 442, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((((0) + (fb) * (2)) + (lb) * (2)) + ((lb) - 1) * (1)) (128) (0) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c14 := WExec.seq c13 (clear1 cap (448 : Fin LNR) (128) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c15 := WExec.seq c14 (incN0 cap (448 : Fin LNR) 160 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c16 := WExec.seq c15 (mulAdd1 cap (⟨![440, 448, 443, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((wl) - 1) (160) (0) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c17 := WExec.seq c16 (clear1 cap (448 : Fin LNR) (160) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c18 := WExec.seq c17 (incN0 cap (448 : Fin LNR) 2 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c19 := WExec.seq c18 (mulAdd1 cap (⟨![442, 448, 443, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((0) + ((((0) + (fb) * (2)) + (lb) * (2)) + ((lb) - 1) * (1)) * (128)) (2) ((0) + ((wl) - 1) * (160)) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c20 := WExec.seq c19 (mulAdd1 cap (⟨![442, 448, 444, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((0) + ((((0) + (fb) * (2)) + (lb) * (2)) + ((lb) - 1) * (1)) * (128)) (2) (0) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c21 := WExec.seq c20 (incN1 cap (444 : Fin LNR) ((0) + ((0) + ((((0) + (fb) * (2)) + (lb) * (2)) + ((lb) - 1) * (1)) * (128)) * (2)) 1 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c22 := WExec.seq c21 (clear1 cap (448 : Fin LNR) (2) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c23 := WExec.seq c22 (incN0 cap (448 : Fin LNR) 1 _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  have c24 := WExec.seq c23 (mulAdd1 cap (⟨![409, 448, 446, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (lb) (1) (0) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c25 := WExec.seq c24 (mulAdd1 cap (⟨![445, 448, 446, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) ((lb) - 1) (1) ((0) + (lb) * (1)) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega) (by omega) (by omega))
  have c26 := WExec.seq c25 (clear1 cap (448 : Fin LNR) (1) _ (by simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451]) (by omega))
  refine ⟨_, WExec.mono c26 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [rAOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega
  · simp [Function.update_apply, h409, h410, h411, z440, z441, z442, z443, z444, z445, z446, z448, z449, z450, z451] <;> omega

/-- The registers `rBW` writes. -/
def rBOut : List (Fin LNR) := [(6 : Fin LNR), (7 : Fin LNR), (8 : Fin LNR), (9 : Fin LNR), (10 : Fin LNR), (223 : Fin LNR), (231 : Fin LNR), (232 : Fin LNR), (233 : Fin LNR), (234 : Fin LNR)]

/-- rB: 10 steps of PA's unary kit. -/
def rBW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR 410 6 451) (FinalPass.Hash4.wcopyR 409 7 451)) (FinalPass.Hash4.wcopyR 445 8 451)) (FinalPass.Hash4.wcopyR 408 9 451)) (FinalPass.Hash4.wcopyR 407 10 451)) (FinalPass.Hash4.wcopyR 410 223 451)) (FinalPass.Hash4.wcopyR 404 231 451)) (FinalPass.Hash4.wcopyR 405 232 451)) (FinalPass.Hash4.wcopyR 406 233 451)) (FinalPass.Hash4.wcopyR 407 234 451)

theorem rB_spec (σ : WState ns LNR) (fb lb lbm pb L r4 G off : ℕ)
    (h410 : σ.val 410 = fb) (h409 : σ.val 409 = lb) (h445 : σ.val 445 = lbm) (h408 : σ.val 408 = pb) (h407 : σ.val 407 = L) (h404 : σ.val 404 = r4) (h405 : σ.val 405 = G) (h406 : σ.val 406 = off)
    (z6 : σ.val 6 = 0) (z7 : σ.val 7 = 0) (z8 : σ.val 8 = 0) (z9 : σ.val 9 = 0) (z10 : σ.val 10 = 0) (z223 : σ.val 223 = 0) (z231 : σ.val 231 = 0) (z232 : σ.val 232 = 0) (z233 : σ.val 233 = 0) (z234 : σ.val 234 = 0) (z451 : σ.val 451 = 0)
    (hc1 : 1 ≤ cap) (hc0 : fb + lb + lbm + pb + L + r4 + G + off + 1000 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap rBW σ τ (20 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ rBOut → τ.val r = σ.val r) ∧
      τ.val 6 = fb ∧
      τ.val 7 = lb ∧
      τ.val 8 = lbm ∧
      τ.val 9 = pb ∧
      τ.val 10 = L ∧
      τ.val 223 = fb ∧
      τ.val 231 = r4 ∧
      τ.val 232 = G ∧
      τ.val 233 = off ∧
      τ.val 234 = L := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := copy1 cap (410 : Fin LNR) (6 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (fb) σ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega)
  have c2 := WExec.seq c1 (copy1 cap (409 : Fin LNR) (7 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (lb) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c3 := WExec.seq c2 (copy1 cap (445 : Fin LNR) (8 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (lbm) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c4 := WExec.seq c3 (copy1 cap (408 : Fin LNR) (9 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (pb) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c5 := WExec.seq c4 (copy1 cap (407 : Fin LNR) (10 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (L) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c6 := WExec.seq c5 (copy1 cap (410 : Fin LNR) (223 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (fb) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c7 := WExec.seq c6 (copy1 cap (404 : Fin LNR) (231 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (r4) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c8 := WExec.seq c7 (copy1 cap (405 : Fin LNR) (232 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (G) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c9 := WExec.seq c8 (copy1 cap (406 : Fin LNR) (233 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (off) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  have c10 := WExec.seq c9 (copy1 cap (407 : Fin LNR) (234 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (L) _ (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451]) (by omega))
  refine ⟨_, WExec.mono c10 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [rBOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega
  · simp [Function.update_apply, h410, h409, h445, h408, h407, h404, h405, h406, z6, z7, z8, z9, z10, z223, z231, z232, z233, z234, z451] <;> omega

/-- The registers `rCW` writes. -/
def rCOut : List (Fin LNR) := [(243 : Fin LNR), (244 : Fin LNR), (245 : Fin LNR), (448 : Fin LNR), (462 : Fin LNR)]

/-- rC: 11 steps of PA's unary kit. -/
def rCW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (StarNums.incN 448 4) (UnaryArith.mulAddW (⟨![407, 448, 243, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)) (StarNums.incN 448 384)) (UnaryArith.mulAddW (⟨![411, 448, 244, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (StarNums.incN 244 1)) (FinalPass.Hash4.wcopyR 411 245 451)) (StarNums.incN 245 1)) (WriteNat.halveM 245 449 462)) (WM.clear 462)) (WM.clear 448)

theorem rC_spec (σ : WState ns LNR) (L wl : ℕ)
    (h407 : σ.val 407 = L) (h411 : σ.val 411 = wl)
    (z243 : σ.val 243 = 0) (z244 : σ.val 244 = 0) (z245 : σ.val 245 = 0) (z448 : σ.val 448 = 0) (z449 : σ.val 449 = 0) (z450 : σ.val 450 = 0) (z451 : σ.val 451 = 0) (z462 : σ.val 462 = 0)
    (hc1 : 1 ≤ cap) (hc0 : 384 * wl + 4 * L + 1000 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap rCW σ τ (22 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ rCOut → τ.val r = σ.val r) ∧
      τ.val 243 = 4 * L ∧
      τ.val 244 = 384 * wl + 1 ∧
      τ.val 245 = (wl + 1) / 2 ∧
      τ.val 448 = 0 ∧
      τ.val 462 = 0 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := incN0 cap (448 : Fin LNR) 4 σ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega)
  have c2 := WExec.seq c1 (mulAdd1 cap (⟨![407, 448, 243, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (L) (4) (0) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega) (by omega) (by omega))
  have c3 := WExec.seq c2 (clear1 cap (448 : Fin LNR) (4) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c4 := WExec.seq c3 (incN0 cap (448 : Fin LNR) 384 _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c5 := WExec.seq c4 (mulAdd1 cap (⟨![411, 448, 244, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (wl) (384) (0) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega) (by omega) (by omega))
  have c6 := WExec.seq c5 (incN1 cap (244 : Fin LNR) ((0) + (wl) * (384)) 1 _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c7 := WExec.seq c6 (copy1 cap (411 : Fin LNR) (245 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (wl) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c8 := WExec.seq c7 (incN1 cap (245 : Fin LNR) (wl) 1 _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c9 := WExec.seq c8 (halve1 cap (245 : Fin LNR) (449 : Fin LNR) (462 : Fin LNR) (by decide) (by decide) (by decide) ((wl) + 1) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega) hc1)
  have c10 := WExec.seq c9 (clear1 cap (462 : Fin LNR) (((wl) + 1) % 2) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  have c11 := WExec.seq c10 (clear1 cap (448 : Fin LNR) (384) _ (by simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462]) (by omega))
  refine ⟨_, WExec.mono c11 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [rCOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega
  · simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega
  · simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega
  · simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega
  · simp [Function.update_apply, h407, h411, z243, z244, z245, z448, z449, z450, z451, z462] <;> omega

/-- The registers `rDW` writes. -/
def rDOut : List (Fin LNR) := [(246 : Fin LNR), (247 : Fin LNR), (448 : Fin LNR), (461 : Fin LNR)]

/-- rD: 14 steps of PA's unary kit. -/
def rDW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (StarNums.incN 448 256) (UnaryArith.mulAddW (⟨![407, 448, 461, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (StarNums.incN 461 258)) (UnaryArith.mulAddW (⟨![411, 461, 247, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (StarNums.incN 247 1)) (FinalPass.Hash4.wcopyR 247 246 451)) (WM.clear 448)) (StarNums.incN 448 2)) (UnaryArith.mulAddW (⟨![407, 448, 246, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear 448)) (StarNums.incN 448 1)) (UnaryArith.mulAddW (⟨![245, 448, 246, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR))) (StarNums.incN 246 41)) (WM.clear 448)

theorem rD_spec (σ : WState ns LNR) (L wl th Z : ℕ)
    (h407 : σ.val 407 = L) (h411 : σ.val 411 = wl) (h245 : σ.val 245 = th)
    (z246 : σ.val 246 = 0) (z247 : σ.val 247 = 0) (z448 : σ.val 448 = 0) (z449 : σ.val 449 = 0) (z450 : σ.val 450 = 0) (z451 : σ.val 451 = 0) (z461 : σ.val 461 = 0)
    (hZ : Z = L * 256 + 258) (hc1 : 1 ≤ cap) (hcz : wl * Z + 2 * L + th + wl + 1000 ≤ cap) (hcL : 256 * L + 1000 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap rDW σ τ (28 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ rDOut → τ.val r = σ.val r) ∧
      τ.val 247 = wl * Z + 1 ∧
      τ.val 246 = wl * Z + 1 + 2 * L + th + 41 ∧
      τ.val 461 = Z ∧
      τ.val 448 = 0 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := incN0 cap (448 : Fin LNR) 256 σ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega)
  have c2 := WExec.seq c1 (mulAdd1 cap (⟨![407, 448, 461, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (L) (256) (0) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega) (by omega) (by omega))
  have c3 := WExec.seq c2 (incN1 cap (461 : Fin LNR) ((0) + (L) * (256)) 258 _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c4 := WExec.seq c3 (mulAdd1 cap (⟨![411, 461, 247, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (wl) (Z) (0) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega) (by omega) (by omega))
  have c5 := WExec.seq c4 (incN1 cap (247 : Fin LNR) ((0) + (wl) * (Z)) 1 _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c6 := WExec.seq c5 (copy1 cap (247 : Fin LNR) (246 : Fin LNR) (451 : Fin LNR) (by decide) (by decide) (by decide) (((0) + (wl) * (Z)) + 1) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c7 := WExec.seq c6 (clear1 cap (448 : Fin LNR) (256) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c8 := WExec.seq c7 (incN0 cap (448 : Fin LNR) 2 _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c9 := WExec.seq c8 (mulAdd1 cap (⟨![407, 448, 246, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (L) (2) (((0) + (wl) * (Z)) + 1) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega) (by omega) (by omega))
  have c10 := WExec.seq c9 (clear1 cap (448 : Fin LNR) (2) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c11 := WExec.seq c10 (incN0 cap (448 : Fin LNR) 1 _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c12 := WExec.seq c11 (mulAdd1 cap (⟨![245, 448, 246, 449, 450], by decide⟩ : Fin 5 ↪ Fin LNR) (th) (1) ((((0) + (wl) * (Z)) + 1) + (L) * (2)) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega) (by omega) (by omega))
  have c13 := WExec.seq c12 (incN1 cap (246 : Fin LNR) (((((0) + (wl) * (Z)) + 1) + (L) * (2)) + (th) * (1)) 41 _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  have c14 := WExec.seq c13 (clear1 cap (448 : Fin LNR) (1) _ (by simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ]) (by omega))
  refine ⟨_, WExec.mono c14 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [rDOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega
  · simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega
  · simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega
  · simp [Function.update_apply, h407, h411, h245, z246, z247, z448, z449, z450, z451, z461, hZ] <;> omega

end NearCubicWires.WireExponent3_5.UnionMachine.FsRegs
