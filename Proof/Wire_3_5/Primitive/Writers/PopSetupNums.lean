import Proof.Wire_3_5.Primitive.Writers.SymQM
import Proof.Wire_3_5.Primitive.Writers.LevelW
import Proof.Wire_3_5.Primitive.Writers.SymDecIdx
import Proof.Wire_3_5.Primitive.Writers.CapNum
import Proof.Wire_3_5.Primitive.Writers.FiltNum
import Proof.Wire_3_5.Primitive.Writers.SymLayout

/-! # PA POP setup, part 3: the POP setup's numbers, in registers

From the POP setup's entry bank (`PopSetup.PopIn`: `M, B, errExp, f, sgn, s, r4, G, off, L` in `400 … 409`), register
programs of PA's value-named kit (`SparseNum`, `FiltNum`, `CapNum`, `SymDec.div1`, `SymQM.clogW`/`maxW`/`sbW`,
`LevelW.sqrtW`, `UnaryArith.subW`) compute the flat list's numbers (list:flatten, P3:1491-1510; list:base's
`J = ⌈log₂ B⌉ + 9`, the rank, Theorem 2.5's walk side bits) and copy them where `UnitReady.PopReady` reads them:
* **`pwA_spec`**: `⌊err/4⌋`, `n = 2⌊err/4⌋`, the walk length `n + 1`, the threshold `⌊err/4⌋ + 1`;
* **`prA_spec`**: `J`, `⌈log₂ M⌉`, `rank = max J ⌈log₂ M⌉`, the side bits `⌊3·rank/2⌋`;
* **`prB_spec`**: `rank − 1`, `3·rank − 1`, `2·rank − 1`, the rulers `2·sb + 1`, the padding `2·sb − (3·rank − 1)`, the index
  word's width `160n + 2·sb`, `J + 1`;
* **`pmC_spec`**: the labels' bound `off + L + (r4 + 4)·G` and `4096·B`; **`psq_spec`**: `⌈√(4096·B)⌉`;
* **`ptD1_spec` … `ptD3_spec`**: C5's builder registers `6, 7, 8, 10, 15` and the POP cell's `X 1 … 4, 20, 21, 44, 45,
  50, 52, 53, 63`, `P 180`.
Every stage states its exact final registers (`… Out`), the streams, heads and cell unchanged.

Paper quantities of the main type: the flat list's walk length, threshold, rank and side bits, the window count
`⌈√(64²·B)⌉` and the labels' bound, in the POP cell's registers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

variable {ns : ℕ} (cap : ℕ)

theorem zfrom1 {f : Fin 10 → ℕ} (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) (h5 : f 5 = 0)
    (h6 : f 6 = 0) (h7 : f 7 = 0) (h8 : f 8 = 0) (h9 : f 9 = 0) : ∀ i : Fin 10, 1 ≤ i.val → f i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem zfrom2 {f : Fin 10 → ℕ} (h2 : f 2 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) (h5 : f 5 = 0)
    (h6 : f 6 = 0) (h7 : f 7 = 0) (h8 : f 8 = 0) (h9 : f 9 = 0) : ∀ i : Fin 10, 2 ≤ i.val → f i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

/-- The value-named truncated subtraction: `a := a − b`, `b` kept. -/
theorem sub1 {nr : ℕ} (R : Fin 4 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha : σ.val (R 0) = a) (hb : σ.val (R 1) = b)
    (ht : σ.val (R 2) = 0) (hw : σ.val (R 3) = 0) (hac : a ≤ cap) (hbc : b ≤ cap) :
    WExec cap (UnaryArith.subW R) σ (σ.setv (R 0) (a - b)) (UnaryPow.sq cap) := by
  have h := UnaryArith.subW_spec cap R σ ht hw (by rw [ha]; exact hac) (by rw [hb]; exact hbc)
  rw [ha, hb] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

/-- The walk numbers: `err/4`, `n = 2⌊err/4⌋`, the walk length `n + 1`, the threshold `⌊err/4⌋ + 1`. -/
def pwAW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (402 : Fin LNR) (411 : Fin LNR) (419 : Fin LNR)) (StarNums.incN (412 : Fin LNR) 4)) (UnaryArith.divW (⟨![411, 412, 410, 413, 414, 415, 416, 417, 418], by decide⟩ : Fin 9 ↪ Fin LNR))) (WM.clear (411 : Fin LNR))) (WM.clear (412 : Fin LNR))) (FinalPass.Hash4.wcopyR (410 : Fin LNR) (441 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (410 : Fin LNR) (441 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (441 : Fin LNR) (442 : Fin LNR) (419 : Fin LNR))) (StarNums.incN (442 : Fin LNR) 1)) (FinalPass.Hash4.wcopyR (410 : Fin LNR) (443 : Fin LNR) (419 : Fin LNR))) (StarNums.incN (443 : Fin LNR) 1)


/-- The registers `pwAW` writes. -/
def pwAOut : List (Fin LNR) := [(411 : Fin LNR), (412 : Fin LNR), (410 : Fin LNR), (441 : Fin LNR), (442 : Fin LNR), (443 : Fin LNR)]

theorem pwA_spec (σ : WState ns LNR) (err : ℕ)
    (h402 : σ.val 402 = err)
    (z410 : σ.val 410 = 0) (z411 : σ.val 411 = 0) (z412 : σ.val 412 = 0) (z413 : σ.val 413 = 0) (z414 : σ.val 414 = 0) (z415 : σ.val 415 = 0) (z416 : σ.val 416 = 0) (z417 : σ.val 417 = 0) (z418 : σ.val 418 = 0) (z419 : σ.val 419 = 0) (z441 : σ.val 441 = 0) (z442 : σ.val 442 = 0) (z443 : σ.val 443 = 0)
    (hcr : err + 100 ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap pwAW σ τ (40 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ pwAOut → τ.val r = σ.val r) ∧
      τ.val 410 = err / 4 ∧
      τ.val 411 = 0 ∧
      τ.val 412 = 0 ∧
      τ.val 441 = 2 * (err / 4) ∧
      τ.val 442 = 2 * (err / 4) + 1 ∧
      τ.val 443 = err / 4 + 1 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (402 : Fin LNR) (411 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (err) σ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega)
  have c2 := WExec.seq c1 (SparseNum.incN0 cap (412 : Fin LNR) 4 _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c3 := WExec.seq c2 (SymDec.div1 cap (⟨![411, 412, 410, 413, 414, 415, 416, 417, 418], by decide⟩ : Fin 9 ↪ Fin LNR) (err) (4) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega) (by omega))
  have c4 := WExec.seq c3 (SparseNum.clear1 cap (411 : Fin LNR) ((err % 4)) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c5 := WExec.seq c4 (SparseNum.clear1 cap (412 : Fin LNR) (4) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c6 := WExec.seq c5 (SparseNum.copy1 cap (410 : Fin LNR) (441 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) ((err / 4)) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c7 := WExec.seq c6 (CapNum.add1 cap (410 : Fin LNR) (441 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) ((err / 4)) ((err / 4)) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega) (by omega))
  have c8 := WExec.seq c7 (SparseNum.copy1 cap (441 : Fin LNR) (442 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (((err / 4) + (err / 4))) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c9 := WExec.seq c8 (FiltNum.incN1 cap (442 : Fin LNR) (((err / 4) + (err / 4))) 1 _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c10 := WExec.seq c9 (SparseNum.copy1 cap (410 : Fin LNR) (443 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) ((err / 4)) _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  have c11 := WExec.seq c10 (FiltNum.incN1 cap (443 : Fin LNR) ((err / 4)) 1 _ (by simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443]) (by omega))
  refine ⟨_, WExec.mono c11 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [pwAOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega
  · simp [Function.update_apply, h402, z410, z411, z412, z413, z414, z415, z416, z417, z418, z419, z441, z442, z443] <;> omega

/-- The rank: `J = ⌈log₂ B⌉ + 9`, `⌈log₂ M⌉`, `rank = max J ⌈log₂ M⌉`, the side bits `⌊3·rank/2⌋`. -/
def prAW : WM ns LNR :=
  .seq (.seq (.seq (.seq (SymQM.clogW (⟨![401, 444, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR)) (StarNums.incN (444 : Fin LNR) 9)) (SymQM.clogW (⟨![400, 445, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR))) (SymQM.maxW (⟨![444, 445, 446, 450, 451, 452, 453, 454, 455, 456], by decide⟩ : Fin 10 ↪ Fin LNR))) (SymQM.sbW (⟨![446, 447, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR))


/-- The registers `prAW` writes. -/
def prAOut : List (Fin LNR) := [(444 : Fin LNR), (445 : Fin LNR), (446 : Fin LNR), (447 : Fin LNR)]

theorem prA_spec (σ : WState ns LNR) (M B : ℕ)
    (h400 : σ.val 400 = M) (h401 : σ.val 401 = B)
    (z444 : σ.val 444 = 0) (z445 : σ.val 445 = 0) (z446 : σ.val 446 = 0) (z447 : σ.val 447 = 0) (z450 : σ.val 450 = 0) (z451 : σ.val 451 = 0) (z452 : σ.val 452 = 0) (z453 : σ.val 453 = 0) (z454 : σ.val 454 = 0) (z455 : σ.val 455 = 0) (z456 : σ.val 456 = 0) (z457 : σ.val 457 = 0)
    (hcB : Nat.clog 2 B ≤ B) (hcM : Nat.clog 2 M ≤ M)
    (hmx : max (Nat.clog 2 B + 9) (Nat.clog 2 M) ≤ B + M + 9) (hcr : 3 * (B + M + 9) + 10 ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap prAW σ τ (70 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ prAOut → τ.val r = σ.val r) ∧
      τ.val 444 = Nat.clog 2 B + 9 ∧
      τ.val 445 = Nat.clog 2 M ∧
      τ.val 446 = max (Nat.clog 2 B + 9) (Nat.clog 2 M) ∧
      τ.val 447 = (max (Nat.clog 2 B + 9) (Nat.clog 2 M) + max (Nat.clog 2 B + 9) (Nat.clog 2 M) + max (Nat.clog 2 B + 9) (Nat.clog 2 M)) / 2 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SymQM.clogW_spec cap (⟨![401, 444, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR) σ (B) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (zfrom1 (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457])) (by omega)
  have c2 := WExec.seq c1 (FiltNum.incN1 cap (444 : Fin LNR) ((Nat.clog 2 B)) 9 _ (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by omega))
  have c3 := WExec.seq c2 (SymQM.clogW_spec cap (⟨![400, 445, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR) _ (M) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (zfrom1 (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457])) (by omega))
  have c4 := WExec.seq c3 (SymQM.maxW_spec cap (⟨![444, 445, 446, 450, 451, 452, 453, 454, 455, 456], by decide⟩ : Fin 10 ↪ Fin LNR) _ (((Nat.clog 2 B) + 9)) ((Nat.clog 2 M)) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (zfrom2 (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457])) (by omega) (by omega) (by omega))
  have c5 := WExec.seq c4 (SymQM.sbW_spec cap (⟨![446, 447, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩ : Fin 10 ↪ Fin LNR) _ ((max ((Nat.clog 2 B) + 9) (Nat.clog 2 M))) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (zfrom1 (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457]) (by simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457])) (by omega))
  refine ⟨_, WExec.mono c5 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [prAOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457] <;> omega
  · simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457] <;> omega
  · simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457] <;> omega
  · simp [Function.update_apply, h400, h401, z444, z445, z446, z447, z450, z451, z452, z453, z454, z455, z456, z457] <;> omega

/-- The widths: `rank − 1`, `3·rank − 1`, `2·rank − 1`, the rulers `2·sb + 1`, the padding `2·sb − (3·rank − 1)`, the index word's `160n + 2·sb`, `J + 1`. -/
def prBW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (446 : Fin LNR) (448 : Fin LNR) (419 : Fin LNR)) (WM.dec (448 : Fin LNR))) (FinalPass.Hash4.wcopyR (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR))) (WM.dec (449 : Fin LNR))) (FinalPass.Hash4.wcopyR (446 : Fin LNR) (458 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (446 : Fin LNR) (458 : Fin LNR) (419 : Fin LNR))) (WM.dec (458 : Fin LNR))) (FinalPass.Hash4.wcopyR (447 : Fin LNR) (459 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (447 : Fin LNR) (459 : Fin LNR) (419 : Fin LNR))) (StarNums.incN (459 : Fin LNR) 1)) (FinalPass.Hash4.wcopyR (447 : Fin LNR) (460 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (447 : Fin LNR) (460 : Fin LNR) (419 : Fin LNR))) (UnaryArith.subW (⟨![460, 449, 419, 420], by decide⟩ : Fin 4 ↪ Fin LNR))) (StarNums.incN (421 : Fin LNR) 160)) (UnaryArith.mulAddW (⟨![441, 421, 461, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear (421 : Fin LNR))) (ParseNat.addTo (447 : Fin LNR) (461 : Fin LNR) (419 : Fin LNR))) (ParseNat.addTo (447 : Fin LNR) (461 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (444 : Fin LNR) (462 : Fin LNR) (419 : Fin LNR))) (StarNums.incN (462 : Fin LNR) 1)


/-- The registers `prBW` writes. -/
def prBOut : List (Fin LNR) := [(448 : Fin LNR), (449 : Fin LNR), (458 : Fin LNR), (459 : Fin LNR), (460 : Fin LNR), (421 : Fin LNR), (461 : Fin LNR), (462 : Fin LNR)]

theorem prB_spec (σ : WState ns LNR) (n J r sb : ℕ)
    (h441 : σ.val 441 = n) (h444 : σ.val 444 = J) (h446 : σ.val 446 = r) (h447 : σ.val 447 = sb)
    (z448 : σ.val 448 = 0) (z449 : σ.val 449 = 0) (z458 : σ.val 458 = 0) (z459 : σ.val 459 = 0) (z460 : σ.val 460 = 0) (z461 : σ.val 461 = 0) (z462 : σ.val 462 = 0) (z419 : σ.val 419 = 0) (z420 : σ.val 420 = 0) (z421 : σ.val 421 = 0) (z413 : σ.val 413 = 0) (z414 : σ.val 414 = 0)
    (hcr : 4 * r + 4 * sb + 160 * n + J + 300 ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap prBW σ τ (60 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ prBOut → τ.val r = σ.val r) ∧
      τ.val 448 = r - 1 ∧
      τ.val 449 = r + r + r - 1 ∧
      τ.val 458 = r + r - 1 ∧
      τ.val 459 = sb + sb + 1 ∧
      τ.val 460 = sb + sb - (r + r + r - 1) ∧
      τ.val 461 = 160 * n + sb + sb ∧
      τ.val 462 = J + 1 ∧
      τ.val 421 = 0 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (446 : Fin LNR) (448 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) σ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega)
  have c2 := WExec.seq c1 (SparseNum.dec1 cap (448 : Fin LNR) (r) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c3 := WExec.seq c2 (SparseNum.copy1 cap (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c4 := WExec.seq c3 (CapNum.add1 cap (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) (r) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c5 := WExec.seq c4 (CapNum.add1 cap (446 : Fin LNR) (449 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) ((r + r)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c6 := WExec.seq c5 (SparseNum.dec1 cap (449 : Fin LNR) (((r + r) + r)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c7 := WExec.seq c6 (SparseNum.copy1 cap (446 : Fin LNR) (458 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c8 := WExec.seq c7 (CapNum.add1 cap (446 : Fin LNR) (458 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) (r) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c9 := WExec.seq c8 (SparseNum.dec1 cap (458 : Fin LNR) ((r + r)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c10 := WExec.seq c9 (SparseNum.copy1 cap (447 : Fin LNR) (459 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c11 := WExec.seq c10 (CapNum.add1 cap (447 : Fin LNR) (459 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) (sb) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c12 := WExec.seq c11 (FiltNum.incN1 cap (459 : Fin LNR) ((sb + sb)) 1 _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c13 := WExec.seq c12 (SparseNum.copy1 cap (447 : Fin LNR) (460 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c14 := WExec.seq c13 (CapNum.add1 cap (447 : Fin LNR) (460 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) (sb) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c15 := WExec.seq c14 (sub1 cap (⟨![460, 449, 419, 420], by decide⟩ : Fin 4 ↪ Fin LNR) ((sb + sb)) ((((r + r) + r) - 1)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c16 := WExec.seq c15 (SparseNum.incN0 cap (421 : Fin LNR) 160 _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c17 := WExec.seq c16 (SparseNum.mulAdd1 cap (⟨![441, 421, 461, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR) (n) (160) (0) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega) (by omega))
  have c18 := WExec.seq c17 (SparseNum.clear1 cap (421 : Fin LNR) (160) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c19 := WExec.seq c18 (CapNum.add1 cap (447 : Fin LNR) (461 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) ((0 + n * 160)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c20 := WExec.seq c19 (CapNum.add1 cap (447 : Fin LNR) (461 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) (((0 + n * 160) + sb)) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega) (by omega))
  have c21 := WExec.seq c20 (SparseNum.copy1 cap (444 : Fin LNR) (462 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (J) _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  have c22 := WExec.seq c21 (FiltNum.incN1 cap (462 : Fin LNR) (J) 1 _ (by simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414]) (by omega))
  refine ⟨_, WExec.mono c22 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [prBOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega
  · simp [Function.update_apply, h441, h444, h446, h447, z448, z449, z458, z459, z460, z461, z462, z419, z420, z421, z413, z414] <;> omega

/-- The labels' bound `Mlab = off + L + (r4 + 4)·G` and the window count's radicand `4096·B`. -/
def pmCW : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (408 : Fin LNR) (465 : Fin LNR) (419 : Fin LNR)) (ParseNat.addTo (409 : Fin LNR) (465 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (406 : Fin LNR) (466 : Fin LNR) (419 : Fin LNR))) (StarNums.incN (466 : Fin LNR) 4)) (UnaryArith.mulAddW (⟨![466, 407, 465, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear (466 : Fin LNR))) (StarNums.incN (422 : Fin LNR) 4096)) (UnaryArith.mulAddW (⟨![401, 422, 463, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR))) (WM.clear (422 : Fin LNR))


/-- The registers `pmCW` writes. -/
def pmCOut : List (Fin LNR) := [(465 : Fin LNR), (466 : Fin LNR), (422 : Fin LNR), (463 : Fin LNR)]

theorem pmC_spec (σ : WState ns LNR) (B r4 G off L : ℕ)
    (h401 : σ.val 401 = B) (h406 : σ.val 406 = r4) (h407 : σ.val 407 = G) (h408 : σ.val 408 = off) (h409 : σ.val 409 = L)
    (z463 : σ.val 463 = 0) (z465 : σ.val 465 = 0) (z466 : σ.val 466 = 0) (z422 : σ.val 422 = 0) (z413 : σ.val 413 = 0) (z414 : σ.val 414 = 0) (z419 : σ.val 419 = 0)
    (hcr : off + L + (r4 + 4) * G + 4096 * B + r4 + G + 5000 ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap pmCW σ τ (20 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ pmCOut → τ.val r = σ.val r) ∧
      τ.val 465 = off + L + (r4 + 4) * G ∧
      τ.val 463 = 4096 * B ∧
      τ.val 466 = 0 ∧
      τ.val 422 = 0 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (408 : Fin LNR) (465 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (off) σ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega)
  have c2 := WExec.seq c1 (CapNum.add1 cap (409 : Fin LNR) (465 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (L) (off) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega) (by omega))
  have c3 := WExec.seq c2 (SparseNum.copy1 cap (406 : Fin LNR) (466 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r4) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega))
  have c4 := WExec.seq c3 (FiltNum.incN1 cap (466 : Fin LNR) (r4) 4 _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega))
  have c5 := WExec.seq c4 (SparseNum.mulAdd1 cap (⟨![466, 407, 465, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR) ((r4 + 4)) (G) ((off + L)) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega) (by omega) (by omega))
  have c6 := WExec.seq c5 (SparseNum.clear1 cap (466 : Fin LNR) ((r4 + 4)) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega))
  have c7 := WExec.seq c6 (SparseNum.incN0 cap (422 : Fin LNR) 4096 _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega))
  have c8 := WExec.seq c7 (SparseNum.mulAdd1 cap (⟨![401, 422, 463, 413, 414], by decide⟩ : Fin 5 ↪ Fin LNR) (B) (4096) (0) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega) (by omega) (by omega))
  have c9 := WExec.seq c8 (SparseNum.clear1 cap (422 : Fin LNR) (4096) _ (by simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419]) (by omega))
  refine ⟨_, WExec.mono c9 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [pmCOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega
  · simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega
  · simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega
  · simp [Function.update_apply, h401, h406, h407, h408, h409, z463, z465, z466, z422, z413, z414, z419] <;> omega

/-- The targets, part 1: C5's builder registers `6, 7, 8, 10, 15` and the POP cell's `X 1`. -/
def ptD1W : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (447 : Fin LNR) (6 : Fin LNR) (419 : Fin LNR)) (FinalPass.Hash4.wcopyR (446 : Fin LNR) (7 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (448 : Fin LNR) (8 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (409 : Fin LNR) (10 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (460 : Fin LNR) (15 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (406 : Fin LNR) (20 : Fin LNR) (419 : Fin LNR))


/-- The registers `ptD1W` writes. -/
def ptD1Out : List (Fin LNR) := [(6 : Fin LNR), (7 : Fin LNR), (8 : Fin LNR), (10 : Fin LNR), (15 : Fin LNR), (20 : Fin LNR)]

theorem ptD1_spec (σ : WState ns LNR) (sb r r1 L pb r4 : ℕ)
    (h447 : σ.val 447 = sb) (h446 : σ.val 446 = r) (h448 : σ.val 448 = r1) (h409 : σ.val 409 = L) (h460 : σ.val 460 = pb) (h406 : σ.val 406 = r4)
    (z6 : σ.val 6 = 0) (z7 : σ.val 7 = 0) (z8 : σ.val 8 = 0) (z10 : σ.val 10 = 0) (z15 : σ.val 15 = 0) (z20 : σ.val 20 = 0) (z419 : σ.val 419 = 0)
    (hcr : sb + r + r1 + L + pb + r4 ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap ptD1W σ τ (20 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ ptD1Out → τ.val r = σ.val r) ∧
      τ.val 6 = sb ∧
      τ.val 7 = r ∧
      τ.val 8 = r1 ∧
      τ.val 10 = L ∧
      τ.val 15 = pb ∧
      τ.val 20 = r4 := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (447 : Fin LNR) (6 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sb) σ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega)
  have c2 := WExec.seq c1 (SparseNum.copy1 cap (446 : Fin LNR) (7 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r) _ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega))
  have c3 := WExec.seq c2 (SparseNum.copy1 cap (448 : Fin LNR) (8 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r1) _ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega))
  have c4 := WExec.seq c3 (SparseNum.copy1 cap (409 : Fin LNR) (10 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (L) _ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega))
  have c5 := WExec.seq c4 (SparseNum.copy1 cap (460 : Fin LNR) (15 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (pb) _ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega))
  have c6 := WExec.seq c5 (SparseNum.copy1 cap (406 : Fin LNR) (20 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (r4) _ (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419]) (by omega))
  refine ⟨_, WExec.mono c6 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [ptD1Out, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega
  · simp [Function.update_apply, h447, h446, h448, h409, h460, h406, z6, z7, z8, z10, z15, z20, z419] <;> omega

/-- The targets, part 2: the POP cell's `X 2, 3, 4, 20, 21, 44`. -/
def ptD2W : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (407 : Fin LNR) (21 : Fin LNR) (419 : Fin LNR)) (FinalPass.Hash4.wcopyR (408 : Fin LNR) (22 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (409 : Fin LNR) (23 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (464 : Fin LNR) (39 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (444 : Fin LNR) (40 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (400 : Fin LNR) (63 : Fin LNR) (419 : Fin LNR))


/-- The registers `ptD2W` writes. -/
def ptD2Out : List (Fin LNR) := [(21 : Fin LNR), (22 : Fin LNR), (23 : Fin LNR), (39 : Fin LNR), (40 : Fin LNR), (63 : Fin LNR)]

theorem ptD2_spec (σ : WState ns LNR) (G off L S J M : ℕ)
    (h407 : σ.val 407 = G) (h408 : σ.val 408 = off) (h409 : σ.val 409 = L) (h464 : σ.val 464 = S) (h444 : σ.val 444 = J) (h400 : σ.val 400 = M)
    (z21 : σ.val 21 = 0) (z22 : σ.val 22 = 0) (z23 : σ.val 23 = 0) (z39 : σ.val 39 = 0) (z40 : σ.val 40 = 0) (z63 : σ.val 63 = 0) (z419 : σ.val 419 = 0)
    (hcr : G + off + L + S + J + M ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap ptD2W σ τ (20 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ ptD2Out → τ.val r = σ.val r) ∧
      τ.val 21 = G ∧
      τ.val 22 = off ∧
      τ.val 23 = L ∧
      τ.val 39 = S ∧
      τ.val 40 = J ∧
      τ.val 63 = M := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (407 : Fin LNR) (21 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (G) σ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega)
  have c2 := WExec.seq c1 (SparseNum.copy1 cap (408 : Fin LNR) (22 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (off) _ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega))
  have c3 := WExec.seq c2 (SparseNum.copy1 cap (409 : Fin LNR) (23 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (L) _ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega))
  have c4 := WExec.seq c3 (SparseNum.copy1 cap (464 : Fin LNR) (39 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (S) _ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega))
  have c5 := WExec.seq c4 (SparseNum.copy1 cap (444 : Fin LNR) (40 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (J) _ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega))
  have c6 := WExec.seq c5 (SparseNum.copy1 cap (400 : Fin LNR) (63 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (M) _ (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419]) (by omega))
  refine ⟨_, WExec.mono c6 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [ptD2Out, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega
  · simp [Function.update_apply, h407, h408, h409, h464, h444, h400, z21, z22, z23, z39, z40, z63, z419] <;> omega

/-- The targets, part 3: the POP cell's `X 45, 50, 52, 53, 63` and `P 180`. -/
def ptD3W : WM ns LNR :=
  .seq (.seq (.seq (.seq (.seq (FinalPass.Hash4.wcopyR (409 : Fin LNR) (64 : Fin LNR) (419 : Fin LNR)) (FinalPass.Hash4.wcopyR (404 : Fin LNR) (69 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (442 : Fin LNR) (71 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (443 : Fin LNR) (72 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (405 : Fin LNR) (82 : Fin LNR) (419 : Fin LNR))) (FinalPass.Hash4.wcopyR (465 : Fin LNR) (199 : Fin LNR) (419 : Fin LNR))


/-- The registers `ptD3W` writes. -/
def ptD3Out : List (Fin LNR) := [(64 : Fin LNR), (69 : Fin LNR), (71 : Fin LNR), (72 : Fin LNR), (82 : Fin LNR), (199 : Fin LNR)]

theorem ptD3_spec (σ : WState ns LNR) (L sg t th s Ml : ℕ)
    (h409 : σ.val 409 = L) (h404 : σ.val 404 = sg) (h442 : σ.val 442 = t) (h443 : σ.val 443 = th) (h405 : σ.val 405 = s) (h465 : σ.val 465 = Ml)
    (z64 : σ.val 64 = 0) (z69 : σ.val 69 = 0) (z71 : σ.val 71 = 0) (z72 : σ.val 72 = 0) (z82 : σ.val 82 = 0) (z199 : σ.val 199 = 0) (z419 : σ.val 419 = 0)
    (hcr : L + sg + t + th + s + Ml ≤ cap)
    (hc1 : 1 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap ptD3W σ τ (20 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ ptD3Out → τ.val r = σ.val r) ∧
      τ.val 64 = L ∧
      τ.val 69 = sg ∧
      τ.val 71 = t ∧
      τ.val 72 = th ∧
      τ.val 82 = s ∧
      τ.val 199 = Ml := by
  have hsq := UnaryPow.sq_ge cap
  have c1 := SparseNum.copy1 cap (409 : Fin LNR) (64 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (L) σ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega)
  have c2 := WExec.seq c1 (SparseNum.copy1 cap (404 : Fin LNR) (69 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (sg) _ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega))
  have c3 := WExec.seq c2 (SparseNum.copy1 cap (442 : Fin LNR) (71 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (t) _ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega))
  have c4 := WExec.seq c3 (SparseNum.copy1 cap (443 : Fin LNR) (72 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (th) _ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega))
  have c5 := WExec.seq c4 (SparseNum.copy1 cap (405 : Fin LNR) (82 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (s) _ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega))
  have c6 := WExec.seq c5 (SparseNum.copy1 cap (465 : Fin LNR) (199 : Fin LNR) (419 : Fin LNR) (by decide) (by decide) (by decide) (Ml) _ (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419]) (by omega))
  refine ⟨_, WExec.mono c6 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [ptD3Out, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [Function.update_apply, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega
  · simp [Function.update_apply, h409, h404, h442, h443, h405, h465, z64, z69, z71, z72, z82, z199, z419] <;> omega

/-! ## The window count `⌈√(4096·B)⌉` -/

/-- `sqrtW`'s registers: `463` the radicand (kept), `464` the root, `450 … 457` scratch. -/
def psqQ : LevelW.QReg LNR := ⟨![463, 464, 450, 451, 452, 453, 454, 455, 456, 457], by decide⟩

/-- The window count's program. -/
def psqW : WM ns LNR := LevelW.sqrtW psqQ

/-- The register `psqW` writes. -/
def psqOut : List (Fin LNR) := [(464 : Fin LNR)]

/-- The window count's cost. -/
def sqCost (X : ℕ) : ℕ :=
  18 * X + 3 + 1 + (3 + 1 + ((X + 1) * (LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4) + 1))

theorem psq_spec (σ : WState ns LNR) (X : ℕ) (h463 : σ.val 463 = X) (z464 : σ.val 464 = 0) (z450 : σ.val 450 = 0)
    (z451 : σ.val 451 = 0) (z452 : σ.val 452 = 0) (z453 : σ.val 453 = 0) (z454 : σ.val 454 = 0) (z455 : σ.val 455 = 0)
    (z456 : σ.val 456 = 0) (z457 : σ.val 457 = 0) (hcap : (X + 2) * (X + 2) + X + 10 ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap psqW σ τ (sqCost X) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      (∀ r : Fin LNR, r ∉ psqOut → τ.val r = σ.val r) ∧ τ.val 464 = CanonicalFourfoldRowProgram.natCeilSqrt X := by
  have h := LevelW.sqrtW_spec cap psqQ σ X h463 z464 z450 z451 z452 z453 z454 z455 z456 z457 hcap
  refine ⟨_, h, by simp, by simp, by simp, ?_, ?_⟩
  · intro r hr
    simp only [psqOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [psqQ, Function.update_apply, hr]
  · simp [psqQ]

theorem sqCost_le (X : ℕ) : sqCost X ≤ 200 * ((X + 2) * (X + 2) * (X + 2)) := by
  have hs := LevelW.natCeilSqrt_le X
  unfold sqCost
  generalize CanonicalFourfoldRowProgram.natCeilSqrt X = s at hs ⊢
  have hst : LevelW.stepCost X s + 4 ≤ 100 * ((X + 2) * (X + 2)) := by
    unfold LevelW.stepCost
    have h1 : s * s ≤ (X + 1) * (X + 1) := Nat.mul_le_mul hs hs
    have h2 : s * (18 * s + 8) ≤ (X + 1) * (18 * (X + 1) + 8) := Nat.mul_le_mul hs (by omega)
    nlinarith
  have h3 : (X + 1) * (LevelW.stepCost X s + 4) ≤ (X + 2) * (100 * ((X + 2) * (X + 2))) :=
    Nat.mul_le_mul (by omega) hst
  nlinarith

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupNums
