import Proof.Wire_3_5.UnionMachine.EwClog

/-! # C6, e/W_j, part 8: the `e` phase

The unary numbers (`EwBin.e1W`), the eight words (`EwWords.e2W`), `P = M^{2t}` (`EwPow.powW`),
`C = 8KA(J·M^{2t} + M) + 1` (`EwPow.prodW`), `e := ⌈log₂ C⌉ + 1` (`EwClog.clW`), the width cleared: **`e_spec`**
(register `6` = `e`, every other register as before, streams `1 … 8` hold width-`wd` words at head `0`, stream `0`
and the cell untouched), and **`listE_eq`** (`e` is `Primitive.listE`).

Paper quantity of the main result: `e = ⌈log₂(8K·A(M + J·M^{2t}) + 1)⌉ + 1` (`Primitive.listE`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwE
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ)

theorem fw_length (w v : ℕ) : (EwWords.fw w v).length = 2 * w + 1 := by
  simp [EwWords.fw, frame_eq_frameP]

/-- `e` is the THR primitive's auxiliary exponent. -/
theorem listE_eq (A Bs M K : ℕ) : Primitive.listE A Bs M K =
    Nat.clog 2 (8 * (K * A) * (Primitive.listJ A Bs K * M ^ (2 * Primitive.listT A Bs K) + M) + 1) + 1 := by
  unfold Primitive.listE
  congr 2
  ring

/-- **The `e` phase.** -/
def eW : WM 8 48 :=
  .seq (.seq (.seq (.seq (.seq EwBin.e1W EwWords.e2W) EwPow.powW) EwPow.prodW) EwClog.clW) (WM.clear 36)

/-- The phase's capacity need. -/
def eNeed (M A K J t : ℕ) : ℕ := 3 * EwBin.zOf M A K J t + 20

/-- The phase's cost. -/
def eCost (M A K J t : ℕ) : ℕ :=
  500 * (EwBin.zOf M A K J t + 1) * (EwBin.zOf M A K J t + 1) +
  600 * (M + J + 8 * (K * A) + EwBin.wdOf M A K J t + 2) * (M + J + 8 * (K * A) + EwBin.wdOf M A K J t + 2) +
  (2 * t * (RegRat.mulCost (EwBin.wdOf M A K J t) + 41 * EwBin.wdOf M A K J t + 12) + 40 * t + 10) +
  (2 * RegRat.mulCost (EwBin.wdOf M A K J t) + 100 * EwBin.wdOf M A K J t + 20) +
  (EwBin.wdOf M A K J t * (100 * EwBin.wdOf M A K J t + 22) + 50 * EwBin.wdOf M A K J t + 20) +
  (3 * EwBin.wdOf M A K J t + 1) + 5

theorem e_spec (σ : WState 8 48) (M A K J t : ℕ) (hM : σ.val 0 = M) (hA : σ.val 1 = A) (hK : σ.val 3 = K)
    (hJ : σ.val 4 = J) (ht : σ.val 5 = t) (hz : ∀ r : Fin 48, 6 ≤ r.val → σ.val r = 0)
    (hs : ∀ i : Fin 9, i ≠ 0 → σ.st i = [] ∧ σ.sh i = 0) (hcap : eNeed M A K J t ≤ cap) :
    ∃ τ : WState 8 48, WExec cap eW σ τ (eCost M A K J t) ∧
      τ.val 6 = Nat.clog 2 (8 * (K * A) * (J * M ^ (2 * t) + M) + 1) + 1 ∧
      (∀ r : Fin 48, r ≠ 6 → τ.val r = σ.val r) ∧
      (∀ i : Fin 9, i ≠ 0 → (τ.st i).length = 2 * EwBin.wdOf M A K J t + 1 ∧ τ.sh i = 0) ∧
      τ.st 0 = σ.st 0 ∧ τ.sh 0 = σ.sh 0 ∧ τ.cell = σ.cell := by
  obtain ⟨hbM, hbP, hbX, hbV⟩ := EwClog.e_bounds M A K J t
  have z6 := hz 6 (by decide)
  have z7 := hz 7 (by decide)
  have z8 := hz 8 (by decide)
  have z9 := hz 9 (by decide)
  have z10 := hz 10 (by decide)
  have z36 := hz 36 (by decide)
  have z37 := hz 37 (by decide)
  have z38 := hz 38 (by decide)
  have z39 := hz 39 (by decide)
  have z40 := hz 40 (by decide)
  have z41 := hz 41 (by decide)
  have z42 := hz 42 (by decide)
  have z43 := hz 43 (by decide)
  have z44 := hz 44 (by decide)
  have z45 := hz 45 (by decide)
  have z46 := hz 46 (by decide)
  have z47 := hz 47 (by decide)
  have b1 := (hs 1 (by decide)).1
  have e1 := (hs 1 (by decide)).2
  have b2 := (hs 2 (by decide)).1
  have e2 := (hs 2 (by decide)).2
  have b3 := (hs 3 (by decide)).1
  have e3 := (hs 3 (by decide)).2
  have b4 := (hs 4 (by decide)).1
  have e4 := (hs 4 (by decide)).2
  have b5 := (hs 5 (by decide)).1
  have e5 := (hs 5 (by decide)).2
  have b6 := (hs 6 (by decide)).1
  have e6 := (hs 6 (by decide)).2
  have b7 := (hs 7 (by decide)).1
  have e7 := (hs 7 (by decide)).2
  have b8 := (hs 8 (by decide)).1
  have e8 := (hs 8 (by decide)).2
  unfold eNeed EwBin.zOf at hcap
  obtain ⟨wd, hwd⟩ : ∃ w, w = EwBin.wdOf M A K J t := ⟨_, rfl⟩
  have hwd' : wd = t * M + t * M + M + J + K + A + 8 := hwd
  rw [← hwd] at hbM hbP hbX hbV hcap ⊢
  have c1 := EwBin.e1_spec cap σ M A K J t hM hA hK hJ ht z8 z9 z10 z36 z37
    (by unfold EwBin.zOf; rw [← hwd]; omega)
  rw [← hwd] at c1
  have c2 := WExec.seq c1 (EwWords.e2_spec cap _ M J (8 * (K * A)) wd (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (fun i hi => by fin_cases i <;> simp_all [Function.update_apply]) (by omega))
  have c3 := WExec.seq c2 (EwPow.pow_spec cap _ wd M t (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) hbP hbM (by omega))
  have c4 := WExec.seq c3 (EwPow.prod_spec cap _ wd M J (8 * (K * A)) (M ^ (2 * t)) (M ^ (2 * t))
    (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega) hbX hbP hbM (by omega))
  have c5 := WExec.seq c4 (EwClog.cl_spec cap _ wd M (8 * (K * A) * (J * M ^ (2 * t) + M) + 1)
    (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) hbV (by omega)
    (by omega))
  have c6 := WExec.seq c5 (wclear_spec cap 36 wd _ (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, EwWords.wordsSt, EwWords.fw, hM, hA, hK, hJ, ht, z6, z7, z8, z9, z10, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]; omega))
  refine ⟨_, WExec.mono c6 (by unfold eCost EwBin.zOf; rw [← hwd]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply]
  · intro r hr
    simp only [WState.setv_val, WState.sets_val, EwWords.wordsSt, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · intro i hi
    fin_cases i <;> simp_all [Function.update_apply, EwWords.wordsSt, fw_length]
  · simp [Function.update_apply, EwWords.wordsSt]
  · simp [Function.update_apply, EwWords.wordsSt]
  · simp [EwWords.wordsSt]

end NearCubicWires.WireExponent3_5.UnionMachine.EwE
