import Proof.Wire_3_5.Primitive.SeedFix.C4KWTypes
import Proof.Wire_3_5.Primitive.SeedFix.C4KWd

/-! # T-c v2: `QCopy2` (the `1^{Q'}` copy at its true cost) and its producer

P3:3011-3016 (the compiler request's `1^{Q'}` beside the kept words): `QCopy` (PrimTC4KWT) asks the copy
`qDockM` within `qCost q = 10q + 10` steps, but its word program `qW = whs 0 (wr 1 true; fwd 1; fwd 0)` costs
`7q + 1` (`ld_spec` for the identical `ldW`) and the masked reset doubles it (`2·steps + 2`), so `14q + 4 > 10q + 10`
for `q ≥ 2` (the finding). **`QCopy2`** is `QCopy` verbatim at **`qCost2 q = 14q + 14`** (the machine
unchanged; the OK); **`qCopy2_ok`**: `∀ x oQ hQ src, QCopy2 x oQ hQ src` (`ld_spec`, `wm_blankR`, `Step.focus`).

Paper quantity of the main type: the compiler request's `1^{Q'}` on the setup's tape (P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- T-c's steps, v2: the copy `7q + 1`, doubled by the masked reset, with slack. -/
def qCost2 (q : ℕ) : ℕ := 14 * q + 14

/-- **T-c's contract, v2**: `QCopy` at `qCost2`. -/
def QCopy2 (x oQ : ℕ) (hQ : oQ + 3 ≤ 3 + x) (src : Fin (3 + x)) : Prop :=
  src.val < oQ → ∀ (q : ℕ) (B : Fin (3 + x) → List Bool), B src = List.replicate q true →
    (∀ i : Fin (3 + x), oQ ≤ i.val → i.val < oQ + 3 → B i = []) →
    ∃ B' : Fin (3 + x) → List Bool, Step (qDockM x oQ hQ src) (qCost2 q) (fun _ => 0) B (fun _ => 0) B' ∧
      B' ⟨oQ, by omega⟩ = List.replicate q true ∧
      (∀ i : Fin (3 + x), (i.val < oQ ∨ oQ + 3 ≤ i.val) → B' i = B i) ∧
      (∀ i : Fin (3 + x), oQ + 1 ≤ i.val → i.val < oQ + 3 → ∃ m ≤ qCost2 q, B' i = List.replicate m false)

theorem qSl_val (x oQ : ℕ) (hQ : oQ + 3 ≤ 3 + x) (src : Fin (3 + x)) (j : Fin (1 + 2 + 0 + 1)) :
    (qSl x oQ hQ src j).val = if j.val = 0 then src.val else oQ + (if j.val = 2 then 0 else if j.val = 1 then 1 else 2) := by
  unfold qSl; split_ifs <;> rfl

/-- **T-c's producer, v2.** -/
theorem qCopy2_ok (x oQ : ℕ) (hQ : oQ + 3 ≤ 3 + x) (src : Fin (3 + x)) : QCopy2 x oQ hQ src := by
  intro hsrc q B hB hbl
  -- the word program's run
  have hw := C4Cap.ld_spec 0 (List.replicate q true) [] q
    (fun i hi => by rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hi])
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp) 0 (Nat.zero_le _)
  simp only [List.replicate_zero, List.append_nil, List.nil_append, List.length_nil, Nat.zero_add, Nat.sub_zero] at hw
  obtain ⟨A', hA, hst, hsc⟩ := wm_blankR 0 qW (C4Cap.cst (List.replicate q true) [] 0 0)
    (C4Cap.cst (List.replicate q true) (List.replicate q true) q q) (q * 7 + 1) hw
    (fun i => by fin_cases i <;> rfl) (fun r => r.elim0) rfl rfl (fun r => r.elim0)
  -- the slots
  have hinj : Function.Injective (qSl x oQ hQ src) := by
    intro a b h
    have hv := congrArg Fin.val h
    rw [qSl_val, qSl_val] at hv
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    split_ifs at hv <;> omega
  have s := hA.focus (qSl x oQ hQ src) hinj (fun _ => 0) B
  have hdz : dockH (qSl x oQ hQ src) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, qSl x oQ hQ src j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [dockH_slot _ hinj]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  have hins : install (qSl x oQ hQ src) B (Fin.addCases (C4Pipe.wblank (C4Cap.cst (List.replicate q true) [] 0 0))
      (fun _ : Fin 1 => [])) = B := by
    apply install_existing
    intro j
    fin_cases j
    · show B (qSl x oQ hQ src 0) = List.replicate q true
      rw [show qSl x oQ hQ src 0 = src from Fin.ext (by rw [qSl_val]; rfl), hB]
    · show B (qSl x oQ hQ src 1) = []
      exact hbl _ (by rw [qSl_val]; simp) (by rw [qSl_val]; simp)
    · show B (qSl x oQ hQ src 2) = []
      exact hbl _ (by rw [qSl_val]; simp) (by rw [qSl_val]; simp)
    · show B (qSl x oQ hQ src 3) = []
      exact hbl _ (by rw [qSl_val]; simp) (by rw [qSl_val]; simp)
  rw [hdz, hins] at s
  refine ⟨install (qSl x oQ hQ src) B A', s.enlarge (by unfold qCost2; omega), ?_, fun i hi => ?_, fun i h1 h2 => ?_⟩
  · have hs := install_slot (qSl x oQ hQ src) hinj B A' 2
    rw [show qSl x oQ hQ src 2 = ⟨oQ, by omega⟩ from Fin.ext (by rw [qSl_val]; rfl)] at hs
    rw [hs]
    exact hst 1
  · by_cases his : i = src
    · rw [his]
      have hs := install_slot (qSl x oQ hQ src) hinj B A' 0
      rw [show qSl x oQ hQ src 0 = src from Fin.ext (by rw [qSl_val]; rfl)] at hs
      rw [hs, hB]
      exact hst 0
    · rw [install_other _ _ _ _ (fun j h => by
        have hv := congrArg Fin.val h
        rw [qSl_val] at hv
        have hjl := j.isLt
        split_ifs at hv with h0
        · exact his (Fin.ext hv.symm)
        all_goals omega)]
  · have hi1 : i.val = oQ + 1 ∨ i.val = oQ + 2 := by omega
    rcases hi1 with e | e
    · obtain ⟨m, hm, hm'⟩ := hsc 1 (fun k => by fin_cases k <;> decide)
      refine ⟨m, by unfold qCost2; omega, ?_⟩
      have hs := install_slot (qSl x oQ hQ src) hinj B A' 1
      rw [show qSl x oQ hQ src 1 = i from Fin.ext (by rw [qSl_val]; simp; omega)] at hs
      rw [hs, hm']
    · obtain ⟨m, hm, hm'⟩ := hsc 3 (fun k => by fin_cases k <;> decide)
      refine ⟨m, by unfold qCost2; omega, ?_⟩
      have hs := install_slot (qSl x oQ hQ src) hinj B A' 3
      rw [show qSl x oQ hQ src 3 = i from Fin.ext (by rw [qSl_val]; simp; omega)] at hs
      rw [hs, hm']

end NearCubicWires.WireExponent3_5.PrimT.C4KW
