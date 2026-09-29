import Proof.Wire_3_5.Primitive.Writers.ThrFin4

/-! # c4 THR block, the THR finisher's dock on the big bank (`C4Wrap.FinDock`)

At the big bank whose first tapes carry the SYM-shaped exit bank (`C4SymW.SymBank`), with the marked hash bits on a
tape `hbT` above the layout and the bank blank from the finisher's region `off₂` up: the finisher `finM` docked by
`extF` (`finExt`, lifted, and `hbT`), its output on port `2` (**`thr_fin`**, from `sym_fin` on the first tapes).

Paper quantity of the main type: the THR seed word's inputs, the loop's decisions and the hash bits (P3:2932-2937,
2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (FinDock postLoop pfxL)
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (L : Lay) {x' : ℕ} (hx : 3 + L.X ≤ 3 + x') (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams)
  (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ) (pre post : List Bool) (q uu : ℕ) (B : Fin L.N → List Bool)
  (ρ : ℕ) (v : List Bool) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)

/-- **The THR finisher's dock on the big bank.** -/
theorem thr_fin (hS : C4SymW.ChShape F pd P ents TWd Cap nT pre post q uu)
    (hB : C4SymW.SymBank L pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd)
    (hP2 : B L.gP2 = []) (hMB : B L.gMB = frame (binary ell (GF.firstPrimitive ell)))
    (hbl : ∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B i = []) (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s)
    (hoff' : L.oLP + (F.T + 1 + 1 + 1) ≤ 3 + x') (B' : Fin (3 + x') → List Bool) (hBB : ∀ i, B' (liftE hx i) = B i)
    (hbF : List Bool) (hbT : Fin (3 + x')) (hbT0 : 3 + L.X ≤ hbT.val) (hbT1 : B' hbT = marks hbF)
    (off2 : ℕ) (hbT2 : hbT.val < off2) (hoff2 : off2 + 34 ≤ 3 + x')
    (hbl2 : ∀ i : Fin (3 + x'), off2 ≤ i.val → B' i = []) :
    FinDock off2 hoff2 (extF L hx hbT) 6 (tinF P s hbF)
      (postLoop F L.oLP hoff' (liftX hx (C4SymW.symExt L pd)) B') := by
  have fD := C4SymW.sym_fin L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hP2 hMB hbl hT htS
    s hG
  have hLN : L.oLP + L.T + 31 ≤ 3 + L.X := C4SymW.hoffF L htS
  have hoffL := C4SymW.hoffL L F hT
  -- the prefix slot is on the first tapes
  have hpl : ∀ i : Fin (3 + x'), 3 + L.X ≤ i.val →
      postLoop F L.oLP hoff' (liftX hx (C4SymW.symExt L pd)) B' i = B' i := by
    intro i hi
    unfold postLoop
    rw [slx_lift hx L.oLP hoffL hoff' (C4SymW.symExt L pd)]
    apply Function.update_of_ne
    intro e
    have := congrArg Fin.val e
    rw [liftE_val] at this
    have := (slx L.oLP hoffL (C4SymW.symExt L pd) (pfxL F)).isLt
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro i j g hi hj
    unfold extF at hi hj
    by_cases hi1 : i.val < 31 <;> by_cases hj1 : j.val < 31
    · rw [dif_pos hi1] at hi
      rw [dif_pos hj1] at hj
      obtain ⟨gi, egi, rfl⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨gj, egj, e⟩ := Option.map_eq_some_iff.mp hj
      have : gj = gi := liftE_inj hx e
      subst this
      have := fD.inj _ _ gj egi egj
      exact Fin.ext (by have h2 := congrArg Fin.val this; simpa using h2)
    · rw [dif_pos hi1] at hi
      rw [dif_neg hj1] at hj
      split_ifs at hj with hj2
      · obtain ⟨gi, egi, rfl⟩ := Option.map_eq_some_iff.mp hi
        simp only [Option.some.injEq] at hj
        have := congrArg Fin.val hj
        rw [liftE_val] at this
        have := gi.isLt
        omega
    · rw [dif_neg hi1] at hi
      rw [dif_pos hj1] at hj
      split_ifs at hi with hi2
      · obtain ⟨gj, egj, rfl⟩ := Option.map_eq_some_iff.mp hj
        simp only [Option.some.injEq] at hi
        have := congrArg Fin.val hi
        rw [liftE_val] at this
        have := gj.isLt
        omega
    · rw [dif_neg hi1] at hi
      rw [dif_neg hj1] at hj
      split_ifs at hi hj with hi2 hj2
      exact Fin.ext (by omega)
  · -- lt
    intro i g hi
    unfold extF at hi
    by_cases hi1 : i.val < 31
    · rw [dif_pos hi1] at hi
      obtain ⟨gi, egi, rfl⟩ := Option.map_eq_some_iff.mp hi
      have := fD.lt _ gi egi
      rw [liftE_val]
      unfold C4SymW.offF at this
      omega
    · rw [dif_neg hi1] at hi
      split_ifs at hi with hi2
      simp only [Option.some.injEq] at hi
      rw [← hi]; exact hbT2
  · -- port
    intro i g hi
    unfold extF at hi
    by_cases hi1 : i.val < 31
    · rw [dif_pos hi1] at hi
      obtain ⟨gi, egi, rfl⟩ := Option.map_eq_some_iff.mp hi
      rw [liftE_val]
      exact fD.port _ gi egi
    · rw [dif_neg hi1] at hi
      split_ifs at hi with hi2
      simp only [Option.some.injEq] at hi
      rw [← hi]; constructor <;> omega
  · -- out
    have h6 : C4SymW.finExt L ⟨6, by norm_num⟩ = some ⟨2, by rw [Lay.N_eq]; omega⟩ := fD.out
    unfold extF
    rw [dif_pos (by decide)]
    show Option.map (liftE hx) (C4SymW.finExt L ⟨6, by norm_num⟩) = _
    rw [h6]
    rfl
  · -- inp
    intro j g hj
    unfold extF at hj
    by_cases hj1 : j.val < 31
    · rw [dif_pos hj1] at hj
      obtain ⟨gj, egj, rfl⟩ := Option.map_eq_some_iff.mp hj
      rw [postLoop_lift L hx F L.oLP hoffL hoff' (C4SymW.symExt L pd) B B' hBB, fD.inp _ gj egj]
      unfold tinF
      rw [dif_pos hj1]
    · rw [dif_neg hj1] at hj
      split_ifs at hj with hj2
      simp only [Option.some.injEq] at hj
      rw [← hj, hpl _ hbT0, hbT1]
      unfold tinF
      rw [dif_neg hj1, if_pos hj2]
  · -- own
    intro j hj
    unfold extF at hj
    unfold tinF
    by_cases hj1 : j.val < 31
    · rw [dif_pos hj1] at hj
      rw [dif_pos hj1]
      exact fD.own _ (Option.map_eq_none_iff.mp hj)
    · rw [dif_neg hj1] at hj
      rw [dif_neg hj1]
      split_ifs at hj with hj2
      rw [if_neg hj2]
  · -- blank
    intro i hi
    rw [hpl i (by omega)]
    exact hbl2 i hi

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
