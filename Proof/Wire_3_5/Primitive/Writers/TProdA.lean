import Proof.Wire_3_5.Primitive.SeedFix.C4KWTypes
import Proof.Wire_3_5.Primitive.Writers.ShellDRun

/-! # T-a: the data stage re-run and the copy-in (`DataRerun`, the contract, generic)

P3:3011-3016 (the setup's counts before the loop): the data stage `S.M3` focused by `drSl` (its request, `1^n`,
`1^L`, `1^W` streams on `t0, tN, tL, tD`, every other tape `j` on `oD + j`) runs from the bank exactly as from its
raw entry (`install_existing`: the raw entry's other tapes are blank, as is the region), then the copy-in `cpZ`
focused by `cpSl` reads the data word `dataWord cs = 0 · frame (unaryList cs)` on `oD + 6` (`sOUT`) and writes
`unaryList cs` on `oD + drTU S` (`C4Set.cpS`, `ShellD.dataWord_eq`).
* `drSl_val`, `drSl_inj`, `drSl_off`, `cpSl_inj`, `raw_eq`; **`dataRerun_ok`**: `∀ S x oD hD t0 tN tL tD,
  DataRerun S x oD hD t0 tN tL tD`.

Paper quantity of the main type: the THR call's counts on the setup's tapes (P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimAsm.TProd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Data (DS DR sIN sNT sLT sCT sOUT rawIn dataWord unaryList)

section DR
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
  (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (x oD : ℕ) (hD : oD + drN S ≤ 3 + x)
  (t0 tN tL tD : Fin (3 + x))

theorem drSl_val (j : Fin (drM3 S)) : (drSl S x oD hD t0 tN tL tD j).val =
    if j.val = 0 then t0.val else if j.val = 2 then tN.val else if j.val = 3 then tL.val else if j.val = 4 then tD.val
    else oD + j.val := by
  unfold drSl; split_ifs <;> rfl

theorem cpSl_val (j : Fin (1 + 2 + 0 + 1)) : (cpSl S x oD hD j).val = if j.val = 0 then oD + 6 else oD + drM3 S + (j.val - 1) :=
  rfl

section H
variable (h01 : t0 ≠ tN) (h02 : t0 ≠ tL) (h03 : t0 ≠ tD) (h12 : tN ≠ tL) (h13 : tN ≠ tD) (h23 : tL ≠ tD)
  (l0 : t0.val < oD) (lN : tN.val < oD) (lL : tL.val < oD) (lD : tD.val < oD)
include h01 h02 h03 h12 h13 h23 l0 lN lL lD

theorem drSl_inj : Function.Injective (drSl S x oD hD t0 tN tL tD) := by
  have v01 : t0.val ≠ tN.val := fun e => h01 (Fin.ext e)
  have v02 : t0.val ≠ tL.val := fun e => h02 (Fin.ext e)
  have v03 : t0.val ≠ tD.val := fun e => h03 (Fin.ext e)
  have v12 : tN.val ≠ tL.val := fun e => h12 (Fin.ext e)
  have v13 : tN.val ≠ tD.val := fun e => h13 (Fin.ext e)
  have v23 : tL.val ≠ tD.val := fun e => h23 (Fin.ext e)
  intro a b h
  have hv := congrArg Fin.val h
  rw [drSl_val, drSl_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- A tape off the four streams and off the region is no slot of the data stage. -/
theorem drSl_off (i : Fin (3 + x)) (hi0 : i ≠ t0) (hiN : i ≠ tN) (hiL : i ≠ tL) (hiD : i ≠ tD)
    (hio : i.val < oD ∨ oD + drM3 S ≤ i.val) : ∀ j, drSl S x oD hD t0 tN tL tD j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  rw [drSl_val] at hv
  have hjl := j.isLt
  split_ifs at hv
  · exact hi0 (Fin.ext hv.symm)
  · exact hiN (Fin.ext hv.symm)
  · exact hiL (Fin.ext hv.symm)
  · exact hiD (Fin.ext hv.symm)
  · omega

theorem cpSl_inj : Function.Injective (cpSl S x oD hD) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [cpSl_val, cpSl_val] at hv
  have e1 : drM3 S = DS + 2 + DR + 1 + S.x3 := rfl
  have e2 : DS = 9883 := rfl
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The data stage's raw entry is the bank at its slots. -/
theorem raw_eq (w : List Bool) (n L W : ℕ) (B : Fin (3 + x) → List Bool) (b0 : B t0 = frame w)
    (bN : B tN = List.replicate n true) (bL : B tL = List.replicate L true) (bD : B tD = List.replicate W true)
    (hbl : ∀ i : Fin (3 + x), oD ≤ i.val → i.val < oD + drN S → B i = []) :
    install (drSl S x oD hD t0 tN tL tD) B
      (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
        (Fin.addCases (rawIn w n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => [])) = B := by
  have e1 : drM3 S = DS + 2 + DR + 1 + S.x3 := rfl
  have e2 : DS = 9883 := rfl
  have eN : drN S = drM3 S + 3 := rfl
  apply install_existing
  intro j
  refine Fin.addCases (fun j1 => ?_) (fun jJ => ?_) j
  · refine Fin.addCases (fun j0 => ?_) (fun jc => ?_) j1
    · simp only [Fin.addCases_left]
      have hv := drSl_val S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 j0))
      simp only [Fin.val_castAdd] at hv
      unfold rawIn
      have s0 : (sTape (nr := DR) sIN : Fin (DS + 2 + DR)).val = 0 := rfl
      have s1 : (sTape (nr := DR) sNT : Fin (DS + 2 + DR)).val = 2 := rfl
      have s2 : (sTape (nr := DR) sLT : Fin (DS + 2 + DR)).val = 3 := rfl
      have s3 : (sTape (nr := DR) sCT : Fin (DS + 2 + DR)).val = 4 := rfl
      by_cases c0 : j0.val = 0
      · rw [if_pos (Fin.ext (by rw [s0]; exact c0))]
        rw [if_pos c0] at hv
        rw [show drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 j0)) = t0 from Fin.ext hv, b0]
      · rw [if_neg (fun e => c0 (by rw [e, s0]))]
        rw [if_neg c0] at hv
        by_cases c2 : j0.val = 2
        · rw [if_pos (Fin.ext (by rw [s1]; exact c2))]
          rw [if_pos c2] at hv
          rw [show drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 j0)) = tN from Fin.ext hv, bN]
        · rw [if_neg (fun e => c2 (by rw [e, s1]))]
          rw [if_neg c2] at hv
          by_cases c3 : j0.val = 3
          · rw [if_pos (Fin.ext (by rw [s2]; exact c3))]
            rw [if_pos c3] at hv
            rw [show drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 j0)) = tL from Fin.ext hv, bL]
          · rw [if_neg (fun e => c3 (by rw [e, s2]))]
            rw [if_neg c3] at hv
            by_cases c4 : j0.val = 4
            · rw [if_pos (Fin.ext (by rw [s3]; exact c4))]
              rw [if_pos c4] at hv
              rw [show drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 j0)) = tD from Fin.ext hv, bD]
            · rw [if_neg (fun e => c4 (by rw [e, s3]))]
              rw [if_neg c4] at hv
              exact hbl _ (by omega) (by have := j0.isLt; omega)
    · simp only [Fin.addCases_left, Fin.addCases_right, List.replicate_zero]
      have hv := drSl_val S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.natAdd (DS + 2 + DR) jc))
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have hjc := jc.isLt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hv
      exact hbl _ (by omega) (by omega)
  · simp only [Fin.addCases_right]
    have hv := drSl_val S x oD hD t0 tN tL tD (Fin.natAdd (DS + 2 + DR + 1) jJ)
    simp only [Fin.val_natAdd] at hv
    have hjJ := jJ.isLt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hv
    exact hbl _ (by omega) (by omega)

end H

/-- **T-a's producer**: the data stage re-run and the copy-in meet `DataRerun` at every layout. -/
theorem dataRerun_ok : DataRerun S x oD hD t0 tN tL tD := by
  intro h01 h02 h03 h12 h13 h23 l0 lN lL lD w n L W cs c3 tout m J B hS hout hin b0 bN bL bD hbl
  have e1 : drM3 S = DS + 2 + DR + 1 + S.x3 := rfl
  have e2 : DS = 9883 := rfl
  have eN : drN S = drM3 S + 3 := rfl
  have eU : drTU S = drM3 S + 1 := rfl
  have hinj1 := drSl_inj S x oD hD t0 tN tL tD h01 h02 h03 h12 h13 h23 l0 lN lL lD
  have hinj2 := cpSl_inj S x oD hD t0 tN tL tD h01 h02 h03 h12 h13 h23 l0 lN lL lD
  -- stage 1: the data stage on the bank
  have s1 := hS.focus (drSl S x oD hD t0 tN tL tD) hinj1 (fun _ => 0) B
  have hdz1 : dockH (drSl S x oD hD t0 tN tL tD) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, drSl S x oD hD t0 tN tL tD j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [dockH_slot _ hinj1]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  rw [hdz1, raw_eq S x oD hD t0 tN tL tD h01 h02 h03 h12 h13 h23 l0 lN lL lD w n L W B b0 bN bL bD hbl] at s1
  set B1 := install (drSl S x oD hD t0 tN tL tD) B
    (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) with hB1
  have f1t0 : B1 t0 = frame w := by
    have hs := install_slot (drSl S x oD hD t0 tN tL tD) hinj1 B
      (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J)
      (Fin.castAdd S.x3 (Fin.castAdd 1 (sTape (nr := DR) sIN)))
    have e : drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 (sTape (nr := DR) sIN))) = t0 := by
      apply Fin.ext; rw [drSl_val]; rfl
    rw [e] at hs
    rw [hB1, hs]
    simp only [Fin.addCases_left]
    exact hin
  have f1o : B1 ⟨oD + 6, by omega⟩ = dataWord cs := by
    have hs := install_slot (drSl S x oD hD t0 tN tL tD) hinj1 B
      (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J)
      (Fin.castAdd S.x3 (Fin.castAdd 1 (sTape (nr := DR) sOUT)))
    have e : drSl S x oD hD t0 tN tL tD (Fin.castAdd S.x3 (Fin.castAdd 1 (sTape (nr := DR) sOUT))) =
        ⟨oD + 6, by omega⟩ := by
      apply Fin.ext; rw [drSl_val]; rfl
    rw [e] at hs
    rw [hB1, hs]
    simp only [Fin.addCases_left]
    exact hout
  have f1off : ∀ i : Fin (3 + x), i ≠ t0 → i ≠ tN → i ≠ tL → i ≠ tD → (i.val < oD ∨ oD + drM3 S ≤ i.val) →
      B1 i = B i := fun i a b c d e =>
    install_other _ _ _ _ (drSl_off S x oD hD t0 tN tL tD h01 h02 h03 h12 h13 h23 l0 lN lL lD i a b c d e)
  -- stage 2: the copy-in
  obtain ⟨t7, h7, e72⟩ := C4Set.cpS (unaryList cs)
  have s2 := h7.focus (cpSl S x oD hD) hinj2 (fun _ => 0) B1
  have hdz2 : dockH (cpSl S x oD hD) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, cpSl S x oD hD j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [dockH_slot _ hinj2]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  have hne : ∀ i : Fin (3 + x), oD + drM3 S ≤ i.val → i ≠ t0 ∧ i ≠ tN ∧ i ≠ tL ∧ i ≠ tD := fun i hi =>
    ⟨fun e => by rw [e] at hi; omega, fun e => by rw [e] at hi; omega, fun e => by rw [e] at hi; omega,
      fun e => by rw [e] at hi; omega⟩
  have hin2 : install (cpSl S x oD hD) B1
      (fun j => if j.val = 0 then false :: (RepairOrdinary.Streaming.marks (unaryList cs) ++ [false]) else []) = B1 := by
    apply install_existing
    intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj]
      have e : cpSl S x oD hD j = ⟨oD + 6, by omega⟩ := by apply Fin.ext; rw [cpSl_val, if_pos hj]
      rw [e, f1o, ShellD.dataWord_eq]
    · rw [if_neg hj]
      have hjl := j.isLt
      have hv : (cpSl S x oD hD j).val = oD + drM3 S + (j.val - 1) := by rw [cpSl_val, if_neg hj]
      obtain ⟨a1, a2, a3, a4⟩ := hne (cpSl S x oD hD j) (by omega)
      rw [f1off _ a1 a2 a3 a4 (Or.inr (by omega))]
      exact hbl _ (by omega) (by omega)
  rw [hdz2, hin2] at s2
  refine ⟨install (cpSl S x oD hD) B1 t7, s1.seq s2, ?_, ?_, fun i a b c d e => ?_⟩
  · have hs := install_slot (cpSl S x oD hD) hinj2 B1 t7 ⟨2, by omega⟩
    have e : cpSl S x oD hD ⟨2, by omega⟩ = ⟨oD + drTU S, by omega⟩ := by apply Fin.ext; rw [cpSl_val]; simp; omega
    rw [e] at hs
    rw [hs, e72]
  · rw [install_other _ _ _ _ (fun j h => by
      have hv := congrArg Fin.val h
      rw [cpSl_val] at hv
      split_ifs at hv <;> omega)]
    exact f1t0
  · rw [install_other _ _ _ _ (fun j h => by
      have hv := congrArg Fin.val h
      rw [cpSl_val] at hv
      have hjl := j.isLt
      split_ifs at hv <;> omega)]
    exact f1off i a b c d (by omega)

end DR

end NearCubicWires.WireExponent3_5.PrimAsm.TProd
