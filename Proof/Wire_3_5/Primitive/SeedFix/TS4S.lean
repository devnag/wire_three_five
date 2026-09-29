import Proof.Wire_3_5.Primitive.SeedFix.TS4R

/-! # thrStage4U, part 8: the docks' inputs match (the hash writer, the collection)

P3:2543-2558, 3068-3084 (as part 6): after the first three phases (register-language state `σ2`), the hash writer runs on
the output stream, the cell, the sixteen value ports and the stage's registers (`σQ`), and the collection runs on the
stage's tapes with the writer's output stream, registers and cell (`σC`):
* `σQ`, **`matchQ`**, **`matchQH`**; `σC`, **`matchC`**, **`matchCH`**.

Paper quantities of the main type: the data word's two parts (the hash numbers, then the slice lengths). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ThrData

/-- The hash writer's state: the stage's output stream, the sixteen numbers in unary, the stage's registers and cell. -/
def σQ (σ2 : WState DS DR) (hs : List ℕ) : WState 16 16 :=
  ⟨fun s => if s.val = 0 then σ2.sh sOUT else 0,
    fun s => if s.val = 0 then σ2.st sOUT else List.replicate (hs.getD (s.val - 1) 0) true, σ2.val, σ2.cell⟩

/-- The collection's state: the stage's with the writer's output stream, registers and cell. -/
def σC (σ2 : WState DS DR) (τQ : WState 16 16) : WState DS DR :=
  ⟨Function.update σ2.sh sOUT (τQ.sh 0), Function.update σ2.st sOUT (τQ.st 0), τQ.val, τQ.cell⟩

theorem sTape_val16 (s : Fin 17) : (sTape (nr := 16) s).val = if s.val = 0 then 0 else s.val + 1 := rfl
theorem sTape_valD (s : Fin (DS + 1)) : (sTape (nr := DR) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

variable (alg : RepairRepresentation.DecompositionAlgorithm)

/-- **The hash writer's input tapes.** -/
theorem matchQ (cap : ℕ) (σ2 : WState DS DR) (hs : List ℕ) (A2 : Fin (TS + t4X alg) → List Bool)
    (outW : Fin (21 + (W6.TI alg + 1)) → List Bool)
    (hW : ∀ k (hk : k < 21 + (W6.TI alg + 1)), 1 ≤ k → k ≤ 16 → install (t4W alg) A2 outW (t4W alg ⟨k, hk⟩) =
      List.replicate (hs.getD (k - 1) 0) true)
    (j : Fin (16 + 2 + 16)) :
    install (t4E alg) (install (t4W alg) A2 outW) (wenc cap σ2).A (t4Q alg j) = (wenc cap (σQ σ2 hs)).A j := by
  have e3 := TS_val; have e4 := TI_w6x alg; have hb := t4X_ge alg; have eD := DS_val
  rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_A_s]
    by_cases h0 : s.val = 0
    · have hs0 : s = 0 := Fin.ext h0
      have e : t4Q alg (sTape s) = t4E alg (sTape sOUT) := Fin.ext (by simp [t4Q, t4E, sTape_val16, sTape, h0, sOUT])
      rw [e, install_slot _ (t4E_inj alg), wenc_A_s]
      simp [σQ, hs0]
    · have hsne : s ≠ 0 := fun e => h0 (by rw [e]; rfl)
      have hs1 := s.isLt
      have hsv : s.val < 21 + (W6.TI alg + 1) := by omega
      rw [install_other _ _ _ _ (fun i e => by
        have hv := congrArg Fin.val e
        simp only [t4Q, t4E, sTape_val16, if_neg h0] at hv
        have := i.isLt
        split_ifs at hv <;> omega)]
      by_cases h1 : s.val = 1
      · have e : t4Q alg (sTape s) = t4W alg ⟨1, by omega⟩ := Fin.ext (by simp [t4Q, t4W, sTape_val16, h0, h1])
        rw [e, hW 1 _ (by omega) (by omega)]; simp [σQ, hsne, h1]
      by_cases h2 : s.val = 2
      · have e : t4Q alg (sTape s) = t4W alg ⟨2, by omega⟩ := Fin.ext (by simp [t4Q, t4W, sTape_val16, h0, h2])
        rw [e, hW 2 _ (by omega) (by omega)]; simp [σQ, hsne, h2]
      · have hq : (sTape (nr := 16) s).val = s.val + 1 := by rw [sTape_val16, if_neg h0]
        have c0 : ¬ (s.val + 1 = 0) := by omega
        have c1 : ¬ (s.val + 1 = 1) := by omega
        have c2 : ¬ (s.val + 1 = 2) := by omega
        have c3 : ¬ (s.val + 1 = 3) := by omega
        have c4 : s.val + 1 < 18 := by omega
        have ev : (t4Q alg (sTape s)).val = TS + (s.val - 3) := by
          simp only [t4Q, hq, if_neg c0, if_neg c1, if_neg c2, if_neg c3, if_pos c4]
          omega
        have d20 : ¬ (s.val = 20) := by omega
        have d19 : s.val < 20 := by omega
        have ew : (t4W alg ⟨s.val, hsv⟩).val = TS + (s.val - 3) := by
          simp only [t4W, if_neg h0, if_neg h1, if_neg h2, if_neg d20, if_pos d19]
        have e : t4Q alg (sTape s) = t4W alg ⟨s.val, hsv⟩ := Fin.ext (by rw [ev, ew])
        rw [e, hW s.val hsv (by omega) (by omega)]; simp [σQ, hsne]
  · have e : t4Q alg cTape = t4E alg cTape := Fin.ext (by simp [t4Q, t4E, cTape, Nat.mod_eq_of_lt (show 1 < TS by decide)])
    rw [e, install_slot _ (t4E_inj alg), wenc_A_c, wenc_A_c]; rfl
  · have e : t4Q alg (rTape r) = t4E alg (rTape r) := Fin.ext (by
      simp only [t4Q, t4E, rTape]; have := r.isLt; split_ifs <;> omega)
    rw [e, install_slot _ (t4E_inj alg), wenc_A_r, wenc_A_r]; rfl

/-- **The hash writer's input heads.** -/
theorem matchQH (cap : ℕ) (σ2 : WState DS DR) (hs : List ℕ) (j : Fin (16 + 2 + 16)) :
    dockH (t4E alg) (fun _ => 0) (wenc cap σ2).H (t4Q alg j) = (wenc cap (σQ σ2 hs)).H j := by
  have e3 := TS_val; have hb := t4X_ge alg; have eD := DS_val
  rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s]
    by_cases h0 : s.val = 0
    · have hs0 : s = 0 := Fin.ext h0
      have e : t4Q alg (sTape s) = t4E alg (sTape sOUT) := Fin.ext (by simp [t4Q, t4E, sTape_val16, sTape, h0, sOUT])
      rw [e, dockH_slot _ (t4E_inj alg), wenc_H_s]
      simp [σQ, hs0]
    · have hsne : s ≠ 0 := fun e => h0 (by rw [e]; rfl)
      have hs1 := s.isLt
      rw [dockH_other _ _ _ _ (fun i e => by
        have hv := congrArg Fin.val e
        simp only [t4Q, t4E, sTape_val16, if_neg h0] at hv
        have := i.isLt
        split_ifs at hv <;> omega)]
      simp [σQ, hsne]
  · have e : t4Q alg cTape = t4E alg cTape := Fin.ext (by simp [t4Q, t4E, cTape, Nat.mod_eq_of_lt (show 1 < TS by decide)])
    rw [e, dockH_slot _ (t4E_inj alg), wenc_H_c, wenc_H_c]
  · have e : t4Q alg (rTape r) = t4E alg (rTape r) := Fin.ext (by
      simp only [t4Q, t4E, rTape]; have := r.isLt; split_ifs <;> omega)
    rw [e, dockH_slot _ (t4E_inj alg), wenc_H_r, wenc_H_r]; rfl

/-- **The collection's input tapes.** -/
theorem matchC (cap : ℕ) (σ2 : WState DS DR) (τQ : WState 16 16) (A2 : Fin (TS + t4X alg) → List Bool) (i : Fin TS) :
    install (t4Q alg) (install (t4E alg) A2 (wenc cap σ2).A) (wenc cap τQ).A (t4E alg i) = (wenc cap (σC σ2 τQ)).A i := by
  have e3 := TS_val; have hb := t4X_ge alg; have eD := DS_val
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_A_s]
    by_cases hO : s = sOUT
    · subst hO
      have e : t4E alg (sTape sOUT) = t4Q alg (sTape 0) := Fin.ext (by simp [t4Q, t4E, sTape, sOUT])
      rw [e, install_slot _ (t4Q_inj alg), wenc_A_s]; simp [σC]
    · have hsv : s.val ≠ 5 := fun h => hO (Fin.ext (by simp [sOUT, h, Nat.mod_eq_of_lt (show 5 < DS + 1 by decide)]))
      rw [install_other _ _ _ _ (fun j e => by
        have hv := congrArg Fin.val e
        simp only [t4Q, t4E, sTape_valD] at hv
        have := j.isLt; have := s.isLt
        split_ifs at hv <;> omega)]
      rw [install_slot _ (t4E_inj alg), wenc_A_s]
      simp [σC, Function.update_of_ne hO]
  · have e : t4E alg cTape = t4Q alg cTape := Fin.ext (by simp [t4Q, t4E, cTape, Nat.mod_eq_of_lt (show 1 < TS by decide)])
    rw [e, install_slot _ (t4Q_inj alg), wenc_A_c, wenc_A_c]; rfl
  · have e : t4E alg (rTape r) = t4Q alg (rTape r) := Fin.ext (by
      simp only [t4Q, t4E, rTape]; have := r.isLt; split_ifs <;> omega)
    rw [e, install_slot _ (t4Q_inj alg), wenc_A_r, wenc_A_r]; rfl

/-- **The collection's input heads.** -/
theorem matchCH (cap : ℕ) (σ2 : WState DS DR) (τQ : WState 16 16) (i : Fin TS) :
    dockH (t4Q alg) (dockH (t4E alg) (fun _ => 0) (wenc cap σ2).H) (wenc cap τQ).H (t4E alg i) =
      (wenc cap (σC σ2 τQ)).H i := by
  have e3 := TS_val; have hb := t4X_ge alg; have eD := DS_val
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s]
    by_cases hO : s = sOUT
    · subst hO
      have e : t4E alg (sTape sOUT) = t4Q alg (sTape 0) := Fin.ext (by simp [t4Q, t4E, sTape, sOUT])
      rw [e, dockH_slot _ (t4Q_inj alg), wenc_H_s]; simp [σC]
    · have hsv : s.val ≠ 5 := fun h => hO (Fin.ext (by simp [sOUT, h, Nat.mod_eq_of_lt (show 5 < DS + 1 by decide)]))
      rw [dockH_other _ _ _ _ (fun j e => by
        have hv := congrArg Fin.val e
        simp only [t4Q, t4E, sTape_valD] at hv
        have := j.isLt; have := s.isLt
        split_ifs at hv <;> omega)]
      rw [dockH_slot _ (t4E_inj alg), wenc_H_s]
      simp [σC, Function.update_of_ne hO]
  · have e : t4E alg cTape = t4Q alg cTape := Fin.ext (by simp [t4Q, t4E, cTape, Nat.mod_eq_of_lt (show 1 < TS by decide)])
    rw [e, dockH_slot _ (t4Q_inj alg), wenc_H_c, wenc_H_c]
  · have e : t4E alg (rTape r) = t4Q alg (rTape r) := Fin.ext (by
      simp only [t4Q, t4E, rTape]; have := r.isLt; split_ifs <;> omega)
    rw [e, dockH_slot _ (t4Q_inj alg), wenc_H_r, wenc_H_r]; rfl

end NearCubicWires.WireExponent3_5.PrimT.TS4
