import Proof.Wire_3_5.Primitive.SeedFix.C4HfL

/-! # The HASH child family, part 13: the family

`filt:soft`, P3:2331-2335: **`chFamH`**, the HASH call's child family (`C4Loop.ChildFam`): one child machine per candidate
bit (the HASH child under base's masked reset), whose sum port holds the recovered child sum `chValH (p ++ [b])` below
`2^W`, the kept tapes unchanged, within `2·Kch + 2` steps; the Hb printer's, the compiler's and the cost conditions
(C4H's `HashEAt`) as hypotheses.

Paper quantity of the main type: the HASH decision's children and their recovered sums. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation

noncomputable section

section Fam
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (D : HashData) (c : HbCaps)

/-- The child's prefix tape (the unit's tape `94`). -/
def hPfxT : Fin (CTH A wa + 1) := Fin.castAdd 1 (hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩)

/-- The child's sum port. -/
def hSumP : Fin (CTH A wa + 1) := Fin.castAdd 1 (hSumT A wa)

/-- The child's kept tapes (the log is not kept). -/
def hKeepF : Fin (CTH A wa + 1) → Bool := Fin.addCases (hKeepC A wa) (fun _ => false)

/-- The kept tapes' words (the prefix tape's is the loop's: blank here). -/
def hKF (i : Fin (CTH A wa + 1)) : List Bool :=
  if i = hPfxT A wa then [] else Fin.addCases (hChInP A wa a R0 D c []) (fun _ => []) i

theorem hUnSl_94 : hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩ =
    Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) ⟨94, by rw [HU_eq]; omega⟩) := by
  rw [hUnSl, if_neg (by decide)]

theorem hChInP_off (p : List Bool) (i : Fin (CTH A wa)) (hk : hKeepC A wa i = false) :
    hChInP A wa a R0 D c p i = [] := by
  refine Fin.addCases (motive := fun i => hKeepC A wa i = false → hChInP A wa a R0 D c p i = [])
    (fun x hx => ?_) (fun y hy => ?_) i hk
  · simp only [hKeepC, Fin.addCases_left, decide_eq_false_iff_not, not_or] at hx
    simp [hChInP, hChIn, C4Child.asmK, hx.1, hx.2]
  · refine Fin.addCases (motive := fun y => hKeepC A wa (Fin.natAdd A.t y) = false →
      hChInP A wa a R0 D c p (Fin.natAdd A.t y) = []) (fun u hu => ?_) (fun k hk => ?_) y hy
    · simp only [hKeepC, Fin.addCases_right, Fin.addCases_left, decide_eq_false_iff_not, not_le] at hu
      simp only [hChInP, hChIn, Fin.addCases_right, Fin.addCases_left, uIn]
      rw [dif_neg (by omega), if_neg (by omega)]
    · simp only [hKeepC, Fin.addCases_right, decide_eq_false_iff_not, not_or] at hk
      simp only [hChInP, hChIn, Fin.addCases_right]
      have h1 : k.val ≠ C4Pipe.PD wa + 98 := fun h => hk.1 (Fin.ext h)
      have h2 : k.val ≠ C4Pipe.PD wa + 99 := fun h => hk.2 (Fin.ext h)
      simp [C4Pipe.childIn, h1, h2]

theorem hChInP_pfx (p : List Bool) (i : Fin (CTH A wa)) (hi : i ≠ hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩) :
    hChInP A wa a R0 D c p i = hChInP A wa a R0 D c [] i := by
  refine Fin.addCases (motive := fun i => i ≠ hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩ →
    hChInP A wa a R0 D c p i = hChInP A wa a R0 D c [] i) (fun x _ => ?_) (fun y hy => ?_) i hi
  · simp [hChInP, hChIn]
  · refine Fin.addCases (motive := fun y => Fin.natAdd A.t y ≠ hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩ →
      hChInP A wa a R0 D c p (Fin.natAdd A.t y) = hChInP A wa a R0 D c [] (Fin.natAdd A.t y))
      (fun u hu => ?_) (fun k _ => ?_) y hy
    · simp only [hChInP, hChIn, Fin.addCases_right, Fin.addCases_left, uIn]
      have h94 : u.val ≠ 94 := fun h => hu (by rw [hUnSl_94]; congr 2; exact Fin.ext h)
      by_cases hl : u.val < 94
      · rw [dif_pos hl, dif_pos hl]
      · rw [dif_neg hl, dif_neg hl, if_neg h94, if_neg h94]
    · simp [hChInP, hChIn]

/-- The child family's entry bank is the child's. -/
theorem hcin_eq (p : List Bool) :
    C4Loop.cin (hPfxT A wa) (hKeepF A wa) (hKF A wa a R0 D c) p =
      Fin.addCases (hChInP A wa a R0 D c p) (fun _ : Fin 1 => []) := by
  funext i
  unfold C4Loop.cin
  by_cases h1 : i = hPfxT A wa
  · rw [if_pos h1, h1, hPfxT, Fin.addCases_left, hUnSl_94]
    simp only [hChInP, hChIn, Fin.addCases_right, Fin.addCases_left, uIn]
    rw [dif_neg (by show ¬ (94 : ℕ) < 94; omega)]
    simp
  · rw [if_neg h1]
    refine Fin.addCases (motive := fun i => i ≠ hPfxT A wa → (if hKeepF A wa i = true then
      hKF A wa a R0 D c i else []) = Fin.addCases (hChInP A wa a R0 D c p)
        (fun _ : Fin 1 => []) i) (fun x hx => ?_) (fun y _ => ?_) i h1
    · simp only [hKeepF, hKF, Fin.addCases_left, if_neg hx]
      have hx' : x ≠ hUnSl A wa ⟨94, by rw [HU_eq]; omega⟩ := fun e => hx (by rw [e]; rfl)
      cases hk : hKeepC A wa x
      · simp [hChInP_off A wa a R0 D c p x hk]
      · simp [hChInP_pfx A wa a R0 D c p x hx']
    · simp [hKeepF, hKF]

theorem hKeepF_pfx : hKeepF A wa (hPfxT A wa) = true := by
  rw [hPfxT, hKeepF, Fin.addCases_left, hUnSl_94, hKeepC, Fin.addCases_right, Fin.addCases_left]
  decide

theorem hKeepF_sum : hKeepF A wa (hSumP A wa) = false := by
  have hne := C4Child.childSum_ne wa
  have e : hSumT A wa = Fin.natAdd A.t (Fin.natAdd HU (C4Pipe.childSum wa)) := by
    rw [hSumT, hCmSl, if_neg hne]
  rw [hSumP, hKeepF, Fin.addCases_left, e, hKeepC, Fin.addCases_right, Fin.addCases_right]
  simp only [decide_eq_false_iff_not, not_or]
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [C4Pipe.childSum, C4Pipe.dcSl, C4Pipe.childQQ, Fin.val_castAdd] at hv
    have := (C4Pipe.dcS (RepairOrdinary.CompetitorCrossScheduler.producer wa)).isLt
    simp only [C4Pipe.DT, C4Pipe.PD] at this hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [C4Pipe.childSum, C4Pipe.dcSl, C4Pipe.childUU, Fin.val_castAdd] at hv
    have := (C4Pipe.dcS (RepairOrdinary.CompetitorCrossScheduler.producer wa)).isLt
    simp only [C4Pipe.DT, C4Pipe.PD] at this hv
    omega

/-- **The HASH child of bit `b`**: the three stages under base's masked reset. -/
noncomputable def chMH (b : Bool) := MaskedReset.machine (coreMH A wa b) (fun _ => true)

/-- The two children at one state count. -/
noncomputable def chMHs (b : Bool) : type_of% (chMH A wa false) :=
  match b with
  | false => chMH A wa false
  | true => chMH A wa true

theorem chValH_lt (p' : List Bool) : chValH R0 D p' < 2 ^ C4Child.chW R0 := by
  have h1 : chValH R0 D p' ≤ 2 ^ R0.dRow * (2 ^ R0.dRow * (2 ^ R0.P.Q - 1)) := by
    unfold chValH
    calc _ ≤ ∑ i ∈ Finset.range (2 ^ R0.dRow), ∑ j ∈ Finset.range (2 ^ R0.dRow), (2 ^ R0.P.Q - 1) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Nat.le_sub_one_of_lt (C4Pipe.lres_lt _ _)
      _ = _ := by simp
  have hq := Nat.two_pow_pos R0.P.Q
  have hd := Nat.two_pow_pos R0.dRow
  have h2 : 2 ^ R0.dRow * (2 ^ R0.dRow * (2 ^ R0.P.Q - 1)) < 2 ^ R0.dRow * (2 ^ R0.dRow * 2 ^ R0.P.Q) := by
    apply Nat.mul_lt_mul_of_pos_left _ hd
    apply Nat.mul_lt_mul_of_pos_left _ hd
    omega
  have h3 : 2 ^ R0.dRow * (2 ^ R0.dRow * 2 ^ R0.P.Q) ≤ 2 ^ C4Child.chW R0 := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by unfold C4Child.chW; omega)
  omega

end Fam

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
