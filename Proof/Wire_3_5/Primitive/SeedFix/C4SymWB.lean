import Proof.Wire_3_5.Primitive.SeedFix.C4SymWA
import Proof.Wire_3_5.Primitive.SeedFix.C4Sym

/-! # C4 SYM stage, part 2: the loop's entry bank, tape by tape

"For each candidate child prefix, print its signed equation expression [...] Choose a child with no larger sum"
(P3:3034-3037): before the first decision the loop's bank is the child family's scrubbed bank (`C4Wrap.loopBank F R L 0`).
This part reads it tape by tape: the scrubbed scratch (`R` falses), the log, the driver, the counter, and for the child
family of C6's assembler (`C4Child.chFam` at `UnionMachine.TailAsm.asmStage`) its kept tapes: the compiler fields, the
enumeration unit's rulers, prefix and constants (`C4Dock.euIn`), the printer child's `1^{Q'}` and mask.

* `loopBank_lt`, `loopBank_log`, `loopBank_drv`, `loopBank_cnt`, `src_scr`, `src_kept`;
* `kept`, `CT_eq`, **`keepF_val`**, `pfxT_val`, `KF_asm0`, `KF_asm2`, `KF_eu`, `KF_qq`, `KF_uu`.

Paper quantity of the main types: the kept words of the decision loop. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary

/-! ## The loop's bank before the first decision -/

section Bank
variable (F : C4Loop.ChildFam) (R L : ℕ)

theorem loopBank_lt (j : Fin (F.T + 1 + 1 + 1)) (h : j.val < F.T) :
    C4Wrap.loopBank F R L 0 j = F.src R 0 ⟨j.val, h⟩ := by
  unfold C4Wrap.loopBank
  rw [ac_lt _ _ j (by omega)]
  unfold Scrub.bank
  rw [ac_lt _ _ _ (by simp; omega), ac_lt _ _ _ (by simp; omega)]

theorem loopBank_log (j : Fin (F.T + 1 + 1 + 1)) (h : j.val = F.T) :
    C4Wrap.loopBank F R L 0 j = List.replicate L false := by
  unfold C4Wrap.loopBank
  rw [ac_lt _ _ j (by omega)]
  unfold Scrub.bank
  rw [ac_lt _ _ _ (by simp; omega), ac_ge _ _ _ (by simp; omega)]

theorem loopBank_drv (j : Fin (F.T + 1 + 1 + 1)) (h : j.val = F.T + 1) :
    C4Wrap.loopBank F R L 0 j = List.replicate R true := by
  unfold C4Wrap.loopBank
  rw [ac_lt _ _ j (by omega)]
  unfold Scrub.bank
  rw [ac_ge _ _ _ (by simp; omega)]

theorem loopBank_cnt (j : Fin (F.T + 1 + 1 + 1)) (h : j.val = F.T + 2) :
    C4Wrap.loopBank F R L 0 j = RepairSource.VerifierDecoding.CompareMachine.word F.bound := by
  unfold C4Wrap.loopBank
  rw [ac_ge _ _ j (by omega)]

theorem src_scr (i : Fin F.T) (h : F.cellS i = true) : F.src R 0 i = List.replicate R false := by
  unfold C4Loop.ChildFam.src Scrub.blank
  rw [if_pos h]

theorem src_kept (i : Fin F.T) (hi : i.val < F.t) (hk : F.keep ⟨i.val, hi⟩ = true) :
    F.src R 0 i = C4Loop.cin F.PFX F.keep F.K [] ⟨i.val, hi⟩ := by
  have hS : F.cellS i = false := by
    unfold C4Loop.ChildFam.cellS
    rw [dif_pos hi, hk]
    rfl
  unfold C4Loop.ChildFam.src Scrub.blank
  rw [hS]
  simp only [Bool.false_eq_true, if_false]
  unfold C4Loop.ChildFam.cellIn
  rw [dif_pos hi]
  rfl

end Bank

/-! ## The child family of C6's assembler -/

section Fam
variable (wa : RepairRepresentation.WilliamsAlgorithm) (a : RepairRepresentation.DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ)

/-- The child's kept tapes (`C4Child.keepF`, by value). -/
def kept (pd v : ℕ) : Prop :=
  v = 0 ∨ v = 2 ∨ v = 6 ∨ (8 ≤ v ∧ v ≤ 17) ∨ (73 ≤ v ∧ v ≤ 89) ∨ v = 199 + pd ∨ v = 200 + pd

instance (pd v : ℕ) : Decidable (kept pd v) := by unfold kept; infer_instance

theorem CT_eq : C4Child.CT UnionMachine.TailAsm.asmStage wa = 201 + C4Pipe.PD wa := by
  unfold C4Child.CT C4Pipe.CN
  show 6 + (C4Dock.EU + (C4Pipe.PD wa + 100)) = _
  have : C4Dock.EU = 95 := rfl
  omega

theorem keepF_val (v : ℕ) (hv : v < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.keepF UnionMachine.TailAsm.asmStage wa ⟨v, hv⟩ = decide (kept (C4Pipe.PD wa) v) := by
  have hCT := CT_eq wa
  have hEU : C4Dock.EU = 95 := rfl
  have hA : UnionMachine.TailAsm.asmStage.t = 6 := rfl
  unfold C4Child.keepF
  by_cases h1 : v < C4Child.CT UnionMachine.TailAsm.asmStage wa
  · rw [ac_lt _ _ _ h1]
    unfold C4Child.keepC
    by_cases h2 : v < UnionMachine.TailAsm.asmStage.t
    · rw [ac_lt _ _ _ h2]
      have e0 : ((⟨v, h2⟩ : Fin UnionMachine.TailAsm.asmStage.t) = UnionMachine.TailAsm.asmStage.pA) ↔ v = 0 := by
        rw [Fin.ext_iff]; rfl
      have e2 : ((⟨v, h2⟩ : Fin UnionMachine.TailAsm.asmStage.t) = UnionMachine.TailAsm.asmStage.pB) ↔ v = 2 := by
        rw [Fin.ext_iff]; rfl
      simp only [e0, e2]
      apply decide_eq_decide.mpr
      unfold kept
      omega
    · rw [ac_ge _ _ _ (by simp only [Fin.val_mk]; omega)]
      by_cases h3 : v - UnionMachine.TailAsm.asmStage.t < C4Dock.EU
      · rw [ac_lt _ _ _ (by simp only [Fin.val_mk]; exact h3)]
        apply decide_eq_decide.mpr
        unfold kept
        simp only [Fin.val_mk]
        omega
      · rw [ac_ge _ _ _ (by simp only [Fin.val_mk]; omega)]
        have eq : ∀ k : Fin (C4Pipe.CN wa), (k = C4Pipe.childQQ wa ↔ k.val = C4Pipe.PD wa + 98) ∧
            (k = C4Pipe.childUU wa ↔ k.val = C4Pipe.PD wa + 99) := fun k =>
          ⟨by rw [Fin.ext_iff]; rfl, by rw [Fin.ext_iff]; rfl⟩
        simp only [(eq _).1, (eq _).2, Fin.val_mk]
        apply decide_eq_decide.mpr
        unfold kept
        omega
  · rw [ac_ge _ _ _ (by simp only [Fin.val_mk]; omega)]
    symm
    apply decide_eq_false
    unfold kept
    omega

theorem pfxT_val : (C4Child.pfxT UnionMachine.TailAsm.asmStage wa).val = 17 := by
  unfold C4Child.pfxT
  rw [Fin.val_castAdd, C4Child.euSl_aS10]
  rfl

theorem KF_asm0 (h : 0 < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.KF UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT ⟨0, h⟩ = frame (C4Child.pre a R0) := by
  unfold C4Child.KF
  rw [ac_lt _ _ _ (by have := CT_eq wa; simp only [Fin.val_mk]; omega)]
  unfold C4Child.chInP C4Child.chIn
  rw [ac_lt _ _ _ (by show 0 < 6; omega)]
  try rfl

theorem KF_asm2 (h : 2 < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.KF UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT ⟨2, h⟩ = frame (C4Child.post a R0) := by
  unfold C4Child.KF
  rw [ac_lt _ _ _ (by have := CT_eq wa; simp only [Fin.val_mk]; omega)]
  unfold C4Child.chInP C4Child.chIn
  rw [ac_lt _ _ _ (by show 2 < 6; omega)]
  try rfl

theorem KF_eu (v : ℕ) (h1 : 6 ≤ v) (h2 : v < 101) (h : v < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.KF UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT ⟨v, h⟩ =
      C4Dock.euIn P ents TWd Cap nT [] ⟨v - 6, by have : C4Dock.EU = 95 := rfl; omega⟩ := by
  have hEU : C4Dock.EU = 95 := rfl
  unfold C4Child.KF
  rw [ac_lt _ _ _ (by have := CT_eq wa; simp only [Fin.val_mk]; omega)]
  unfold C4Child.chInP C4Child.chIn
  rw [ac_ge _ _ _ (by show 6 ≤ v; omega)]
  rw [ac_lt _ _ _ (by simp only [Fin.val_mk]; show v - 6 < C4Dock.EU; omega)]
  try rfl

theorem KF_qq (h : 199 + C4Pipe.PD wa < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.KF UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT ⟨199 + C4Pipe.PD wa, h⟩ =
      List.replicate R0.P.Q true := by
  have hEU : C4Dock.EU = 95 := rfl
  have hCT := CT_eq wa
  unfold C4Child.KF
  rw [ac_lt _ _ _ (by simp; omega)]
  unfold C4Child.chInP C4Child.chIn
  rw [ac_ge _ _ _ (by show 6 ≤ 199 + C4Pipe.PD wa; omega)]
  rw [ac_ge _ _ _ (by simp only [Fin.val_mk]; show C4Dock.EU ≤ 199 + C4Pipe.PD wa - 6; omega)]
  simp only [C4Pipe.childIn, Fin.val_mk]
  rw [if_neg (by show ¬ (199 + C4Pipe.PD wa - 6 - C4Dock.EU = C4Pipe.PD wa); omega),
    if_pos (by show 199 + C4Pipe.PD wa - 6 - C4Dock.EU = C4Pipe.PD wa + 98; omega)]

theorem KF_uu (h : 200 + C4Pipe.PD wa < C4Child.CT UnionMachine.TailAsm.asmStage wa + 1) :
    C4Child.KF UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT ⟨200 + C4Pipe.PD wa, h⟩ =
      List.replicate (2 ^ R0.dRow * 2 ^ R0.dRow) true := by
  have hEU : C4Dock.EU = 95 := rfl
  have hCT := CT_eq wa
  unfold C4Child.KF
  rw [ac_lt _ _ _ (by simp; omega)]
  unfold C4Child.chInP C4Child.chIn
  rw [ac_ge _ _ _ (by show 6 ≤ 200 + C4Pipe.PD wa; omega)]
  rw [ac_ge _ _ _ (by simp only [Fin.val_mk]; show C4Dock.EU ≤ 200 + C4Pipe.PD wa - 6; omega)]
  simp only [C4Pipe.childIn, Fin.val_mk]
  rw [if_neg (by show ¬ (200 + C4Pipe.PD wa - 6 - C4Dock.EU = C4Pipe.PD wa); omega),
    if_neg (by show ¬ (200 + C4Pipe.PD wa - 6 - C4Dock.EU = C4Pipe.PD wa + 98); omega),
    if_pos (by show 200 + C4Pipe.PD wa - 6 - C4Dock.EU = C4Pipe.PD wa + 99; omega)]

end Fam

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
