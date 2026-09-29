import Proof.Wire_3_5.Primitive.SeedFix.C4HfI

/-! # The HASH child family, part 10: one HASH child as a machine

`filt:soft`, P3:2331-2335 ("Greedily choose a child with no larger value, using at most two printer calls per hash
bit"), P3:3034-3037: the HASH child of bit `b` at prefix `p` is C4Child's pipeline with the Hb unit in place of the
enumeration unit: the Hb unit prints `exprWord V_{p ++ [b]}` on the assembler's expression port, the assembler frames
the compiler's input, the printer child compiles, prints and sums (**`core_stepH`**: the sum port holds
`frame (binary W (chValH …))`, the kept tapes unchanged).

Paper quantity of the main type: the recovered child sum `chValH` of the printed hash objective. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation

noncomputable section

section Layout
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm)

/-- The assembler's tapes. -/
def hAsmSl (i : Fin A.t) : Fin (CTH A wa) := Fin.castAdd _ i

/-- The Hb unit's tapes: its output tape `95` is the assembler's expression port. -/
def hUnSl (u : Fin HU) : Fin (CTH A wa) :=
  if u.val = 95 then Fin.castAdd _ A.pE else Fin.natAdd A.t (Fin.castAdd (C4Pipe.CN wa) u)

/-- The printer child's tapes: its request tape is the assembler's output port. -/
def hCmSl (k : Fin (C4Pipe.CN wa)) : Fin (CTH A wa) :=
  if k = C4Child.pdT wa then Fin.castAdd _ A.pO else Fin.natAdd A.t (Fin.natAdd HU k)

theorem hAsmSl_val (i : Fin A.t) : (hAsmSl A wa i).val = i.val := rfl

theorem hUnSl_val (u : Fin HU) : (hUnSl A wa u).val = if u.val = 95 then A.pE.val else A.t + u.val := by
  unfold hUnSl; split_ifs <;> rfl

theorem hCmSl_val (k : Fin (C4Pipe.CN wa)) :
    (hCmSl A wa k).val = if k = C4Child.pdT wa then A.pO.val else A.t + (HU + k.val) := by
  unfold hCmSl; split_ifs <;> rfl

theorem hAsmSl_inj : Function.Injective (hAsmSl A wa) := fun i j h => Fin.ext (by
  have hv := congrArg Fin.val h; rwa [hAsmSl_val, hAsmSl_val] at hv)

theorem hUnSl_inj : Function.Injective (hUnSl A wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [hUnSl_val, hUnSl_val] at hv
  have := A.pE.isLt
  apply Fin.ext
  split_ifs at hv with hi hj hj <;> omega

theorem hCmSl_inj : Function.Injective (hCmSl A wa) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [hCmSl_val, hCmSl_val] at hv
  have := A.pO.isLt
  split_ifs at hv with hi hj hj
  · rw [hi, hj]
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by omega)

theorem un_ne_asm (u : Fin HU) (i : Fin A.t) (hi : i ≠ A.pE) : hUnSl A wa u ≠ hAsmSl A wa i := by
  intro e
  have hv := congrArg Fin.val e
  rw [hUnSl_val, hAsmSl_val] at hv
  have := i.isLt
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · omega

theorem cm_ne_asmH (k : Fin (C4Pipe.CN wa)) (i : Fin A.t) (hi : i ≠ A.pO) : hCmSl A wa k ≠ hAsmSl A wa i := by
  intro e
  have hv := congrArg Fin.val e
  rw [hCmSl_val, hAsmSl_val] at hv
  have := i.isLt
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · omega

theorem cm_ne_un (k : Fin (C4Pipe.CN wa)) (u : Fin HU) : hCmSl A wa k ≠ hUnSl A wa u := by
  intro e
  have hv := congrArg Fin.val e
  rw [hCmSl_val, hUnSl_val] at hv
  have := A.pO.isLt
  have := A.pE.isLt
  have := u.isLt
  have hOE : A.pO.val ≠ A.pE.val := fun h => A.hEO (Fin.ext h.symm)
  split_ifs at hv <;> omega

/-- The child's kept tapes: the assembler's field words, the unit's framed words and prefix, `1^Q`, the mask. -/
def hKeepC : Fin (CTH A wa) → Bool :=
  Fin.addCases (fun i => decide (i = A.pA ∨ i = A.pB))
    (Fin.addCases (fun u : Fin HU => decide (u.val ≤ 94))
      (fun k => decide (k = C4Pipe.childQQ wa ∨ k = C4Pipe.childUU wa)))

/-- **The child's entry bank** at the prefix `p`. -/
def hChIn (PRE POST : List Bool) (KW : Fin 94 → List Bool) (qq uu p : List Bool) : Fin (CTH A wa) → List Bool :=
  Fin.addCases (C4Child.asmK A PRE POST) (Fin.addCases (uIn KW p) (C4Pipe.childIn wa [] qq uu))

/-- **The HASH child's three stages.** -/
noncomputable def coreMH (b : Bool) :=
  Composition.machine (RecoveryFocus.machine (hUnSl A wa) (unitM b))
    (Composition.machine (RecoveryFocus.machine (hAsmSl A wa) A.M) (RecoveryFocus.machine (hCmSl A wa) (C4Pipe.childM wa)))

/-- The child's sum port. -/
def hSumT : Fin (CTH A wa) := hCmSl A wa (C4Pipe.childSum wa)

end Layout

/-- **The recovered HASH child sum**: over the table positions, the least residues of `2^{m−1}·V_{p'}(z)`. -/
def chValH (R0 : CompilerMachine.Req.C3Req) (D : HashData) (p' : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (2 ^ R0.dRow), ∑ j ∈ Finset.range (2 ^ R0.dRow),
    C4Pipe.lres (2 ^ (R0.m - 1) * Shared.IntExpression.eval (hV D p')
      (CompilerMachine.Req.atomVal R0.P (MatrixScorePhi.value R0.cols i) (MatrixScorePhi.value R0.cols j))) R0.P.Q

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
