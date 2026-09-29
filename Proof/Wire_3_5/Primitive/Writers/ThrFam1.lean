import Proof.Wire_3_5.Primitive.SeedFix.C4Sym

/-! # c4 THR block, item 2: the THR child family and the fixed seed (P3:3034-3038)

"For each candidate child prefix, print its signed equation expression, reduce modulo the chosen power of two at each
column, and sum the recovered integers. Choose a child with no larger sum. After `S` decisions the actual trace
objective is no larger than its random expectation" (P3:3034-3038). At a THR call (the SYM family, `C4Val`/`C4Sym`,
with PA's THR batch):
* `thrSP` (samp:seed at the THR count), `thrChild` (C4's `sampTerms` over PA's `thrExprs`, `thrNT` states);
* **`thr_value`**, **`thr_sum`**: each child's recovered sum is `mult·2^{m−1}·sampSum` over the THR states;
* `thrR0` (the call's compiler request on the THR pool), **`thrFam`** (`C4Child.chFam` at C6's assembler);
* **`thr_prefix`**: after the `8ℓ` decisions the prefix tape holds `frame (ofFn greedyBitsQ)`, the THR fixed seed.

Paper quantity of the main types: the recovered child sums over the THR states and the THR fixed seed `greedyBitsQ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Geo NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary

noncomputable section

section Thr
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- The call's sampler parameters: `samp:seed` at the THR sample count. -/
abbrev thrSP : SeedParams := seedParamsFor (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs)

/-- **The THR child expression of a prefix** `p'`: C4's printed conditional objective over PA's THR batch. -/
def thrChild (p' : List Bool) : SeedFix.SExpr :=
  SeedFix.sampTerms (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
    (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) p'.length (SeedFix.listNum p')

/-- **The THR child's value at a table position is the printed column value of its center.** -/
theorem thr_value (h Q psi : ℕ) (p' : List Bool) (row col : ℕ) :
    IntExpression.eval (thrChild alg I hs Cs carriers translation p')
        (CompilerMachine.Req.atomVal
          (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi)
          (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) row)
          (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) col)) =
      SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation (C4Val.symCenter I hs translation row col))
        p'.length (SeedFix.listNum p') := by
  rw [← PrimAsm.Enum.thrSampElim_enum alg I hs Cs]
  apply SeedFix.sampTerms_eval
  intro t x
  exact PrimAsm.WriterIface.thr_hD alg I hs Cs carriers translation (C4Val.symCenter I hs translation row col) _
    (fun x gi hgi k => atomVal_center _ _ _ h Q psi row col x gi hgi k) t x

/-- **The THR child's recovered sum is `mult·2^{m−1}·sampSum`** when every center's scaled value is recovered exactly
(`0 ≤ 2^{m−1}·V_p(z) < 2^{Q'}`, `alg:recovery`). -/
theorem thr_sum (h Q psi m : ℕ) (p' : List Bool) (hplen : p'.length ≤ 8 * (thrSP alg I hs Cs).ell)
    (hrange : ∀ z, (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
      (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    ((∑ i : Fin (2 ^ dRow (I.starParams n hs)), ∑ j : Fin (2 ^ dRow (I.starParams n hs)),
        C4Pipe.lres (2 ^ (m - 1) * IntExpression.eval (thrChild alg I hs Cs carriers translation p')
          (CompilerMachine.Req.atomVal
            (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
              (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi)
            (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) i)
            (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) j))) Q : ℕ) : ℤ) =
      (mult (I.starParams n hs) : ℤ) * 2 ^ (m - 1) *
        SeedFix.sampSum (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation) p' := by
  let g : ℕ → ℕ → ℤ := fun row col => ((C4Pipe.lres (2 ^ (m - 1) *
      IntExpression.eval (thrChild alg I hs Cs carriers translation p')
      (CompilerMachine.Req.atomVal (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi)
        (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) row)
        (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) col))) Q : ℕ) : ℤ)
  let F : BitInput (I.starParams n hs).n → ℤ := fun c =>
    if hc : (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c then
      2 ^ (m - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation ⟨c, hc⟩) p'.length (SeedFix.listNum p') else 0
  have hterm : ∀ row col : ℕ, g row col = F (centerAt (I.starParams n hs)
      ((I.starParams n hs).translationOfCodes translation) row col) := by
    intro row col
    simp only [g, F, dif_pos (centerAt_isCenter (I.starParams n hs) _ row col)]
    rw [C4Pipe.lres_cast, thr_value alg I hs Cs carriers translation h Q psi p' row col]
    have h0 := SeedFix.sampElim_nonneg (thrSP alg I hs Cs)
      (SeedFix.thrStateBits alg I hs Cs carriers translation (C4Val.symCenter I hs translation row col))
      p'.length (SeedFix.listNum p') hplen
    have h1 := hrange (C4Val.symCenter I hs translation row col)
    exact Int.emod_eq_of_lt (by positivity) h1
  push_cast
  show (∑ i : Fin (2 ^ dRow (I.starParams n hs)), ∑ j : Fin (2 ^ dRow (I.starParams n hs)), g i j) = _
  have hs1 : (∑ i : Fin (2 ^ dRow (I.starParams n hs)), ∑ j : Fin (2 ^ dRow (I.starParams n hs)), g i j) =
      ∑ i ∈ Finset.range (2 ^ dRow (I.starParams n hs)), ∑ j ∈ Finset.range (2 ^ dRow (I.starParams n hs)), g i j := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (2 ^ dRow (I.starParams n hs)), g i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (g i) _
  rw [hs1]
  simp only [hterm]
  rw [sum_table (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) F, nsmul_eq_mul]
  unfold SeedFix.sampSum
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [F, dif_pos z.2]

/-- **The THR call's compiler request** (each child replaces its expression): the THR pool of the call's geometry. -/
def thrR0 (h Q psi m d pr k : ℕ) : CompilerMachine.Req.C3Req :=
  ⟨poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
    (PrimAsm.Records.thrPool (I.starParams n hs) Cs carriers) h Q psi, [], m, d, dRow (I.starParams n hs),
    cols (I.starParams n hs), pr, k, psi⟩

/-- **The THR child's recovered sum is `mult·2^{m−1}·sampSum`** under exact recovery (`alg:recovery`). -/
theorem thr_chVal (h Q psi m d pr k : ℕ) (p' : List Bool) (hplen : p'.length ≤ 8 * (thrSP alg I hs Cs).ell)
    (hrange : ∀ z, (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
      (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    (C4Child.chVal (thrR0 I hs Cs carriers translation h Q psi m d pr k) (thrSP alg I hs Cs)
        (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
        (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) p' : ℤ) =
      (mult (I.starParams n hs) : ℤ) * 2 ^ (m - 1) *
        SeedFix.sampSum (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation) p' := by
  rw [← thr_sum alg I hs Cs carriers translation h Q psi m p' hplen hrange]
  congr 1
  unfold C4Child.chVal
  exact (C4Child.sum_fin_range _ _).symm

/-- **The THR call's child family**: C4Child's, with C6's assembler and the THR batch. -/
def thrFam (wa : WilliamsAlgorithm) (E3 : Cost.Envelope)
    (h Q psi m d pr k : ℕ) (ents : List (List SeedFix.SExpr)) (TWd Cap K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      C4Dock.EnumOk (thrSP alg I hs Cs) ents TWd Cap (PrimAsm.Enum.thrNT alg I hs Cs)
        (carriers.length + 1) K (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      (C4Child.chR (thrR0 I hs Cs carriers translation h Q psi m d pr k) (thrSP alg I hs Cs)
        (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
        (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) (p ++ [b])).Pre alg)
    (hQp : Q ≤ pr)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (thrSP alg I hs Cs).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (dRow (I.starParams n hs)) (pr + 1)
        (thrR0 I hs Cs carriers translation h Q psi m d pr k).P.width (cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (thrR0 I hs Cs carriers translation h Q psi m d pr k)
          (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
          (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) (p ++ [b]))) →
      C4Child.coreCost wa alg (thrR0 I hs Cs carriers translation h Q psi m d pr k) (thrSP alg I hs Cs)
        TWd Cap (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K
        (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) (p ++ [b]) r ≤ Kch) : C4Loop.ChildFam :=
  C4Child.chFam UnionMachine.TailAsm.asmStage wa alg (thrR0 I hs Cs carriers translation h Q psi m d pr k)
    (thrSP alg I hs Cs) ents TWd Cap (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K
    (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) E3 Kch hok hpre hQp hcost

/-- **The fixed seed at a THR call**: after the `8ℓ` decisions of the THR child family, the prefix tape holds
`frame (ofFn greedyBitsQ)`, the seed of `samp:seed` at the call's own THR states. -/
theorem thr_prefix (wa : WilliamsAlgorithm) (E3 : Cost.Envelope)
    (h Q psi m d pr k : ℕ) (ents : List (List SeedFix.SExpr)) (TWd Cap K Kch : ℕ) hok hpre (hQp : Q ≤ pr) hcost
    (R : ℕ)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (thrSP alg I hs Cs).ell → ∀ z,
      (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    (thrFam alg I hs Cs carriers translation wa E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).src R
        (thrFam alg I hs Cs carriers translation wa E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).bound
        ((thrFam alg I hs Cs carriers translation wa E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).sl0
          (thrFam alg I hs Cs carriers translation wa E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).PFX) =
      frame (List.ofFn (SeedFix.greedyBitsQ (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation))) := by
  rw [C4Loop.ChildFam.src_pfx]
  congr 1
  have hK : 0 < mult (I.starParams n hs) * 2 ^ (m - 1) := Nat.mul_pos (C4Sym.mult_pos _) (Nat.two_pow_pos _)
  rw [← C4Val.greedy_scaled (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation) _ hK]
  apply C4Loop.greedyLoop_congr
  intro p' hp'
  show ((C4Child.chVal (thrR0 I hs Cs carriers translation h Q psi m d pr k) (thrSP alg I hs Cs)
    (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
    (PrimAsm.WriterIface.thrExprs alg I hs Cs carriers translation) p' : ℕ) : ℤ) = _
  rw [thr_chVal alg I hs Cs carriers translation h Q psi m d pr k p' hp' (hrange p' hp')]
  push_cast
  ring

end Thr

end

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
