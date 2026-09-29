import Proof.Wire_3_5.Primitive.SeedFix.C4Pipe
import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV

/-! # SEEDFIX C4.L, the value link: the printed child sums are the greedy's scaled objectives (P3:3035-3039)

"For each candidate child prefix [...] sum the recovered integers. Choose a child with no larger sum" (P3:3035-3037).
At a SYM call, the child expression of a prefix `p'` is C4's `sampTerms` over PA's batch (`symExprs`), and the C3
request's pool is the call's geometry (`C4Geo.poolReq`, the star pool `symPool`). Then:
* **`child_value`**: at the table position `(row, col)`, the expression's value at the pool atoms is the printed
  column value `sampElim` of the center `centerAt row col` (`sampTerms_eval` + PA's `sym_hD` + V2 `atomVal_center` +
  PA's `symSampElim_enum`);
* **`child_sum`**: when `0 ≤ 2^{m−1}·sampElim < 2^{Q'}` (the exact recovery of `alg:recovery`, P3:1966-1972), the
  child's recovered sum (`child_step`'s port) is `mult·2^{m−1}·sampSum` (V3 `sum_table`);
* **`greedy_scaled`**: the greedy loop over any positive multiple of the child sums prints `greedyBitsQ`, the seed
  of `greedySampler` (`sampLoop_eq` scaled).

Paper quantities of the main types: `sampSum` (the recovered child sums) and `greedyBitsQ` (the fixed seed). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Val
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars

section Sym
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n)) (translation : List ℕ)

/-- The call's sampler parameters: `samp:seed` at the SYM sample count. -/
abbrev symSP : SeedParams := seedParamsFor (SeedFix.callKh (I.starParams n hs)) (SeedFix.symCount I hs Cs carriers)

/-- **The child expression of a prefix** `p'`: C4's printed conditional objective over PA's SYM batch. -/
def symChild (p' : List Bool) : SeedFix.SExpr :=
  SeedFix.sampTerms (symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
    (PrimAsm.WriterIface.symExprs I hs Cs carriers) p'.length (SeedFix.listNum p')

/-- The center of a table position, with its proof. -/
def symCenter (row col : ℕ) :
    {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} :=
  ⟨centerAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) row col,
    centerAt_isCenter _ _ row col⟩

/-- **The child's value at a table position is the printed column value of its center.** -/
theorem child_value (h Q psi : ℕ) (p' : List Bool) (row col : ℕ) :
    IntExpression.eval (symChild I hs Cs carriers p')
        (CompilerMachine.Req.atomVal
          (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            (PrimAsm.Records.symPool Cs carriers) h Q psi)
          (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) row)
          (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) col)) =
      SeedFix.sampElim (symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation (symCenter I hs translation row col))
        p'.length (SeedFix.listNum p') := by
  rw [← PrimAsm.Enum.symSampElim_enum I hs Cs carriers]
  apply SeedFix.sampTerms_eval
  intro t x
  exact PrimAsm.WriterIface.sym_hD I hs Cs carriers translation (symCenter I hs translation row col) _
    (fun x gi hgi k => atomVal_center _ _ _ h Q psi row col x gi hgi k) t x

/-- **The child's recovered sum is `mult·2^{m−1}·sampSum`** when every center's scaled value is recovered exactly
(`0 ≤ 2^{m−1}·V_p(z) < 2^{Q'}`, `alg:recovery`). -/
theorem child_sum (h Q psi m : ℕ) (p' : List Bool) (hplen : p'.length ≤ 8 * (symSP I hs Cs carriers).ell)
    (hrange : ∀ z, (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (symSP I hs Cs carriers)
      (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    ((∑ i : Fin (2 ^ dRow (I.starParams n hs)), ∑ j : Fin (2 ^ dRow (I.starParams n hs)),
        C4Pipe.lres (2 ^ (m - 1) * IntExpression.eval (symChild I hs Cs carriers p')
          (CompilerMachine.Req.atomVal
            (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
              (PrimAsm.Records.symPool Cs carriers) h Q psi)
            (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) i)
            (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) j))) Q : ℕ) : ℤ) =
      (mult (I.starParams n hs) : ℤ) * 2 ^ (m - 1) *
        SeedFix.sampSum (symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation) p' := by
  let g : ℕ → ℕ → ℤ := fun row col => ((C4Pipe.lres (2 ^ (m - 1) * IntExpression.eval (symChild I hs Cs carriers p')
      (CompilerMachine.Req.atomVal (poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        (PrimAsm.Records.symPool Cs carriers) h Q psi)
        (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) row)
        (RepairOrdinary.MatrixScorePhi.value (cols (I.starParams n hs)) col))) Q : ℕ) : ℤ)
  let F : BitInput (I.starParams n hs).n → ℤ := fun c =>
    if hc : (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c then
      2 ^ (m - 1) * SeedFix.sampElim (symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation ⟨c, hc⟩) p'.length (SeedFix.listNum p') else 0
  have hterm : ∀ row col : ℕ, g row col = F (centerAt (I.starParams n hs)
      ((I.starParams n hs).translationOfCodes translation) row col) := by
    intro row col
    simp only [g, F, dif_pos (centerAt_isCenter (I.starParams n hs) _ row col)]
    rw [C4Pipe.lres_cast, child_value I hs Cs carriers translation h Q psi p' row col]
    have h0 := SeedFix.sampElim_nonneg (symSP I hs Cs carriers)
      (SeedFix.symStateBits I hs Cs carriers translation (symCenter I hs translation row col))
      p'.length (SeedFix.listNum p') hplen
    have h1 := hrange (symCenter I hs translation row col)
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

end Sym

/-! ## The greedy over scaled sums -/

section Greedy
variable {Z T : Type} [Fintype Z] [Fintype T]

/-- **The greedy loop over any positive multiple of the child sums prints the greedy seed** (P3:3035-3039,
`sampLoop_eq` scaled): the machine compares `K·sampSum` (`K = mult·2^{m−1}`), with the same decisions. -/
theorem greedy_scaled (P : SeedParams) (D : Z → T → Cell P.N → Bool) (K : ℕ) (hK : 0 < K) :
    SeedFix.greedyLoop (8 * P.ell) (fun p => (K : ℤ) * SeedFix.sampSum P D p) =
      List.ofFn (SeedFix.greedyBitsQ P D) := by
  obtain ⟨hpos, heq⟩ := SeedFix.sampSum_scaled P D
  apply SeedFix.greedyLoop_eq_greedyQ (8 * P.ell) _ _ (fun i => (K : ℚ) * 2 ^ (8 * P.ell - i - 1))
  refine ⟨fun i => by positivity, fun p b hp => ?_⟩
  have e := heq p b hp
  push_cast
  rw [e]
  ring

end Greedy

section SymTail

end SymTail

end NearCubicWires.WireExponent3_5.PrimT.C4Val
