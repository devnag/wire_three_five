import Proof.Wire_3_5.Primitive.SeedFix.C4Child
import Proof.Wire_3_5.UnionMachine.TailAsm

/-! # SEEDFIX C4.L at a SYM call: the child family and the fixed seed (P3:3034-3038)

"For each candidate child prefix, print its signed equation expression, reduce modulo the chosen power of two at each
column, and sum the recovered integers. Choose a child with no larger sum. After `S` decisions the actual trace
objective is no larger than its random expectation" (P3:3034-3038). At a SYM call:
* `symR0`: the call's compiler request, on the pool of the call's geometry (`C4Geo.poolReq … symPool`), the table's
  row width `dRow` and columns `cols`;
* **`symFam`**: `C4Child.chFam` with C6's assembler (`TailAsm.asmStage`) and the SYM batch (`symSP`,
  `symNT`, `symExprs`); its machine-level loop is `C4Loop.ChildFam.loop_run (symFam …)`;
* **`sym_chVal`**: each child's recovered sum is `mult·2^{m−1}·sampSum` (C4Val's `child_sum`, exact recovery);
* **`sym_prefix`**: after the `8ℓ` decisions the prefix tape holds `frame (ofFn greedyBitsQ)`, the fixed seed of
  `samp:seed` (`src_pfx`, `greedyLoop_congr`, `greedy_scaled`).

Paper quantity of the main types: the recovered child sums `mult·2^{m−1}·sampSum` and the fixed seed `greedyBitsQ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Sym
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary

noncomputable section

section Sym
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n)) (translation : List ℕ)

/-- **The SYM call's compiler request** (each child replaces its expression): the pool of the call's geometry. -/
def symR0 (h Q psi m d pr k : ℕ) : CompilerMachine.Req.C3Req :=
  ⟨poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) (PrimAsm.Records.symPool Cs carriers)
    h Q psi, [], m, d, dRow (I.starParams n hs), cols (I.starParams n hs), pr, k, psi⟩

/-- **The SYM child's recovered sum is `mult·2^{m−1}·sampSum`** under exact recovery (`alg:recovery`). -/
theorem sym_chVal (h Q psi m d pr k : ℕ) (p' : List Bool) (hplen : p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell)
    (hrange : ∀ z, (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
      (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    (C4Child.chVal (symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
        (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) (PrimAsm.WriterIface.symExprs I hs Cs carriers)
        p' : ℤ) =
      (mult (I.starParams n hs) : ℤ) * 2 ^ (m - 1) *
        SeedFix.sampSum (C4Val.symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation) p' := by
  rw [← C4Val.child_sum I hs Cs carriers translation h Q psi m p' hplen hrange]
  congr 1
  unfold C4Child.chVal
  exact (C4Child.sum_fin_range _ _).symm

/-- **The SYM call's child family**: C4Child's, with C6's assembler and the SYM batch. -/
def symFam (wa : WilliamsAlgorithm) (alg : DecompositionAlgorithm) (E3 : Cost.Envelope)
    (h Q psi m d pr k : ℕ) (ents : List (List SeedFix.SExpr)) (TWd Cap K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) ents TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers)
        (carriers.length + 2 * a) K (PrimAsm.WriterIface.symExprs I hs Cs carriers) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
        (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) (PrimAsm.WriterIface.symExprs I hs Cs carriers)
        (p ++ [b])).Pre alg)
    (hQp : Q ≤ pr)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (dRow (I.starParams n hs)) (pr + 1)
        (symR0 I hs Cs carriers translation h Q psi m d pr k).P.width (cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (symR0 I hs Cs carriers translation h Q psi m d pr k)
          (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
          (PrimAsm.WriterIface.symExprs I hs Cs carriers) (p ++ [b]))) →
      C4Child.coreCost wa alg (symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
        TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K
        (PrimAsm.WriterIface.symExprs I hs Cs carriers) (p ++ [b]) r ≤ Kch) : C4Loop.ChildFam :=
  C4Child.chFam UnionMachine.TailAsm.asmStage wa alg (symR0 I hs Cs carriers translation h Q psi m d pr k)
    (C4Val.symSP I hs Cs carriers) ents TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K
    (PrimAsm.WriterIface.symExprs I hs Cs carriers) E3 Kch hok hpre hQp hcost

theorem mult_pos (P : StarParams) : 0 < mult P := by
  unfold mult; split_ifs <;> norm_num

/-- **The fixed seed at a SYM call**: after the `8ℓ` decisions of the SYM child family, the prefix tape holds
`frame (ofFn greedyBitsQ)`, the seed of `samp:seed` at the call's own states. -/
theorem sym_prefix (wa : WilliamsAlgorithm) (alg : DecompositionAlgorithm) (E3 : Cost.Envelope)
    (h Q psi m d pr k : ℕ) (ents : List (List SeedFix.SExpr)) (TWd Cap K Kch : ℕ) hok hpre (hQp : Q ≤ pr) hcost
    (R : ℕ)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    (symFam I hs Cs carriers translation wa alg E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).src R
        (symFam I hs Cs carriers translation wa alg E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).bound
        ((symFam I hs Cs carriers translation wa alg E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).sl0
          (symFam I hs Cs carriers translation wa alg E3 h Q psi m d pr k ents TWd Cap K Kch hok hpre hQp hcost).PFX) =
      frame (List.ofFn (SeedFix.greedyBitsQ (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation))) := by
  rw [C4Loop.ChildFam.src_pfx]
  congr 1
  have hK : 0 < mult (I.starParams n hs) * 2 ^ (m - 1) := Nat.mul_pos (mult_pos _) (Nat.two_pow_pos _)
  rw [← C4Val.greedy_scaled (C4Val.symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation) _ hK]
  apply C4Loop.greedyLoop_congr
  intro p' hp'
  show ((C4Child.chVal (symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
    (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) (PrimAsm.WriterIface.symExprs I hs Cs carriers)
    p' : ℕ) : ℤ) = _
  rw [sym_chVal I hs Cs carriers translation h Q psi m d pr k p' hp' (hrange p' hp')]
  push_cast
  ring

end Sym

end

end NearCubicWires.WireExponent3_5.PrimT.C4Sym
