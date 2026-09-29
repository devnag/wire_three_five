import Proof.Wire_3_5.Primitive.SeedFix.C4SymWF

/-! # C4.K SYM, part 1: the SYM stage at every call, from its side conditions

"For each candidate child prefix [...] Choose a child with no larger sum. After `S` decisions the actual trace objective
is no larger than its random expectation" (P3:3034-3038); the fixed seed's samples are the seeds a SYM call fixes
before its final pass (`seedWord`, P3:3165-3175). The SYM stage's machine does not depend on the call: its loop is the
loop of the proof-free family `famU wa` (`C4Child.chFam`'s machine fields depend only on C6's assembler and the
printer's algorithm; `sym_uniform`, by `rfl`), so one `Stage3` (**`symStageU`**) serves every call. At a call, the child
family is `C4Sym.symFam` at the free numbers `fr` (`TWd = fr 0`, `Cap = fr 1`, `Q' = fr 2`, `h = fr 3`, `m = fr 4`,
`pr = fr 5`, `ρ = fr 6`), the seed is `greedyBitsQ` (`C4Sym.sym_prefix`), and the stage's output is the call's
`seedWord` (**`seedWord_sym`**, definitional).

* `famU`, `sym_uniform`, `seedWord_sym`, `symStageU`, **`sym_call_run`** (the stage's run at a call within the seed
  budget, from the remaining side conditions: the data stage, the numbers program's run, the C3 writer's run, the
  numbers' links, the enumeration's and the compiler's conditions, the recovery range, the pad, the budget).

Paper quantity of the main type: the call's `seedWord` (the fixed SYM seed's samples). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **The loop's family without call data** (no decisions): the machine fields of every child family of C6's
assembler. -/
noncomputable def famU (wa : RepairRepresentation.WilliamsAlgorithm) : C4Loop.ChildFam where
  t := C4Child.CT UnionMachine.TailAsm.asmStage wa + 1
  s := _
  M := C4Child.chMs UnionMachine.TailAsm.asmStage wa
  cost := 0
  PFX := C4Child.pfxT _ wa
  SUM := C4Child.sumP _ wa
  keep := C4Child.keepF _ wa
  hPFX := C4Child.keepF_pfx _ wa
  hSUM := C4Child.keepF_sum _ wa
  K := fun _ => []
  W := 0
  bound := 0
  val := fun _ => 0
  run := fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- **The SYM call's seeds are the samples of the greedy seed** (`seedWord`, definitional). -/
theorem seedWord_sym {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) :
    seedWord I alg (symReq n a ha Cs carriers translation) =
      FinalPass.Sample.sampleWord (C4Val.symSP I hs Cs carriers).kh
        (C4Iface.seedPairs (C4Val.symSP I hs Cs carriers)
          (SeedFix.greedyBitsQ (C4Val.symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation))) := by
  show (if hs' : I.StarAt n then _ else []) = _
  rw [dif_pos hs]
  rfl

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
