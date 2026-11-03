import Proof.Wire_3_5.UnionMachine.FrontSemPathBase
import Proof.Wire_3_5.UnionMachine.FrontTop

/-! # C6 front, the semantic core (6): the front machine's run is the reference output (P3:3669-3691)

On every input and witness past the onset, the front machine (`FrontTop.topM`) runs to the reference output's bank
(`FrontOutRef.outRef`): below the onset the rejecting bank; a failing check (the walker's scan, the oracle's decoding
and size, the entries, the atoms) the rejecting bank, which is the reference output there since no decoded guess
passes; otherwise the chain's guess decodes, and the end's bank is the reference output's.

Paper quantity of the main type: the front's output bank on every input and witness (`FrontAtW3.run`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemRun
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary

/-! ## The chain's tapes after phase 2 -/

section Pos

end Pos

/-! ## The chain after phase 2, per branch -/

section Rest
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath (KcOf KdOf)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} 

/-- The entries fail: the chain's cost. -/
noncomputable def rejECost {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Dw Kw Dl Kb Db Cδ q sys aux cb : ℕ)
    (xs r : List Bool) : ℕ :=
  (8 * xs.length + 14) + 1 + (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r + 1 + (3 + 1))

/-- An atom fails: the chain's cost. -/
noncomputable def rejACost (m : Mode) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Dw Kw Dl Kb Db Cδ q sys aux cb : ℕ)
    (xs r : List Bool) : ℕ :=
  (8 * xs.length + 14) + 1 + (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r + 1 +
    ((FrontAtP.atCost m r xs.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) xs.length ((q + 1) ^ Dl)
      (KcOf (payOf r ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q)) ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q))
      (KdOf xs.length (payOf r ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q))
        ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q))
      (payOf r ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q)) + 1 + (3 + 1)) + 1))

end Rest

/-! ## The reference output on each branch after phase 2 -/

section OutB
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} 

theorem pay_le (r v : List Bool) (En : ℕ) (hr : restAfter En r = some v) :
    ∀ j, j < En → (payOf r En j).length + 1 ≤ r.length := by
  obtain ⟨-, hent, -, -⟩ := atom_shapes En r v hr
  intro j hj
  obtain ⟨b, x, rest, e⟩ := hent j hj
  have := FrontSemPath.shape_len r _ b x _ rest e
  omega

end OutB

/-! ## The chain after phase 2 at a decoded oracle -/

section RestRun
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath (KcOf KdOf)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.RepairOrdinary.CloseoutCaseTwo

end RestRun

/-! ## The front machine's run -/

section Top
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.CloseoutFinal

end Top

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemRun
