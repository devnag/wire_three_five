import Proof.Wire_3_5.UnionMachine.FrontPh1
import Proof.Wire_3_5.UnionMachine.FrontHierarchy
import Proof.Wire_3_5.UnionMachine.FrontCapStage
import Proof.Wire_3_5.Recovery.CaseTwoPadGSource

/-! # C6 front, the chain, phase 2: the hierarchy word, the capacity, the PCPP output (P3:3632-3653, 3669-3672)

On five regions after phase 1 (whose `1^q` and oracle descriptor are shared tapes `tq`, `td`):
1. a copy of `frame x`; 2. the hierarchy word `frame (hierarchyInput H ⟨N, x⟩)` (`FrontHierarchy.hier_ready`, on the
copy); 3. the capacity `1^{64(q+|x|)}` (`FrontCapStage.cap_ready`, sharing `x`, `1^q`); 4. a copy of `1^q` (base's
`ClockUnarySum.sum_ready q 0`); 5. The padded source (`FrontG3.g3_step`) on the hierarchy word, the descriptor,
the copy of `1^q` and the capacity: the PCPP output word `pcppOutput request (a.output request)` at head `0`.
**`ph2_step`**: the run and the PCPP word; `x`, `1^q` kept; every tape below the regions but the descriptor
untouched; the front's tapes past the regions blank.

Paper quantity: the PCPP output of the substituted circuit of the guessed oracle (P3:3672). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontPh2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.UnionMachine.FrontPh1 (xT xT_val)

section Ph
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm) (k k0 : ℕ)

/-- The phase's size. -/
noncomputable abbrev PH2 : ℕ := 4 + FrontHierarchy.HT k + FrontCapStage.CT + 4 + gtapes source a k



variable (h : k0 + PH2 source a k ≤ tf) (tq td : Fin (NW P tf))


noncomputable def shA (j : Fin 4) : Option (Fin (NW P tf)) := if j.val = 0 then some (xT P tf) else none


/-! ## Injectivity -/

theorem shA_some (j : Fin 4) (b : Fin (NW P tf)) (hj : shA P tf j = some b) : j.val = 0 ∧ b.val = 0 := by
  unfold shA at hj; split_ifs at hj with a0; cases hj; exact ⟨a0, rfl⟩

/-! ## The phase's machine -/

/-! ## Entries -/

theorem clauseData_zero (src : List Bool) (ar C : ℕ) :
    PCPPQueryIndexPadding.clauseData src ar 0 C [] 0 = src := by
  simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]

theorem heads_zero : PCPPQueryClauseReuse.heads 0 = 0 := by decide


end Ph

end NearCubicWires.WireExponent3_5.UnionMachine.FrontPh2
