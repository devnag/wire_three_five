import Lean
import Proof.Wire_3_5.Foundations.Skeleton
import Proof.Wire_3_5.Foundations.Contracts
import Proof.Wire_3_5.Ledger.LedgerBudget
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.UnionMachine.UnionEventual
import Statement_Wire_3_5
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Foundations.SkeletonBase
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule


noncomputable section


/-! # The freeze-gate split of `Parts`

`literals_rowB_of_parts` leaves `Literals → Parts`. This module splits `Parts` into three independent leaves along the
paper's order of choice (P3:3114-3115, 3632-3655, 3797-3811):
* the **gate constants** `Gate`, fixed by root before any leaf: the envelope `E` ("every polynomial exponent, fixed
  before `r`"), the width padding `A_pad` (P3:3637-3640), the row-B ledger constants (`RowBParams`: `tr:B`, `C_D`,
  `c_r`, `s(q)`), and the caller's inputs of `lem:primitive` (P3:3068-3084: `D`, the envelopes, the name count, the
  endpoint error exponent);
* the **union setup** `S` (the hierarchy language's PCP/PCPP data, P3:3232-3260, 3669-3697), pinned at the gate, because
  the union's completeness and the recovery are both stated at it;
* the **primitive leaf** (B7 + C1–C5): the primitive's coefficient `coef` (its own choice, `G2`) and `lem:primitive` at
  the gate inputs for every clock and source work (they enter only `B.q`, never `callBudget`);
* the **union leaf** (B8 + C6 + C7): the clock `kclk` and the source work `A·(N+1)^a` (its own choices, `G3`), and the
  union construction with `tr:completeness` (`CompleteFor`) for every primitive coefficient;
* the **recovery leaf** (D1 + D2): `Recovery U P` for every union leaf `U` at the pinned setup and every primitive `P`.

`parts_of_leaves` assembles `Parts` from the three leaves; nothing else is chosen. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Transfer NearCubicWires.ExecutableInterfaces

/-- The gate constants, fixed by root at the freeze gate before any leaf. -/
structure Gate where
  /-- every polynomial exponent of the machines (P3:3114-3115, 3803-3804) -/
  E : Envelope
  /-- the width padding `A_pad` of `q(N)` (P3:3637-3640), with the table exponent `A_pad + 1 ≤ σ` (P3:3644) -/
  Apad : ℕ
  hσ : Apad + 1 ≤ E.sigma
  /-- the row-B ledger constants (`tr:B`, `C_D`, `c_r`, `s(q)`; P3:3425-3430, 3094-3097, 3820-3824) -/
  row : RowBParams
  /-- the caller's inputs of `lem:primitive` (P3:3068-3084) -/
  D : ℕ
  D_pos : 0 < D
  kDeg : ℕ
  descDeg : ℕ
  nameCount : ℕ
  carrierDeg : ℕ
  filterErrDeg : ℕ
  /-- G7 (SYM): the endpoint error beats the accuracy exponent (P3:3074-3077, 3147-3153; `sym_call_error`) -/
  hG7 : D + 2 ≤ filterErrDeg
  /-- the exact decomposition algorithm of the THR rows: the `cw19` literal's `DecompositionSource`
  (`Nonempty DecompositionAlgorithm`, via `EightSources.decomposition`), NOT the legacy `ExecutableExactDecompositionAlgorithm`,
  whose every producer needs a `PublishedContracts` binder (a ninth assumption). Pinned here because G7'
  (THR: `filterErrDeg ≥ D + deg|𝒢| + c`) reads its child-count degree. -/
  alg : RepairRepresentation.DecompositionAlgorithm

namespace Gate
variable (G : Gate)

/-- The time ledger (`rowBNativeBudget`) at the gate constants, the machines' coefficient `coef` (the
cost contracts `costsOf`), and the union's clock and source work. -/
noncomputable def budget (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : TimeBudget kclk G.E :=
  rowBNativeBudget kclk G.Apad G.E G.hσ (Machine.costsOf G.E coef) G.row A a ha

/-- The caller's inputs of `lem:primitive` at the gate constants. -/
def inputs (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : PrimitiveInputs (G.budget kclk coef A a ha) :=
  ⟨G.D, G.D_pos, G.kDeg, G.descDeg, G.nameCount, G.carrierDeg, G.filterErrDeg⟩

/-- A union setup for every hierarchy language of the clock `T(N) = N^{kclk+2}` (P3:3633), at every ledger. -/
abbrev Setup :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language), InNTIME (fun n => n ^ (kclk + 2)) L →
    UnionSetup (G.inputs kclk coef A a ha)

end Gate

/-- The union construction with `tr:completeness` at a pinned setup (made EVENTUAL by #39): past an
onset chosen after the primitive and the language, every accepting guess of the setup makes the built machine accept.
The machine "rejects outright" at the finitely many lengths below it (P3:3675-3680; "Finite exceptional lengths may be
fixed", P3:3771), which is what lets `tr:time` hold with the ledger's onset fixed before the language.
`tr:soundness` and `tr:time` are the `UnionConstruction` fields. -/
structure UnionLeafAt {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (S : ∀ L : Language, InNTIME (fun n => n ^ (kclk + 2)) L → UnionSetup I) extends UnionConstruction I where
  complete : ∀ (P : FusedPrimitive I) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L),
    CompleteForEventually (S L hL) P (build P L)

variable (G : Gate) (S : G.Setup)

/-- **Leaf P** (B7 + C1–C5): the primitive's coefficient, and `lem:primitive` at the gate inputs for every clock and
source work. -/
def PrimitiveLeaf :=
  Σ coef : ℕ, ∀ (kclk A a : ℕ) (ha : a ≤ kclk + 1), FusedPrimitive (G.inputs kclk coef A a ha)

end NearCubicWires.WireExponent3_5.Split

end
