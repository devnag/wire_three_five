import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalPrologueUniform

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutSchedule
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The sentinel strip -/

/-! ## §2 The unary power `(q+1)^D` -/

/-! ## §3 The engine's flat layout

`tw` tapes of the width reader, then a private band of `46 + 2r + 2D` tapes:

| band offset | use |
|---|---|
| `0` | the driver word -- `hengine`'s `driverSlot` |
| `1` | the envelope exponent -- `hengine`'s `expSlot` |
| `2`, `3` | the adder's and the strip's private scratch |
| `4`, `5` | the fixed-word writer |
| `6 + i` | the dimension polynomial's window, `i = 1 .. 13+2r` |
| `20 + 2r + i` | the clause-width program's window, `i = 1 .. 25+2D` |

The two programs read the reader's own output tape `qW` in place, so no unary
copy is spent. -/

/-- The engine's private band. -/
def band (r D : ℕ) : ℕ := 46 + 2 * r + 2 * D

/-- The engine's tape count: the reader's tapes plus the band. -/
def tapesOf (tw r D : ℕ) : ℕ := tw + band r D


/-! ## §4 Where each stage's slot map lands, as a `val` disjunction -/

/-! ## §5 A width reader, docked -/

/-! ## §6 The engine, and its fuel -/

/-! ## §7 Slot values, and the slot identifications the chain needs -/

/-! ## §8 The engine runs: `hengine` from one width reader -/

/-! ## §9 The engine docked onto the C10 bank, and `Seed` -/


noncomputable abbrev rp (sources : RepairSource.EightSources) : ℕ :=
  (fixedProjection sources).degrees.proofLog

noncomputable abbrev rq (sources : RepairSource.EightSources) : ℕ :=
  (fixedProjection sources).degrees.queries

/-! ## §12 `Prologue` at the pinned schedule, with NO open hypothesis -/


open NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)


end NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine
