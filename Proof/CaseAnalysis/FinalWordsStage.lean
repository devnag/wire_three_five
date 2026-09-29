import Proof.CaseAnalysis.FinalWordEngines2
import Proof.CaseAnalysis.FinalWorkerLoaderPorts

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WordsStage

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The private block, measured -/

/-- The number of private tapes the seventeen stages consume.  `abbrev`, not `def`: the
bank numerals `83 : Fin (219 + s)` need the `NeZero (219 + s)` instance. -/
abbrev s : ℕ := 59

/-! ## §2 The seventeen slot maps -/

def slots1 : Fin 19 → Fin (219 + s) :=
  ![218, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 83, 234,
      219, 235]
def slots2 : Fin 2 → Fin (219 + s) :=
  ![236, 237]
def slots3 : Fin 4 → Fin (219 + s) :=
  ![83, 236, 238, 239]
def slots4 : Fin 4 → Fin (219 + s) :=
  ![238, 90, 240, 241]
def slots5 : Fin 4 → Fin (219 + s) :=
  ![240, 238, 85, 242]
def slots6 : Fin 19 → Fin (219 + s) :=
  ![85, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 84, 257,
      86, 258]
def slots7 : Fin 4 → Fin (219 + s) :=
  ![84, 259, 98, 260]
def slots8 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 176, 261]
def slots9 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 187, 262]
def slots10 : Fin 4 → Fin (219 + s) :=
  ![86, 259, 182, 263]
def slots11 : Fin 4 → Fin (219 + s) :=
  ![236, 90, 264, 265]
def slots12 : Fin 4 → Fin (219 + s) :=
  ![264, 266, 186, 267]
def slots13 : Fin 2 → Fin (219 + s) :=
  ![268, 269]
def slots14 : Fin 5 → Fin (219 + s) :=
  ![85, 268, 213, 270, 271]
def slots15 : Fin 5 → Fin (219 + s) :=
  ![85, 268, 214, 272, 273]
def slots16 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 274, 276]
def slots17 : Fin 4 → Fin (219 + s) :=
  ![84, 259, 275, 277]


/-! ## §3 The public ports, and the ports still pending after each stage -/



/-! ## §4 The four bookkeeping lemmas -/

/-! ## §5 The machine and its fuel -/

noncomputable def stage1 := RecoveryFocus.machine slots1 CompetitorDimensions.machine
noncomputable def stage2 := RecoveryFocus.machine slots2 (HierarchyFixedWord.machine [true])
noncomputable def stage3 := RecoveryFocus.machine slots3 ClockUnarySum.machine
noncomputable def stage4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def stage5 := RecoveryFocus.machine slots5 ClockUnarySum.machine
noncomputable def stage6 := RecoveryFocus.machine slots6 CompetitorDimensions.machine
noncomputable def stage7 := RecoveryFocus.machine slots7 ClockUnarySum.machine
noncomputable def stage8 := RecoveryFocus.machine slots8 ClockUnarySum.machine
noncomputable def stage9 := RecoveryFocus.machine slots9 ClockUnarySum.machine
noncomputable def stage10 := RecoveryFocus.machine slots10 ClockUnarySum.machine
noncomputable def stage11 := RecoveryFocus.machine slots11 ClockUnaryProduct.machine
noncomputable def stage12 := RecoveryFocus.machine slots12 NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine
noncomputable def stage13 := RecoveryFocus.machine slots13 (HierarchyFixedWord.machine [true, true, false])
noncomputable def stage14 := RecoveryFocus.machine slots14 ClockNormalize.machine
noncomputable def stage15 := RecoveryFocus.machine slots15 ClockNormalize.machine
noncomputable def stage16 := RecoveryFocus.machine slots16 ClockUnarySum.machine
noncomputable def stage17 := RecoveryFocus.machine slots17 ClockUnarySum.machine

/-- The seventeen docked runs, composed left to right. -/
noncomputable def wordsMachine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine stage1
    stage2) stage3) stage4) stage5) stage6) stage7) stage8) stage9) stage10) stage11) stage12)
    stage13) stage14) stage15) stage16) stage17

/-! ## §6 The stage, port by port -/

/-! ## §7 The stage's output, as the loader's obligation -/

-- The two std3-FREE results (`keep`, `s_le_64`) are printed last on purpose: Lean prints
-- `does not depend on any axioms` for them, and an audit that scans the whole log with one
-- non-greedy `'(.+?)' depends on axioms: [...]` pattern would otherwise absorb the NEXT
-- declaration's name into that line.
end NearCubicWires.RepairOrdinary.CloseoutFinalC10WordsStage
