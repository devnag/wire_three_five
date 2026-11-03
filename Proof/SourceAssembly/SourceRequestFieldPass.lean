import Proof.SourceAssembly.SLoadMaskReady
import Proof.Hierarchy.CompetitorRawScalarPaddedAppend
import Proof.Assembly.AppendOutputLength
import Proof.PCP.ProjectionNormalizationForwardRules
import Proof.SourceAssembly.SourceReuse

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.FieldPass
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization
noncomputable section

/-! ## 1. The unframe-append primitive -/

/-! ## 2. The chain of `n` appends on a local universe `Fin (n+2)` -/

variable (n : Nat)

def srcT (i : Fin n) : Fin (n + 2) := ⟨i.val, by omega⟩
def outT : Fin (n + 2) := ⟨n, by omega⟩
def logT : Fin (n + 2) := ⟨n + 1, by omega⟩

def stageSlots (i : Fin n) : Fin 3 → Fin (n + 2) := ![srcT n i, outT n, logT n]

def stage (i : Fin n) : Machine (n + 2) 4 :=
  RecoveryFocus.machine (stageSlots n i) CompetitorRawScalarEmit.machine

/-- The first `k` stages, left-nested after a halting start. -/
def chain : (k : Nat) → k ≤ n → Σ s, Machine (n + 2) s
  | 0, _ => ⟨1, PCJ6e421fabe2aa4155_SourceReuse.haltMachine (n + 2)⟩
  | k + 1, h => ⟨_, Composition.machine (chain k (by omega)).2 (stage n ⟨k, h⟩)⟩

def chainCost (w : Fin n → List Bool) (k : Nat) : Nat :=
  (((List.ofFn w).take k).map (fun x => 4 * x.length + 4)).sum

/-! ## 3. The pass: measure, then frame -/

def outP : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 1 (outT n)))
def cntP : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 (((0 : Fin 1).natAdd (n + 2)).castAdd 1)
def dstP : Fin (n + 2 + 1 + 1 + 2) := (0 : Fin 2).natAdd (n + 2 + 1 + 1)
def flogP : Fin (n + 2 + 1 + 1 + 2) := (1 : Fin 2).natAdd (n + 2 + 1 + 1)


def lengthMachine := AppendOutputLength.machine (chain n n le_rfl).2 (outT n)

def machine :=
  Composition.machine (TapeEmbedding.machine 2 (lengthMachine n))
    (SLoad.MaskFrame.machine (outP n) (cntP n) (dstP n) (flogP n))

def cost (w : Fin n → List Bool) : Nat :=
  2 * chainCost n w n + 2 + 1 + (4 * (List.ofFn w).flatten.length + 4)


end
end NearCubicWires.SourceRequest.FieldPass
