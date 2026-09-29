import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmFields

/-! Owned padding and seven simultaneous metadata copies. The extra
unused output port is empty; the growing scalar stream stays external. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := Reuse.tapes p+7
def old (p : Program) (i : Fin (WholePrefix.tapes p)) : Fin (tapes p) := (Reuse.old p i).castAdd 7
def source (p : Program) (i : Fin 7) : Fin (tapes p) := i.natAdd (Reuse.tapes p)
def dest (p : Program) (i : Fin 7) : Fin (tapes p) := old p (WarmFields.slots p i)
def driver (p : Program) : Fin (tapes p) := (Reuse.driver p).castAdd 7
def log (p : Program) : Fin (tapes p) := (Reuse.log p).castAdd 7
def padSlots (p : Program) (i : Fin (WholePrefix.tapes p-2+1+1)) : Fin (tapes p) :=
  (Reuse.eraseSlots p i).castAdd 7
def copySlots (p : Program) : Fin (7+(7+1)+1) → Fin (tapes p) :=
  Fin.addCases (Fin.addCases (source p) (Fin.addCases (dest p) (fun _ : Fin 1=>driver p))) (fun _ : Fin 1=>log p)

def bank (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ) : Fin (Reuse.tapes p) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1=>List.replicate L false)) (![[],List.replicate D true] : Fin 2 → List Bool)
def data (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) : Fin (tapes p) → List Bool := Fin.addCases (bank p A D L) fields
noncomputable def pad (p : Program) := RecoveryFocus.machine (padSlots p) (Pad.machine (WholePrefix.tapes p-2))
noncomputable def copy (p : Program) := RecoveryFocus.machine (copySlots p) (MetadataBatch.machine 7)
noncomputable def machine (p : Program) := Composition.machine (pad p) (copy p)


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
