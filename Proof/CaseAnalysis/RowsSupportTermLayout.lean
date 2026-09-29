import Proof.CaseAnalysis.RowsCircuitPadding
import Proof.CaseAnalysis.RowsSupportSymmetricCircuit
import Proof.CaseAnalysis.WitnessTermRound

/-! The strengthened term controller adds one public support tape. Every
original term, coefficient, native, reset-driver and log port keeps its index. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape CloseoutWitness RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1704) : Fin 2533:=
  if h:i.val<1703 then (TermCircuitDock.slots ⟨i.val,h⟩).castAdd 1 else 2532

noncomputable def sizes (s : ℕ):=TermRound.sizes s
noncomputable def programs {s : ℕ} (circuit : Machine 1704 s) : (j : Fin 5) → Machine 2533 (sizes s j)
  | 0=>TapeEmbedding.machine 1 TermRound.begin
  | 1=>RecoveryFocus.machine slots circuit
  | 2=>TapeEmbedding.machine 1 TermRound.foldFlag
  | 3=>TapeEmbedding.machine 1 TermRound.ending
  | 4=>TapeEmbedding.machine 1 TermCircuitReset.machine

def next {s : ℕ} (j : Fin 5) (state : Fin (sizes s j)) (bits : Fin 2533 → Bool) : Option (Fin 5):=
  TermRound.next j state (fun i=>bits (i.castAdd 1))
noncomputable def machine {s : ℕ} (circuit : Machine 1704 s):=
  RecoveryCalls.machine (sizes s) (programs circuit) 0 next

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
