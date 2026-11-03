import Proof.Packets.SrcMetaAsm

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaProg
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.Regs NearCubicWires.SourceStart.MetaAsm
noncomputable section

/-! ## 1. The tracking invariant and one stage -/

/-! ## 2. One or two named registers -/

/-- One named local tape `io ↦ o`. -/
def nm1 {NL n : ℕ} (o : Fin NL) (io : ℕ) (j : Fin n) : Option (Fin NL) := if j.val = io then some o else none

/-- Two named local tapes `ia ↦ a`, `ib ↦ b`. -/
def nm2 {NL n : ℕ} (a : Fin NL) (ia : ℕ) (b : Fin NL) (ib : ℕ) (j : Fin n) : Option (Fin NL) :=
  if j.val = ia then some a else if j.val = ib then some b else none

/-! ## 3. The stage kinds -/

def fixM {NL : ℕ} (bits : List Bool) (o : Fin NL) (f : ℕ) (hs : f + 2 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm1 (n := 2) o 0) f hs) (HierarchyFixedWord.machine bits)

/-- `1^b ↦ frame 1^b` from register `src` onto `o` (PG `FrameUnary`, masked). -/
def fruM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 3 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3) src 0 o 1) f hs)
    (MaskedReset.machine PacketsGlue.FrameUnary.machine (fun _ => true))

def zerM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 3 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3) src 0 o 1) f hs) (MaskedReset.machine zerosM (fun _ => true))

def cntM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 10 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 10) src 0 o 5) f hs) CloseoutRowsCountBinary.machine

def natM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 22 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 22) src 0 o 20) f hs) CloseoutRowsEstimatorParity.Natural.machine

/-! ## 4. The two assembly phases -/

def nmA {NL : ℕ} (m pb : ℕ) (hpb : pb + m ≤ NL) (out : Fin NL) (j : Fin (m + 2 + 1)) : Option (Fin NL) :=
  if h : j.val < m then some ⟨pb + j.val, by omega⟩ else if j.val = m then some out else none

def phAM {NL : ℕ} (m pb : ℕ) (hpb : pb + m ≤ NL) (out : Fin NL) (f : ℕ) (hs : f + (m + 2 + 1) ≤ NL) :=
  RecoveryFocus.machine (nslot (nmA m pb hpb out) f hs) (MaskedReset.machine (innerA m).2 (fun _ => true))

/-- Phase B docked: `src` (kept) to `out`. -/
def phBM {NL : ℕ} (src out : Fin NL) (f : ℕ) (hs : f + (3 + 1) ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3 + 1) src 0 out 2) f hs) (MaskedReset.machine innerB.2 (fun _ => true))

end
end NearCubicWires.SourceStart.MetaProg

