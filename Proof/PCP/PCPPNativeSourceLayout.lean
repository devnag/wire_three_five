import Proof.PCP.PCPPNativeFrame
import Proof.PCP.PCPPSourceCacheBounds

/-! Static docking of the actual framed native descriptor and its retained
raw size/domain into the one-source shared-cache producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSource
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (a : PointwisePCPPAlgorithm) (t : ℕ) := ((t+2)+2)+PCPPSourceCache.tapes a
def oldSlot (a : PointwisePCPPAlgorithm) {t : ℕ} (i : Fin t) : Fin (tapes a t) :=
  (PCPPNativeFrame.old i).castAdd (PCPPSourceCache.tapes a)
def frameSlot (a : PointwisePCPPAlgorithm) (t : ℕ) : Fin (tapes a t) :=
  ((0 : Fin 2).natAdd (t+2)).castAdd (PCPPSourceCache.tapes a)
def sourceSlots (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t)
    (j : Fin (PCPPSourceCache.tapes a)) : Fin (tapes a t) :=
  if j.val=PCPPSourceCache.coldTapes a then frameSlot a t
  else if j.val=21 then oldSlot a size else if j.val=19 then oldSlot a domain
  else j.natAdd ((t+2)+2)

noncomputable def first (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s) (target : Fin t) :=
  TapeEmbedding.machine (PCPPSourceCache.tapes a) (AppendOutputFrame.machine p target)
noncomputable def last (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t) :=
  RecoveryFocus.machine (sourceSlots a size domain) (PCPPSourceCache.machine a)
noncomputable def machine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target size domain : Fin t) := Composition.machine (first a p target) (last a size domain)

end NearCubicWires.RepairOrdinary.PCPPNativeSource
