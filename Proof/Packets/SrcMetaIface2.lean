import Proof.Packets.SrcMetaIface

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceStart.Meta
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction
noncomputable section

/-- The `V`-mantissa `v0C·(q+1)^v0E` (`VvOf L q = mV q · 2^(q−K)`). -/
def mV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) : ℕ :=
  v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)

theorem VvOf_eq (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L q : ℕ) :
    VvOf selector s p L q = mV selector s p q * 2^(q - normalizedLiveCount q L) := by
  unfold VvOf mV RuntimeShape.tableClass
  ring

def KFc3 (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) : CallKFam := fun s g hg hh p L =>
  { KFc selector mask packets rows s g hg hh p L with
    hdC := 2*hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L + 2
    cpTC := 4*cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 4
    cpSC := 4*cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 4
    rwC := 2*((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1) + 2 }

/-- **The meta pipeline's contract, decision 80b** (POOL-10; supersedes `MetaVals`). -/
structure MetaVals2 (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) where
  NP : ℕ
  states : ℕ
  machine : Machine NP states
  cost : ℕ → ℕ
  costC : ℕ
  costE : ℕ
  cost_le : ∀ q, cost q ≤ costC * (q+1)^costE
  iq : Fin NP
  iK : Fin NP
  oW : Fin NP
  oD : Fin NP
  oX : Fin NP
  oXK : Fin NP
  oM : Fin NP
  oB : Fin NP
  oH : Fin NP
  oC : Fin NP
  oMV : Fin NP
  oBV : Fin NP
  oR : Fin NP
  nodup : [iq, iK, oW, oD, oX, oXK, oM, oB, oH, oC, oMV, oBV, oR].Nodup
  run : ∀ (q R : ℕ) (E : Fin NP → List Bool),
    E iq = ZeroPadding.pad R (List.replicate q true) →
    E iK = ZeroPadding.pad R (List.replicate (2*normalizedLiveCount q L) true) →
    (∀ x, x ≠ iq → x ≠ iK → E x = List.replicate R false) →
    ∃ E' : Fin NP → List Bool, Step machine (cost q) (fun _ => 0) E (fun _ => 0) E' ∧
      E' iq = E iq ∧ E' iK = E iK ∧
      E' oW = ZeroPadding.pad R (List.replicate (wA q L) true) ∧
      E' oD = ZeroPadding.pad R (List.replicate (uniformDeg q L) true) ∧
      E' oX = ZeroPadding.pad R (List.replicate (q/4) true) ∧
      E' oXK = ZeroPadding.pad R (List.replicate (q - normalizedLiveCount q L) true) ∧
      E' oM = ZeroPadding.pad R (List.replicate (mC selector s p q) true) ∧
      E' oB = ZeroPadding.pad R (List.replicate (Nat.clog 2 (mC selector s p q + 1) + q/4) true) ∧
      E' oH = ZeroPadding.pad R (List.replicate (yH selector s p L q) true) ∧
      E' oC = ZeroPadding.pad R (List.replicate (max (yA selector s p L q) (yB selector s p q) + 1) true) ∧
      E' oMV = ZeroPadding.pad R (List.replicate (mV selector s p q) true) ∧
      E' oBV = ZeroPadding.pad R (List.replicate (Nat.clog 2 (mV selector s p q + 1) + (q - normalizedLiveCount q L)) true) ∧
      E' oR = ZeroPadding.pad R (List.replicate (yR selector s p packets q) true)

end
end NearCubicWires.SourceStart.Meta

