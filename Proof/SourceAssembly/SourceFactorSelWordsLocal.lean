import Proof.SourceAssembly.SourceFactorSelWordsRunB

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- **The words stage's local machine** (fixed per `(mask, a, SB)`). -/
def wordsLoc (mask : MaskProducer) {a : DecompositionAlgorithm} {k : Nat} (SB : Item4.StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (m1 mask.work (Cold.tapes a) k) SourceResident.copiesM)
  (Composition.machine (RecoveryFocus.machine (m2 mask.work (Cold.tapes a) k) SourceResident.occM)
  (Composition.machine (RecoveryFocus.machine (m3 mask.work (Cold.tapes a) k) (Item4.lmM mask))
  (Composition.machine (RecoveryFocus.machine (m4 mask.work (Cold.tapes a) k) (Item4.idxBlock SB))
  (Composition.machine (RecoveryFocus.machine (m5 mask.work (Cold.tapes a) k) (SourceRequest.InputPass.machine mask))
  (Composition.machine (RecoveryFocus.machine (m6 mask.work (Cold.tapes a) k) Item4.tkM)
  (Composition.machine (RecoveryFocus.machine (M7 mask.work a k) (Item4.poolBlock SB))
  (Composition.machine (RecoveryFocus.machine (m8 mask.work (Cold.tapes a) k) P1Closure.BinaryCacheColdMeasure.machine)
  (Composition.machine (RecoveryFocus.machine (m9 mask.work (Cold.tapes a) k) Streaming.machine)
    (RecoveryFocus.machine (m10 mask.work (Cold.tapes a) k) Streaming.machine)))))))))

/-- **Its per-request cost** (`Rc`-free). -/
def wordsCost (mask : MaskProducer) {a : DecompositionAlgorithm} {k : Nat} (SB : Item4.StartBank a k) (r : Request)
    (MB : List Bool) : Nat :=
  SourceResident.copiesCost (cw a r) + 1 +
  (SourceResident.occCost (r.supportWord a).length (r.family a).occurrences.length + 1 +
  (Item4.lmCost mask a r + 1 +
  (Item4.idxCost SB r + 1 +
  (SourceRequest.InputPass.cost mask a r + 1 +
  ((2 * (2 * (maskData a r).K + 5) + 2) + 1 +
  (Item4.poolCost SB r + 1 +
  (P1Closure.BinaryCacheColdMeasure.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs + 1 +
  ((4 * MB.length + 2) + 1 + (4 * (List.replicate MB.length true).length + 2)))))))))

end
end NearCubicWires.SourceFactorSel.Words

