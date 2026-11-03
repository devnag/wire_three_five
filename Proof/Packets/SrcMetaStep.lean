import Proof.Packets.SrcMetaRun
import Proof.SourceAssembly.SourceSkelInitXA
import Proof.CaseAnalysis.FinalWorkerEmitShape

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceStart.MetaStep
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission
open NearCubicWires.SourceStart.MetaProg NearCubicWires.SourceStart.MetaRun
open NearCubicWires.SourceSkeleton.InitS (InitInv MetaRun stripT extF extF_val eb sb slotVal slotVal_some slotVal_none
  fixedOf ResExt pad_frame_ones)
noncomputable section

/-! ## 1. The degenerate-case flags -/

/-- `cc0 = 0` (then `mC q = 0` for every `q`). -/
def czOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) : Bool :=
  decide (cc0 selector (decompositionOf s) p.clauseDegree (tgt s p) = 0)

/-- `v0C = 0` (then `mV q = 0` for every `q`). -/
def vzOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) : Bool :=
  decide (v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) = 0)

theorem czOf_iff (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) :
    czOf selector s p = true ↔ Meta.mC selector s p q = 0 := by
  unfold czOf Meta.mC
  simp [Nat.mul_eq_zero, pow_eq_zero_iff']

theorem vzOf_iff (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) :
    vzOf selector s p = true ↔ Meta.mV selector s p q = 0 := by
  unfold vzOf Meta.mV
  simp [Nat.mul_eq_zero, pow_eq_zero_iff']

variable {selector : CyclicChoice.Laws} {s : EightSources} {gamma : Real} {p : Parameters s gamma}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector} {L : ℕ}

/-- **The meta stage's cost.** -/
def metaCost (V : Meta.MetaVals2 selector s p packets L) (q : ℕ) : ℕ :=
  progCost V (czOf selector s p) (vzOf selector s p) q

/-! ## 2. The dock -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- The slot map: four locals onto `rsT 4` and strip slots `15, 17, 18`; local `i` otherwise onto extension tape `u + i`. -/
def gsl (V : Meta.MetaVals2 selector s p packets L) (u : ℕ) (i : Fin (191 + V.NP)) : Fin T :=
  if i.val = 0 then Dims.rsT pl.ext.rest pl.hT 4
  else if i.val = 1 then stripT pl hh 15 (by decide)
  else if i.val = 13 then stripT pl hh 17 (by decide)
  else if i.val = 14 then stripT pl hh 18 (by decide)
  else extF (NS := NS) pl (u + i.val)

/-- **The meta stage** (ONE fixed machine on the site universe). -/
def metaM (V : Meta.MetaVals2 selector s p packets L) (u : ℕ) :=
  RecoveryFocus.machine (gsl pl hh V u) (progM V (czOf selector s p) (vzOf selector s p))

/-! ## 3. The contract -/

end
end NearCubicWires.SourceStart.MetaStep

