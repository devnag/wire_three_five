import Proof.Packets.SourceParamsK

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget.Params
open NearCubicWires.SourceBudget NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-- **`B`'s table exponent from the exponents alone**: family ⊔ (refill: `max hR yT`) ⊔ (first: `max hR (max yT (hR+1))`). -/
def siteHT : ParNat := fun s g hg hh p =>
  max (max ((famSite printerOf (cVcN selector) (hVN selector)).hT s g hg hh p)
      (max (hRx selector mask packets rows s g hg hh p) (yTx selector mask packets rows s g hg hh p)))
    (max (hRx selector mask packets rows s g hg hh p)
      (max (yTx selector mask packets rows s g hg hh p) (hRx selector mask packets rows s g hg hh p + 1)))

def siteL : ParNat := liveOf (siteHT selector mask packets rows)

/-- **`y`**: the refill's `Rc`-free class, coefficients at `siteL`. -/
def siteY : ClsFam := yFam mask packets rows degOf tgOf (KFc selector mask packets rows) (siteL selector mask packets rows)
/-- **`yF0`**: the first cycle's `Rc`-free class, coefficients at `siteL`. -/
def siteYF0 : ClsFam := yF0Fam mask packets rows degOf tgOf (KFc selector mask packets rows) (siteL selector mask packets rows)
/-- **The site's reserve** (`C = 1`, `hR` from the classes). -/
def siteR : RcChoice :=
  siteRc printerOf (cVcN selector) (hVN selector) (siteY selector mask packets rows) (siteYF0 selector mask packets rows)
/-- **The init's class** at the site's reserve and live scale. -/
def siteI : ClsFam := IFam (siteR selector mask packets rows) (IKc selector mask packets rows) (siteL selector mask packets rows)

end site

section args
variable (selector : CyclicChoice.Laws)

def cVcP : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → ParNat := fun _ _ _ => cVcN selector

def hVP : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → ParNat := fun _ _ _ => hVN selector

end args

end
end NearCubicWires.SourceBudget.Params
end

