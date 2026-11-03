import Proof.SourceAssembly.SourceFactorSelG7Fam
import Proof.SourceAssembly.SourceSkelFirstW
import Proof.SourceAssembly.SourceRequestSelKeptS

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceConstruction NearCubicWires.SourceRequest
open NearCubicWires.SourceSkeleton.FirstW
open NearCubicWires.SourceSkeleton.Fill (XtraW)
namespace NearCubicWires.SourceFactorSel.G7W
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

theorem hresS : 49 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra
    (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW ≤
    (dSite selector xtra mask packets rows sources gamma hg hh p).res := by
  have h10 : 10 ≤ NearCubicWires.SourceSkeleton.FillV5.xRV5 selector mask packets rows sources gamma hg hh p :=
    le_trans (SelLocal.ten_le_xROf _ _ sources gamma hg hh p) (Nat.le_add_right _ _)
  exact SelLocal.hres_resOfX (DSite selector mask packets rows sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.FillV5.xRV5 selector mask packets rows sources gamma hg hh p) h10

theorem hNTS : SelFront.NF + (19 + 4 * SelLocal.tT (decompositionOf sources)) ≤
    (DSite selector mask packets rows sources gamma hg hh p).gW :=
  le_trans (SelLocal.hG_thr sources gamma hg hh p) (Nat.le_add_right _ _)

theorem hNSS : SelFront.NF + (19 + 4 * SelLocal.tS) ≤ (DSite selector mask packets rows sources gamma hg hh p).gW :=
  le_trans (SelLocal.hG_sym sources gamma hg hh p) (Nat.le_add_right _ _)

theorem hroomS : NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p +
    Words.gwW mask.work (Cold.tapes (decompositionOf sources)) (G7Fam.kb sources) ≤ (DSite selector mask packets rows sources gamma hg hh p).gW := by
  have h := NearCubicWires.SourceSkeleton.Params.gwW_le_gwWS mask sources gamma hg hh p 194 (by decide)
  show NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p + (725 + 2 * mask.work + 2 * Cold.tapes (decompositionOf sources) + 2 * 194) ≤
    NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p + NearCubicWires.SourceSkeleton.Params.gwWS mask sources gamma hg hh p
  omega

end site

def G7Site (selector : CyclicChoice.Laws) (xtra : XtraW selector) : G7W selector xtra :=
  fun mask packets rows sources gamma hg hh p mode ph V hV =>
    G7Fam.g7At mask packets rows sources (resSite selector mask packets rows sources gamma hg hh p) p
      (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)
      (eSite selector xtra mask packets rows sources gamma hg hh p) hV (NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p)
      (cacheSite selector xtra mask packets rows sources gamma hg hh p V hV) (terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)
      (hresS selector xtra mask packets rows sources gamma hg hh p) (hNTS selector mask packets rows sources gamma hg hh p)
      (hNSS selector mask packets rows sources gamma hg hh p) (hroomS selector mask packets rows sources gamma hg hh p) mode ph

end
end NearCubicWires.SourceFactorSel.G7W
end

