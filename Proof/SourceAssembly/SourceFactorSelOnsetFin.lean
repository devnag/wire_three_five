import Proof.Packets.SrcEntryW4
import Proof.SourceAssembly.SourceRequestSelLoopSite
import Proof.SourceAssembly.SourceSkelOnsetW
import Proof.SourceAssembly.SourceFactorSelSeamSite

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceSkeleton
open PCJ9eff70d512234a4c_Fixed PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceFactorSel.OnsetFin
noncomputable section

/-- **THE FINAL ONSET**: every posted onset, one `XtraW`. -/
def oFinal (selector : CyclicChoice.Laws) : Fill.XtraW selector := fun mask packets rows sources gamma hg hh p =>
  max (NearCubicWires.SourceStart.EntryW.res284W selector mask packets rows sources gamma hg hh p)
    (max (NearCubicWires.SourceStart.SeamRP.seamOnW selector mask packets rows sources gamma hg hh p)
    (max (NearCubicWires.SourceStart.SeamRP.hfamOnW selector mask packets rows sources gamma hg hh p)
    (max (NearCubicWires.SourceStart.LayRP.layOnW selector mask packets rows sources gamma hg hh p)
    (max (NearCubicWires.SourceRequest.SelLoopSite.g7OnsetF selector mask packets rows sources gamma hg hh p (ParamsV4.LW selector mask packets rows sources gamma hg hh p) (SourceBudget.tgt sources p) (SourceBudget.tgt sources p))
    (max (NearCubicWires.SourceFactorSel.ClauseCost.refOnS selector mask packets rows sources gamma hg hh p (SourceBudget.capIndexOf (ParamsV4.den0W selector mask packets rows)))
    (max (NearCubicWires.SourceFactorSel.ClauseCost.firstOnS selector mask packets rows sources gamma hg hh p (SourceBudget.capIndexOf (ParamsV4.den0W selector mask packets rows)))
    (NearCubicWires.SourceFactorSel.SeamSiteGF.siteOnGF mask packets rows sources p hg hh ((ParamsV4.fPW selector (XtraF.xtraF selector) mask packets rows).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _))))))))

/-- **The final fill's onset** `max xtraF oFinal`. -/
def xtraFin (selector : CyclicChoice.Laws) : Fill.XtraW selector := OnsetW.xtraF2 selector (oFinal selector)

section comps
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

/-- The steps' guard form: past `extraW xtraFin`, `oFinal ≤ n`. -/
theorem oFinal_le_of_extraW (n : ℕ) (hn : ParamsV4.extraW selector (xtraFin selector) mask packets rows sources gamma hg hh p ≤ n) :
    oFinal selector mask packets rows sources gamma hg hh p ≤ n :=
  OnsetW.o_le_of_onset selector (oFinal selector) mask packets rows sources gamma hg hh p n hn

theorem layOnW_le_oFinal : NearCubicWires.SourceStart.LayRP.layOnW selector mask packets rows sources gamma hg hh p ≤ oFinal selector mask packets rows sources gamma hg hh p :=
  le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)

theorem pastE_layOnW (n : ℕ) (hn : ParamsV4.extraW selector (xtraFin selector) mask packets rows sources gamma hg hh p ≤ n) : NearCubicWires.SourceStart.LayRP.layOnW selector mask packets rows sources gamma hg hh p ≤ n :=
  le_trans (layOnW_le_oFinal selector mask packets rows sources gamma hg hh p)
    (oFinal_le_of_extraW selector mask packets rows sources gamma hg hh p n hn)

end comps

end
end NearCubicWires.SourceFactorSel.OnsetFin
end

