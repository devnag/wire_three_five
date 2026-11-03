import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceRequestSelDockSym
import Proof.SourceAssembly.SourceRequestSelFrontA
import Proof.SourceAssembly.SourceRequestSelLocalMach
import Proof.SourceAssembly.SourceRequestSelSymMach
import Proof.SourceAssembly.SourceSkelInitXA
import Proof.SourceAssembly.SourceSkelParams

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton.InitS (initResVal valAllX cwidOf)
open NearCubicWires.SourceRequest.SelFront (NF)
noncomputable section

section kept

end kept

theorem hres_resOfX {a : RepairRepresentation.DecompositionAlgorithm} (D : SourceSkeleton.RestData a) (xR : Nat) (h : 10 ≤ xR) :
    49 + restPc D.se.extra D.sp.extra D.gW ≤ SourceSkeleton.resOfX D xR := by
  unfold SourceSkeleton.resOfX; omega

theorem ten_le_xROf (hR hV : SourceBudget.ParNat) (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    10 ≤ SourceSkeleton.Params.xROf hR hV sources gamma hg hh p := by
  unfold SourceSkeleton.Params.xROf; omega

theorem hG_thr (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    NF + (19 + 4 * tT (RepairSource.CloseoutFinal.decompositionOf sources)) ≤
      SourceSkeleton.Params.gG7 sources gamma hg hh p := by
  have e : tT (RepairSource.CloseoutFinal.decompositionOf sources) =
      3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources) := rfl
  have hm := le_max_left (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  show NF + (19 + 4 * tT (RepairSource.CloseoutFinal.decompositionOf sources)) ≤
    7000 + 19 + 4 * max (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  rw [e]; unfold NF; omega

theorem hG_sym (sources : RepairSource.EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : RepairSource.CloseoutFinal.Parameters sources gamma) :
    NF + (19 + 4 * tS) ≤ SourceSkeleton.Params.gG7 sources gamma hg hh p := by
  have hm := le_max_right (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  show NF + (19 + 4 * tS) ≤
    7000 + 19 + 4 * max (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (RepairSource.CloseoutFinal.decompositionOf sources)) 3778
  unfold NF tS; omega

end
end NearCubicWires.SourceRequest.SelLocal

