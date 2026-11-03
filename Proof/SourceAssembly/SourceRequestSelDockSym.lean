import Proof.SourceAssembly.SourceRequestSelDockS
import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceRequestSelLocalMach
import Proof.SourceAssembly.SourceRequestSelSymMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.SourceConstruction
noncomputable section

section dockSym
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

def gSS (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)
    (z : Fin (NF + (19 + 4 * tS))) : Fin V :=
  if h : z.val < 19 then cacheT ⟨z.val, h⟩
  else if h19 : z.val = 19 then ⟨1, one_lt_V e hV⟩
  else if h32 : z.val = 32 then terminal
  else ⟨d.B + hv (restPc eX pX gW) (eX + pX) z.val, B_lt_U hV _ (by
    have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
    have := hv_lt (eX + pX) gW z.val (by unfold Low; omega) (Nat.lt_of_lt_of_le z.isLt hN)
    rw [e1] at hres ⊢; omega)⟩

end dockSym

/-- The ten FactorSelection residents' words for SYM (header fields in mode `true`). -/
def resWS (q Pw W Ld L target cwid cw i : Nat) : List Bool :=
  if i = 0 then UnaryTemplate.tape q else if i = 1 then List.replicate Pw true
  else if i = 2 then List.replicate W true else if i = 3 then List.replicate Ld true
  else if h : i < 8 then RepairOrdinary.frame (SourceFactorSel.Header.fields true q L target 0 ⟨i - 4, by omega⟩)
  else if i = 8 then List.replicate cwid true else List.replicate cw true

section SS

end SS

section SelRunSS

end SelRunSS

end
end NearCubicWires.SourceRequest.SelLocal

