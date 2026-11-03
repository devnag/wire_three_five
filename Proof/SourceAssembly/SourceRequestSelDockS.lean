import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceRequestSelLocalMach
import Proof.SourceAssembly.SourceRestIn4

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

/-! ## The high offsets and their inverse (injectivity without per-case arithmetic loops) -/

/-- The offset above `B` of a non-low local port (`x = eX + pX`, `Pc = restPc eX pX gW`). -/
def hv (Pc x z : Nat) : Nat :=
  if z = 20 then 83 else if z < 31 then 29 + Pc + (z - 21) else if z = 31 then 41 + Pc else if z = 33 then 89
  else if z < 37 then 80 + (z - 34) else if z = 39 then 48 + Pc else 90 + x + z

/-- A local port is LOW when it lands below `F` (cache, witness, terminal). -/
def Low (z : Nat) : Prop := z < 19 ∨ z = 19 ∨ z = 32

/-- Every high offset lies below the high residents' end `49 + Pc`, and region offsets lie in `[90 + x, 19 + Pc)`. -/
theorem hv_lt (x gW z : Nat) (hz : ¬ Low z) (hzg : z < gW) : hv (71 + x + gW) x z < 49 + (71 + x + gW) := by
  unfold Low at hz
  unfold hv
  by_cases h20 : z = 20
  · rw [if_pos h20]; omega
  rw [if_neg h20]
  by_cases h31 : z < 31
  · rw [if_pos h31]; omega
  rw [if_neg h31]
  by_cases h31' : z = 31
  · rw [if_pos h31']; omega
  rw [if_neg h31']
  by_cases h33 : z = 33
  · rw [if_pos h33]; omega
  rw [if_neg h33]
  by_cases h37 : z < 37
  · rw [if_pos h37]; omega
  rw [if_neg h37]
  by_cases h39 : z = 39
  · rw [if_pos h39]; omega
  rw [if_neg h39]; omega

section dock
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

theorem B_lt_U (hV : d.U ≤ V) (i : Nat) (hi : i < d.res) : d.B + i < V := by
  have h : d.B + i < d.U := by
    unfold SourceConstruction.Dims.B SourceConstruction.Dims.U SourceConstruction.Dims.G SourceConstruction.Dims.prepT
    omega
  exact Nat.lt_of_lt_of_le h hV

theorem one_lt_V (e : d.RestExt3 eX pX gW) (hV : d.U ≤ V) : 1 < V := by
  have hF := e.ext2.ext1.ext.hF
  have h : 1 < d.U := by
    unfold SourceConstruction.Dims.U SourceConstruction.Dims.G SourceConstruction.Dims.prepT
    omega
  exact Nat.lt_of_lt_of_le h hV

def gS (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)
    (z : Fin (NF + (19 + 4 * tT da))) : Fin V :=
  if h : z.val < 19 then cacheT ⟨z.val, h⟩
  else if h19 : z.val = 19 then ⟨1, one_lt_V e hV⟩
  else if h32 : z.val = 32 then terminal
  else ⟨d.B + hv (restPc eX pX gW) (eX + pX) z.val, B_lt_U hV _ (by
    have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
    have := hv_lt (eX + pX) gW z.val (by unfold Low; omega) (Nat.lt_of_lt_of_le z.isLt hN)
    rw [e1] at hres ⊢; omega)⟩

end dock

/-! ## The ports: offsets of the named local ports -/


def resW (q Pw W Ld L target cwid cw i : Nat) : List Bool :=
  if i = 0 then UnaryTemplate.tape q else if i = 1 then List.replicate Pw true
  else if i = 2 then List.replicate W true else if i = 3 then List.replicate Ld true
  else if h : i < 8 then RepairOrdinary.frame (SourceFactorSel.Header.fields false q L target 0 ⟨i - 4, by omega⟩)
  else if i = 8 then List.replicate cwid true else List.replicate cw true

section S

end S

section SelRunS

end SelRunS

end
end NearCubicWires.SourceRequest.SelLocal

