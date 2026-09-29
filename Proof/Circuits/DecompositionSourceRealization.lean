import Proof.Circuits.DecompositionSourceEntry

/-! Literal ordinary source-entry realization, with a polynomial envelope
derived from the selected constructor's own coefficient and degree. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parameter (r : ExactDecompositionRequest) := r.arity+r.gate.encodingBits+1

theorem entry_budget_coarse (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    Entry.budget a r ≤ 1024*(sourceBudget a r+parameter r+1)^2 := by
  let n := r.arity
  let m := (a.output r).children.length
  let S := parameter r
  let B := sourceBudget a r
  let W := B+S+1
  have hn : n+1 ≤ S := by dsimp [n,S,parameter]; omega
  have hm : m ≤ B := children_bound a r
  have hout := output_length a r
  have hbody : ((a.output r).children.flatMap exactWord).length ≤ B := by
    have hx : (natWord m).length+((a.output r).children.flatMap exactWord).length ≤ B := by
      simpa only [exactListWord,List.length_append] using hout
    omega
  have hinput := thresholdWord_bound r.gate
  have hinput' : (natWord n++Call.tail r).length ≤ 8*S := by
    simpa only [thresholdWord,Call.tail,List.append_assoc,n,S,parameter] using hinput
  have harity := Count.budget_bound n
  have hchildren := Count.budget_bound m
  have hnbit : natBitLength n ≤ n+1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  have hmbit : natBitLength m ≤ m+1 := by unfold natBitLength; have := Nat.log_le_self 2 m; omega
  have hNW : n+1 ≤ W := by dsimp [W]; omega
  have hMW : m+1 ≤ W := by dsimp [W]; omega
  have hBW : B ≤ W := by dsimp [W]; omega
  have hSW : S ≤ W := by dsimp [W]; omega
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hn2 : (n+1)^2 ≤ W^2 := Nat.pow_le_pow_left hNW 2
  have hm2 : (m+1)^2 ≤ W^2 := Nat.pow_le_pow_left hMW 2
  have hnm : n*m ≤ W^2 := by
    calc n*m ≤ W*W := Nat.mul_le_mul (by omega) (by omega)
         _ = W^2 := by ring
  have hW2 : W ≤ W^2 := by nlinarith
  change Entry.budget a r ≤ 1024*W^2
  unfold Entry.budget Counted.budget Call.budget Prepare.budget PCPPQueryField.fieldCost
  change 4*(natWord n++Call.tail r).length+Count.budget n+(2*natBitLength n+3)+4+
      2*B+3+Count.budget m+1+(2*natBitLength m+3)+
      ((a.output r).children.flatMap exactWord).length+(6*n+10)*m+5 ≤ _
  nlinarith

end NearCubicWires.RepairOrdinary.DecompositionSource
