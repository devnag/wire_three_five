import Proof.Rows.ClosureConstantGate
import Proof.Rows.ClosureReusable48

/-! Complete reusable X/C frozen-gate field computation with a uniform
quadratic bound derived from the original retained description. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline
open VerifierDecoding SignedSortKey
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (g : NormalizedThresholdGate q)
def C (w : Nat) := 8*w+12
def E (B q : Nat) := B+15*q+3

private theorem part_le (z : Int) : z.toNat≤z.natAbs := by cases z <;>simp
private theorem neg_le (z : Int) : (-z).toNat≤z.natAbs := by
  simpa only [Int.natAbs_neg] using part_le (-z)

theorem bounds (w : Nat) (hw : 0<w)
    (hm : (g.threshold-1).natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    (∀ x∈CloseoutRowsPoolMinimum.items g live,natBitLength x.1.natAbs≤w) ∧
    CloseoutRowsPoolMinimum.negSum (CloseoutRowsPoolMinimum.items g live)<2^w ∧
    natBitLength (g.threshold-1).natAbs≤w ∧
    C10NaturalHardwireTarget.pPart (g.threshold-1)
      (CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live))<2^w ∧
    C10NaturalHardwireTarget.nPart (g.threshold-1) 0<2^w := by
  have hn : CloseoutRowsPoolMinimum.negSum (CloseoutRowsPoolMinimum.items g live)≤
      ∑ i,(g.weight i).natAbs := by
    simp only [CloseoutRowsPoolMinimum.negSum,CloseoutRowsPoolMinimum.items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    exact Finset.sum_le_sum (fun i _=>neg_le (g.weight i))
  have hs : CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g live)≤
      ∑ i,(g.weight i).natAbs := by
    simp only [CloseoutRowsPoolMinimum.liveSum,CloseoutRowsPoolMinimum.items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    apply Finset.sum_le_sum
    intro i _
    split
    · exact neg_le (g.weight i)
    · exact Nat.zero_le _
  refine ⟨?_,by omega,CompactCacheCost.bit_bound (g.threshold-1) w hw (by omega),?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have hi := Finset.single_le_sum (fun j _=>Nat.zero_le (g.weight j).natAbs) (Finset.mem_univ i)
    exact CompactCacheCost.bit_bound (g.weight i) w hw (by omega)
  · unfold C10NaturalHardwireTarget.pPart
    have hp := part_le (g.threshold-1)
    omega
  · unfold C10NaturalHardwireTarget.nPart
    have hp := neg_le (g.threshold-1)
    omega

theorem weight_fit (tail : List Bool) (B : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B) :
    CloseoutRowsPoolWeight.loopBudget (CloseoutRowsPoolMinimum.items g live)≤E B q := by
  simp only [CloseoutRowsPoolWeight.loopBudget,CloseoutRowsPoolMinimum.items_length,E]
  simp only [List.length_append] at hb
  omega

theorem worker_bound (tail : List Bool) (B w : Nat)
    (hb : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g live)++intWord (g.threshold-1)++tail).length≤B)
    (ht : natBitLength (g.threshold-1).natAbs≤w) :
    ConstantGate.budget (CloseoutRowsPoolMinimum.items g live) (g.threshold-1) w (C w)≤512*(B+q+w+1)^2 := by
  have he := weight_fit live g tail B hb
  have hz := C10NaturalHardwireTarget.budget_le (g.threshold-1) w ht
  simp only [ConstantGate.budget,ConstantGate.scoreTargetBudget,ConstantGate.scoreBudget,
    CloseoutRowsPoolMinimum.loopBudget,CloseoutRowsPoolMinimum.items_length,
    CloseoutRowsPoolMinimum.uniformBudget]
  unfold C E at *
  nlinarith

end NearCubicWires.P1Closure.ConstantGateReusable
