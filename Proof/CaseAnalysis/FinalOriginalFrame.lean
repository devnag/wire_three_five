import Proof.CaseAnalysis.FinalCacheRewind
import Proof.MachineModel.Layout

/-! Original input, witness and mode bytes belong to the same original-input
cold run. One recording rewind resets every head, and focus retains the exact
ambient complement. No prepared bank or second source execution is assumed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdOriginalFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch SourceInterfaces
open RepairSource RepairRepresentation ProjectionNormalization CloseoutWitness
open RecoveryRootRound CloseoutFinalC10ColdCacheAtAdmission
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

theorem original_slot (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) :
    BoundedFamilySupport.slots source a k D G E sym
      (ColdFamilySupport.originalTape source a k D G (BoundedFamily.exponent sym) E) =
      (HeaderDock.old (BoundedFamily.workspace source a k D G E) 0).castAdd 1 := by
  let j := FamilyCold.Call.old (FamilyCapacity.Call.old E
    (ColdFamily.originalTape source a k D G (BoundedFamily.exponent sym)))
  have lo : 2 < ColdInput.oracleIndex source k := by dsimp [ColdInput.oracleIndex]; omega
  have lt : 2 < ColdLegal.tapes source a k D G (BoundedFamily.exponent sym) :=
    (ColdLegal.originalTape source a k D G (BoundedFamily.exponent sym)).isLt
  have localOriginal : BoundedFamily.slots source a k D G E sym j =
      HeaderDock.old (BoundedFamily.workspace source a k D G E) 0 := by
    simp only [BoundedFamily.slots, HeaderDock.slots, show j.val=2 from rfl,
      if_neg (Nat.ne_of_lt lt), if_neg (Nat.ne_of_lt lo), ite_true]
  exact (SupportDock.slots_old (BoundedFamily.slots source a k D G E sym) j).trans
    (congrArg (fun i : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)) => i.castAdd 1) localOriginal)

variable
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (CH : Nat)
    (Cpad : Nat)
    (cutoff : Nat)
    (D : Nat)
    (G : Nat)
    (copies : Nat)
    (delta : Rat)
    (code : List Bool)
    (n : Nat)
    (x : BitInput n)
    (hpad : k+3 ≤ Cpad)
    (hD : 1 ≤ D)
    (E : Nat)
    (K : Nat)
    (bits : List Bool)
    (hK : 0<K)
    (hcut : 2^a.minimumArity ≤ cutoff)
    (hd : 0<delta)
    (hh : delta<1/2)
    (hc : 1≤copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N) ≤ K*(N+1)^E)
    (symDen : Nat)
    (thrDen : Nat)
    (hsym : 0<symDen)
    (hthr : 0<thrDen)

include hD hsym hthr hK hcut hd hh hc hbudget

theorem bounded_originals
    (actual : ExecutionReceipt (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1) _)
    (hrun : run (BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies) code) (2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad) (BoundedFamilySupport.input source a k D G E (List.ofFn x) bits)=some actual)
    (admitted : BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad=true) :
    actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 0).castAdd 1)=frame (List.ofFn x) ∧
    actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1)=frame bits ∧
    actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)=[BoundedFields.symmetric bits] := by
  classical
  have both := admitted
  unfold BoundedFamily.passed at both
  simp only [Bool.and_eq_true] at both
  have cap : 16*bits.length≤n := by
    have h := (of_decide_eq_true both.1).1
    simpa only [List.length_ofFn] using h
  have rawCap : 16*(BoundedFields.oracle bits).length≤n := by rw [(BoundedFields.lengths bits).1]; exact cap
  have familyCap : 16*(BoundedFields.family bits).length≤n := by rw [(BoundedFields.lengths bits).2]; exact cap
  have outerRich := BoundedFamilySupport.bounded_run_with_originals source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
  obtain ⟨outer, retained, outerRun, _steps, _flagH, _flagT, selected⟩ := outerRich
  have selectedFacts := selected both.1
  obtain ⟨child, childRun, _childHeads, childTapes⟩ := selectedFacts
  have childRich := ColdFamilySupport.family_run_with_originals source a k CH Cpad cutoff D G copies
    (BoundedFamily.exponent (BoundedFields.symmetric bits)) E K
    (BoundedFamily.denominator (BoundedFields.symmetric bits) symDen thrDen) delta code
    (BoundedFields.symmetric bits) x (BoundedFields.oracle bits) (BoundedFields.family bits)
    hpad hD (by unfold BoundedFamily.denominator; split_ifs <;> assumption)
    hK hcut hd hh hc hbudget rawCap familyCap
  obtain ⟨rich, original, richRun, _richFacts⟩ := childRich
  have sameChild : child=rich := Option.some.inj (childRun.symm.trans richRun)
  have childData := congrArg (fun r => r.final.tapes) sameChild
  have childOriginal := (congrFun childData _).trans (original both.2)
  have mappedOriginal := (childTapes _).trans childOriginal
  have outerOriginal := (congrArg outer.final.tapes
    (original_slot source a k D G E (BoundedFields.symmetric bits)).symm).trans mappedOriginal
  have other := retained both.1
  have same : actual=outer := Option.some.inj (hrun.symm.trans outerRun)
  have tapes := congrArg (fun r => r.final.tapes) same
  exact ⟨(congrFun tapes _).trans outerOriginal, (congrFun tapes _).trans other.1,
    (congrFun tapes _).trans other.2⟩


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdOriginalFrame
