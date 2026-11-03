import Proof.CaseAnalysis.RawRowsDegree
import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PacketsXNormalizerOperations

/-! The literal-first intermediate alphabet and support census. This is
separate from the smaller alphabet after source lowering: no relationship
between occurrence population and decomposition-child count is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAlphabet
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.RepairSource.CloseoutRawRows

def codes (depth population : Nat) : Finset Nat :=
  (terminalLiteralVariableCodes depth population).toFinset ∪
    Finset.univ.biUnion (fun level : Fin depth=>(deltaLiteralVariableCodes (population:=population) level).toFinset)

def Supported (S : Finset Nat) (P : Ring.Poly Nat) : Prop := ∀ m∈P,∀ x∈m,x∈S
def Good (S : Finset Nat) (P : Ring.Poly Nat) : Prop := Ring.Normal P ∧ Supported S P

theorem codes_card (depth population : Nat) : (codes depth population).card≤population*(2*depth+1) := by
  have ht : (terminalLiteralVariableCodes depth population).toFinset.card≤population := by
    simpa only [terminalLiteralVariableCodes,List.length_ofFn] using
      List.toFinset_card_le (terminalLiteralVariableCodes depth population)
  have hd : ∀ level : Fin depth,
      (deltaLiteralVariableCodes (population:=population) level).toFinset.card≤2*population := by
    intro level
    simpa only [deltaLiteralVariableCodes,List.length_ofFn] using
      List.toFinset_card_le (deltaLiteralVariableCodes (population:=population) level)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun level _=>hd level)
  have hbi := Finset.card_biUnion_le (s:=Finset.univ)
    (t:=fun level : Fin depth=>(deltaLiteralVariableCodes (population:=population) level).toFinset)
  have hu := Finset.card_union_le (terminalLiteralVariableCodes depth population).toFinset
    (Finset.univ.biUnion (fun level : Fin depth=>(deltaLiteralVariableCodes (population:=population) level).toFinset))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  unfold codes
  nlinarith

/-- The physical mask width retains the actual frozen Nat.pair codes.
No arbitrary renaming of literals is used during ordered substitution. -/
theorem pair_lt_square (a b : Nat) : Nat.pair a b<(a+b+1)^2 := by
  unfold Nat.pair
  split <;> nlinarith

theorem codes_lt_square (depth population : Nat) (code : Nat)
    (hc : code∈codes depth population) : code<(depth+2*population+2)^2 := by
  rcases Finset.mem_union.mp hc with hc|hc
  · obtain ⟨coordinate,rfl⟩:=List.mem_ofFn.mp (List.mem_toFinset.mp hc)
    change Nat.pair 0 coordinate.val< _
    exact (pair_lt_square 0 coordinate.val).trans_le
      (Nat.pow_le_pow_left (by have h:=coordinate.isLt;omega) 2)
  · obtain ⟨level,_,hc⟩:=Finset.mem_biUnion.mp hc
    obtain ⟨slot,rfl⟩:=List.mem_ofFn.mp (List.mem_toFinset.mp hc)
    change Nat.pair (level.val+1) slot.val< _
    exact (pair_lt_square (level.val+1) slot.val).trans_le
      (Nat.pow_le_pow_left (by have hl:=level.isLt;have hs:=slot.isLt;omega) 2)

theorem good_zero (S : Finset Nat) : Good S structuralGF2Zero := by
  simp [Good,Ring.Normal,Supported,structuralGF2Zero]

theorem good_norm (S : Finset Nat) (P : Ring.Poly Nat) (hP : Supported S P) : Good S (Ring.norm P) :=
  ⟨Ring.normal_norm P,Ring.support_norm S P hP⟩

theorem good_add {S : Finset Nat} {P Q : Ring.Poly Nat} (hP : Good S P) (hQ : Good S Q) :
    Good S (Ring.add P Q) := by
  refine ⟨Ring.normal_add hP.1 hQ.1,?_⟩
  exact Ring.fold_toggle_property (fun m=>∀ x∈m,x∈S) id Q P hP.2 hQ.2

theorem good_mul {S : Finset Nat} {P Q : Ring.Poly Nat} (hP : Good S P) (hQ : Good S Q) :
    Good S (Ring.mul P Q) := by
  rw [←NormalizerOrder.mul_raw]
  apply good_norm
  intro m hm x hx
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
  rcases List.mem_append.mp hx with hx|hx
  · exact hP.2 p hp x hx
  · exact hQ.2 q hq x hx

theorem good_scale {S : Finset Nat} {P : Ring.Poly Nat} (c : ZMod 2) (hP : Good S P) :
    Good S (structuralGF2Scale c P) := by
  unfold structuralGF2Scale
  split
  · exact good_zero S
  · exact hP

theorem good_fold {S : Finset Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Good S P) (A : Ring.Poly Nat) (hA : Good S A) :
    Good S (ps.foldl Ring.add A) := by
  induction ps generalizing A with
  | nil => exact hA
  | cons P ps ih =>
    exact ih (fun Q hQ=>hps Q (by simp [hQ])) _ (good_add hA (hps P (by simp)))

theorem good_sum {S : Finset Nat} (ps : List (Ring.Poly Nat))
    (hps : ∀ P∈ps,Good S P) : Good S (Normalized.structuralGF2Sum ps) :=
  good_fold ps hps _ (good_zero S)

theorem good_elementary (S : Finset Nat) (xs : List Nat) (k : Nat) (hx : ∀ x∈xs,x∈S) :
    Good S (Normalized.structuralGF2ElementarySymmetric xs k) := by
  apply good_norm
  intro m hm x hxm
  exact hx x ((List.mem_sublistsLen.mp hm).1.subset hxm)

theorem good_shifted (S : Finset Nat) (xs : List Nat) (offset degree : Nat)
    (hx : ∀ x∈xs,x∈S) : Good S (Normalized.structuralGF2ShiftedElementarySymmetric xs offset degree) := by
  apply good_sum
  intro P hP
  obtain ⟨indices,_,rfl⟩ := List.mem_map.mp hP
  exact good_scale _ (good_elementary S xs indices.1 hx)

theorem good_window (S : Finset Nat) (xs : List Nat) (offset width target : Nat)
    (hx : ∀ x∈xs,x∈S) : Good S (Normalized.structuralGF2ConsecutiveWindowIndicator xs offset width target) := by
  apply good_sum
  intro P hP
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hP
  exact good_scale _ (good_shifted S xs offset d hx)

theorem good_terminal (depth population terminalWindow : Nat) (candidate : Fin (population+1)) :
    Good (codes depth population)
      (Normalized.structuralTerminalPolynomialVector depth population terminalWindow candidate) := by
  apply good_window
  intro x hx
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr hx)

theorem good_delta {rank depth population : Nat}
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth→Nat) (level : Fin depth) (parent child : Fin (population+1)) :
    Good (codes depth population) (Normalized.structuralDeltaFactor label seed window level parent child) := by
  unfold Normalized.structuralDeltaFactor
  dsimp only
  split
  · exact good_zero _
  · apply good_window
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨level,Finset.mem_univ _,List.mem_toFinset.mpr hx⟩)

theorem good_combine {rank depth population : Nat}
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth→Nat) (level : Fin depth)
    (children : StructuralListPolynomialVector population)
    (hc : ∀ child,Good (codes depth population) (children child)) (parent : Fin (population+1)) :
    Good (codes depth population) (Normalized.structuralCombineListLevel label seed window level children parent) := by
  apply good_sum
  intro P hP
  obtain ⟨child,rfl⟩ := List.mem_ofFn.mp hP
  exact good_mul (hc child) (good_delta label seed window level parent child)

theorem good_vectorFrom {rank depth population : Nat}
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth→Nat) (terminalWindow level : Nat) (candidate : Fin (population+1)) :
    Good (codes depth population)
      (Normalized.structuralListPolynomialVectorFrom label seed window terminalWindow level candidate) := by
  rw [Normalized.structuralListPolynomialVectorFrom]
  split
  · apply good_combine
    intro child
    exact good_vectorFrom label seed window terminalWindow (level+1) child
  · exact good_terminal depth population terminalWindow candidate
termination_by depth-level
decreasing_by omega

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAlphabet
