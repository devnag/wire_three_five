import Proof.MachineModel.OrdinaryMatrixScoreBatchCodec

/-! The exact paper B.2 row-to-matrix boundary. A weighted integer equation
becomes two weak cuts in ONE request. Width growth, doubled gate count and
the optional ignored final right coordinate are explicit. The ordinary byte
producer is a separate remaining obligation; these definitions do not assume
it and do not add a literature premise. -/
namespace NearCubicWires.RepairOrdinary.EquationRow
open MatrixScoreBatch SupplierPrinter SignedSortKey RepairRepresentation ExecutableInterfaces SourceInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedRight (odd : Bool) (xs : List ℤ) : List ℤ :=
  xs++if odd then [0] else []

def padded (odd : Bool) (c : Cut) : Cut :=
  {c with rightWeights := paddedRight odd c.rightWeights}

def successor (c : Cut) : Cut :=
  {c with threshold := c.threshold+1,coefficient := -c.coefficient}

def doubled (odd : Bool) (cs : List Cut) : List Cut :=
  cs.flatMap (fun c => [padded odd c,successor (padded odd c)])

def Fits (p : ℕ) (c : Cut) : Prop :=
  (∀ w ∈ c.leftWeights++c.rightWeights,w.natAbs<2^p) ∧
    c.threshold.natAbs<2^p ∧ c.coefficient.natAbs<2^p

structure Input where
  d : ℕ
  p : ℕ
  odd : Bool
  cuts : List Cut
  lengths : ∀ c ∈ cuts,c.leftWeights.length=d ∧ c.rightWeights.length+odd.toNat=d
  fits : ∀ c ∈ cuts,Fits p c
  oddPositive : odd=true → 0<d
  gateSquare : (2*cuts.length)*(2*cuts.length) ≤ rectangularInnerDimension (2^d)

theorem paddedRight_length (odd : Bool) (xs : List ℤ) :
    (paddedRight odd xs).length=xs.length+odd.toNat := by
  cases odd <;> simp [paddedRight]

theorem doubled_length (odd : Bool) (cs : List Cut) :
    (doubled odd cs).length=2*cs.length := by
  simp [doubled,List.length_flatMap]
  omega

theorem widen (p : ℕ) {z : ℤ} (hz : z.natAbs<2^p) :
    z.natAbs<2^(p+1) := by
  have hp : 0<2^p := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem successor_fit (p : ℕ) (z : ℤ) (hz : z.natAbs<2^p) :
    (z+1).natAbs<2^(p+1) := by
  have ha := Int.natAbs_add_le z 1
  have hp : 0<2^p := Nat.pow_pos (by decide)
  simp only [Int.natAbs_one] at ha
  rw [pow_succ]
  omega

theorem padded_fits (odd : Bool) (p : ℕ) (c : Cut) (hc : Fits p c) :
    Fits p (padded odd c) := by
  rcases hc with ⟨hw,ht,hc⟩
  refine ⟨?_,ht,hc⟩
  intro w hm
  cases odd
  · exact hw w (by simpa [padded,paddedRight] using hm)
  · simp only [padded,paddedRight,ite_true,List.mem_append,List.mem_singleton] at hm
    rcases hm with hl | hr | hz
    · exact hw w (List.mem_append.mpr (Or.inl hl))
    · exact hw w (List.mem_append.mpr (Or.inr hr))
    · subst w
      exact Nat.pow_pos (by decide)

theorem fits_widen (p : ℕ) (c : Cut) (hc : Fits p c) : Fits (p+1) c :=
  ⟨fun w hw => widen p (hc.1 w hw),widen p hc.2.1,widen p hc.2.2⟩

theorem successor_fits (p : ℕ) (c : Cut) (hc : Fits p c) : Fits (p+1) (successor c) := by
  refine ⟨fun w hw => widen p (hc.1 w hw),successor_fit p c.threshold hc.2.1,?_⟩
  simpa only [successor,Int.natAbs_neg] using widen p hc.2.2

def request (r : Input) : Request where
  d := r.d
  p := r.p+1
  cuts := doubled r.odd r.cuts
  lengths := by
    intro c hc
    simp only [doubled,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hc
    obtain ⟨a,ha,hc⟩ := hc
    have hl := r.lengths a ha
    rcases hc with rfl | rfl
    · exact ⟨hl.1,(paddedRight_length _ _).trans hl.2⟩
    · exact ⟨hl.1,(paddedRight_length _ _).trans hl.2⟩
  fits := by
    intro c hc
    simp only [doubled,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hc
    obtain ⟨a,ha,hc⟩ := hc
    have hf := padded_fits r.odd r.p a (r.fits a ha)
    rcases hc with rfl | rfl
    · exact fits_widen r.p _ hf
    · exact successor_fits r.p _ hf
  gateSquare := by
    rw [doubled_length]
    exact r.gateSquare

theorem linearForm_paddedRight (odd : Bool) (xs : List ℤ) (a : ℕ) :
    linearForm (paddedRight odd xs) a=linearForm xs a := by
  cases odd
  · simp [paddedRight]
  · simp [linearForm,paddedRight,List.zipIdx_append]

def weakValue (c : Cut) (row column : ℕ) : ℤ :=
  c.coefficient*((weakCut c.threshold
    (linearForm c.leftWeights row+linearForm c.rightWeights column)).toNat : ℤ)

def exactValue (c : Cut) (row column : ℕ) : ℤ :=
  c.coefficient*((exactCut c.threshold
    (linearForm c.leftWeights row+linearForm c.rightWeights column)).toNat : ℤ)

theorem pair_value (odd : Bool) (c : Cut) (row column : ℕ) :
    weakValue (padded odd c) row column+
      weakValue (successor (padded odd c)) row column=exactValue c row column := by
  simp only [weakValue,exactValue,padded,successor,linearForm_paddedRight]
  rw [exactCut_eq_successiveCuts]
  ring

theorem doubled_value (odd : Bool) (cs : List Cut) (row column : ℕ) :
    ((doubled odd cs).map (fun c => weakValue c row column)).sum=
      (cs.map (fun c => exactValue c row column)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [doubled,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil] at *
    rw [← add_assoc,add_zero, pair_value,ih]

end NearCubicWires.RepairOrdinary.EquationRow
