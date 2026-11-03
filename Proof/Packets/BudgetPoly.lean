import Proof.Assembly.ClosureBinaryCacheRun
import Proof.MachineModel.ClosureBinaryCacheMetadataCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceBudget.Cold
open NearCubicWires NearCubicWires.P1Closure NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.P1Closure.BinaryCacheColdJoin

/-- The polynomial base. -/
def X (q : ℕ) (r : Args q) : ℕ := (exactListWord r.gs).length + r.gs.length + q + 2 ^ r.live.card + 1

/-- `f` is bounded by a fixed power of `X`. -/
def Pol (f : ∀ q, Args q → ℕ) : Prop := ∃ c d : ℕ, ∀ q (r : Args q), f q r ≤ c * (X q r) ^ d

theorem X_pos (q : ℕ) (r : Args q) : 1 ≤ X q r := by unfold X; generalize 2 ^ r.live.card = P; omega

theorem Pol.mono {f g : ∀ q, Args q → ℕ} (hg : Pol g) (h : ∀ q r, f q r ≤ g q r) : Pol f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun q r => (h q r).trans (hc q r)⟩

theorem Pol.const (k : ℕ) : Pol (fun _ _ => k) := ⟨k, 0, fun q r => by simp⟩

theorem Pol.ofX {f : ∀ q, Args q → ℕ} (h : ∀ q r, f q r ≤ X q r) : Pol f :=
  ⟨1, 1, fun q r => by simpa using h q r⟩

theorem Pol.add {f g h : ∀ q, Args q → ℕ} (hf : Pol f) (hg : Pol g) (e : ∀ q r, h q r ≤ f q r + g q r) : Pol h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, d1 + d2, fun q r => ?_⟩
  have hs := X_pos q r
  have p1 : (X q r) ^ d1 ≤ (X q r) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p2 : (X q r) ^ d2 ≤ (X q r) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have q1 := (h1 q r).trans (Nat.mul_le_mul_left c1 p1)
  have q2 := (h2 q r).trans (Nat.mul_le_mul_left c2 p2)
  have e2 := e q r
  rw [Nat.add_mul]
  omega

theorem Pol.mul {f g h : ∀ q, Args q → ℕ} (hf : Pol f) (hg : Pol g) (e : ∀ q r, h q r ≤ f q r * g q r) : Pol h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun q r => (e q r).trans ?_⟩
  calc f q r * g q r ≤ (c1 * (X q r) ^ d1) * (c2 * (X q r) ^ d2) := Nat.mul_le_mul (h1 q r) (h2 q r)
    _ = c1 * c2 * (X q r) ^ (d1 + d2) := by rw [pow_add]; ring

theorem Pol.pow {f h : ∀ q, Args q → ℕ} (hf : Pol f) (k : ℕ) (e : ∀ q r, h q r ≤ f q r ^ k) : Pol h := by
  obtain ⟨c, d, h1⟩ := hf
  refine ⟨c ^ k, d * k, fun q r => (e q r).trans ?_⟩
  calc f q r ^ k ≤ (c * (X q r) ^ d) ^ k := Nat.pow_le_pow_left (h1 q r) k
    _ = c ^ k * (X q r) ^ (d * k) := by rw [mul_pow, ← pow_mul]

/-! ## The atoms -/

theorem nbl_le (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem pL : Pol (fun _ r => (exactListWord r.gs).length) := Pol.ofX (fun q r => by unfold X; generalize 2 ^ r.live.card = P; omega)
theorem pN : Pol (fun _ r => r.gs.length) := Pol.ofX (fun q r => by unfold X; generalize 2 ^ r.live.card = P; omega)
theorem pq : Pol (fun q _ => q) := Pol.ofX (fun q r => by unfold X; generalize 2 ^ r.live.card = P; omega)
theorem pP : Pol (fun _ r => 2 ^ r.live.card) := Pol.ofX (fun q r => by unfold X; generalize 2 ^ r.live.card = P; omega)
theorem pK : Pol (fun _ r => r.live.card) :=
  Pol.ofX (fun q r => by have := (Nat.lt_two_pow_self (n := r.live.card)).le; unfold X; generalize 2 ^ r.live.card = P at *; omega)
theorem pW : Pol (fun _ r => natBitLength r.gs.length) :=
  Pol.ofX (fun q r => by have := nbl_le r.gs.length; unfold X; generalize 2 ^ r.live.card = P; omega)

theorem flat_le {q : ℕ} (gs : List (ExactThresholdGate q)) (k : ℕ) :
    ((gs.take k).flatMap exactWord).length ≤ (exactListWord gs).length := by
  have h := congrArg (fun l => (List.flatMap exactWord l).length) (List.take_append_drop k gs)
  simp only [List.flatMap_append, List.length_append] at h
  simp only [exactListWord, List.length_append]
  omega

/-! ## The ten local budgets -/

theorem p1 : Pol (fun _ r => localBudget1 r) := by
  have hNW : Pol (fun _ r => r.gs.length * (8 * natBitLength r.gs.length + 10)) :=
    Pol.mul pN (Pol.add (Pol.mul (Pol.const 8) pW (fun _ _ => le_refl _)) (Pol.const 10) (fun _ _ => le_refl _))
      (fun _ _ => le_refl _)
  have hqN : Pol (fun q r => (6 * q + 10) * r.gs.length) :=
    Pol.mul (Pol.add (Pol.mul (Pol.const 6) pq (fun _ _ => le_refl _)) (Pol.const 10) (fun _ _ => le_refl _)) pN
      (fun _ _ => le_refl _)
  have hsum := Pol.add (Pol.add (Pol.add (Pol.add hNW hqN (fun _ _ => le_refl _)) pW (fun _ _ => le_refl _)) pN
    (fun _ _ => le_refl _)) (Pol.add pL (Pol.const 200) (fun _ _ => le_refl _)) (fun _ _ => le_refl _)
  refine Pol.mono (Pol.mul (Pol.const 64) hsum (fun _ _ => le_refl _)) (fun q r => ?_)
  have hf := flat_le r.gs r.gs.length
  simp only [localBudget1, BinaryCacheColdMeasure.budget, BinaryCacheColdMeasure.rawBudget,
    DecompositionSource.Count.budget, PCPPQueryNatural.budget, MatrixDimensionPrepare.budget,
    DecompositionCachedChild.budget, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  omega

theorem p2 : Pol (fun _ r => localBudget2 r) := by
  refine Pol.mono (Pol.add (Pol.mul (Pol.const 12) pW (fun _ _ => le_refl _)) (Pol.const 16) (fun _ _ => le_refl _))
    (fun q r => ?_)
  simp only [localBudget2, BinaryCacheColdHeader.budget, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  omega

theorem p3 : Pol (fun _ r => localBudget3 r) := by
  have hs : Pol (fun q r => (exactListWord r.gs).length + q + r.gs.length + r.live.card +
      natBitLength r.gs.length + 1) :=
    Pol.add (Pol.add (Pol.add (Pol.add (Pol.add pL pq (fun _ _ => le_refl _)) pN (fun _ _ => le_refl _)) pK
      (fun _ _ => le_refl _)) pW (fun _ _ => le_refl _)) (Pol.const 1) (fun _ _ => le_refl _)
  refine Pol.mono (Pol.mul (Pol.const (2 ^ 24)) (Pol.pow hs 3 (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (fun q r => ?_)
  exact BinaryCacheColdMetadata.budget_bound _ _ _ _ _

theorem p4 : Pol (fun _ r => localBudget4 r) := by
  have hK1 : Pol (fun _ r => r.live.card + 1) := Pol.add pK (Pol.const 1) (fun _ _ => le_refl _)
  refine Pol.mono (Pol.add (Pol.mul (Pol.mul (Pol.const 80) hK1 (fun _ _ => le_refl _)) pP (fun _ _ => le_refl _))
    (Pol.const 5) (fun _ _ => le_refl _)) (fun q r => ?_)
  have := BinaryInitialize.budget_le r.live.card
  simp only [localBudget4, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  omega

theorem p6 : Pol (fun _ r => localBudget6 r) := by
  have hPN : Pol (fun _ r => 2 ^ r.live.card * r.gs.length) := Pol.mul pP pN (fun _ _ => le_refl _)
  have hS := Pol.add (Pol.add (Pol.mul (Pol.const 20) hPN (fun _ _ => le_refl _))
    (Pol.mul (Pol.const 20) pP (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (Pol.add (Pol.mul (Pol.const 20) pN (fun _ _ => le_refl _)) (Pol.const 40) (fun _ _ => le_refl _))
    (fun _ _ => le_refl _)
  refine Pol.mono hS (fun q r => ?_)
  have hp : 1 ≤ 2 ^ r.live.card := Nat.one_le_two_pow
  simp only [localBudget6, BinaryCacheColdPoolCount.budget, WilliamsUnaryProduct.budget, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  have e1 : 2 ^ r.live.card - 1 + 1 = 2 ^ r.live.card := by omega
  rw [e1]
  have e2 : 2 ^ r.live.card * (2 * r.gs.length + 3) = 2 * (2 ^ r.live.card * r.gs.length) + 3 * 2 ^ r.live.card := by
    ring
  rw [e2]
  omega

theorem p9 : Pol (fun _ r => localBudget9 r) := by
  have hC : Pol (fun _ r => 2 ^ r.live.card * r.gs.length + 1) :=
    Pol.add (Pol.mul pP pN (fun _ _ => le_refl _)) (Pol.const 1) (fun _ _ => le_refl _)
  have hH : Pol (fun _ r => EquationNaturalHeader.budget (2 ^ r.live.card * r.gs.length + 1)) := by
    refine Pol.mono (Pol.add (Pol.add (Pol.mul (Pol.const 16) (Pol.pow hC 2 (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
      (Pol.mul (Pol.const 82) hC (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (Pol.const 62) (fun _ _ => le_refl _))
      (fun q r => ?_)
    have := nbl_le (2 ^ r.live.card * r.gs.length + 1)
    simp only [EquationNaturalHeader.budget]
    generalize 2 ^ r.live.card * r.gs.length = PN at *
    omega
  have hq : Pol (fun q r => (q - r.live.card) * ((intWord 0).length + 3)) :=
    Pol.mul (Pol.mono pq (fun q r => Nat.sub_le q r.live.card)) (Pol.const _) (fun _ _ => le_refl _)
  refine Pol.mono (Pol.add (Pol.add hH (Pol.mul (Pol.const 2) hC (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (Pol.add hq (Pol.const ((intWord 1).length + 20)) (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (fun q r => ?_)
  have := nbl_le (2 ^ r.live.card * r.gs.length + 1)
  simp only [localBudget9, BinaryCachePrefix.budget, PCPPNativeNaturalAppend.budget, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  generalize 2 ^ r.live.card * r.gs.length = PN at *
  omega

/-- The hardwire parameters `B = L + 2`, `w = L + 1`: one quadratic `(B+q+w+1)^2`. -/
theorem pQ : Pol (fun q r => ((exactListWord r.gs).length + 2 + q + ((exactListWord r.gs).length + 1) + 1) ^ 2) :=
  Pol.pow (Pol.add (Pol.add (Pol.mul (Pol.const 2) pL (fun _ _ => le_refl _)) pq (fun _ _ => le_refl _))
    (Pol.const 4) (fun q r => by omega)) 2 (fun _ _ => le_refl _)

theorem pRaw : Pol (fun _ r => HardwireAssignmentsRaw.budget r.live r.gs r.B r.w) := by
  have hNB : Pol (fun q r => r.gs.length * (16384 * ((exactListWord r.gs).length + 2 + q +
      ((exactListWord r.gs).length + 1) + 1) ^ 2 + 3)) :=
    Pol.mul pN (Pol.add (Pol.mul (Pol.const 16384) pQ (fun _ _ => le_refl _)) (Pol.const 3) (fun _ _ => le_refl _))
      (fun _ _ => le_refl _)
  refine Pol.mono (Pol.add (Pol.add (Pol.add hNB (Pol.mul (Pol.const 4096) pQ (fun _ _ => le_refl _))
    (fun _ _ => le_refl _)) (Pol.add (Pol.mul (Pol.const 4) pK (fun _ _ => le_refl _))
      (Pol.mul (Pol.const 8) pq (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (Pol.add (Pol.mul (Pol.const 2) pW (fun _ _ => le_refl _)) (Pol.const 33) (fun _ _ => le_refl _))
    (fun _ _ => le_refl _)) (fun q r => ?_)
  simp only [HardwireAssignmentsRaw.budget, HardwireCacheLoop.budget, HardwireCacheLoop.bodyBudget, HardwireBudget.R,
    Args.B, Args.w, Args.L, Args.N, Args.K, Args.W]
  omega

theorem pRes : Pol (fun _ r => HardwireAssignments.reserve r.live r.gs r.B r.w (2 * r.live.card)) := by
  refine Pol.mono (Pol.add (Pol.add pRaw (Pol.mul (Pol.const 1024) pQ (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (Pol.add (Pol.add pN pq (fun _ _ => le_refl _)) (Pol.add (Pol.mul (Pol.const 3) pK (fun _ _ => le_refl _))
      (Pol.const 100) (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (fun q r => ?_)
  simp only [HardwireAssignments.reserve, HardwireBudget.R, Args.B, Args.w, Args.L, Args.N, Args.K, Args.W]
  omega

theorem p10 : Pol (fun _ r => localBudget10 r) := by
  have hcb : Pol (fun q r => HardwireAssignments.callbackBudget r.live r.gs r.B r.w (2 * r.live.card)) :=
    Pol.mono (Pol.add (Pol.add (Pol.mul (Pol.const 2) pRaw (fun _ _ => le_refl _))
      (Pol.mul (Pol.const 4) pRes (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (Pol.const 12)
      (fun _ _ => le_refl _)) (fun q r => by simp only [HardwireAssignments.callbackBudget]; omega)
  have hin : Pol (fun q r => HardwireAssignments.callbackBudget r.live r.gs r.B r.w (2 * r.live.card) +
      4 * r.live.card + 6) :=
    Pol.add (Pol.add hcb (Pol.mul (Pol.const 4) pK (fun _ _ => le_refl _)) (fun _ _ => le_refl _)) (Pol.const 6)
      (fun _ _ => le_refl _)
  have hE : Pol (fun q r => BinaryEnumerator.budget r.live.card
      (HardwireAssignments.callbackBudget r.live r.gs r.B r.w (2 * r.live.card))) := by
    refine Pol.mono (Pol.add (Pol.mul pP hin (fun _ _ => le_refl _)) (Pol.add hcb (Pol.const 4) (fun _ _ => le_refl _))
      (fun _ _ => le_refl _)) (fun q r => ?_)
    have := Nat.mul_le_mul_right (HardwireAssignments.callbackBudget r.live r.gs r.B r.w (2 * r.live.card) +
      4 * r.live.card + 6) (Nat.sub_le (2 ^ r.live.card) 1)
    simp only [BinaryEnumerator.budget]
    omega
  refine Pol.mono (Pol.add (Pol.add (Pol.mul (Pol.const 2) pRes (fun _ _ => le_refl _)) (Pol.const 7)
    (fun _ _ => le_refl _)) hE (fun _ _ => le_refl _)) (fun q r => ?_)
  simp only [localBudget10, BinaryCacheColdInitialize.budget, BinaryCacheColdPalette.U, BinaryCacheColdPalette.S,
    HardwireAssignments.budget, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  omega

/-- **The cold-cache budget is a fixed polynomial** in `X = |exactListWord gs| + |gs| + q + 2^|live| + 1`. -/
theorem coldBudget_pol : Pol (fun _ r => BinaryCacheColdRun.budget r) := by
  have h7 : Pol (fun q _ => 2 * q + 8) :=
    Pol.add (Pol.mul (Pol.const 2) pq (fun _ _ => le_refl _)) (Pol.const 8) (fun _ _ => le_refl _)
  have hs := Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add p1 p2 (fun _ _ => le_refl _)) p3
    (fun _ _ => le_refl _)) p4 (fun _ _ => le_refl _)) p6 (fun _ _ => le_refl _)) h7 (fun _ _ => le_refl _)) p9
    (fun _ _ => le_refl _)) (Pol.add p10 (Pol.const 20) (fun _ _ => le_refl _)) (fun _ _ => le_refl _)
  refine Pol.mono (Pol.mul (Pol.const 2) (Pol.add hs (Pol.const 1) (fun _ _ => le_refl _)) (fun _ _ => le_refl _))
    (fun q r => ?_)
  simp only [BinaryCacheColdRun.budget, BinaryCacheColdRun.rawBudget, budget9, budget8, budget7, budget6, budget5,
    budget4, budget3, budget2, budget1, localBudget5, localBudget7, localBudget8, Args.L, Args.N, Args.K, Args.W, Args.B, Args.w, Args.poolCount]
  omega

theorem coldBudget_poly : ∃ cc dc : ℕ, ∀ (q : ℕ) (r : NearCubicWires.P1Closure.BinaryCacheColdJoin.Args q),
    NearCubicWires.P1Closure.BinaryCacheColdRun.budget r ≤
      cc * ((RepairRepresentation.exactListWord r.gs).length + r.gs.length + q + 2 ^ r.live.card + 1) ^ dc :=
  coldBudget_pol

end NearCubicWires.SourceBudget.Cold

