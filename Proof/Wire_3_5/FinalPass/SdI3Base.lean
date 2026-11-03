import Proof.Wire_3_5.FinalPass.SdI2Base

/-! # S4 (the seeds phase), part 52: the call's sizes below one polynomial `X = KX·(n+2)^{ZX}` (P3:3170-3178)

At a star call of the family every size the seeds phase's hypotheses name is at most `Xf n = KX·(n+2)^{ZX}`
(`AtomsX`, **`atoms_of`**: `n + 2`, the filter's `len, cap, errExp + 1`, the seeds `|E|`, the mask lengths, the
tables' widths `Hof`, the filter tables; `x_vsym`, `x_vthr`: the per-point values; `x_T`: the width `Tf`;
`x_ssz`/`x_sfn`, `x_tsz`/`x_tfn`: the evaluators' sizes and their `need`, `bound`), with `KX`, `ZX` from the literals,
the gate, the SYM evaluator's constants and the two size polynomials only (`SymSizeOK`, `ThrSizeOK`, the named
producers and `ThrSz.thrSize_poly`).

Paper quantity of the main type: the call's sizes, polynomial in `n` (P3:3170-3178, "All powers of `n` are fixed
before a fixed `r`", P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 symCallOf thrCallOf thrWords thrNums)

theorem lift {q c z K Z N : ℕ} (hN : 1 ≤ N) (hq : q ≤ c * N ^ z) (hc : c ≤ K) (hz : z ≤ Z) : q ≤ K * N ^ Z :=
  hq.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hN hz))

/-- A size below `Cs·N^{Ds}` through a polynomial bound `C·(·+1)^D`. -/
theorem poly_comp (C D Cs Ds N sz v : ℕ) (hf : v ≤ C * (sz + 1) ^ D) (hsz : sz ≤ Cs * N ^ Ds) (hN : 1 ≤ N) :
    v + 1 ≤ ((C + 1) * (Cs + 1) ^ D) * N ^ (Ds * D) := by
  have hp : 1 ≤ N ^ Ds := Nat.one_le_pow _ _ hN
  have h1 : sz + 1 ≤ (Cs + 1) * N ^ Ds := by rw [Nat.add_mul, one_mul]; omega
  have h2 : (sz + 1) ^ D ≤ (Cs + 1) ^ D * N ^ (Ds * D) := by
    rw [pow_mul, ← mul_pow]; exact Nat.pow_le_pow_left h1 D
  have h3 : 1 ≤ (Cs + 1) ^ D * N ^ (Ds * D) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h4 := Nat.mul_le_mul_left C h2
  have e : (C + 1) * (Cs + 1) ^ D * N ^ (Ds * D) = C * ((Cs + 1) ^ D * N ^ (Ds * D)) + (Cs + 1) ^ D * N ^ (Ds * D) := by
    ring
  rw [e]
  omega

/-- **The sizes the seeds phase's hypotheses name**, at most `X`. -/
structure AtomsX (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (X : ℕ) : Prop where
  n2 : P.n + 2 ≤ X
  len : FP.len ≤ X
  cap : FP.cap ≤ X
  err : FP.errExp + 1 ≤ X
  G : Fintype.card (GapSeed FP) ≤ X
  car2 : carriers.length ≤ 2
  cl : ∀ k, Seams.carLen carriers k ≤ X
  hof : ∀ k, Hof carriers k ≤ X
  tabH : ∀ k (hk : k < carriers.length), PrimT.tabH (carriers.get ⟨k, hk⟩) ≤ X
  mask : ∀ k (hk : k < carriers.length), (maskGates (carriers.get ⟨k, hk⟩)).length ≤ X
  tbl : ∀ (e : GapSeed FP) k (hk : k < carriers.length),
    (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, hk⟩)).length)).length ≤ X

theorem hof_get {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) (hk : k < carriers.length) (h2 : k < 2) :
    Hof carriers ⟨k, h2⟩ = PrimT.tabH (carriers.get ⟨k, hk⟩) := by
  unfold Hof; exact dif_pos hk

theorem clog_le (N : ℕ) : Nat.clog 2 N ≤ N := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem hof35 (n : ℕ) : (n + 1) ^ 26 * (8 * n + 19 + 8 * (n + 1) ^ 26) ≤ 35 * (n + 2) ^ 52 := by
  have h1 : (n + 1) ^ 26 ≤ (n + 2) ^ 26 := Nat.pow_le_pow_left (by omega) 26
  have h2 : n + 2 ≤ (n + 2) ^ 26 := Nat.le_self_pow (by norm_num) _
  have e : (n + 2) ^ 52 = (n + 2) ^ 26 * (n + 2) ^ 26 := by rw [← pow_add]
  rw [e]
  generalize (n + 2) ^ 26 = y at h1 h2 ⊢
  generalize (n + 1) ^ 26 = x at h1 ⊢
  calc x * (8 * n + 19 + 8 * x) ≤ y * (35 * y) := Nat.mul_le_mul h1 (by omega)
    _ = 35 * (y * y) := by ring

theorem tbl771 (FP : GapParams) (e : GapSeed FP) (L n c : ℕ) (hE : FP.errExp + 1 ≤ c * (n + 2))
    (hL : L ≤ 2 * (n + 2) ^ 26) : (tableWord (filterTable FP e L)).length ≤ 771 * c * (n + 2) ^ 27 := by
  have h0 := tbl_len FP e L
  have hy : 1 ≤ (n + 2) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have e27 : (n + 2) ^ 27 = (n + 2) ^ 26 * (n + 2) := pow_succ _ _
  rw [e27]
  generalize (n + 2) ^ 26 = y at hL hy ⊢
  generalize n + 2 = N at hE ⊢
  have h1 : (FP.errExp + 1) * (258 + 256 * L) ≤ (c * N) * (258 + 512 * y) := Nat.mul_le_mul hE (by omega)
  have h2 : c * N ≤ c * N * y := Nat.le_mul_of_pos_right _ hy
  have e1 : (c * N) * (258 + 512 * y) = 258 * (c * N) + 512 * (c * N * y) := by ring
  have e2 : 771 * c * (y * N) = 771 * (c * N * y) := by ring
  rw [e2]
  have h3 : 0 < c * N * y ∨ c * N * y = 0 := by omega
  rcases h3 with h3 | h3
  · omega
  · have : FP.errExp + 1 ≤ 0 := by
      have : c * N = 0 := by
        rcases Nat.eq_zero_or_pos (c * N) with h | h
        · exact h
        · exfalso; have := Nat.mul_pos h hy; omega
      omega
    omega

section Family
variable (l : Literals) 

variable (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The SYM evaluator's size at a call. -/
def symSize (E : SymPtEval2) (k : Seams.SymCall) : ℕ := k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

