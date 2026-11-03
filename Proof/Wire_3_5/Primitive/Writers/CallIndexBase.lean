import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.EndpointBase
import Proof.Wire_3_5.Filters.FilterGap
import Proof.Wire_3_5.Lists.ListFlatten
import Proof.Wire_3_5.Rows.RowsSampler
import Proof.CaseAnalysis.FinalPrimeWindow

/-! # PA params: the index counts of a call are polynomial in `n`

The sampler of `samp:printable` is run at "`Q = O(2^{(5k_h+3)/4}·|T|·n^{2D})`" samples for the call's `|T|` state
matrices per column (P3:2987-2988, 3154-3162); C4's `Sampler.sampleCount_le` bounds `Q` by `2^{⌈3k/4⌉}·n^{13+C+2D}`
PROVIDED the index count `I = |T|·𝔐² + 1` is at most `n^C`. This module produces that `C` at every call of the gate:
- **`symIndex_le`**: `|SymIndex|·symMassNat² + 1 ≤ n^C` (SYM: the filter seeds, the amplified lists' seeds, the joint
  states `Π_j(m_j+1)²`, and `2𝔐 = 2Π(m_j+1)²ΠP_j`);
- **`thrIndex_le`**: `|ThrIndex|·thrMassNat² + 1 ≤ n^C` (THR: the filter seeds, the equations `|𝒢|` of
  `selection_count`, the prime rows `Σ_{p ≤ cutoff} p`, and `2|𝒢|·cutoff + 1`);
- **`seedSpace_le`**: `|GapSeed × FlatSeed| ≤ n^{C_s}` (the seed space the final pass sums over).
Each `C` depends only on the gate's constants (the literals, `c_r`, `fe`), never on the call.

The per-call facts used: `I.Call` (`descriptionBits ≤ (n+1)^26`, at most two carriers, `a ≤ 4`) and `StarAt`
(`n ≥ 8`). Donors: base `selection_count`, `familyMagnitudeExponent_le`, `canonicalPrimeCutoff_mono`, `primesUpTo`;
`Filters.card_gapSeed`/`seedBits_le`; `Lists.FlatListParams.card_flatSeed`; `Rows.card_symState`; `Gate0.gateSp_le`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CallIndex
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

/-! ## Powers of `N` -/

section Pow
variable {N : ℕ}

theorem pw_const (hN : 2 ≤ N) (c : ℕ) : c ≤ N ^ c := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hN c)

theorem pw_mul {x y a b : ℕ} (hx : x ≤ N ^ a) (hy : y ≤ N ^ b) : x * y ≤ N ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem pw_pow {x a : ℕ} (hx : x ≤ N ^ a) (k : ℕ) : x ^ k ≤ N ^ (a * k) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx k

theorem pw_clog {x a : ℕ} (hx : x ≤ N ^ a) : Nat.clog 2 x ≤ a * Nat.clog 2 N := by
  apply Nat.clog_le_of_le_pow
  calc x ≤ N ^ a := hx
    _ ≤ (2 ^ Nat.clog 2 N) ^ a := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) N) a
    _ = 2 ^ (a * Nat.clog 2 N) := by rw [← pow_mul, Nat.mul_comm]

theorem two_pow_clog_le (hN : 2 ≤ N) : 2 ^ Nat.clog 2 N ≤ N ^ 2 := by
  have hpos : 1 ≤ Nat.clog 2 N := Nat.clog_pos (by norm_num) (by omega)
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < N by omega)
  have e : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : 2 * N ≤ N ^ 2 := by nlinarith
  simp only [Nat.pred_eq_sub_one] at h
  rw [e]; omega

theorem pw_two_pow_clog (hN : 2 ≤ N) (k : ℕ) : 2 ^ (k * Nat.clog 2 N) ≤ N ^ (2 * k) :=
  calc 2 ^ (k * Nat.clog 2 N) = (2 ^ Nat.clog 2 N) ^ k := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (N ^ 2) ^ k := Nat.pow_le_pow_left (two_pow_clog_le hN) k
    _ = N ^ (2 * k) := by rw [← pow_mul]

end Pow

/-! ## The gate's cap and filter seeds, at `N = n + 2` -/

section Gate
variable (l : Literals) 

theorem Lq_le_N (n : ℕ) : Ledger.Lq n ≤ n + 2 := by have := Ledger.Lq_le n; omega

theorem pw_succ_const {N : ℕ} (hN : 2 ≤ N) (c : ℕ) : c + 1 ≤ N ^ c :=
  le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_left hN c)

theorem rowBCap_le (C : Ledger.CapParams) (m : Mode) (r s q : ℕ) :
    Ledger.rowBCap C m r s q ≤
      1 + (Ledger.capMainNum C m r s q + Ledger.Lq q ^ Ledger.capExp32 m) + Ledger.capEncPow C r q := by
  unfold Ledger.rowBCap Ledger.capMainPow
  have h1 := Ledger.ceilRoot_le_self 31
    ((Ledger.capMainNum C m r s q + Ledger.Lq q ^ Ledger.capExp32 m - 1) / Ledger.Lq q ^ Ledger.capExp32 m)
  have h2 := Ledger.ceilRoot_le_self 1 (Ledger.capEncPow C r q)
  have h3 := Nat.div_le_self (Ledger.capMainNum C m r s q + Ledger.Lq q ^ Ledger.capExp32 m - 1)
    (Ledger.Lq q ^ Ledger.capExp32 m)
  omega

theorem capExp32_le (m : Mode) : Ledger.capExp32 m ≤ 174 := by cases m <;> decide

end Gate

/-! ## SYM calls -/

section Sym
variable (l : Literals) 

theorem prod_le_pow4 {a : ℕ} (ha : a ≤ 4) (f : Fin a → ℕ) {N X : ℕ} (hN : 1 ≤ N) (h : ∀ j, f j ≤ N ^ X) :
    ∏ j, f j ≤ N ^ (X * 4) := by
  calc ∏ j, f j ≤ ∏ _j : Fin a, N ^ X := Finset.prod_le_prod' (fun j _ => h j)
    _ = (N ^ X) ^ a := by simp
    _ ≤ (N ^ X) ^ 4 := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hN) ha
    _ = N ^ (X * 4) := by rw [← pow_mul]

theorem bottomCount_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (h : C.descriptionBits ≤ (n + 1) ^ 26) :
    C.bottomCount ≤ (n + 1) ^ 26 := by
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits at h; omega

theorem succ_le_N26 (n : ℕ) : (n + 1) ^ 26 + 1 ≤ (n + 2) ^ 26 := by
  have h1 : (n + 1) ^ 26 < (n + 2) ^ 26 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-- The walk's constant (kept symbolic). -/
def wC : ℕ := 400

end Sym

/-! ## THR calls -/

section Thr
variable (l : Literals) 
open NearCubicWires.WireExponent3_5.PrimAsm.Endpoint

/-- The prime rows `Σ_{p ≤ c} |ZMod p|`. -/
theorem sigma_le (c : ℕ) : Fintype.card (Σ pr : SupplierPrime.PrimeIndex c, ZMod pr.val) ≤ (c + 1) * c := by
  rw [Fintype.card_sigma]
  have h1 : ∀ pr : SupplierPrime.PrimeIndex c, Fintype.card (ZMod pr.val) ≤ c := by
    intro pr; rw [ZMod.card]; exact (SupplierPrime.mem_primesUpTo.mp pr.2).2
  calc ∑ pr, Fintype.card (ZMod pr.val) ≤ ∑ _pr : SupplierPrime.PrimeIndex c, c :=
        Finset.sum_le_sum (fun pr _ => h1 pr)
    _ = Fintype.card (SupplierPrime.PrimeIndex c) * c := by simp
    _ ≤ (c + 1) * c := Nat.mul_le_mul_right _ (by
        rw [Fintype.card_coe]; exact RepairOrdinary.CloseoutFinalC10WireEnvelope.primesUpTo_card_le c)

end Thr

/-! ## The index counts -/

section Index

end Index

end NearCubicWires.WireExponent3_5.PrimAsm.CallIndex
