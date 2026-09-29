import Proof.CaseAnalysis.FinalPrimeWindow
import Proof.Wire_3_5.Primitive.Writers.Endpoint

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
variable (l : Literals) (F : GateFree l)

theorem Lq_le_N (n : ℕ) : Ledger.Lq n ≤ n + 2 := by have := Ledger.Lq_le n; omega

theorem pw_succ_const {N : ℕ} (hN : 2 ≤ N) (c : ℕ) : c + 1 ≤ N ^ c :=
  le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_left hN c)

theorem sp_le (n : ℕ) : gateSp l n ≤ (n + 2) ^ (gateCsp l + 3) := by
  have hN : 2 ≤ n + 2 := by omega
  have h8 : gateSp l n ≤ gateSp l n ^ 8 := Nat.le_self_pow (by norm_num) _
  have h := gateSp_le l n
  have hL3 : Ledger.Lq n ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (Lq_le_N n) 3
  have hc := pw_const hN (gateCsp l)
  calc gateSp l n ≤ gateCsp l * Ledger.Lq n ^ 3 := le_trans h8 h
    _ ≤ (n + 2) ^ gateCsp l * (n + 2) ^ 3 := Nat.mul_le_mul hc hL3
    _ = (n + 2) ^ (gateCsp l + 3) := by rw [← pow_add]

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

theorem gateCoef (m : Mode) : (gateCap l).coef m = 1 := by cases m <;> rfl

theorem capExp32_le (m : Mode) : Ledger.capExp32 m ≤ 174 := by cases m <;> decide

end Gate

/-! ## SYM calls -/

section Sym
variable (l : Literals) (F : GateFree l)

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

/-- The joint states `Π_j (m_j + 1)²` of a call. -/
theorem symState_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Fintype.card (Rows.SymState (Primitive.symM ((callInputs l F kclk coef A a ha).starParams n hs) Cs)) ≤
      (n + 2) ^ (52 * 4) := by
  rw [Rows.card_symState]
  refine prod_le_pow4 ha' _ (by omega) (fun j => ?_)
  have h1 : (Cs j).bottomCount + 1 ≤ (n + 2) ^ 26 := by
    have := bottomCount_le (Cs j) (hd j); have := succ_le_N26 n; omega
  show ((Cs j).bottomCount + 1) ^ 2 ≤ (n + 2) ^ 52
  calc ((Cs j).bottomCount + 1) ^ 2 ≤ ((n + 2) ^ 26) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = (n + 2) ^ 52 := by rw [← pow_mul]

/-- The SYM mass `2𝔐 = 2Π(m_j+1)²ΠP_j` of a call. -/
theorem symMass_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    SeedFix.symMassNat (callInputs l F kclk coef A a ha) hs Cs ≤ (n + 2) ^ (1 + (52 * 4 + 29 * 4)) := by
  have hN : 2 ≤ n + 2 := by omega
  have hst := symState_le l F kclk coef A a ha n hs ha' Cs hd
  rw [Rows.card_symState] at hst
  have hmod : ∏ j, Rows.symModulus (Primitive.symM ((callInputs l F kclk coef A a ha).starParams n hs) Cs j) ≤
      (n + 2) ^ (29 * 4) := by
    refine prod_le_pow4 ha' _ (by omega) (fun j => ?_)
    have h1 := bottomCount_le (Cs j) (hd j)
    have h26 : (n + 1) ^ 26 ≤ (n + 2) ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have h8 : 8 ≤ (n + 2) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hN 3
    show 6 * (Cs j).bottomCount + 2 ≤ (n + 2) ^ 29
    have hp : 1 ≤ (n + 2) ^ 26 := Nat.one_le_pow _ _ (by omega)
    have e : (n + 2) ^ 29 = (n + 2) ^ 3 * (n + 2) ^ 26 := by rw [← pow_add]
    rw [e]; nlinarith
  have h2 : 2 ≤ (n + 2) ^ 1 := by rw [pow_one]; omega
  unfold SeedFix.symMassNat
  exact pw_mul h2 (pw_mul hst hmod)

end Sym

/-! ## THR calls -/

section Thr
variable (l : Literals) (F : GateFree l)
open NearCubicWires.WireExponent3_5.PrimAsm.Endpoint

/-- The decomposition's exponent at the gate: `X = c + 28d`. -/
noncomputable def algX : ℕ := (gateAlg l).coefficient + 28 * (gateAlg l).degree

/-- `sourceChildBound + 1 ≤ N^{c + 28d}` at `desc = (n+1)^{26}` (the steps of `Endpoint.count_le_pow`). -/
theorem scb_le (n : ℕ) :
    RepairSource.CloseoutRawRows.sourceChildBound (gateAlg l) ((n + 1) ^ 26) + 1 ≤ (n + 2) ^ algX l := by
  unfold RepairSource.CloseoutRawRows.sourceChildBound algX
  set c := (gateAlg l).coefficient
  set d := (gateAlg l).degree
  have h2 : 2 ≤ n + 2 := by omega
  have hA : (n + 1) ^ 26 + 2 ≤ (n + 2) ^ 28 := by
    have e1 : (n + 1) ^ 26 ≤ (n + 2) ^ 26 := Nat.pow_le_pow_left (by omega) _
    have e2 : 4 ≤ (n + 2) ^ 2 := by nlinarith
    have e3 : 1 ≤ (n + 2) ^ 26 := Nat.one_le_pow _ _ (by omega)
    calc (n + 1) ^ 26 + 2 ≤ (n + 2) ^ 26 * 4 := by omega
      _ ≤ (n + 2) ^ 26 * (n + 2) ^ 2 := Nat.mul_le_mul_left _ e2
      _ = (n + 2) ^ 28 := by rw [← pow_add]
  have hB : ((n + 1) ^ 26 + 2) ^ d ≤ (n + 2) ^ (28 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hA d
  have hX : 1 ≤ (n + 2) ^ (28 * d) := Nat.one_le_pow _ _ (by omega)
  have hc : c + 1 ≤ (n + 2) ^ c := pw_succ_const h2 c
  calc c * ((n + 1) ^ 26 + 2) ^ d + 1 ≤ c * (n + 2) ^ (28 * d) + (n + 2) ^ (28 * d) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hB) hX
    _ = (c + 1) * (n + 2) ^ (28 * d) := by ring
    _ ≤ (n + 2) ^ c * (n + 2) ^ (28 * d) := Nat.mul_le_mul_right _ hc
    _ = (n + 2) ^ (c + 28 * d) := by rw [← pow_add]

theorem thrDesc (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    ∀ c ∈ (Primitive.thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs).circuits,
      c.descriptionBits ≤ (n + 1) ^ 26 := by
  intro c hc
  rw [List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  exact hd i

/-- `|𝒢| ≤ N^{4X}` (base `selection_count`). -/
theorem thrEq_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) ≤
      (n + 2) ^ (algX l * 4) := by
  have hfour : (Primitive.thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs).circuits.length ≤ 4 := by
    simp only [List.length_ofFn]; exact ha'
  have h := RepairSource.CloseoutRawRows.selection_count (gate0 l F).alg
    (Primitive.thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs) ((n + 1) ^ 26) hfour
    (thrDesc l F kclk coef A a ha n hs Cs hd)
  exact le_trans h (pw_pow (scb_le l n) 4)

/-- The prime surrogate's denominator `8(|𝒢|+1)n^D`. -/
theorem den_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      (n + 2) ^ (3 + (algX l * 4 + 1) + 1) := by
  have hN : 2 ≤ n + 2 := by omega
  have e : Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs =
      8 * (Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) + 1) *
        n ^ 1 := rfl
  rw [e]
  have h8 : 8 ≤ (n + 2) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hN 3
  have hc1 : Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) + 1
      ≤ (n + 2) ^ (algX l * 4 + 1) := by
    have h := thrEq_le l F kclk coef A a ha n hs ha' Cs hd
    have hp : 1 ≤ (n + 2) ^ (algX l * 4) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]; nlinarith
  have hn : n ^ 1 ≤ (n + 2) ^ 1 := Nat.pow_le_pow_left (by omega) 1
  exact pw_mul (pw_mul h8 hc1) hn

/-- The family's magnitude exponent (base `familyMagnitudeExponent_le`). -/
theorem fme_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    SupplierPrime.familyMagnitudeExponent
        (Primitive.thrRealize ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) ≤
      (n + 2) ^ (algX l + 5) := by
  have hN : 2 ≤ n + 2 := by omega
  have hfour : (Primitive.thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs).circuits.length ≤ 4 := by
    simp only [List.length_ofFn]; exact ha'
  have h := RepairOrdinary.CloseoutFinalC10PrimeWindow.familyMagnitudeExponent_le (gate0 l F).alg
    (Primitive.thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs) ((n + 1) ^ 26) hfour
    (thrDesc l F kclk coef A a ha n hs Cs hd)
  refine le_trans h ?_
  unfold RepairOrdinary.CloseoutFinalC10PrimeWindow.tupleExponentBound
    RepairSource.CloseoutRawRows.thresholdMagnitudeExponent
  have hV := scb_le l n
  set V := RepairSource.CloseoutRawRows.sourceChildBound (gateAlg l) ((n + 1) ^ 26) with hVd
  have hc : Nat.clog 2 (V + 1) ≤ V + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h32 : 32 ≤ (n + 2) ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left hN 5
  have e : (n + 2) ^ (algX l + 5) = (n + 2) ^ algX l * (n + 2) ^ 5 := by rw [pow_add]
  have hg : (gate0 l F).alg = gateAlg l := rfl
  rw [hg, e]
  nlinarith

/-- The prime cutoff `(max 24 (6(e+1)(K+1)))²` (base `canonicalPrimeCutoff`). -/
theorem cut_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
        (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤
      (n + 2) ^ (10 * algX l + 32) := by
  have hN : 2 ≤ n + 2 := by omega
  have he := fme_le l F kclk coef A a ha n hs ha' Cs hd
  have hk := den_le l F kclk coef A a ha n hs ha' Cs hd
  set e := SupplierPrime.familyMagnitudeExponent
    (Primitive.thrRealize ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) with hed
  set K := Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs with hKd
  have hp0 : 1 ≤ (n + 2) ^ (algX l + 5) := Nat.one_le_pow _ _ (by omega)
  have hp1 : 1 ≤ (n + 2) ^ (3 + (algX l * 4 + 1) + 1) := Nat.one_le_pow _ _ (by omega)
  have he1 : e + 1 ≤ (n + 2) ^ (algX l + 6) := by rw [pow_succ]; nlinarith
  have hk1 : K + 1 ≤ (n + 2) ^ (4 * algX l + 6) := by
    have e1 : (n + 2) ^ (4 * algX l + 6) = (n + 2) ^ (3 + (algX l * 4 + 1) + 1) * (n + 2) := by
      rw [← pow_succ]; congr 1; ring
    rw [e1]; nlinarith
  have h6 : 6 ≤ (n + 2) ^ 3 := by
    calc 6 ≤ 2 ^ 3 := by norm_num
      _ ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hN 3
  have hprod : 6 * (e + 1) * (K + 1) ≤ (n + 2) ^ (3 + (algX l + 6) + (4 * algX l + 6)) :=
    pw_mul (pw_mul h6 he1) hk1
  have h24 : 24 ≤ (n + 2) ^ 5 := by
    calc 24 ≤ 2 ^ 5 := by norm_num
      _ ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left hN 5
  have hm5 : (n + 2) ^ 5 ≤ (n + 2) ^ (3 + (algX l + 6) + (4 * algX l + 6)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hmax : max 24 (6 * (e + 1) * (K + 1)) ≤ (n + 2) ^ (5 * algX l + 16) := by
    have e2 : (n + 2) ^ (5 * algX l + 16) = (n + 2) ^ (3 + (algX l + 6) + (4 * algX l + 6)) * (n + 2) := by
      rw [← pow_succ]; congr 1; ring
    rw [e2]
    have := max_le_add_of_nonneg (show (0 : ℕ) ≤ 24 by omega) (show 0 ≤ 6 * (e + 1) * (K + 1) by omega)
    nlinarith
  unfold Primitive.thrCutoff SupplierPrime.canonicalPrimeCutoff SupplierPrime.canonicalPrimeScale
  calc (max 24 (6 * (e + 1) * (K + 1))) ^ 2 ≤ ((n + 2) ^ (5 * algX l + 16)) ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = (n + 2) ^ (10 * algX l + 32) := by rw [← pow_mul]; congr 1; ring

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
variable (l : Literals) (F : GateFree l)

theorem n_ge_two {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ≤ n := by
  have h1 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := hs.2.1
  have h2 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := hs.2.2.1
  omega

end Index

end NearCubicWires.WireExponent3_5.PrimAsm.CallIndex
