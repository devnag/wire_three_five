import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.SymQ

/-! # PA (e), part 1: the call's counts with `c_r`-free exponents

`prim:runtime` (P3:3114-3115): "All powers of `n` are fixed before a fixed `r` or a positive endpoint coefficient is
chosen." Leaf P's children choose their floors `E₄, E₅` after `fe` and BEFORE the free constants `F` (so before
`c_r`); only the coefficients `c₄, c₅` come after `F`. `CallIndex` bounds the counts by
`n^{2·symZ}` with `symZ` depending on `c_r` (through the cap's exponent); that bound serves but not the class
links. Here every count is `K·N^Z` with `N = n + 2`, the constant `K` a function of `c_r` (it goes into `c₄, c₅`), and
the exponent `Z` a function of the literals `l` and of `fe` ONLY (its arguments say so):

* `cap_leR`: `B_m(n) ≤ capK c_r·N^{capZR l}` (the multiplier `r = 2(⌊log₂ L⌋ + c_r) ≤ (2c_r+2)·N`);
* `gapSeed_leR`, `flatSeed_leR`: the filter's and the list's seeds;
* `symI_leR`, `thrI_leR`: the index counts `I = |T|·(2𝔐)² + 1` of `symCount`, `thrCount`;
* `symCount_leR`, `thrCount_leR`: the sample counts `Q ≤ 2^{(5kh+3)/4}·8192·K·N^{Z+2}`.

Paper quantities of the main types: `SeedFix.symCount`, `SeedFix.thrCount` (`symCount_leR`, `thrCount_leR`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CallIndexR
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.CallIndex

/-! ## Symbolic constants (large literal exponents are never evaluated) -/

def k6 : ℕ := 6000
def k4 : ℕ := 400
def k36 : ℕ := 36

theorem k6_eq : k6 = 6000 := rfl
theorem k4_eq : k4 = 400 := rfl
theorem k36_eq : k36 = 36 := rfl

/-! ## `⌈log₂⌉` of a product and `2^{⌈log₂ x⌉}` -/

theorem clog_mul_le (x y : ℕ) : Nat.clog 2 (x * y) ≤ Nat.clog 2 x + Nat.clog 2 y := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) x) (Nat.le_pow_clog (by norm_num) y)

theorem two_pow_clog_le_two_mul (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) h
    have e : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [Nat.pred_eq_sub_one] at h1
    omega
  · have hx1 : x = 1 := by omega
    subst hx1; simp

theorem clog_KN_le {N K Z x : ℕ} (hx : x ≤ K * N ^ Z) : Nat.clog 2 x ≤ Nat.clog 2 K + Z * Nat.clog 2 N :=
  le_trans (Nat.clog_mono_right 2 hx) (le_trans (clog_mul_le _ _) (Nat.add_le_add_left (pw_clog le_rfl) _))

/-! ## The cap -/

/-- The multiplier `r = 2(⌊log₂ L⌋ + c_r) ≤ (2c_r + 2)·N`. -/
theorem rowBr_leR (cr n : ℕ) : Ledger.rowBr cr n ≤ (2 * cr + 2) * (n + 2) := by
  have h1 : Nat.log 2 (Ledger.Lq n) ≤ n + 2 := le_trans (Nat.log_le_self 2 _) (Lq_le_N n)
  unfold Ledger.rowBr
  nlinarith

/-- The cap's exponent: the literals only. -/
noncomputable def capZR (l : Literals) : ℕ := 500 + 32 * gateCsp l + 34 * gateBetaInv l

/-- The cap's constant: `c_r` only. -/
def capK (cr : ℕ) : ℕ := (2 * cr + 2) ^ 48

theorem capK_pos (cr : ℕ) : 1 ≤ capK cr := Nat.one_le_pow _ _ (by omega)

theorem capMain_leR (l : Literals) (cr : ℕ) (m : Mode) (n : ℕ) {N : ℕ} (hNd : N = n + 2) :
    Ledger.capMainNum (gateCap l) m (Ledger.rowBr cr n) (gateSp l n) n ≤
      capK cr * N ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32) := by
  have hN : 2 ≤ N := by omega
  have hr : Ledger.rowBr cr n ≤ (2 * cr + 2) * N := hNd ▸ rowBr_leR cr n
  have hs : gateSp l n ≤ N ^ (gateCsp l + 3) := hNd ▸ sp_le l n
  have hβ := pw_const hN (gateBetaInv l)
  have hq : n ≤ N := by omega
  unfold Ledger.capMainNum capK
  rw [gateCoef, one_pow, mul_one]
  obtain ⟨E1, hE1⟩ : ∃ E, E = (gateCsp l + 3) * 32 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E, E = gateBetaInv l * 32 := ⟨_, rfl⟩
  have hs32 : gateSp l n ^ 32 ≤ N ^ E1 := hE1 ▸ pw_pow hs 32
  have hβ32 : gateBetaInv l ^ 32 ≤ N ^ E2 := hE2 ▸ pw_pow hβ 32
  have e80 : (2 : ℕ) ^ 80 ≤ N ^ 80 := Nat.pow_le_pow_left hN 80
  have hr48 : Ledger.rowBr cr n ^ 48 ≤ (2 * cr + 2) ^ 48 * N ^ 48 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hr 48
  have hq64 : n ^ 64 ≤ N ^ 64 := Nat.pow_le_pow_left hq 64
  rw [← hE1, ← hE2]
  calc 2 ^ 80 * Ledger.rowBr cr n ^ 48 * gateSp l n ^ 32 * n ^ 64 * gateBetaInv l ^ 32
      ≤ N ^ 80 * ((2 * cr + 2) ^ 48 * N ^ 48) * N ^ E1 * N ^ 64 * N ^ E2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e80 hr48) hs32) hq64) hβ32
    _ = (2 * cr + 2) ^ 48 * N ^ (80 + 48 + E1 + 64 + E2) := by
        simp only [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem capEnc_leR (l : Literals) (cr : ℕ) (n : ℕ) {N : ℕ} (hNd : N = n + 2) :
    Ledger.capEncPow (gateCap l) (Ledger.rowBr cr n) n ≤ capK cr * N ^ (5 + 3 + 2 + 1 + gateBetaInv l * 2) := by
  have hN : 2 ≤ N := by omega
  have hr : Ledger.rowBr cr n ≤ (2 * cr + 2) * N := hNd ▸ rowBr_leR cr n
  have hβ := pw_const hN (gateBetaInv l)
  have hq : n ≤ N := by omega
  have hR : 1 ≤ 2 * cr + 2 := by omega
  have hr3 : Ledger.rowBr cr n ^ 3 ≤ (2 * cr + 2) ^ 48 * N ^ 3 := by
    calc Ledger.rowBr cr n ^ 3 ≤ ((2 * cr + 2) * N) ^ 3 := Nat.pow_le_pow_left hr 3
      _ = (2 * cr + 2) ^ 3 * N ^ 3 := by rw [mul_pow]
      _ ≤ (2 * cr + 2) ^ 48 * N ^ 3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hR (by norm_num))
  have h32 : (32 : ℕ) ≤ N ^ 5 := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ N ^ 5 := Nat.pow_le_pow_left hN 5
  have h2 : (gateCap l).Cpar ^ 2 ≤ N ^ 2 := by
    show 2 ^ 2 ≤ N ^ 2; exact Nat.pow_le_pow_left hN 2
  obtain ⟨E3, hE3⟩ : ∃ E, E = gateBetaInv l * 2 := ⟨_, rfl⟩
  have hβ2 : gateBetaInv l ^ 2 ≤ N ^ E3 := hE3 ▸ pw_pow hβ 2
  unfold Ledger.capEncPow capK
  rw [← hE3]
  calc 32 * Ledger.rowBr cr n ^ 3 * (gateCap l).Cpar ^ 2 * n * gateBetaInv l ^ 2
      ≤ N ^ 5 * ((2 * cr + 2) ^ 48 * N ^ 3) * N ^ 2 * N ^ 1 * N ^ E3 := by
        rw [pow_one]
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h32 hr3) h2) hq) hβ2
    _ = (2 * cr + 2) ^ 48 * N ^ (5 + 3 + 2 + 1 + E3) := by
        simp only [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- **The cap, `c_r` in the constant**: `B_m(n) ≤ capK c_r·N^{capZR l}`. -/
theorem cap_leR (l : Literals) (cr : ℕ) (m : Mode) (n : ℕ) :
    Ledger.rowBCap (gateCap l) m (Ledger.rowBr cr n) (gateSp l n) n ≤ capK cr * (n + 2) ^ capZR l := by
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  rw [← hNd]
  have hN : 2 ≤ N := by omega
  have hnum := capMain_leR l cr m n hNd
  have henc := capEnc_leR l cr n hNd
  have hD : Ledger.Lq n ^ Ledger.capExp32 m ≤ N ^ 174 :=
    le_trans (Nat.pow_le_pow_left (hNd ▸ Lq_le_N n) _) (Nat.pow_le_pow_right (by omega) (capExp32_le m))
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = capZR l := ⟨_, rfl⟩
  rw [← hZd]
  have hZ1 : 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32 ≤ Z - 2 := by rw [hZd]; unfold capZR; omega
  have hZ2 : 174 ≤ Z - 2 := by rw [hZd]; unfold capZR; omega
  have hZ3 : 5 + 3 + 2 + 1 + gateBetaInv l * 2 ≤ Z - 2 := by rw [hZd]; unfold capZR; omega
  have hZ4 : Z = Z - 2 + 2 := by rw [hZd]; unfold capZR; omega
  have hPow : ∀ {e : ℕ}, e ≤ Z - 2 → N ^ e ≤ N ^ (Z - 2) := fun h => Nat.pow_le_pow_right (by omega) h
  have hK := capK_pos cr
  have hP : 1 ≤ N ^ (Z - 2) := Nat.one_le_pow _ _ (by omega)
  have hA := le_trans hnum (Nat.mul_le_mul_left (capK cr) (hPow hZ1))
  have hB := le_trans henc (Nat.mul_le_mul_left (capK cr) (hPow hZ3))
  have hKP : 1 ≤ capK cr * N ^ (Z - 2) := Nat.mul_le_mul hK hP
  have hC : Ledger.Lq n ^ Ledger.capExp32 m ≤ capK cr * N ^ (Z - 2) :=
    le_trans (le_trans hD (hPow hZ2)) (Nat.le_mul_of_pos_left _ (by omega))
  have h4 : 4 ≤ N ^ 2 := by nlinarith
  have hsum : 1 + (Ledger.capMainNum (gateCap l) m (Ledger.rowBr cr n) (gateSp l n) n +
      Ledger.Lq n ^ Ledger.capExp32 m) + Ledger.capEncPow (gateCap l) (Ledger.rowBr cr n) n ≤
      4 * (capK cr * N ^ (Z - 2)) := by omega
  refine le_trans (rowBCap_le _ _ _ _ _) (le_trans hsum ?_)
  calc 4 * (capK cr * N ^ (Z - 2)) = capK cr * (N ^ (Z - 2) * 4) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ capK cr * (N ^ (Z - 2) * N ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
    _ = capK cr * N ^ Z := by rw [← pow_add, ← hZ4]

/-! ## The seeds -/

/-- The filter seeds' constant (`c_r` only) and exponent (`l`, `fe` only). -/
def gapK (cr : ℕ) : ℕ := (8 * capK cr) ^ k6
noncomputable def gapZR (l : Literals) (fe : ℕ) : ℕ := 2 * k6 * (28 + capZR l + fe) + 2 * k6

theorem gapK_pos (cr : ℕ) : 1 ≤ gapK cr := Nat.one_le_pow _ _ (by have := capK_pos cr; omega)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The filter seeds, `c_r` in the constant**: `|GapSeed| ≤ gapK c_r·N^{gapZR l fe}`. -/
theorem gapSeed_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (m : Mode) (n : ℕ) :
    Fintype.card (Filters.GapSeed ((callInputs l F kclk coef A a ha).filterParams m n)) ≤
      gapK F.cr * (n + 2) ^ gapZR l F.filterErrDeg := by
  rw [Filters.card_gapSeed]
  set P := (callInputs l F kclk coef A a ha).filterParams m n with hPd
  have hb := Filters.seedBits_le P
  have e1 : P.len = 2 * (n + 1) ^ 26 := rfl
  have e2 : P.cap = Ledger.rowBCap (gateCap l) m (Ledger.rowBr F.cr n) (gateSp l n) n := rfl
  have herr : P.errExp = F.filterErrDeg * Nat.clog 2 (n + 2) := rfl
  have hc := cap_leR l F.cr m n
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  rw [← hNd] at hc herr ⊢
  have hN : 2 ≤ N := by omega
  have hlen : P.len + 1 ≤ N ^ 28 := by
    rw [e1]
    have h26 : (n + 1) ^ 26 ≤ N ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have hp : 1 ≤ N ^ 26 := Nat.one_le_pow _ _ (by omega)
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    have e3 : N ^ 28 = N ^ 26 * N ^ 2 := by rw [← pow_add]
    rw [e3]; nlinarith
  have hK := capK_pos F.cr
  have hcap : P.cap + 1 ≤ (2 * capK F.cr) * N ^ capZR l := by
    rw [e2]
    have hp : 1 ≤ capK F.cr * N ^ capZR l := Nat.mul_le_mul hK (Nat.one_le_pow _ _ (by omega))
    calc _ ≤ capK F.cr * N ^ capZR l + capK F.cr * N ^ capZR l := by omega
      _ = (2 * capK F.cr) * N ^ capZR l := by rw [Nat.mul_assoc, Nat.two_mul]
  have c1 := pw_clog hlen
  have c2 := clog_KN_le hcap
  have hK2 : 2 ^ (Nat.clog 2 (2 * capK F.cr) + 1) ≤ 8 * capK F.cr := by
    have := two_pow_clog_le_two_mul (2 * capK F.cr) (by omega); rw [pow_succ]; omega
  obtain ⟨W, hWd⟩ : ∃ W, W = 28 + capZR l + F.filterErrDeg := ⟨_, rfl⟩
  have hsb : P.seedBits ≤ k6 * (Nat.clog 2 (2 * capK F.cr) + 1) + (k6 * W) * Nat.clog 2 N := by
    rw [herr, ← k6_eq] at hb; rw [hWd]; nlinarith
  have hL : 2 ^ ((k6 * W) * Nat.clog 2 N) ≤ N ^ (2 * (k6 * W)) := pw_two_pow_clog hN _
  have hKk : 2 ^ (k6 * (Nat.clog 2 (2 * capK F.cr) + 1)) ≤ gapK F.cr := by
    unfold gapK
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hK2 _
  have hZ : 2 * (k6 * W) ≤ gapZR l F.filterErrDeg := by unfold gapZR; rw [hWd]; nlinarith
  calc 2 ^ P.seedBits
      ≤ 2 ^ (k6 * (Nat.clog 2 (2 * capK F.cr) + 1) + (k6 * W) * Nat.clog 2 N) :=
        Nat.pow_le_pow_right (by norm_num) hsb
    _ = 2 ^ (k6 * (Nat.clog 2 (2 * capK F.cr) + 1)) * 2 ^ ((k6 * W) * Nat.clog 2 N) := by rw [pow_add]
    _ ≤ gapK F.cr * N ^ (2 * (k6 * W)) := Nat.mul_le_mul hKk hL
    _ ≤ gapK F.cr * N ^ gapZR l F.filterErrDeg := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hZ)

end Gate

/-- The flattened lists' constant (`c_r` only) and exponent (`l` only). -/
def flatK (cr : ℕ) : ℕ := 2 ^ k36 * (16384 * capK cr) ^ 4 * 2 ^ k4
noncomputable def flatZR (l : Literals) : ℕ := 8 * (capZR l + 28) + 2 * k4

theorem flatK_pos (cr : ℕ) : 1 ≤ flatK cr :=
  Nat.one_le_iff_ne_zero.mpr (by unfold flatK; have := capK_pos cr; positivity)

section Gate2
variable (l : Literals) (F : GateFree l)

/-- **The flattened lists' seeds, `c_r` in the constant**: `|FlatSeed| ≤ flatK c_r·N^{flatZR l}` at a SYM call. -/
theorem flatSeed_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    Fintype.card (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed ≤
      flatK F.cr * (n + 2) ^ flatZR l := by
  rw [Lists.FlatListParams.card_flatSeed]
  set P := Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers with hPd
  have eB : P.B = carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n) :=
    rfl
  have eW1 : P.walkLen - 1 = 2 * (P.errExp / 4) := by show 2 * (P.errExp / 4) + 1 - 1 = _; omega
  have eE : P.errExp = 1 * Nat.clog 2 (n + 2) + 5 := rfl
  have hc := cap_leR l F.cr .sym n
  have hM0 : P.M ≤ 4 * (n + 1) ^ 26 := by
    show ∑ i, (Cs i).bottomCount ≤ _
    have h1 : ∑ i, (Cs i).bottomCount ≤ ∑ _i : Fin a', (n + 1) ^ 26 :=
      Finset.sum_le_sum (fun i _ => bottomCount_le (Cs i) (hd i))
    have h2 : ∑ _i : Fin a', (n + 1) ^ 26 = a' * (n + 1) ^ 26 := by simp
    have h3 : a' * (n + 1) ^ 26 ≤ 4 * (n + 1) ^ 26 := Nat.mul_le_mul_right _ ha'
    omega
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  rw [← hNd] at hc eE ⊢
  have hN : 2 ≤ N := by omega
  have hM : P.M ≤ N ^ 28 := by
    have h26 : (n + 1) ^ 26 ≤ N ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    have e : N ^ 28 = N ^ 26 * N ^ 2 := by rw [← pow_add]
    have h5 : 4 * N ^ 26 ≤ N ^ 26 * N ^ 2 := by rw [Nat.mul_comm 4]; exact Nat.mul_le_mul_left _ h4
    have h6 : 4 * (n + 1) ^ 26 ≤ 4 * N ^ 26 := Nat.mul_le_mul_left _ h26
    rw [e]; omega
  have hB : P.B ≤ (8192 * capK F.cr) * N ^ capZR l := by
    rw [eB]
    calc _ ≤ 2 * (4096 * (capK F.cr * N ^ capZR l)) := Nat.mul_le_mul hcar (Nat.mul_le_mul_left _ hc)
      _ = (8192 * capK F.cr) * N ^ capZR l := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  have cM := pw_clog hM
  have cB := clog_KN_le hB
  have hrank : P.base.rank ≤ Nat.clog 2 (8192 * capK F.cr) + 9 + (capZR l + 28) * Nat.clog 2 N := by
    show max (Nat.clog 2 P.B + 9) (Nat.clog 2 P.M) ≤ _
    rw [Nat.add_mul]
    omega
  have hsb : SupplierWalkBridge.toeplitzWalkSideBits P.base.rank ≤ 2 * P.base.rank := by
    unfold SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits; omega
  have hK := capK_pos F.cr
  have hK2 : 2 ^ Nat.clog 2 (8192 * capK F.cr) ≤ 16384 * capK F.cr := by
    have := two_pow_clog_le_two_mul (8192 * capK F.cr) (by omega); omega
  obtain ⟨C, hCd⟩ : ∃ C, C = Nat.clog 2 (8192 * capK F.cr) := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W, W = capZR l + 28 := ⟨_, rfl⟩
  rw [← hCd, ← hWd] at hrank
  rw [← hCd] at hK2
  have hside : P.side * P.side ≤ (2 ^ k36 * (16384 * capK F.cr) ^ 4) * N ^ (8 * W) := by
    show 2 ^ SupplierWalkBridge.toeplitzWalkSideBits P.base.rank * 2 ^ SupplierWalkBridge.toeplitzWalkSideBits P.base.rank ≤ _
    rw [← pow_add]
    have hexp : SupplierWalkBridge.toeplitzWalkSideBits P.base.rank + SupplierWalkBridge.toeplitzWalkSideBits P.base.rank ≤
        k36 + 4 * C + (4 * W) * Nat.clog 2 N := by rw [k36_eq]; nlinarith
    calc 2 ^ (SupplierWalkBridge.toeplitzWalkSideBits P.base.rank + SupplierWalkBridge.toeplitzWalkSideBits P.base.rank)
        ≤ 2 ^ (k36 + 4 * C + (4 * W) * Nat.clog 2 N) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 2 ^ k36 * (2 ^ C) ^ 4 * 2 ^ ((4 * W) * Nat.clog 2 N) := by
          rw [pow_add, pow_add, ← pow_mul, Nat.mul_comm C 4]
      _ ≤ 2 ^ k36 * (16384 * capK F.cr) ^ 4 * N ^ (2 * (4 * W)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK2 4)) (pw_two_pow_clog hN _)
      _ = (2 ^ k36 * (16384 * capK F.cr) ^ 4) * N ^ (8 * W) := by rw [← Nat.mul_assoc 2 4 W]
  have hwalk : (16 ^ 40) ^ (P.walkLen - 1) ≤ 2 ^ k4 * N ^ (2 * k4) := by
    have e4 : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
    rw [eW1, e4, ← pow_mul]
    have hle : 160 * (2 * (P.errExp / 4)) ≤ k4 + k4 * Nat.clog 2 N := by rw [eE, k4_eq]; omega
    calc 2 ^ (160 * (2 * (P.errExp / 4))) ≤ 2 ^ (k4 + k4 * Nat.clog 2 N) := Nat.pow_le_pow_right (by norm_num) hle
      _ = 2 ^ k4 * 2 ^ (k4 * Nat.clog 2 N) := by rw [pow_add]
      _ ≤ 2 ^ k4 * N ^ (2 * k4) := Nat.mul_le_mul_left _ (pw_two_pow_clog hN k4)
  calc P.side * P.side * (16 ^ 40) ^ (P.walkLen - 1)
      ≤ ((2 ^ k36 * (16384 * capK F.cr) ^ 4) * N ^ (8 * W)) * (2 ^ k4 * N ^ (2 * k4)) := Nat.mul_le_mul hside hwalk
    _ = flatK F.cr * N ^ flatZR l := by
        unfold flatK flatZR; rw [← hWd, pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end Gate2

/-! ## The index counts and the sample counts -/

/-- The SYM index constant (`c_r` only) and exponent (`l`, `fe` only). -/
def symKI (cr : ℕ) : ℕ := gapK cr * flatK cr
noncomputable def symZI (l : Literals) (fe : ℕ) : ℕ := gapZR l fe + flatZR l + 52 * 4 + 2 * (1 + (52 * 4 + 29 * 4)) + 1

theorem symKI_pos (cr : ℕ) : 1 ≤ symKI cr := Nat.mul_le_mul (gapK_pos cr) (flatK_pos cr)

/-- The THR index exponent (`l`, `fe` only). -/
noncomputable def thrZI (l : Literals) (fe : ℕ) : ℕ :=
  gapZR l fe + (algX l * 4 + (20 * algX l + 65)) + 2 * (14 * algX l + 34) + 1

/-- `x·y² + 1 ≤ K·N^{a+2b+1}` from `x ≤ K·N^a`, `y ≤ N^b`, `N ≥ 2`, `K ≥ 1`. -/
theorem idx_mass_le {N K a b x y : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K) (hx : x ≤ K * N ^ a) (hy : y ≤ N ^ b) :
    x * y ^ 2 + 1 ≤ K * N ^ (a + 2 * b + 1) := by
  have hy2 : y ^ 2 ≤ N ^ (2 * b) := by rw [pow_mul']; exact Nat.pow_le_pow_left hy 2
  have hxy : x * y ^ 2 ≤ K * N ^ a * N ^ (2 * b) := Nat.mul_le_mul hx hy2
  have hp : 1 ≤ K * N ^ a * N ^ (2 * b) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (by omega))
  calc x * y ^ 2 + 1 ≤ K * N ^ a * N ^ (2 * b) * 2 := by omega
    _ ≤ K * N ^ a * N ^ (2 * b) * N := Nat.mul_le_mul_left _ hN
    _ = K * N ^ (a + 2 * b + 1) := by rw [pow_add, pow_add, pow_one]; simp only [Nat.mul_assoc]

section Index
variable (l : Literals) (F : GateFree l)

/-- **`I` at a SYM call, `c_r` in the constant.** -/
theorem symI_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    Fintype.card (SeedFix.SymIndex (callInputs l F kclk coef A a ha) hs Cs carriers) *
        SeedFix.symMassNat (callInputs l F kclk coef A a ha) hs Cs ^ 2 + 1 ≤
      symKI F.cr * (n + 2) ^ symZI l F.filterErrDeg := by
  have hg := gapSeed_leR l F kclk coef A a ha .sym n
  have hf := flatSeed_leR l F kclk coef A a ha n ha' Cs carriers hd hcar
  have hst := symState_le l F kclk coef A a ha n hs ha' Cs hd
  have hm := symMass_le l F kclk coef A a ha n hs ha' Cs hd
  have hidx : Fintype.card (SeedFix.SymIndex (callInputs l F kclk coef A a ha) hs Cs carriers) ≤
      symKI F.cr * (n + 2) ^ (gapZR l F.filterErrDeg + flatZR l + 52 * 4) := by
    unfold SeedFix.SymIndex
    rw [Fintype.card_prod, Fintype.card_prod]
    calc _ ≤ (gapK F.cr * (n + 2) ^ gapZR l F.filterErrDeg) * (flatK F.cr * (n + 2) ^ flatZR l) * (n + 2) ^ (52 * 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul hg hf) hst
      _ = symKI F.cr * (n + 2) ^ (gapZR l F.filterErrDeg + flatZR l + 52 * 4) := by
          unfold symKI; rw [pow_add, pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h := idx_mass_le (by omega) (symKI_pos F.cr) hidx hm
  unfold symZI
  exact h

/-- **`I` at a THR call, `c_r` in the constant.** -/
theorem thrI_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Fintype.card (SeedFix.ThrIndex (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) *
        SeedFix.thrMassNat (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ^ 2 + 1 ≤
      gapK F.cr * (n + 2) ^ thrZI l F.filterErrDeg := by
  have hg := gapSeed_leR l F kclk coef A a ha .thr n
  have hq := thrEq_le l F kclk coef A a ha n hs ha' Cs hd
  have hc := cut_le l F kclk coef A a ha n hs ha' Cs hd
  set c := Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
    (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) with hcd
  set G := Fintype.card (Primitive.ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
    with hGd
  have hmass0 : SeedFix.thrMassNat (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs = 2 * G * c + 1 := rfl
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  rw [← hNd] at hg hq hc ⊢
  have hN : 2 ≤ N := by omega
  have hp : 1 ≤ N ^ (10 * algX l + 32) := Nat.one_le_pow _ _ (by omega)
  have hsig : Fintype.card (Σ pr : SupplierPrime.PrimeIndex c, ZMod pr.val) ≤ N ^ (20 * algX l + 65) := by
    have h := sigma_le c
    have hc1 : c + 1 ≤ N ^ (10 * algX l + 33) := by rw [pow_succ]; nlinarith
    have e : N ^ (20 * algX l + 65) = N ^ (10 * algX l + 33) * N ^ (10 * algX l + 32) := by
      rw [← pow_add]; congr 1; omega
    rw [e]; exact le_trans h (Nat.mul_le_mul hc1 hc)
  have hidx : Fintype.card (SeedFix.ThrIndex (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤
      gapK F.cr * N ^ (gapZR l F.filterErrDeg + (algX l * 4 + (20 * algX l + 65))) := by
    unfold SeedFix.ThrIndex
    rw [Fintype.card_prod, Fintype.card_prod]
    calc _ ≤ (gapK F.cr * N ^ gapZR l F.filterErrDeg) * (N ^ (algX l * 4) * N ^ (20 * algX l + 65)) :=
          Nat.mul_le_mul hg (Nat.mul_le_mul hq hsig)
      _ = gapK F.cr * N ^ (gapZR l F.filterErrDeg + (algX l * 4 + (20 * algX l + 65))) := by
          rw [Nat.mul_assoc, ← pow_add, ← pow_add]
  have hmass : SeedFix.thrMassNat (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤ N ^ (14 * algX l + 34) := by
    rw [hmass0]
    have hGc : G * c ≤ N ^ (algX l * 4 + (10 * algX l + 32)) := pw_mul hq hc
    have hp2 : 1 ≤ N ^ (algX l * 4 + (10 * algX l + 32)) := Nat.one_le_pow _ _ (by omega)
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    have e2 : N ^ (14 * algX l + 34) = N ^ (algX l * 4 + (10 * algX l + 32)) * N ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e2]; nlinarith
  have h := idx_mass_le hN (gapK_pos F.cr) hidx hmass
  unfold thrZI
  exact h

/-- **`Q` at a SYM call**: `symCount ≤ 2^{(5kh+3)/4}·(8192·symKI c_r)·N^{symZI l fe + 2}`. -/
theorem symCount_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
        ((8192 * symKI F.cr) * (n + 2) ^ (symZI l F.filterErrDeg + 2)) := by
  have hI := symI_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
  unfold SeedFix.symCount Sampler.sampleCount
  apply Nat.mul_le_mul_left
  have hD : (callInputs l F kclk coef A a ha).D = 1 := rfl
  rw [hD, pow_add]
  have hn : n ^ (2 * 1) ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc 2 ^ 13 * _ * n ^ (2 * 1) ≤ 2 ^ 13 * (symKI F.cr * (n + 2) ^ symZI l F.filterErrDeg) * (n + 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hI) hn
    _ = 8192 * symKI F.cr * ((n + 2) ^ symZI l F.filterErrDeg * (n + 2) ^ 2) := by
        norm_num [Nat.mul_assoc]

/-- **`Q` at a THR call**: `thrCount ≤ 2^{(5kh+3)/4}·(8192·gapK c_r)·N^{thrZI l fe + 2}`. -/
theorem thrCount_leR (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) *
        ((8192 * gapK F.cr) * (n + 2) ^ (thrZI l F.filterErrDeg + 2)) := by
  have hI := thrI_leR l F kclk coef A a ha n hs ha' Cs hd
  unfold SeedFix.thrCount Sampler.sampleCount
  apply Nat.mul_le_mul_left
  have hD : (callInputs l F kclk coef A a ha).D = 1 := rfl
  rw [hD, pow_add]
  have hn : n ^ (2 * 1) ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc 2 ^ 13 * _ * n ^ (2 * 1) ≤ 2 ^ 13 * (gapK F.cr * (n + 2) ^ thrZI l F.filterErrDeg) * (n + 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hI) hn
    _ = 8192 * gapK F.cr * ((n + 2) ^ thrZI l F.filterErrDeg * (n + 2) ^ 2) := by
        norm_num [Nat.mul_assoc]

/-! ## In terms of the star width `k` -/

/-- `kh = k/2` at a call (`r` even): `(5kh+3)/4 ≤ 5k/8 + 1`. -/
theorem kh_exp_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4 ≤
      5 * ((gate0 l F).budget kclk coef A a ha).kOf n / 8 + 1 := by
  obtain ⟨j, hj⟩ := hs.1
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf n =
      ((gate0 l F).budget kclk coef A a ha).rOf n * Nat.log 2 (n / ((gate0 l F).budget kclk coef A a ha).rOf n + 1) :=
    rfl
  have hkh : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) =
      Nat.log 2 (n / ((gate0 l F).budget kclk coef A a ha).rOf n + 1) * (((gate0 l F).budget kclk coef A a ha).rOf n / 2) :=
    rfl
  rw [hk, hkh, hj]
  obtain ⟨S, hS⟩ : ∃ S, S = Nat.log 2 (n / (j + j) + 1) := ⟨_, rfl⟩
  rw [← hS, show (j + j) / 2 = j by omega]
  have e : (j + j) * S = 2 * (S * j) := by ring
  rw [e]
  omega

/-- **`Q` at a SYM call, in `k`**: `symCount ≤ (16384·symKI c_r)·2^{5k/8}·N^{symZI l fe + 2}`. -/
theorem symCount_leK (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      (16384 * symKI F.cr) * 2 ^ (5 * ((gate0 l F).budget kclk coef A a ha).kOf n / 8) *
        (n + 2) ^ (symZI l F.filterErrDeg + 2) := by
  have h := symCount_leR l F kclk coef A a ha n hs ha' Cs carriers hd hcar
  have hx := kh_exp_le l F kclk coef A a ha n hs
  have hp : 2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) ≤
      2 * 2 ^ (5 * ((gate0 l F).budget kclk coef A a ha).kOf n / 8) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine le_trans h (le_trans (Nat.mul_le_mul_right _ hp) ?_)
  apply le_of_eq
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ring

/-- **`Q` at a THR call, in `k`**: `thrCount ≤ (16384·gapK c_r)·2^{5k/8}·N^{thrZI l fe + 2}`. -/
theorem thrCount_leK (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      (16384 * gapK F.cr) * 2 ^ (5 * ((gate0 l F).budget kclk coef A a ha).kOf n / 8) *
        (n + 2) ^ (thrZI l F.filterErrDeg + 2) := by
  have h := thrCount_leR l F kclk coef A a ha n hs ha' Cs hd
  have hx := kh_exp_le l F kclk coef A a ha n hs
  have hp : 2 ^ ((5 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 3) / 4) ≤
      2 * 2 ^ (5 * ((gate0 l F).budget kclk coef A a ha).kOf n / 8) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine le_trans h (le_trans (Nat.mul_le_mul_right _ hp) ?_)
  apply le_of_eq
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ring

end Index

end NearCubicWires.WireExponent3_5.PrimAsm.CallIndexR
