import Proof.SourceAssembly.AdmissionRuntime
import Proof.CaseAnalysis.FinalFuelRepin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.SupplierEstimator NearCubicWires.Admission
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

/-! ## 1. Log-scale arithmetic -/

/-- `2^(logScale q) ≤ 2·(q+2)`. -/
theorem two_pow_logScale_le (q : ℕ) : 2^(logScale q) ≤ 2*(q+2) := by
  unfold logScale
  have hpos : 0 < Nat.clog 2 (q+2) := Nat.clog_pos (by decide) (by omega)
  have hlt : 2^(Nat.clog 2 (q+2)).pred < q+2 := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have e : 2^(Nat.clog 2 (q+2)) = 2 * 2^(Nat.clog 2 (q+2)).pred := by
    rw [← pow_succ']
    congr 1
  omega

theorem one_le_logScale (q : ℕ) : 1 ≤ logScale q := by
  have := log_succ_le_logScale q
  omega

/-- `2^K ≤ (2(q+2))^L` for the live count `K = normalizedLiveCount q L`. -/
theorem two_pow_live_le (q L : ℕ) : 2^(normalizedLiveCount q L) ≤ (2*(q+2))^L := by
  have hK : normalizedLiveCount q L ≤ L*logScale q := min_le_right _ _
  calc 2^(normalizedLiveCount q L) ≤ 2^(L*logScale q) := Nat.pow_le_pow_right (by decide) hK
    _ = (2^logScale q)^L := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2*(q+2))^L := Nat.pow_le_pow_left (two_pow_logScale_le q) L

/-- The width is eventually above any constant (from the clock: `2^23·(n+1)^(k+2) ≤ 2^q`). -/
theorem widthAt_ge_eventually (sources : EightSources) (k c : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → c ≤ C10PartsSchedule.widthAt sources k n := by
  refine ⟨2^c, fun n hn => ?_⟩
  have h1 := C10FuelRepin.pow_widthAt_ge sources k n
  have h2 : n + 1 ≤ (n+1)^(k+2) := Nat.le_self_pow (by omega) _
  have h3 : 2^c ≤ 2^(C10PartsSchedule.widthAt sources k n) := by omega
  exact (Nat.pow_le_pow_iff_right (by decide)).mp h3

/-! ## 2. The three classes below the table factor `2^(q-K)` -/

/-- **A polynomial in the input length of degree `≤ k+1`** is below `2^(q-K)` at `q = widthAt sources k n`, past an onset
chosen after `(a, d, L)` (and `k`). This is the paper's `2^{q(N)} ≥ T(N) = N^{k+2}` at work. -/
theorem npoly_le_twoPow_res (sources : EightSources) (k a d L : ℕ) (hd : d + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → a * (n+1)^d ≤
      2^(C10PartsSchedule.widthAt sources k n - normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L) := by
  set W := C10PartsSchedule.widthConst sources k with hW
  obtain ⟨n1, h1⟩ := SupplierCapacity.coefficient_mul_logScale_pow_eventually_le (a * (2*(W+1))^L) L
  refine ⟨n1, fun n hn => ?_⟩
  set q := C10PartsSchedule.widthAt sources k n with hq
  set K := normalizedLiveCount q L with hKdef
  have hKq : K ≤ q := normalizedLiveCount_le q L
  have hls := one_le_logScale n
  -- `q + 2 ≤ (W+1)·logScale n`
  have hwq : q + 1 ≤ W * logScale n := C10PartsSchedule.widthAt_succ_le sources k n
  have hq2 : q + 2 ≤ (W+1) * logScale n := by
    have : (W+1) * logScale n = W * logScale n + logScale n := by ring
    omega
  -- `2^K ≤ (2(W+1))^L · (logScale n)^L`
  have hK2 : 2^K ≤ (2*(W+1))^L * (logScale n)^L := by
    calc 2^K ≤ (2*(q+2))^L := two_pow_live_le q L
      _ ≤ (2*((W+1) * logScale n))^L := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hq2) L
      _ = (2*(W+1))^L * (logScale n)^L := by rw [← mul_pow]; ring_nf
  have hon := h1 n hn
  -- the product with `2^K` is below `2^q`
  have hprod : a * (n+1)^d * 2^K ≤ 2^q := by
    calc a * (n+1)^d * 2^K ≤ a * (n+1)^d * ((2*(W+1))^L * (logScale n)^L) := Nat.mul_le_mul_left _ hK2
      _ = (a * (2*(W+1))^L * (logScale n)^L) * (n+1)^d := by ring
      _ ≤ n * (n+1)^d := Nat.mul_le_mul_right _ hon
      _ ≤ (n+1) * (n+1)^d := Nat.mul_le_mul_right _ (by omega)
      _ = (n+1)^(d+1) := by rw [pow_succ]; ring
      _ ≤ (n+1)^(k+2) := Nat.pow_le_pow_right (by omega) hd
      _ ≤ 2^23 * (n+1)^(k+2) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ 2^q := C10FuelRepin.pow_widthAt_ge sources k n
  have hsplit : 2^q = 2^(q - K) * 2^K := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hprod
  exact Nat.le_of_mul_le_mul_right hprod (by positivity)

/-- **The small class** `c·(q+1)^hS·2^(q/m)` (`m ≥ 2`) is below `2^(q-K)` past an onset chosen after `(m, hS, c, L)`. -/
theorem small_le_twoPow_res (m hS c L : ℕ) (hm : 2 ≤ m) :
    ∃ q0, ∀ q, q0 ≤ q → c * smallClass m hS q ≤ 2^(q - normalizedLiveCount q L) := by
  obtain ⟨q1, h1⟩ := SupplierCapacity.coefficient_mul_logScale_eventually_le (2*(c + hS + L))
  refine ⟨q1, fun q hq => ?_⟩
  have hl := h1 q hq
  have hls := one_le_logScale q
  have hK : normalizedLiveCount q L ≤ L*logScale q := min_le_right _ _
  have hc : c < 2^c := Nat.lt_two_pow_self
  have hp : (q+1)^hS ≤ 2^(hS*logScale q) := succ_pow_le q hS
  have hdiv : q/m ≤ q/2 := Nat.div_le_div_left hm (by decide)
  have hsplit : 2*(c + hS + L)*logScale q = 2*(c*logScale q) + 2*(hS*logScale q) + 2*(L*logScale q) := by ring
  have hcl : c ≤ c*logScale q := Nat.le_mul_of_pos_right _ hls
  have hexp : c + hS*logScale q + q/m ≤ q - normalizedLiveCount q L := by omega
  unfold smallClass
  calc c * ((q+1)^hS * 2^(q/m)) ≤ 2^c * (2^(hS*logScale q) * 2^(q/m)) :=
        Nat.mul_le_mul hc.le (Nat.mul_le_mul_right _ hp)
    _ = 2^(c + hS*logScale q + q/m) := by rw [pow_add, pow_add]; ring
    _ ≤ 2^(q - normalizedLiveCount q L) := Nat.pow_le_pow_right (by decide) hexp

/-! ## 3. A whole cost class plus a table-class extra, below the reserve -/

/-- **Any `Split.bound` summand plus a table extra fits the reserve** `C·tableClass L hR q` at `q = widthAt sources k n`,
for EVERY `C ≥ 1`, past one onset chosen after `L` and the class: needs `dP + 1 ≤ k + 2` (the clock), `2 ≤ m`, and a reserve
exponent `hR ≥ max hT hX + 2`. -/
theorem split_add_lt_Rc (sources : EightSources) (k dP hT hS m L cP cT cS hX cX : ℕ) (hm : 2 ≤ m)
    (hd : dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ x : ℕ, x ≤ cX * tableClass L hX (C10PartsSchedule.widthAt sources k n) →
      ∀ C hR : ℕ, 1 ≤ C → hT + 2 ≤ hR → hX + 2 ≤ hR →
        splitRHS dP hT hS m L cP cT cS n (C10PartsSchedule.widthAt sources k n) + x + 1 ≤
          C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n1, h1⟩ := npoly_le_twoPow_res sources k cP dP L hd
  obtain ⟨q3, h3⟩ := small_le_twoPow_res m hS cS L hm
  obtain ⟨n2, h2⟩ := widthAt_ge_eventually sources k (q3 + cT + cX + 4)
  refine ⟨max n1 n2, fun n hn x hx C hR hC hTR hXR => ?_⟩
  set q := C10PartsSchedule.widthAt sources k n with hqdef
  have hn1 : n1 ≤ n := le_of_max_le_left hn
  have hn2 : n2 ≤ n := le_of_max_le_right hn
  have hq := h2 n hn2
  set T0 := 2^(q - normalizedLiveCount q L) with hT0
  have hT01 : 1 ≤ T0 := Nat.one_le_two_pow
  have hi : cP * (n+1)^dP ≤ T0 := h1 n hn1
  have hiii : cS * smallClass m hS q ≤ T0 := h3 q (by omega)
  -- `hR = h1 + 1`
  obtain ⟨h1', rfl⟩ : ∃ h1', hR = h1' + 1 := ⟨hR - 1, by omega⟩
  have mono : ∀ h, h ≤ h1' → (q+1)^h * T0 ≤ (q+1)^h1' * T0 := fun h hh =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) hh)
  have hii : cT * ((q+1)^hT * T0) ≤ (q+1)^h1' * T0 := by
    calc cT * ((q+1)^hT * T0) ≤ (q+1) * ((q+1)^hT * T0) := Nat.mul_le_mul_right _ (by omega)
      _ = (q+1)^(hT+1) * T0 := by rw [pow_succ]; ring
      _ ≤ (q+1)^h1' * T0 := mono _ (by omega)
  have hiv : x ≤ (q+1)^h1' * T0 := by
    calc x ≤ cX * ((q+1)^hX * T0) := hx
      _ ≤ (q+1) * ((q+1)^hX * T0) := Nat.mul_le_mul_right _ (by omega)
      _ = (q+1)^(hX+1) * T0 := by rw [pow_succ]; ring
      _ ≤ (q+1)^h1' * T0 := mono _ (by omega)
  have h0 : T0 ≤ (q+1)^h1' * T0 := by
    have := mono 0 (Nat.zero_le _)
    simpa using this
  have hfive : 5 * ((q+1)^h1' * T0) ≤ (q+1)^(h1'+1) * T0 := by
    calc 5 * ((q+1)^h1' * T0) ≤ (q+1) * ((q+1)^h1' * T0) := Nat.mul_le_mul_right _ (by omega)
      _ = (q+1)^(h1'+1) * T0 := by rw [pow_succ]; ring
  have hCC : (q+1)^(h1'+1) * T0 ≤ C * ((q+1)^(h1'+1) * T0) := Nat.le_mul_of_pos_left _ hC
  unfold splitRHS
  simp only [tableClass, smallClass] at hiii ⊢
  rw [← hT0]
  omega

end NearCubicWires.SourceBudget

