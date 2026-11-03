import Proof.PCP.PCPPowerSlice
import Mathlib.Data.Nat.Log

/-! Numerical audit of the fixed-verifier ledger. These theorems establish
common field capacity, aggregate cost and language-preserving slice bounds.
They do not assume or assert an ordinary implementation of the verifier. -/
namespace NearCubicWires.RepairOrdinary.PCPResourceLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ell (N : ℕ) : ℕ := Nat.clog 2 (N+1)
def q (N : ℕ) : ℕ := ell N+1
def width (N : ℕ) : ℕ := Nat.clog 2 (4*PowerSlice.limit N+4)

theorem width_bounds (N : ℕ) :
    4*PowerSlice.limit N+4 ≤ 2^width N ∧ width N ≤ 3*q N^2 := by
  have hN : N ≤ 2^ell N := le_trans (Nat.le_succ N) (Nat.le_pow_clog (by decide) (N+1))
  have hD : PowerSlice.degree N ≤ ell N+2 := by
    have := Nat.factorization_le_of_le_pow hN
    dsimp only [PowerSlice.degree]
    omega
  have hL : PowerSlice.limit N ≤ 2^(ell N*(ell N+2)) := by
    calc
      PowerSlice.limit N = N^PowerSlice.degree N := rfl
      _ ≤ (2^ell N)^PowerSlice.degree N := Nat.pow_le_pow_left hN _
      _ = 2^(ell N*PowerSlice.degree N) := (pow_mul _ _ _).symm
      _ ≤ 2^(ell N*(ell N+2)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hD)
  have hb : 4*PowerSlice.limit N+4 ≤ 2^(ell N*(ell N+2)+3) := by
    rw [pow_add]
    have hp : 1 ≤ 2^(ell N*(ell N+2)) := Nat.one_le_pow _ _ (by decide)
    norm_num
    omega
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hw := Nat.clog_le_of_le_pow hb
  have he : ell N*(ell N+2)+3 ≤ 3*q N^2 := by dsimp [q]; nlinarith
  exact le_trans hw he

def events (n B m t : ℕ) : ℕ := 2*n+2*B+2+t*m

theorem record_count (n B m t c L : ℕ) (hL : 2 ≤ L)
    (hn : n ≤ B) (hB : B ≤ L) (hm : m ≤ B) (ht : t ≤ c) :
    events n B m t ≤ L*(c+5) := by
  have htm : t*m ≤ c*L := Nat.mul_le_mul ht (hm.trans hB)
  dsimp only [events]
  nlinarith

theorem record_capacity (n B m t c L w : ℕ) (hL : 2 ≤ L)
    (hn : n ≤ B) (hB : B ≤ L) (hm : m ≤ B) (ht : t ≤ c)
    (hc : c ≤ L) (hw : 4*L+4 ≤ 2^w) :
    events n B m t < 2^(2*w) ∧
      ∀ tape address : ℕ, tape ≤ L → address ≤ 2*L →
        address < 2^w ∧ tape*2^w+address < 2^(2*w+2) := by
  have hE := record_count n B m t c L hL hn hB hm ht
  have hsquare : (4*L+4)^2 ≤ (2^w)^2 := Nat.pow_le_pow_left hw _
  have hpower : 2^(2*w) = (2^w)^2 := by rw [Nat.mul_comm 2 w, pow_mul]
  constructor
  · rw [hpower]
    nlinarith
  · intro tape address htape haddress
    have ha : address < 2^w := by omega
    have htape' : tape+1 ≤ 2^w := by omega
    have hmul := Nat.mul_le_mul_right (2^w) htape'
    constructor
    · exact ha
    · rw [pow_add, hpower]
      norm_num
      nlinarith

theorem reduced_currency (N n B m t c L w q : ℕ) (hL : 2 ≤ L)
    (hN : N ≤ L) (hn : n ≤ B) (hB : B ≤ L) (hm : m ≤ B)
    (ht : t ≤ c) (hq : 1 ≤ q) (hc : c+1 ≤ q) (hw : w ≤ 3*q^2) :
    N+events n B m t+1 ≤ 7*L*q ∧ w+c+1 ≤ 4*q^2 ∧
      w+B+t*m ≤ 4*L*q^2 := by
  have hE := record_count n B m t c L hL hn hB hm ht
  have htm : t*m ≤ c*L := Nat.mul_le_mul ht (hm.trans hB)
  have hq2 : q ≤ q^2 := Nat.le_self_pow (by decide) q
  have hpoly : 0 ≤ L*(q^2-q) := Nat.zero_le _
  have hscale : L*q ≤ L*q^2 := Nat.mul_le_mul_left L hq2
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Apply the numerical ledger at its actual length-dependent widths. The
remaining hypotheses are the explicit entry guards, not assumed phase costs. -/
theorem guarded_bounds (N n B m t c : ℕ) (hN : 2 ≤ N)
    (hn : n ≤ B) (hB : B ≤ PowerSlice.limit N) (hm : m ≤ B)
    (ht : t ≤ c) (hc : c ≤ Nat.log 2 N) :
    events n B m t < 2^(2*width N) ∧
    N+events n B m t+1 ≤ 7*PowerSlice.limit N*q N ∧
    width N+c+1 ≤ 4*q N^2 ∧
    width N+B+t*m ≤ 4*PowerSlice.limit N*q N^2 := by
  have hNL : N ≤ PowerSlice.limit N := Nat.le_self_pow (by simp [PowerSlice.degree]) N
  have hL : 2 ≤ PowerSlice.limit N := hN.trans hNL
  have hce : c ≤ ell N := hc.trans
    ((Nat.log_mono_right (Nat.le_succ N)).trans (Nat.log_le_clog 2 (N+1)))
  have heN : ell N ≤ N := by
    apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hcap := record_capacity n B m t c (PowerSlice.limit N) (width N) hL hn hB hm ht
    (hce.trans (heN.trans hNL)) (width_bounds N).1
  have hcurrency := reduced_currency N n B m t c (PowerSlice.limit N) (width N) (q N)
    hL hNL hn hB hm ht (by simp [q]) (by dsimp [q]; omega) (width_bounds N).2
  exact ⟨hcap.1, hcurrency⟩

def clock (C d N : ℕ) : ℕ := C*(N+PowerSlice.limit N+1)*q N^(2*d+1)

/-- The padding allocation coefficient is separate from the language's
original witness bound. Enlarging the former preserves the latter exactly. -/
theorem separate_padding (k C_H C_pad header n : ℕ)
    (hH : 1 ≤ C_H) (hpad : C_H ≤ C_pad) :
    C_H*(n^(k+2)+1) ≤ PowerSlice.limit
      (PowerSlice.length k ((2*C_pad+1)*(n+1)+header)) ∧
    PowerSlice.limit (PowerSlice.length k ((2*C_pad+1)*(n+1)+header)) ≤
      ((2*(2*C_pad+1+header+2^(k+2)))^(k+2)*C_pad)*(C_H*(n^(k+2)+1)) := by
  constructor
  · exact (Nat.mul_le_mul_right _ hpad).trans (PowerSlice.hierarchy_fits k C_pad header n)
  · have hb := PowerSlice.hierarchy_limit_bound k C_pad header n (by omega)
    have hclock : n^(k+2)+1 ≤ C_H*(n^(k+2)+1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (n^(k+2)+1) hH
    calc
      _ ≤ (2*(2*C_pad+1+header+2^(k+2)))^(k+2)*(C_pad*(n^(k+2)+1)) := hb
      _ = ((2*(2*C_pad+1+header+2^(k+2)))^(k+2)*C_pad)*(n^(k+2)+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hclock

end NearCubicWires.RepairOrdinary.PCPResourceLedger
