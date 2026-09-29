import Proof.Wire_3_5.Primitive.SeedFix.W6ZC

/-! # W6, part 30: the THR call's first numbers are polynomial in the call's base

P3:2552-2557 (`K = 8(|𝒢|+1)n^D`), P3:2552-2553 (the cutoff), P3:2573-2580 (`|primes|`, `Σp`, `τ₀`) and P3:2121-2157
(`A`, `B_*`): with `|𝒢| ≤ N^4`, `E ≤ N^2`, `n, cap_T ≤ N` (`thr_basic`), each is at most a power of `N` fixed by `D` alone
(P3:3114-3115: "All powers of `n` are fixed before a fixed `r`"); the hash's `J, t, e, ℓ₀` and the modulus follow in
part 31:
* `primeSum_le`, `bDig`, `pow16` (`N^e` swallows small constants), `pw_succ`, `pw_two`, **`bK`**, **`bCut`**, `bPr`,
  `bPs`, **`bA`**, `bB`.

Paper quantities of the main types: `K`, the cutoff, `|primes|`, `Σp`, `τ₀`, `A`, `B_*`, each `≤ N^{O(D)}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.SupplierPrime

theorem primeSum_le (c : ℕ) : PrimAsm.ThrQ.primeSum c ≤ (c + 1) * c := by
  unfold PrimAsm.ThrQ.primeSum
  calc ∑ p ∈ primesUpTo c, p ≤ ∑ _p ∈ primesUpTo c, c :=
        Finset.sum_le_sum (fun p hp => (mem_primesUpTo.mp hp).2)
    _ = (primesUpTo c).card * c := by simp
    _ ≤ (c + 1) * c := Nat.mul_le_mul_right _ (RepairOrdinary.CloseoutFinalC10WireEnvelope.primesUpTo_card_le c)

theorem bDig {N : ℕ} (c e : ℕ) (hc : c ≤ N ^ e) : Nat.clog 2 c ≤ N ^ e :=
  (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hc

variable {N : ℕ} (hN : 16 ≤ N)
include hN

theorem pw_succ {x e : ℕ} (hx : x ≤ N ^ e) (k : ℕ) (hk : k ≤ 15) : x + k ≤ N ^ (e + 1) := by
  have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  have h2 : N ^ (e + 1) = N ^ e * N := pow_succ N e
  nlinarith

theorem pw_two {x e : ℕ} (hx : x ≤ N ^ e) : 2 * x + 4 ≤ N ^ (e + 1) := by
  have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  have h2 : N ^ (e + 1) = N ^ e * N := pow_succ N e
  nlinarith

theorem bK (g n D : ℕ) (hg : g ≤ N ^ 4) (hn : n ≤ N) : 8 * (g + 1) * n ^ D ≤ N ^ (D + 6) := by
  have h8 : 8 ≤ N ^ 1 := by rw [pow_one]; omega
  have hg1 : g + 1 ≤ N ^ 5 := pw_succ hN hg 1 (by omega)
  have hnD : n ^ D ≤ N ^ D := Nat.pow_le_pow_left hn D
  have h := pw_mul (pw_mul h8 hg1) hnD
  rw [show 1 + 5 + D = D + 6 by ring] at h
  exact h

theorem bCut (E K D : ℕ) (hE : E ≤ N ^ 2) (hK : K ≤ N ^ (D + 6)) :
    canonicalPrimeCutoff E K ≤ N ^ (2 * D + 24) := by
  unfold canonicalPrimeCutoff canonicalPrimeScale
  have h6 : 6 ≤ N ^ 1 := by rw [pow_one]; omega
  have hE1 : E + 1 ≤ N ^ 3 := pw_succ hN hE 1 (by omega)
  have hK1 : K + 1 ≤ N ^ (D + 7) := pw_succ hN hK 1 (by omega)
  have hx : 6 * (E + 1) * (K + 1) ≤ N ^ (D + 11) := by
    have h := pw_mul (pw_mul h6 hE1) hK1
    rw [show 1 + 3 + (D + 7) = D + 11 by ring] at h
    exact h
  have h24 : 24 ≤ N ^ (D + 11) := by
    have h2 : 16 * 16 ≤ N * N := Nat.mul_le_mul hN hN
    have h3 : N ^ 2 ≤ N ^ (D + 11) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_two] at h3
    omega
  have hm : max 24 (6 * (E + 1) * (K + 1)) ≤ N ^ (D + 11) := max_le h24 hx
  have h := pw_pow hm 2
  rw [show (D + 11) * 2 = 2 * D + 22 by ring] at h
  exact pw_mono (by omega) h (by omega)

theorem bPr (c e : ℕ) (hc : c ≤ N ^ e) : (primesUpTo c).card ≤ N ^ (e + 1) :=
  (RepairOrdinary.CloseoutFinalC10WireEnvelope.primesUpTo_card_le c).trans (pw_succ hN hc 1 (by omega))

theorem bPs (c e : ℕ) (hc : c ≤ N ^ e) : PrimAsm.ThrQ.primeSum c ≤ N ^ (2 * e + 1) := by
  have h := pw_mul (pw_succ hN hc 1 (by omega)) hc
  rw [show e + 1 + e = 2 * e + 1 by ring] at h
  exact (primeSum_le c).trans h

theorem bA (g pr d e : ℕ) (hg : g ≤ N ^ 4) (hpr : pr ≤ N ^ (e + 1)) (hd : d ≤ N ^ e) :
    g * (pr * (d * 2)) ≤ N ^ (2 * e + 6) := by
  have h2 : d * 2 ≤ N ^ (e + 1) := by
    have := pw_succ hN hd 0 (by omega)
    have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]; nlinarith
  have h := pw_mul hg (pw_mul hpr h2)
  rw [show 4 + (e + 1 + (e + 1)) = 2 * e + 6 by ring] at h
  exact h

theorem bB (a nc ct : ℕ) (ha : a ≤ 4) (hnc : nc ≤ 2) (hct : ct ≤ N) :
    a * (4096 * ((nc + 1) * (4096 * ct))) ≤ N ^ 9 := by
  have h1 : a ≤ N ^ 1 := by rw [pow_one]; omega
  have h3 : 4096 ≤ N ^ 3 := by
    have : 16 ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    norm_num at this; exact this
  have hn : nc + 1 ≤ N ^ 1 := by rw [pow_one]; omega
  have hc : 4096 * ct ≤ N ^ 4 := by
    have h := pw_mul h3 (show ct ≤ N ^ 1 by rw [pow_one]; exact hct)
    exact h
  have h := pw_mul h1 (pw_mul h3 (pw_mul hn hc))
  exact h

end NearCubicWires.WireExponent3_5.PrimT.W6
