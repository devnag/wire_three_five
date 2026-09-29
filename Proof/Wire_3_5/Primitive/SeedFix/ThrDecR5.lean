import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR4

/-! # THR decode front, RADIX part 5: the scan's item is the prime row's prime

`Enum.primeRowEquiv c` enumerates the prime rows `(p, s mod p)` primes increasing, then the residue
(`finSigmaFinEquiv`: row `(i, a)` at `Σ_{j<i} p_j + a`). **`primeRow_symm`**: at an index `f` with
`Σ_{j<t} p_j ≤ f < Σ_{j≤t} p_j` (the scan's item `t`, `ThrDecR4.scan_run`, over `primesList c`), the row's prime is
`p_t` and its residue is `f − Σ_{j<t} p_j` — the values the RADIX setup reads (`RadSetup.radVals`' `p`, `s`).

Paper quantity of the main type: the prime row `(p, s mod p)` of a THR state (row:prime, P3:2573-2580). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

theorem sum_take_le_sum (l : List ℕ) (a : ℕ) : (l.take a).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop a l]
  rw [List.sum_append]; omega

theorem sum_take_mono (L : List ℕ) {a b : ℕ} (h : a ≤ b) : (L.take a).sum ≤ (L.take b).sum := by
  have e : (L.take b).take a = L.take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [← e]; exact sum_take_le_sum _ _

/-- **The bucket of a prefix-sum index is unique.** -/
theorem bucket_unique (L : List ℕ) (i t f : ℕ) (h1 : (L.take i).sum ≤ f) (h2 : f < (L.take (i + 1)).sum)
    (h3 : (L.take t).sum ≤ f) (h4 : f < (L.take (t + 1)).sum) : i = t := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := sum_take_mono L (show i + 1 ≤ t by omega); omega
  · have := sum_take_mono L (show t + 1 ≤ i by omega); omega

theorem sum_fin_getD (L : List ℕ) : ∀ i, i ≤ L.length → ∑ j : Fin i, L.getD j.val 0 = (L.take i).sum := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), sum_take_succ' L i (by omega)]

theorem val_finEquiv (n : ℕ) [NeZero n] (a : Fin n) : (ZMod.finEquiv n a).val = a.val := by
  cases n with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ k => rfl

theorem primesList_length (c : ℕ) : (PrimThrW.Joins.primesList c).length = (SupplierPrime.primesUpTo c).card := by
  rw [PrimThrW.Joins.primesList_sorted, Finset.length_sort]

/-- **The prime row at a prefix-sum index**: the row's prime is the `t`-th prime, its residue the index's excess. -/
theorem primeRow_symm (c : ℕ) (f : Fin (∑ i : Fin (SupplierPrime.primesUpTo c).card, ((Enum.primeEquiv c i) : ℕ)))
    (t : ℕ) (h1 : ((PrimThrW.Joins.primesList c).take t).sum ≤ f.val)
    (h2 : f.val < ((PrimThrW.Joins.primesList c).take (t + 1)).sum) :
    ((((Enum.primeRowEquiv c).symm f).1 : ℕ) = (PrimThrW.Joins.primesList c).getD t 0) ∧
      (((Enum.primeRowEquiv c).symm f).2).val = f.val - ((PrimThrW.Joins.primesList c).take t).sum := by
  set L := PrimThrW.Joins.primesList c with hL
  have hlen := primesList_length c
  set p := (finSigmaFinEquiv (n := fun i : Fin (SupplierPrime.primesUpTo c).card => ((Enum.primeEquiv c i) : ℕ))).symm f
    with hp
  have hf : (finSigmaFinEquiv (n := fun i : Fin (SupplierPrime.primesUpTo c).card => ((Enum.primeEquiv c i) : ℕ)) p :
      ℕ) = f.val := by rw [hp, Equiv.apply_symm_apply]
  rw [finSigmaFinEquiv_apply] at hf
  have hs : ∑ j : Fin p.1, ((Enum.primeEquiv c (Fin.castLE p.1.2.le j)) : ℕ) = (L.take p.1.val).sum := by
    rw [← sum_fin_getD L p.1.val (by rw [hlen]; exact p.1.2.le)]
    apply Finset.sum_congr rfl
    intro j _
    rw [PrimThrW.Joins.primesList_get]
    rfl
  rw [hs] at hf
  have ha := p.2.isLt
  have hpv : ((Enum.primeEquiv c p.1) : ℕ) = L.getD p.1.val 0 := PrimThrW.Joins.primesList_get c p.1
  have hsucc : (L.take (p.1.val + 1)).sum = (L.take p.1.val).sum + L.getD p.1.val 0 :=
    sum_take_succ' L p.1.val (by rw [hlen]; exact p.1.2)
  have hit : p.1.val = t := bucket_unique L p.1.val t f.val (by omega) (by rw [hsucc, ← hpv]; omega) h1 h2
  have hsymm : (Enum.primeRowEquiv c).symm f =
      ⟨Enum.primeEquiv c p.1, @ZMod.finEquiv ((Enum.primeEquiv c p.1) : ℕ) ⟨Enum.primeEquiv_ne_zero c p.1⟩ p.2⟩ := by
    rfl
  rw [hsymm]
  refine ⟨?_, ?_⟩
  · show ((Enum.primeEquiv c p.1) : ℕ) = L.getD t 0
    rw [hpv, hit]
  · show (@ZMod.finEquiv ((Enum.primeEquiv c p.1) : ℕ) ⟨Enum.primeEquiv_ne_zero c p.1⟩ p.2).val = _
    rw [@val_finEquiv _ ⟨Enum.primeEquiv_ne_zero c p.1⟩, ← hit]
    omega

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
