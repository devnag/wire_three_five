import Proof.Wire_3_5.Foundations.Skeleton
import Proof.Wire_3_5.Rows.RowsSymState

/-! # Primitive: the uniform averages of `prim:truth` (P3:3087-3091)

Realizes the bookkeeping of the averages in `lem:primitive`: "`e` is uniform on their common finite seed space" and the
target `E_{e,x}[M(e,x)Π_iC_i(x)]` (prim:truth, P3:3079-3091) as an iterated uniform mean, with the seed's normalized
sum `maskedMean` (the mask multiplies inside the average and is never divided out). A uniform average over a product
is the iterated average; it is invariant under bijections of the index set; the live-pair average `E_{u,v∈[N]}` is the
iterated average over `Fin N`.

Paper quantities: the seed's `maskedMean` (`E_{e,x}[M·ΠC_i]`) and S7's `uMean` (`E`). Results: **`seedMaskedMean_eq`**
(the seed's normalized sum is `E_eE_x[bit(M)·bit(ΠC_i)]`), `uMean_prod_eq`, `uMean_equiv`, `uMean_const`,
`uMean_prod_swap`, `liveMean_eq_uMean`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Rows

instance instNonemptyMargulisWalkSample (m t : ℕ) [NeZero m] : Nonempty (SupplierWalk.MargulisWalkSample m t) :=
  ⟨⟨(0, 0), fun _ _ => 0⟩⟩

theorem uMean_prod_eq {A C : Type} [Fintype A] [Fintype C] (f : A × C → ℝ) :
    uMean f = uMean (fun a => uMean (fun c => f (a, c))) := by
  unfold uMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

theorem uMean_equiv {A C : Type} [Fintype A] [Fintype C] (e : A ≃ C) (f : C → ℝ) :
    uMean (fun a => f (e a)) = uMean f := by
  unfold uMean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem uMean_const {A : Type} [Fintype A] [Nonempty A] (r : ℝ) : uMean (fun _ : A => r) = r := by
  unfold uMean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem uMean_prod_swap {A C : Type} [Fintype A] [Fintype C] (f : A → C → ℝ) :
    uMean (fun a => uMean (fun c => f a c)) = uMean (fun c => uMean (fun a => f a c)) := by
  rw [← uMean_prod_eq (fun p : A × C => f p.1 p.2), ← uMean_prod_eq (fun p : C × A => f p.2 p.1)]
  exact (uMean_equiv (Equiv.prodComm C A) (fun p : A × C => f p.1 p.2)).symm

/-- The live-pair average over `Fin N` is the iterated average. -/
theorem liveMean_eq_uMean {N : ℕ} (f : Fin N → Fin N → ℝ) :
    liveMean f = uMean (fun i => uMean (fun j => f i j)) := by
  unfold liveMean uMean
  simp only [Fintype.card_fin]
  rw [← Finset.sum_div, div_div, sq]

/-- **The seed's `prim:truth` average** (P3:3087-3091): `maskedMean M C = E_eE_x[bit(M(e,x))·bit(Π_iC_i(x))]`. -/
theorem seedMaskedMean_eq {Seed : Type} [Fintype Seed] {n a : ℕ} (M : Seed → BitInput n → Bool)
    (C : Fin a → BitInput n → Bool) :
    WireExponent3_5.maskedMean M C =
      uMean (fun e => uMean (fun x => bitR (M e x) * bitR (decide (∀ i, C i x = true)))) := by
  unfold WireExponent3_5.maskedMean
  have hcard : (Fintype.card (BitInput n) : ℝ) = 2 ^ n := by simp [BitInput]
  have h1 : ∀ e x, ((if M e x then (1 : ℝ) else 0) * ∏ i, (if C i x then (1 : ℝ) else 0)) =
      bitR (M e x) * bitR (decide (∀ i, C i x = true)) := by
    intro e x
    rw [← bitR_prod_eq]
    rfl
  simp only [h1]
  unfold uMean
  rw [hcard, ← Finset.sum_div, div_div, mul_comm (2 ^ n : ℝ)]

end NearCubicWires.WireExponent3_5.Primitive
