import Proof.Wire_3_5.FinalPass.FreeGenH

/-! # The HASH free numbers' program, part 2: the bounds (`HashFreeOk`'s program fields)

The HASH program `freeProgH κ` (P3:2291-2296: `Q' = d_Q(β³ + 2k_h + β)`) in the forms of `HashFreeOk` (= `SymFreeOk7`'s):
the capacity `need + needH ≤ Ko·2^{⌊n/8⌋}` and the values but `ρ` below it on every small `x` (the extra terms
`β², β³, k_h` absorbed as in FreeGen9 by `c·(B+1)² ≤ ⌊n/16⌋ + K₀`), the steps `≤ K(cap+1)²`, and `ρ` and the pad
unchanged from the v2 program (slot 6 is the same number).

* `needH_extra`, **`capH_bound`**, **`okH_le`**, **`costH_le`**, `valH_le_need`, **`valH_le`**, **`rhoH_le`**, **`padH`**.

Paper quantities of the main types: the HASH free numbers' capacity and values against `2^{⌊n/8⌋}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- The HASH pass's extra capacity on a small `x`. -/
theorem needH_extra (κ : FreeK2) (Ds : ℕ) (x : FreeIn) (hs : FreeSmall Ds x) :
    β x * β x + β x * (β x * β x) + (β x * (β x * β x) + x.kh + x.kh + β x) +
        κ.k.dQ * (β x * (β x * β x) + x.kh + x.kh + β x) ≤
      (κ.k.dQ + 2) * 6 * 2 ^ ((Ds + 3) * (natBitLength x.n + 1) ^ 2) := by
  have hB := beta_le_B x
  have hkh := hs.1
  obtain ⟨s, hsd⟩ : ∃ s, s = (natBitLength x.n + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hsd] at hkh ⊢
  have hs1 : natBitLength x.n + 1 ≤ s := by rw [hsd]; nlinarith
  have hb : β x ≤ 2 ^ s := le_trans (by omega) (Nat.lt_two_pow_self).le
  have h2 : β x * β x ≤ 2 ^ (2 * s) := by
    rw [show 2 * s = s + s by ring, pow_add]; exact Nat.mul_le_mul hb hb
  have h3 : β x * (β x * β x) ≤ 2 ^ (3 * s) := by
    rw [show 3 * s = s + 2 * s by ring, pow_add]; exact Nat.mul_le_mul hb h2
  have hU : ∀ e, e ≤ Ds + 3 → 2 ^ (e * s) ≤ 2 ^ ((Ds + 3) * s) := fun e he =>
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right s he)
  have g1 := hU 1 (by omega)
  have g2 := hU 2 (by omega)
  have g3 := hU 3 (by omega)
  have gD := hU Ds (by omega)
  rw [Nat.one_mul] at g1
  have hsum : β x * (β x * β x) + x.kh + x.kh + β x ≤ 5 * 2 ^ ((Ds + 3) * s) := by omega
  have hq := Nat.mul_le_mul_left κ.k.dQ hsum
  have e : (κ.k.dQ + 2) * 6 * 2 ^ ((Ds + 3) * s) = 6 * (κ.k.dQ * 2 ^ ((Ds + 3) * s)) + 12 * 2 ^ ((Ds + 3) * s) := by
    ring
  have e2 : κ.k.dQ * (5 * 2 ^ ((Ds + 3) * s)) = 5 * (κ.k.dQ * 2 ^ ((Ds + 3) * s)) := by ring
  rw [e]
  rw [e2] at hq
  omega

/-- **The HASH capacity** `need + needH ≤ Ko·2^{⌊n/8⌋}` on small `x`. -/
theorem capH_bound (κ : FreeK2) (Ds : ℕ) : ∃ Ko : ℕ, ∀ x : FreeIn, FreeSmall Ds x →
    need κ.base x + needH κ x ≤ Ko * 2 ^ (x.n / 8) := by
  obtain ⟨Ko1, hK1⟩ := cap_bound κ Ds
  obtain ⟨K0, hK0⟩ := bsq_le_n16 (Ds + 3)
  refine ⟨Ko1 + (κ.k.dQ + 2) * 6 * 2 ^ K0, fun x hs => ?_⟩
  have h1 := hK1 x hs
  have h2 := needH_extra κ Ds x hs
  have h3 : (2 : ℕ) ^ ((Ds + 3) * (natBitLength x.n + 1) ^ 2) ≤ 2 ^ K0 * 2 ^ (x.n / 8) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by have := hK0 x.n; omega)
  have h4 := Nat.mul_le_mul_left ((κ.k.dQ + 2) * 6) h3
  unfold needH
  have e : (Ko1 + (κ.k.dQ + 2) * 6 * 2 ^ K0) * 2 ^ (x.n / 8) =
      Ko1 * 2 ^ (x.n / 8) + (κ.k.dQ + 2) * 6 * (2 ^ K0 * 2 ^ (x.n / 8)) := by ring
  rw [e]
  omega

/-- **`ok_le`** at `freeProgH κ`. -/
theorem okH_le (κ : FreeK2) : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), FreeSmall Ds x →
    Ko * 2 ^ (x.n / 8) ≤ cap → (freeProgH κ).ok cap x := fun Ds => by
  obtain ⟨Ko, hKo⟩ := capH_bound κ Ds
  exact ⟨Ko, fun _ x hs hc => (hKo x hs).trans hc⟩

/-- **`cost_le`** at `freeProgH κ`. -/
theorem costH_le (κ : FreeK2) : ∃ Kc : ℕ, ∀ (cap : ℕ) (x : FreeIn), (freeProgH κ).cost cap x ≤ Kc * (cap + 1) ^ 2 :=
  ⟨(201 + fixNH κ) * 800, fun cap _ => by
    show (201 + fixNH κ) * PrimAsm.UnaryPow.sq cap ≤ (201 + fixNH κ) * 800 * (cap + 1) ^ 2
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    unfold PrimAsm.UnaryPow.sq
    nlinarith⟩

theorem valH_le_need (κ : FreeK2) (x : FreeIn) (j : Fin 7) (hj : j.val ≠ 6) :
    freeValH κ x j ≤ need κ.base x + needH κ x := by
  have h2 := val2_le_need κ x j hj
  by_cases hj2 : j = 2
  · subst hj2
    show κ.k.dQ * (β x * (β x * β x) + x.kh + x.kh + β x) ≤ _
    unfold needH
    omega
  · have e : freeValH κ x j = freeVal2 κ x j := by
      fin_cases j <;> first | rfl | exact absurd rfl hj2
    rw [e]
    unfold needH
    omega

/-- **`val_le`** at `freeProgH κ`. -/
theorem valH_le (κ : FreeK2) : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), FreeSmall Ds x → j.val ≠ 6 →
    (freeProgH κ).val x j ≤ Kv * 2 ^ (x.n / 8) := fun Ds => by
  obtain ⟨Ko, hKo⟩ := capH_bound κ Ds
  exact ⟨Ko, fun x j hs hj => (valH_le_need κ x j hj).trans (hKo x hs)⟩

/-- **`rho_le`** at `freeProgH κ`. -/
theorem rhoH_le (κ : FreeK2) : ∃ Kr Dr : ℕ, ∀ x : FreeIn, (freeProgH κ).val x 6 ≤ Kr * (x.n + 1) ^ Dr := by
  obtain ⟨Kr, Dr, h⟩ := rho2_le κ
  exact ⟨Kr, Dr, fun x => h x⟩

/-- **The pad** at `freeProgH κ` (the v2 program's `ρ`). -/
theorem padH (κ : FreeK2) (x : FreeIn) :
    2 ^ (freeProgH κ).val x 6 ≤ (4 ^ κ.k.dA + 1) * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.k.dA + κ.k.dR) +
      2 ^ (x.n / 2) * 2 ^ ((κ.k.dA + κ.k.dR) * (natBitLength x.n + 1) ^ 2)) :=
  pad2 κ x

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen
