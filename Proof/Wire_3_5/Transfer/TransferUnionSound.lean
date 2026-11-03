import Lean
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.Transfer.TransferUnionSoundBase


noncomputable section


/-! # `tr:soundness` for the union machine: no accepting guess on a no-instance, and `OneSided` from `SoundFor`

Realizes Lemma `tr:soundness` (P3:3504-3554) at the union machine's acceptance condition: "For sufficiently small fixed
`v₀, ε₀`, no branch of the weak machine accepts a hierarchy no-instance, for all sufficiently large source lengths.
This holds for every syntactically legal real-valued sparse guess [...] and for proof-dependent, seed-dependent
masks." A branch is a guess `g` with `UnionAccepts S P z g`. Its grid sums, constant and encoding
parities are the atom forms (`UnionGuess.forms`), so the machine's estimates `V̂, Q̂, μ̂` formed from the fused
primitive's printed values are within `(1+Λ̄)⁴q^{−D} ≤ ε₀` of the tests (the `seed_propagated_*`, which consume
`FusedPrimitive.error` on the admissible calls), and the masked tests at the seed's filters cannot pass on a
no-instance: the rounding (`tr:rounding`, corrected), the one-sided mask (`tr:one-sided`), pointwise PCPP soundness
(`PointwisePCPPAlgorithm.sound`) and the outer soundness `N^{−10}` (the chain, here with real estimates:
`masked_soundness_real`).

Main results: **`UnionGuess.not_unionAccepts`** (at a no-instance with `N^{−10} ≤ η` and `(1+Λ̄(q))⁴q^{−D} ≤ ε₀`, no
guess is accepted) and **`oneSided_of_soundFor`** (every machine with `SoundFor` is `OneSided` for the hierarchy
language, the seed's refuter premise). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The atoms' functions. -/
abbrev atoms : g.AtomIx → BitInput g.q → Bool := fun a x => g.mode.eval (g.circ a) x

theorem linForm_wOne (x : BitInput g.q) : linForm g.atoms g.wOne x = 1 := by
  unfold linForm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, g.wOne (Sum.inl u) * bitR (g.atoms (Sum.inl u) x) = 1 := by
    rw [Fintype.sum_unique]
    show 1 * bitR (g.mode.eval (S.constAtom g.mode g.q) x) = 1
    rw [S.constAtom_eval]; simp [bitR]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, g.wOne (Sum.inr (Sum.inl p)) * bitR (g.atoms (Sum.inr (Sum.inl p)) x) =
      0 := Finset.sum_eq_zero fun p _ => by simp [wOne]
  have h3 : ∑ Y : PcppVar g.pcpp, g.wOne (Sum.inr (Sum.inr Y)) * bitR (g.atoms (Sum.inr (Sum.inr Y)) x) = 0 :=
    Finset.sum_eq_zero fun Y _ => by simp [wOne]
  rw [h1, h2, h3]; ring

theorem linForm_wE (X : PcppVar g.pcpp) (x : BitInput g.q) :
    linForm g.atoms (g.wE X) x = bitR (parityOn (g.support X) x) := by
  unfold linForm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, g.wE X (Sum.inl u) * bitR (g.atoms (Sum.inl u) x) = 0 :=
    Finset.sum_eq_zero fun u _ => by simp [wE]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, g.wE X (Sum.inr (Sum.inl p)) * bitR (g.atoms (Sum.inr (Sum.inl p)) x) =
      0 := Finset.sum_eq_zero fun p _ => by simp [wE]
  have h3 : ∑ Y : PcppVar g.pcpp, g.wE X (Sum.inr (Sum.inr Y)) * bitR (g.atoms (Sum.inr (Sum.inr Y)) x) =
      bitR (g.atoms (Sum.inr (Sum.inr X)) x) := by
    rw [Finset.sum_eq_single X]
    · simp [wE]
    · intro Y _ hY; simp [wE, hY]
    · simp
  rw [h1, h2, h3, zero_add, zero_add]
  show bitR (g.mode.eval (S.parityAtom g.mode g.q (g.support X)) x) = _
  rw [S.parityAtom_eval]

theorem constraint_eq (X : PcppVar g.pcpp) (x : BitInput g.q) :
    systematicConstraint g.pcpp x X = if g.sysBit X then some (parityOn (g.support X) x) else none := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) X
  · simp [systematicConstraint, sysBit, support, i.isLt]
  · simp [systematicConstraint, sysBit]

theorem linMass_wS (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (X : PcppVar g.pcpp) :
    linMass (g.wS X) ≤ S.gridMass g.q := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  have hc : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) / g.s := div_nonneg hL (Nat.cast_nonneg _)
  have hsum : linMass (g.wS X) = ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| := by
    unfold linMass
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    have h1 : ∑ u : Unit, |g.wS X (Sum.inl u)| = 0 := Finset.sum_eq_zero fun u _ => by simp [wS]
    have h3 : ∑ Y : PcppVar g.pcpp, |g.wS X (Sum.inr (Sum.inr Y))| = 0 :=
      Finset.sum_eq_zero fun Y _ => by simp [wS]
    have h2 : ∑ Y : PcppVar g.pcpp, ∑ a : Fin g.s, |g.wS X (Sum.inr (Sum.inl (Y, a)))| =
        ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| := by
      rw [Finset.sum_eq_single X]
      · exact Finset.sum_congr rfl fun a _ => by simp [wS]
      · intro Y _ hY; exact Finset.sum_eq_zero fun a _ => by simp [wS, hY]
      · simp
    rw [h1, h2, h3, zero_add, add_zero]
  have habs : ∀ a, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| ≤ (S.gridMass g.q : ℝ) / g.s := by
    intro a
    rw [abs_mul, abs_of_nonneg hc]
    have h := hsign X a
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have : |(g.sign X a : ℝ)| ≤ 1 := by rcases h with h | h | h <;> simp [h]
    exact mul_le_of_le_one_right hc this
  rw [hsum]
  calc ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| ≤ ∑ _a : Fin g.s, (S.gridMass g.q : ℝ) / g.s :=
        Finset.sum_le_sum fun a _ => habs a
    _ ≤ (S.gridMass g.q : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos g.s with h0 | hpos
        · rw [h0]; simpa using hL
        · rw [mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')]

theorem linMass_wOne : linMass g.wOne ≤ 1 := by
  unfold linMass
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [wOne]

theorem linMass_wE (X : PcppVar g.pcpp) : linMass (g.wE X) ≤ 1 := by
  unfold linMass
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, |g.wE X (Sum.inl u)| = 0 := Finset.sum_eq_zero fun u _ => by simp [wE]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, |g.wE X (Sum.inr (Sum.inl p))| = 0 :=
    Finset.sum_eq_zero fun p _ => by simp [wE]
  have h3 : ∑ Y : PcppVar g.pcpp, |g.wE X (Sum.inr (Sum.inr Y))| = 1 := by
    rw [Finset.sum_eq_single X]
    · simp [wE]
    · intro Y _ hY; simp [wE, hY]
    · simp
  rw [h1, h2, h3]; norm_num

/-- The guess's atom forms (M4): its grid sums, the constant and the encoding parities, at mass `Λ̄(q)`. -/
noncomputable def forms (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) :
    AtomForms g.pcpp g.atoms (S.gridMass g.q) where
  wS := g.wS
  wOne := g.wOne
  wE := g.wE
  sys := g.sysBit
  parity := fun X x => parityOn (g.support X) x
  one_eq := g.linForm_wOne
  E_eq := g.linForm_wE
  constraint_eq := g.constraint_eq
  S_mass := g.linMass_wS hsign
  one_mass := g.linMass_wOne
  E_mass := g.linMass_wE

end UnionGuess

/-- On a guess passing the length gate (`N = 2^a` past the onset), the PCPP arity is the width `q(N)`. -/
theorem q_eq_width (S : UnionSetup I) {N : ℕ} {z : BitInput N} (g : UnionGuess S z)
    (hN : N = 2 ^ Nat.log 2 N) (hon : S.onset ≤ Nat.log 2 N) : g.q = S.width N := by
  have hq : S.pcppAlg.minimumArity ≤ NearCubicGates.Close.Outer.width S.mw S.SV N := by
    have h := S.onset_arity (Nat.log 2 N) hon
    rwa [← hN] at h
  show (S.request z g.pair).arity = _
  unfold UnionSetup.request
  rw [W3.NearCubicWires.RepairSource.Outer3.requestAt_of S.mw S.SV S.pcppAlg (Nat.log 2 N) g.pair hq]
  rfl

end Union

end NearCubicWires.WireExponent3_5.Transfer

end
