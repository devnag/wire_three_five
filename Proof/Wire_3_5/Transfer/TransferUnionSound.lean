import Proof.Wire_3_5.Transfer.TransferUnion

/-! # `tr:soundness` for the union machine: no accepting guess on a no-instance, and `OneSided` from `SoundFor`

Realizes Lemma `tr:soundness` (P3:3504-3554) at the union machine's acceptance condition: "For sufficiently small fixed
`v₀, ε₀`, no branch of the weak machine accepts a hierarchy no-instance, for all sufficiently large source lengths.
This holds for every syntactically legal real-valued sparse guess [...] and for proof-dependent, seed-dependent
masks." A branch is a guess `g` with `UnionAccepts S P z g`. Its grid sums, constant and encoding
parities are the atom forms (`UnionGuess.forms`), so the machine's estimates `V̂, Q̂, μ̂` formed from the fused
primitive's printed values are within `(1+Λ̄)⁴q^{−D} ≤ ε₀` of the tests (`seed_propagated_*`, which consume
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

/-- `tr:soundness` with real estimates (the machine's estimates are exact rationals; their real values are what the
accuracy bounds speak about): estimates within `ε₀` of the tests of any guess and any masks cannot pass
`tr:thresholds` on a PCPP that is pointwise sound and whose circuit the outer verifier accepts on at most `η` of the
random inputs. -/
theorem masked_soundness_real {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    (params : MaskedSoundnessParameters cp sp) {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp)
    (houter : uMean (fun x : BitInput q => bitR (H.eval x)) ≤ params.outerError)
    (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) (Vh Qh μh : ℝ)
    (hV : |Vh - testV pcpp S G| ≤ params.eps0) (hQ : |Qh - testQ pcpp S G| ≤ params.eps0)
    (hμ : |μh - testMu pcpp S G| ≤ params.eps0) (hVp : Vh ≤ 2 * (params.v0 : ℝ)) (hQp : Qh ≤ 1 + (params.v0 : ℝ))
    (hμp : (params.threshold : ℝ) ≤ μh) : False := by
  have hv0 : (0 : ℝ) < params.v0 := by exact_mod_cast params.v0_pos
  have hv24 : (params.v0 : ℝ) ≤ 1 / 24 :=
    calc (params.v0 : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) := Rat.cast_le.mpr params.v0_le
      _ = 1 / 24 := by norm_num
  have hεv : (params.eps0 : ℝ) ≤ params.v0 := by exact_mod_cast params.eps0_le_v0
  have hV' : testV pcpp S G ≤ 3 * (params.v0 : ℝ) := by linarith [(abs_le.mp hV).1]
  have hQ' : testQ pcpp S G ≤ 1 + 2 * (params.v0 : ℝ) := by linarith [(abs_le.mp hQ).1]
  have h1 := testMu_le_rounded pcpp S G params.v0 hv0 hv24 hV' hQ'
  have h2 := maskedRoundedScore_le pcpp S G
  have h3 := roundedScore_le_soundness pcpp params.sp_nonneg hsound S
  have h4 := (abs_le.mp hμ).2
  have hmid := params.thresholdAboveMidpoint
  have hres := params.roundingReserve
  have hout := params.outerReserve
  linarith

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

/-- The guess's atom forms: its grid sums, the constant and the encoding parities, at mass `Λ̄(q)`. -/
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

/-- The PCPP arity is at least the native width. -/
theorem nativeWidth_le_q (S : UnionSetup I) {N : ℕ} {z : BitInput N} (g : UnionGuess S z) :
    S.pcp.nativeWidth N ≤ g.q :=
  le_max_left _ _

end Union

end NearCubicWires.WireExponent3_5.Transfer
