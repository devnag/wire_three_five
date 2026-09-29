import Proof.Wire_3_5.Transfer.TransferUnionComplete
import Proof.Wire_3_5.UnionMachine.UnionAtomsOk

/-! # The honest guess passes the atom test (the satisfiability of `CompleteForEventuallyOk`)

"It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid" (P3:3670-3671); the
completeness the paper uses is at the guess it constructs from the bounded approximate sums of Lemma tr:xor
(Case 2, P3:3711-3729). **`exists_unionAccepts_ok`** is `exists_unionAccepts` (the accepting guess of a sparse
witness, P3:3564-3614) with its atom test: the guess's grid atoms are the family's atoms or the constant, each within
the description envelope by the hypotheses `hdescC`, `hdescK` (the proof's `hdesc`), so the guess is accepted AND
passes `AtomsOkG`.

Paper quantity of the main type: the constructed guess, accepted by the union machine with every atom in the
envelope `(q+1)^descDeg`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR uMean_mono)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

section Build
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (m : Mode)
variable {J : PcppVar (S.pcppOf z oracle) → Type}

/-- **The honest guess is accepted and passes the atom test** (`exists_unionAccepts` with `AtomsOkG`, P3:3670). -/
theorem exists_unionAccepts_ok (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true)
    [∀ X, Fintype (J X)] (C : ∀ X, J X → m.Circuit (S.request z oracle).arity) (α : ∀ X, J X → ℝ)
    (hT : ∀ X x, 0 ≤ ∑ j, α X j * bitR (m.eval (C X j) x) ∧ ∑ j, α X j * bitR (m.eval (C X j) x) ≤ 1)
    (happrox : uMean (fun p : Fin (2 ^ (S.pcppOf z oracle).clauseBits) × Fin 2 × BitInput (S.request z oracle).arity =>
      |∑ j, α (posVar (S.pcppOf z oracle) p.1 p.2.1) j *
          bitR (m.eval (C (posVar (S.pcppOf z oracle) p.1 p.2.1) j) p.2.2) -
        honestBit (S.pcppOf z oracle) (S.pcppOf z oracle).honestAuxiliary
          (posVar (S.pcppOf z oracle) p.1 p.2.1) p.2.2|) ≤ (cparams.ζ : ℝ))
    (hmass : ∀ X, ∑ j, |α X j| ≤ (S.gridMass (S.request z oracle).arity : ℝ))
    (hΛ : 1 ≤ (S.gridMass (S.request z oracle).arity : ℝ)) (hs : 1 ≤ S.gridSize (S.request z oracle).arity)
    (hsδ : 19 * (S.gridMass (S.request z oracle).arity : ℝ) ^ 4 ≤
      (S.gridSize (S.request z oracle).arity : ℝ) ^ 2 * (cparams.δ : ℝ) ^ 4)
    (hStar : I.StarAt (S.request z oracle).arity) (hFit : B.FitsAt (S.request z oracle).arity)
    (hname : 2 ≤ I.nameCount)
    (hdescC : ∀ X j, m.descriptionBits (C X j) ≤ ((S.request z oracle).arity + 1) ^ I.descDeg)
    (hdescK : m.descriptionBits (S.constAtom m (S.request z oracle).arity) ≤
      ((S.request z oracle).arity + 1) ^ I.descDeg)
    (hdescP : ∀ Sp, m.descriptionBits (S.parityAtom m (S.request z oracle).arity Sp) ≤
      ((S.request z oracle).arity + 1) ^ I.descDeg)
    (K : ℕ) (hKC : ∀ X j, (m.gates (C X j)).length ≤ K)
    (hKP : ∀ Sp, (m.gates (S.parityAtom m (S.request z oracle).arity Sp)).length ≤ K)
    (hlen : (S.gridSize (S.request z oracle).arity + 1) * K ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (hbC : ∀ X j, ∀ gt ∈ m.gates (C X j), gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (hbP : ∀ Sp, ∀ gt ∈ m.gates (S.parityAtom m (S.request z oracle).arity Sp),
      gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg)
    (w Cpar : ℝ) (hw0 : 0 ≤ w) (hCpar : 0 ≤ Cpar) (hwC : ∀ X j, ((m.gates (C X j)).wires : ℝ) ≤ w)
    (hwP : ∀ Sp, ((m.gates (S.parityAtom m (S.request z oracle).arity Sp)).wires : ℝ) ≤
      Cpar * ((S.request z oracle).arity : ℝ) ^ 2)
    (hcap : (I.starParams (S.request z oracle).arity hStar).popRate *
        ((S.gridSize (S.request z oracle).arity : ℝ) * w + Cpar * ((S.request z oracle).arity : ℝ) ^ 2) ≤
      (cparams.β : ℝ) * (B.capOf m (S.request z oracle).arity : ℝ))
    (spectrum : ExpanderSpectrumContract)
    (hξ : 1 / (2 : ℝ) ^ (I.filterParams m (S.request z oracle).arity).errExp ≤ (cparams.ξ : ℝ))
    (hD : (1 + (S.gridMass (S.request z oracle).arity : ℝ)) ^ 4 *
        ((S.request z oracle).arity : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ))
    (Ko Ks Kc : ℕ) (hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko)
    (hKs : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ Ks)
    (hcodeC : ∀ X j, (natWord (m.code (C X j))).length ≤ Kc)
    (hcodeK : (natWord (m.code (S.constAtom m (S.request z oracle).arity))).length ≤ Kc)
    (hbudget : 1 + Ko + ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits) *
      (S.gridSize (S.request z oracle).arity * (Ks + Kc)) ≤ N / 16) :
    ∃ g : UnionGuess S z, UnionAccepts S P z g ∧ AtomsOkG g := by
  have hδ0 : (0 : ℝ) ≤ cparams.δ := by exact_mod_cast cparams.δ_nonneg
  -- the sparse witness of every named variable, at one `s` and grid
  obtain ⟨σ, atom, hσ, -, hL4⟩ := sparseGuess_exists (fun X j x => m.eval (C X j) x) α
    (S.gridMass (S.request z oracle).arity : ℝ) (S.gridSize (S.request z oracle).arity) hs hΛ hmass
    (cparams.δ : ℝ) hsδ
  set g := guessOfWitness S z oracle m C σ atom with hg
  have hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro X a
    show witnessSign S z oracle σ atom X a ∈ _
    unfold witnessSign
    split
    · exact hσ X a
    · simp
  -- the completeness witness: the guess's grid sums are the sparse witnesses
  have wit : CompletenessWitness g.pcpp g.pcpp.honestAuxiliary (fun X x => ∑ j, α X j * bitR (m.eval (C X j) x))
      (g.forms hsign).guess cparams.ζ cparams.δ := by
    refine ⟨hT, happrox, fun X => ?_, by exact_mod_cast cparams.ζ_nonneg, hδ0⟩
    refine le_of_eq_of_le ?_ (hL4 X)
    refine congrArg uMean (funext fun x => ?_)
    congr 2
    rw [g.forms_guess hsign X x]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    show (witnessSign S z oracle σ atom X a : ℝ) * bitR (m.eval (witnessAtom S z oracle m C atom X a) x) = _
    unfold witnessSign witnessAtom
    cases atom X a
    · simp
    · rfl
  -- the calls, the missing mass, the word
  have hdesc : ∀ a : g.AtomIx, g.mode.descriptionBits (g.circ a) ≤ (g.q + 1) ^ I.descDeg := by
    rintro (u | ⟨X, b⟩ | X)
    · exact hdescK
    · show m.descriptionBits (witnessAtom S z oracle m C atom X b) ≤ _
      unfold witnessAtom
      split
      · exact hdescC X _
      · exact hdescK
    · exact hdescP _
  have hKA : ∀ X a, (g.mode.gates (g.atom X a)).length ≤ K := by
    intro X a
    show (m.gates (witnessAtom S z oracle m C atom X a)).length ≤ K
    unfold witnessAtom
    split
    · exact hKC X _
    · rw [S.constAtom_gates]; exact Nat.zero_le _
  have hbA : ∀ X a, ∀ gt ∈ g.mode.gates (g.atom X a), gt.encodingBits ≤ (g.q + 1) ^ I.carrierDeg := by
    intro X a gt hgt
    change gt ∈ m.gates (witnessAtom S z oracle m C atom X a) at hgt
    unfold witnessAtom at hgt
    split at hgt
    · exact hbC X _ gt hgt
    · rw [S.constAtom_gates] at hgt; cases hgt
  have henv : ∀ X, (g.carrier X).WithinEnvelope I.carrierDeg :=
    g.carrier_envelope K hKA (fun X => hKP _) hlen hbA (fun X => hbP _)
  have hwA : ∀ X a, ((g.mode.gates (g.atom X a)).wires : ℝ) ≤ w := by
    intro X a
    show ((m.gates (witnessAtom S z oracle m C atom X a)).wires : ℝ) ≤ w
    unfold witnessAtom
    split
    · exact hwC X _
    · rw [S.constAtom_gates]
      show ((0 : ℕ) : ℝ) ≤ w
      simpa using hw0
  obtain ⟨hVcall, hQcall, hμcall⟩ := g.calls_admissible hStar hFit hname henv hdesc
  have hmissing := g.missing_at_guess hStar spectrum cparams.β cparams.ξ w Cpar (by exact_mod_cast cparams.ξ_nonneg)
    hξ henv (g.carrier_wires_le w Cpar hwA (fun X => hwP _) hCpar) hcap
  have hword : g.word.length ≤ N / 16 := by
    refine (g.word_length_le Ko Ks Kc hO (fun X a => hKs _ (hsign X a)) fun X a => ?_).trans hbudget
    show (natWord (m.code (witnessAtom S z oracle m C atom X a))).length ≤ Kc
    unfold witnessAtom
    split
    · exact hcodeC X _
    · exact hcodeK
  exact ⟨g, g.unionAccepts_of_parts P cparams hsize hsign hword hVcall hQcall hμcall htaut _ wit hmissing hD,
    fun X a => hdesc (Sum.inr (Sum.inl (X, a)))⟩

end Build

end Union

end NearCubicWires.WireExponent3_5.Transfer
