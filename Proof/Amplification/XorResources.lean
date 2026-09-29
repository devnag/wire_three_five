import Proof.Amplification.XorResourcesBits

/-! The exact CLW sampled witness supplies the old consumer's finite rational
resources. The source-facing statement is unchanged; the formerly explicit
RationalXorResources premise is proved here and removed from the application. -/
namespace NearCubicWires.RepairXor
open SourceInterfaces ExecutableInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem one_coefficient_bits (delta : ℚ) (n k : ℕ) :
    natBitLength (1 : ℚ).num.natAbs ≤ xorBits delta n k ∧
      natBitLength (1 : ℚ).den ≤ xorBits delta n k := by
  have h : 1 ≤ xorBits delta n k := by
    unfold xorBits
    nlinarith
  simpa [natBitLength] using And.intro h h

theorem sampleForm_resources (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {n k : ℕ} (hn : 1 ≤ n) (terms : List (ℚ × BoolFunction n))
    (form : SampleForm delta n k terms) :
    terms.length ≤ xorTermBound delta n k ∧
    (∀ term ∈ terms, natBitLength term.1.num.natAbs ≤ xorBits delta n k ∧
      natBitLength term.1.den ≤ xorBits delta n k) ∧
    terms.foldl (fun total term => total + |(term.1 : ℝ)|) 0 ≤
      1 / xorEpsilon (delta : ℝ) k := by
  cases form with
  | direct atom =>
    refine ⟨?_, ?_, ?_⟩
    · exact one_le_terms delta hd hh hn
    · intro term hterm
      have he : term = (1, atom) := List.mem_singleton.mp hterm
      subst term
      exact one_coefficient_bits delta n k
    · have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
      have hhr := radius_cast_half delta hh
      have he := epsilon_positive (delta : ℝ) hdr hhr k
      have hb := epsilon_le_half (delta : ℝ) hdr hhr k
      simp only [List.foldl_cons, List.foldl_nil, Rat.cast_one, abs_one, zero_add]
      apply (le_div_iff₀ he).2
      linarith
  | affine j hj hjk atoms hcount one _hone =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_singleton, hcount]
      exact sampleCount_add_one_le_terms delta hd hh hn hjk
    · have hb := affine_coefficient_bits delta hd hh n j k hj hjk
      intro term hterm
      rcases List.mem_append.mp hterm with hsample | hconstant
      · obtain ⟨atom, _hatom, rfl⟩ := List.mem_map.mp hsample
        simpa only [hcount] using hb.1
      · have he : term = ((1 - alphaQ delta j) / 2, one) := List.mem_singleton.mp hconstant
        subst term
        exact hb.2
    · exact affine_mass delta hd hh hjk atoms hcount one

end NearCubicWires.RepairXor
