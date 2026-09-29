import Proof.Wire_3_5.UnionMachine.RoundDiv
import Proof.CaseAnalysis.FinalWordFunctionDock

/-! # C6, part 3d: one primitive call and its rounded answer (P3:3669-3691, 3797-3807)

The union machine calls the fused primitive's estimator (`P.estimator`, an `OrdinaryWordFunction` within
`B.callBudget`) on each admissible scheduled request and rounds the printed answer to `p` bits. This module is that
step at ANY caller layout:
* the call is base's rewound dock (`WordFunction.reset` + `C10WordFunctionDock.rewound_dock`), paying
  `2·callBudget + 2`;
* its output tape IS stream `0` of the rounding program's bank (`rs 0 = es outputTape`), so the answer's word
  `ratWord v` is read in place;
* the rounding program (`round_spec`) leaves `MP − MN = ⌊v·2^p⌋` (`v = P.value req`).
The hypothesis `|num| < 4·den` of the division holds on every admissible call (`value_small`): `|v − truth| ≤ n^{−D}`
and `truth ∈ [0,1]` (`truth_mem`). **`callRound_step`**: the composed machine's `Step`; everything outside the two
slot images is untouched. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires.WireExponent3_5.Cost

/-! ## Admissible answers are small -/

section Small
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- **The masked mean is a probability.** -/
theorem truth_mem (req : PrimRequest) : 0 ≤ I.truth req ∧ I.truth req ≤ 1 := by
  unfold PrimitiveInputs.truth maskedMean
  have hterm : ∀ e x, (0 : ℝ) ≤ (if I.mask req e x then (1 : ℝ) else 0) *
      ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ∧
      (if I.mask req e x then (1 : ℝ) else 0) * ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 := by
    intro e x
    have h1 : ∀ i, (0 : ℝ) ≤ (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ∧
        (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 := by
      intro i; split_ifs <;> norm_num
    have hp0 : (0 : ℝ) ≤ ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) :=
      Finset.prod_nonneg fun i _ => (h1 i).1
    have hp1 : ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 :=
      Finset.prod_le_one (fun i _ => (h1 i).1) (fun i _ => (h1 i).2)
    split_ifs <;> constructor <;> nlinarith
  set S := ∑ e, ∑ x, (if I.mask req e x then (1 : ℝ) else 0) *
      ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun x _ => (hterm e x).1
  have hS1 : S ≤ (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by
    calc S ≤ ∑ _e : I.Seed req.mode req.n, ∑ _x : BitInput req.n, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun x _ => (hterm e x).2
      _ = (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by
          simp [Finset.card_univ, BitInput, Fintype.card_fun, Fintype.card_bool]
  have hden : (0 : ℝ) ≤ (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by positivity
  refine ⟨div_nonneg hS0 hden, ?_⟩
  rcases hden.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · exact (div_le_one hpos).mpr hS1

/-- **An admissible call's answer is small**: `|num| < 4·den`. -/
theorem value_small (P : FusedPrimitive I) (req : PrimRequest) (h : I.Call req) :
    (P.value req).num.natAbs < 4 * (P.value req).den := by
  have he := P.error req h
  have ht := truth_mem I req
  have hD : (req.n : ℝ) ^ (-(I.D : ℝ)) ≤ 1 := by
    rcases Nat.eq_zero_or_pos req.n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.zero_rpow (by have := I.D_pos; norm_cast; omega)]; norm_num
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpos) (by have := I.D_pos; simp)
  have hv : |((P.value req : ℚ) : ℝ)| < 4 := by
    rw [abs_lt]; constructor <;> linarith [(abs_le.mp he).1, (abs_le.mp he).2]
  have hq : |P.value req| < 4 := by exact_mod_cast hv
  set v := P.value req with hvdef
  have hd : (0 : ℚ) < v.den := by exact_mod_cast v.den_pos
  have hnum : (v.num.natAbs : ℚ) = |v| * v.den := by
    have e1 : (v.num : ℚ) = v * v.den := by rw [Rat.mul_den_eq_num]
    have e2 : (v.num.natAbs : ℚ) = |(v.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e2, e1, abs_mul, abs_of_pos hd]
  have : (v.num.natAbs : ℚ) < 4 * v.den := by rw [hnum]; nlinarith [abs_nonneg v]
  exact_mod_cast this

end Small

/-! ## The call and the rounding, docked -/

section CallRound
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The rewound estimator. -/
noncomputable abbrev estRW := P.estimator.reset

/-- The rounding program's compiled machine. -/
abbrev roundM : Machine (2 + 2 + 14) roundP.toProg.size := roundP.toProg.compile

/-- **The call-and-round machine** at the slot maps `es` (estimator) and `rs` (rounding bank). -/
noncomputable def callRoundM {N : ℕ} (es : Fin (estRW P).program.tapeCount → Fin N) (rs : Fin (2 + 2 + 14) → Fin N) :
    Machine N ((estRW P).program.stateCount + roundP.toProg.size) :=
  Composition.machine (RecoveryFocus.machine es (estRW P).program.machine) (RecoveryFocus.machine rs roundM)

end CallRound


end NearCubicWires.WireExponent3_5.UnionMachine
