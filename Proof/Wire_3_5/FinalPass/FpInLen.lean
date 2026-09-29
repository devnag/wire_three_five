import Proof.Wire_3_5.FinalPass.PlanFP

/-!
# The final pass reads at least `n` bits (for the S4 register capacity and the S5 `len_le`)

"The seeds a call fixes before its final pass" (P3:3165-3175) include `samp:printable`'s greedy sample, printed as
`Q` pairs of `kh`-bit halves, with `Q = 2^{⌊(5kh+3)/4⌋}·2^{13}·I·n^{2D}` (`Sampler.sampleCount`, P3:2994-3000). Every
call of the family is on-star (`PrimitiveInputs.Call` contains `StarAt`), so the final pass's input
`fpIn = req.word ++ seedWord` carries the whole sample, and `Q ≥ n` because `D ≥ 1` and `I ≥ 1`. Hence
`n ≤ |fpIn|`: every register bound polynomial in `n` is polynomial in `|fpIn|`, and the shared register capacity
`Kc·(|fpIn|+1)^Dc` of `SeedsWS2` / `S5Seam2` can hold `n`, the table lengths and the unary request.

Paper quantity of the main type: `n`, the call's input length, against the final pass's input word `fpIn`.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.FpInLen
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Primitive

/-- `n ≤ Q`: the printed sample has at least `n` pairs once `D ≥ 1` and the count argument is positive. -/
theorem n_le_sampleCount (kh D n I : ℕ) (hD : 1 ≤ D) (hI : 1 ≤ I) : n ≤ Sampler.sampleCount kh D n I := by
  unfold Sampler.sampleCount
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · calc n ≤ n ^ (2 * D) := Nat.le_self_pow (by omega) n
      _ ≤ 2 ^ 13 * I * n ^ (2 * D) := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) hI)
      _ ≤ 2 ^ ((5 * kh + 3) / 4) * (2 ^ 13 * I * n ^ (2 * D)) := Nat.le_mul_of_pos_left _ (by positivity)

/-- The printed sample has at least one bit per pair. -/
theorem length_le_sampleWord (kh : ℕ) (S : List (ℕ × ℕ)) : S.length ≤ (Sample.sampleWord kh S).length := by
  induction S with
  | nil => simp
  | cons p S ih =>
      simp only [Sample.sampleWord, List.flatMap_cons, List.length_append, RepairOrdinary.frame_length,
        List.length_cons] at ih ⊢
      omega

/-- **The seed word of an on-star call is at least `n` bits long** (both class modes). -/
theorem n_le_seedWord {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) (req : PrimRequest) (hs : I.StarAt req.n) :
    req.n ≤ (PrimAsm.Plan.seedWord I alg req).length := by
  obtain ⟨n, mode, a, ha, Cs, carriers, translation⟩ := req
  cases mode with
  | sym =>
      simp only [PrimAsm.Plan.seedWord, dif_pos hs]
      refine le_trans ?_ (length_le_sampleWord _ _)
      rw [List.length_ofFn]
      exact n_le_sampleCount _ _ _ _ I.D_pos (Nat.succ_pos _)
  | thr =>
      simp only [PrimAsm.Plan.seedWord, dif_pos hs, List.length_append]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine le_trans ?_ (length_le_sampleWord _ _)
      rw [List.length_ofFn]
      exact n_le_sampleCount _ _ _ _ I.D_pos (Nat.succ_pos _)

section Family
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- **`n ≤ |fpIn|`** at every request of every call family: the final pass's input word carries the printed sample. -/
theorem n_le_fpIn (r : PlanFP.FReq l F kclk coef A a ha) : r.1.n ≤ (PlanFP.fpIn l F kclk coef A a ha r).length := by
  unfold PlanFP.fpIn
  rw [List.length_append]
  exact le_trans (n_le_seedWord _ _ r.1 r.2.2.2.2.2.2.1) (Nat.le_add_left _ _)

end Family

end NearCubicWires.WireExponent3_5.FinalPass.FpInLen
