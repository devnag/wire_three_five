import Proof.Wire_3_5.Primitive.SeedFix.S3Maj
import Proof.Wire_3_5.FinalPass.TermEval

/-! # S3, part 3: stage 8 with the factor in a register, on the evaluator's layout (P3:3170-3178)

"Evaluate the reported lookups" (P3:3046-3048): one SYM circuit's factor is stage 8's test `termOk X W R⁺ R⁻` of its
corner word `X`, its top table `W` and the reports `R^±`. A word program cannot branch on the result cell, so the
factor lands in a register: `term8K` is C5's stage 8 (`Term`, verified) with the final read into the clamp register
`K`: **`term8K_spec`**. Lifted to the
evaluator's layout (C5's `RM.liftR`; `X` on `sX`, `W` on `sTop`, the reports in `26`/`27`, the factor in `28`, scratch
`0 … 6`): **`termS_spec`**, relationally.

Paper quantity of the main type: stage 8's factor `termOk X W p m` (the circuit's `R̂` term at a sampled point). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Term

section Term
variable (inp : Fin 2 → List Bool) (cap : ℕ) (h0 h1 : ℕ)

/-- Read the entry at the head into `K` (`0` at the table's end). -/
def rd8K : TProg := .ifs 1 (.seq (RM.fwdC 1 rT) (.ifs 1 (.inc rK) .skip)) .skip

theorem rd8K_spec (rest : List Bool) (x t p m g s n a f : ℕ) (c : Bool) (V : List Bool)
    (hV : (inp 1).drop (h1 + t) = frameP V ++ false :: rest) (ht : t < cap) (hk : 1 ≤ cap) :
    RExec inp cap rd8K (S8 h0 h1 x t p m g s n a f 0 c)
      (S8 h0 h1 x (t + min 1 V.length) p m g s n a f (V.getD 0 false).toNat c) 11 := by
  rcases V with _ | ⟨w, V⟩
  · have hr : readTapeBit (inp 1) (h1 + t) = false := ListEval.read_of_cons (by simpa using hV)
    exact RExec.cast inp cap (RExec.ifsF hr (RExec.skip _)) (by s8_args) (by omega)
  · have hV0 : (inp 1).drop (h1 + t) = true :: w :: (frameP V ++ false :: rest) := by simpa [frameP] using hV
    have hr : readTapeBit (inp 1) (h1 + t) = true := ListEval.read_of_cons hV0
    have hr1 : readTapeBit (inp 1) (h1 + (t + 1)) = w := by
      rw [← Nat.add_assoc]; exact ListEval.read_of_cons (ListEval.drop_succ_of_cons hV0)
    have f1 := fT_spec inp cap h0 h1 x t p m g s n a f 0 c ht
    cases w
    · exact RExec.cast inp cap (RExec.ifsT hr (RExec.seq f1 (RExec.ifsF hr1 (RExec.skip _)))) (by s8_args)
        (by omega)
    · have i1 := RExec.inc (inp := inp) (cap := cap) rK (S8 h0 h1 x (t + 1) p m g s n a f 0 c) (show 0 < cap by omega)
      rw [S8_val_K, S8_setv_K] at i1
      exact RExec.cast inp cap (RExec.ifsT hr (RExec.seq f1 (RExec.ifsT hr1 i1))) (by s8_args) (by omega)

/-- Walk to entry `S`, read it into `K`, rewind the table. -/
def lookK : TProg := .seq idxL (.seq rd8K (RM.rewind 1 rT))

theorem lookK_spec (rest : List Bool) (W : List Bool) (s : ℕ) (c : Bool)
    (hW : (inp 1).drop h1 = frameP W ++ false :: rest) (hc : 2 * W.length + 1 ≤ cap) (hs : s ≤ cap) :
    RExec inp cap lookK (S8 h0 h1 0 0 0 0 0 s 0 0 0 0 c) (S8 h0 h1 0 0 0 0 0 0 0 0 0 (W.getD s false).toNat c)
      (16 * s + 10 * W.length + 22) := by
  have hmin : min s W.length ≤ W.length := Nat.min_le_right _ _
  have s1 := idxL_spec inp cap h0 h1 rest 0 0 0 0 0 0 0 0 c s W 0 (by simpa using hW) (by omega) hs
  rw [Nat.zero_add] at s1
  have hV : (inp 1).drop (h1 + 2 * min s W.length) = frameP (W.drop s) ++ false :: rest := by
    rw [← List.drop_drop, hW, frameP_drop]
  have hdl : min 1 (W.drop s).length ≤ 1 := Nat.min_le_left _ _
  have s2 := rd8K_spec inp cap h0 h1 rest 0 (2 * min s W.length) 0 0 0 0 0 0 0 c (W.drop s) hV (by omega) (by omega)
  have hg : (W.drop s).getD 0 false = W.getD s false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [hg] at s2
  have s3 := rewind_spec inp cap 1 rT (2 * min s W.length + min 1 (W.drop s).length)
    (S8 h0 h1 0 (2 * min s W.length + min 1 (W.drop s).length) 0 0 0 0 0 0 0 (W.getD s false).toNat c) rfl
    (by show 2 * min s W.length + min 1 (W.drop s).length ≤ cap; omega)
  rw [S8_rewT] at s3
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 s3)) rfl (by omega)

/-- A negative score reads `0`; otherwise the table at `S`, into `K`. -/
def pickK : TProg := .ifr rF (.dec rF) lookK

theorem pickK_spec (rest : List Bool) (W : List Bool) (s : ℕ) (fb c : Bool)
    (hW : (inp 1).drop h1 = frameP W ++ false :: rest) (hc : 2 * W.length + 1 ≤ cap) (hs : s ≤ cap)
    (hs0 : fb = true → s = 0) :
    RExec inp cap pickK (S8 h0 h1 0 0 0 0 0 s 0 0 fb.toNat 0 c)
      (S8 h0 h1 0 0 0 0 0 0 0 0 0 (!fb && W.getD s false).toNat c) (16 * s + 10 * W.length + 23) := by
  cases fb
  · exact RExec.cast inp cap (RExec.ifrF (S8_val_F ..) (lookK_spec inp cap h0 h1 rest W s c hW hc hs)) rfl (by omega)
  · have e := hs0 rfl
    subst e
    have d1 := RExec.dec (inp := inp) (cap := cap) rF (S8 h0 h1 0 0 0 0 0 0 0 0 (true).toNat 0 c)
      (by show 1 ≤ cap; omega)
    rw [S8_val_F, S8_setv_F] at d1
    exact RExec.cast inp cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) d1) (by s8_args) (by omega)

/-- **Stage 8 with the factor in `K`.** -/
def term8K : TProg := .seq count8 (.seq (RM.rewind 0 rX) (.seq phase2 (.seq sgnL pickK)))

/-- **Stage 8, one circuit's factor, in a register**: from the framed corner word (stream 0 at `h₀`), the framed top
table (stream 1 at `h₁`) and the reports `p, m`, the register `K` becomes `[termOk X W p m]`; every other register
ends at `0`, both heads return and the cell is unchanged. -/
theorem term8K_spec (X W : List Bool) (L p m : ℕ) (c : Bool) (rest0 rest1 : List Bool) (hl : X.length = 4 * L)
    (hX : (inp 0).drop h0 = frameP X ++ false :: rest0) (hW : (inp 1).drop h1 = frameP W ++ false :: rest1)
    (hcap : capOf8 L W.length p m ≤ cap) :
    RExec inp cap term8K (S8 h0 h1 0 0 p m 0 0 0 0 0 0 c) (S8 h0 h1 0 0 0 0 0 0 0 0 0 (termOk X W p m).toNat c)
      (cost8 L W.length p m + 2) := by
  unfold capOf8 at hcap
  have c1 := cnt_le_of_length 1 L X hl
  have c2 := cnt_le_of_length 2 L X hl
  have c3 := cnt_le_of_length 3 L X hl
  have s1 := count8_spec inp cap h0 h1 rest0 0 p m 0 0 0 c L X 0 0 0 0 hl (by simpa using hX) (by omega) (by omega)
    (by omega) (by omega)
  simp only [Nat.zero_add] at s1
  have s2 := rewind_spec inp cap 0 rX (8 * L) (S8 h0 h1 (8 * L) 0 p m L (cnt 1 X + cnt 2 X) (cnt 3 X) 0 0 0 c) rfl
    (by show 8 * L ≤ cap; omega)
  rw [S8_rewX] at s2
  have s3 := phase2_spec inp cap h0 h1 0 p m L (cnt 1 X + cnt 2 X) (cnt 3 X) c (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hcp : clampN L p ≤ L := by unfold clampN; split <;> omega
  have hcm : clampN L m ≤ L := by unfold clampN; split <;> omega
  generalize hS : cnt 1 X + cnt 2 X + clampN L p = S at s3
  generalize hN : cnt 3 X + clampN L m = N at s3
  have s4 := sgnL_spec inp cap h0 h1 0 0 0 0 0 0 0 c (by omega) N S 0 (by omega) (by omega) (by omega)
  have ef : (if S < N then 1 else 0) = (decide (S < N)).toNat := by by_cases h : S < N <;> simp [h]
  rw [ef] at s4
  have s5 := pickK_spec inp cap h0 h1 rest1 W (S - N) (decide (S < N)) c hW (by omega) (by omega)
    (fun h => by simp at h; omega)
  have hres : (!decide (S < N) && W.getD (S - N) false) = termOk X W p m := by
    rw [termOk_of_counts X W p m L (groups_of_length L X hl), hS, hN]
  rw [hres] at s5
  unfold cost8
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 s5)))) rfl (by omega)

end Term

/-! ## Stage 8 lifted -/

/-- Stage 8's streams: the corner word and the top table. -/
def fs8 : Fin 2 → Fin 14 := ![6, 13]
/-- Stage 8's registers: the reports at `26`/`27`, the scratch at `0 … 6`, the factor at `28`. -/
def fr8 : Fin 10 → Fin 32 := ![26, 27, 0, 1, 2, 3, 4, 5, 6, 28]

theorem fs8_inj : Function.Injective fs8 := by decide
theorem fr8_inj : Function.Injective fr8 := by decide

/-- **Stage 8 on the evaluator's layout.** -/
def termS : SM := term8K.liftR fs8 fr8

theorem termS_spec (cap : ℕ) (X W : List Bool) (L p m : ℕ) (rest0 rest1 : List Bool) (ω : SS)
    (hl : X.length = 4 * L) (hX : ω.st sX = frameP X ++ false :: rest0) (hW : ω.st sTop = frameP W ++ false :: rest1)
    (hshX : ω.sh sX = 0) (hshT : ω.sh sTop = 0) (hp : ω.val 26 = p) (hm : ω.val 27 = m) (hk : ω.val 28 = 0)
    (hz : ∀ q : Fin 32, q.val < 7 → ω.val q = 0) (hcap : capOf8 L W.length p m ≤ cap) :
    ∃ ω', WExec cap termS ω ω' (cost8 L W.length p m + 2) ∧ ω'.val 28 = (termOk X W p m).toNat ∧
      ω'.val 26 = 0 ∧ ω'.val 27 = 0 ∧ (∀ q : Fin 32, q.val < 7 → ω'.val q = 0) ∧ ω'.st = ω.st ∧
      (∀ i, ω'.sh i = ω.sh i) ∧ (∀ q : Fin 32, 7 ≤ q.val → q ≠ 26 → q ≠ 27 → q ≠ 28 → ω'.val q = ω.val q) ∧
      ω'.cell = ω.cell := by
  let inp : Fin 2 → List Bool := fun i => ω.st (fs8 i)
  have h8 := term8K_spec inp cap 0 0 X W L p m ω.cell rest0 rest1 hl (by simpa [inp, fs8] using hX)
    (by simpa [inp, fs8] using hW) hcap
  have hL : LiftRelR fs8 fr8 inp ω (S8 0 0 0 0 p m 0 0 0 0 0 0 ω.cell) := by
    refine ⟨fun i => ?_, fun i q => rfl, fun r => ?_, rfl⟩
    · fin_cases i
      · exact hshX
      · exact hshT
    · fin_cases r
      · exact hp
      · exact hm
      all_goals first | exact hk | exact hz _ (by decide)
  obtain ⟨ω', e, hL', hO'⟩ := RExec.liftR inp cap cap le_rfl fs8 fs8_inj fr8 fr8_inj h8 ω hL
  refine ⟨ω', e, hL'.val 9, hL'.val 0, hL'.val 1, fun q hq => ?_, hO'.1, fun i => ?_, fun q q1 q2 q3 q4 => ?_, ?_⟩
  · obtain ⟨k0, hk0⟩ := q
    simp only at hq
    have : k0 = 0 ∨ k0 = 1 ∨ k0 = 2 ∨ k0 = 3 ∨ k0 = 4 ∨ k0 = 5 ∨ k0 = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL'.val 2
    · exact hL'.val 3
    · exact hL'.val 4
    · exact hL'.val 5
    · exact hL'.val 6
    · exact hL'.val 7
    · exact hL'.val 8
  · by_cases h6 : i = sX
    · subst h6; exact (hL'.sh 0).trans hshX.symm
    · by_cases h13 : i = sTop
      · subst h13; exact (hL'.sh 1).trans hshT.symm
      · exact hO'.2.1 i (fun j => by fin_cases j <;> simp [fs8] <;> first | exact Ne.symm h6 | exact Ne.symm h13)
  · refine hO'.2.2 q (fun j => ?_)
    fin_cases j <;> simp [fr8] <;> first
      | exact Ne.symm q2 | exact Ne.symm q3 | exact Ne.symm q4
      | (intro e; rw [← e] at q1; simp at q1)
  · rw [hL'.cell]; rfl

end NearCubicWires.WireExponent3_5.PrimT.S3
