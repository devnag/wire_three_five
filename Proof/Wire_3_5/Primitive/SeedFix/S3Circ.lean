import Proof.Wire_3_5.Primitive.SeedFix.S3Term
import Proof.Wire_3_5.Primitive.SeedFix.TabRef

/-! # S3, part 5: one SYM circuit's factor at a sampled point, on the evaluator's layout (P3:3170-3178)

"Evaluate the reported lookups at the sampled pairs" (P3:3046-3048): one circuit's factor of `R̂` at the list seed
`e'` is stage 8's test `termOk X W R⁺ R⁻` of the circuit's corner word `X = cornerWord (G.map eval) c u v` (stage 2
on its bottom gates `G`), its top table `W`, and the amplified list's reports `R^± = flatReportFast Pl e' (popBits ± X)`
(stage 3, then the majority machine on the seed's flat table). **`circS`** runs stage 2, the `+` population, the
majority machine, the report into `26`, the population blanked, the `−` population, the majority machine, the report
into `27`, the population blanked, stage 8: **`circS_spec`**: the factor in `28`, every scratch register `0 … 27` at
`0`, the population blank again, the compared state blank, the corner word, the accumulators and the template left on
their streams, every other stream and every head kept.

Paper quantity of the main type: the circuit's factor `termOk X W R⁺ R⁻` (a conjunct of `R̂`, `symRhatFast_circ`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Term NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists

theorem flatReportFast_le (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) : flatReportFast P e Z ≤ P.M := by
  unfold flatReportFast
  cases h : ((List.range P.M).map (· + 1)).find? (fun s => majStateFast P e Z s) with
  | none => simp
  | some s =>
    have hm := List.mem_of_find?_eq_some h
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp
    omega

theorem cornerWord_length {n : ℕ} (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    (cornerWord Ts c u v).length = 4 * Ts.length := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih => simp [cornerWord, List.length_flatMap] at ih ⊢; omega

theorem gatesW_length (h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) :
    (gatesW h G).length = G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 := by
  unfold gatesW
  rw [List.length_append, List.length_flatMap]
  simp only [gateW_length, List.map_const', List.sum_replicate, smul_eq_mul, List.length_singleton]

/-! ## The circuit's factor -/

/-- The `±` populations and their blanking, on the corner word `sX`. -/
def popP : SM := pop sX sZ sSp 0
def popM : SM := pop sX sZ sSm 0
def blankP : SM := blankOut sX sZ sSp 0
def blankM : SM := blankOut sX sZ sSm 0

/-- The first half: stage 2, the `+` population, its report into `26`, the population blanked. -/
def circA : SM := .seq cwS (.seq popP (.seq majS (.seq (WM.move 18 26) blankP)))

/-- The second half: the `−` population, its report into `27`, the population blanked, stage 8. -/
def circB : SM := .seq popM (.seq majS (.seq (WM.move 18 27) (.seq blankM termS)))

/-- **One circuit's factor.** -/
def circS : SM := .seq circA circB

/-- The factor's capacity needs. -/
structure CircCap (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) (n : ℕ) (G : List (NormalizedThresholdGate n))
    (W : ℕ) : Prop where
  one : 1 ≤ cap
  hh : 2 * tabH G ≤ cap
  nn : 2 * n ≤ cap
  kk : G.length * (1 + (n + 1) * (2 * (2 * tabH G + 1))) ≤ cap
  oo : 8 * G.length ≤ cap
  maj : Maj.MajCap Pl el G.length cap
  t8 : capOf8 G.length W Pl.M Pl.M ≤ cap
  mm : 2 * Pl.M ≤ cap

/-- The half-A cost. -/
def costA (h n g : ℕ) (P : FlatListParams) (e : P.FlatSeed) : ℕ :=
  cwCost h n g + 1 + (passCost g + 1 + (Maj.majBound P e g + 1 + (7 * P.M + 1 + 1 + passCost g)))

theorem circA_spec (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (c u v : BitInput n) (W : List Bool) (ω : SS)
    (hG : ω.st sG = gatesW (tabH G) G) (hC : ω.st sC = frameP (List.ofFn c) ++ [false])
    (hU : ω.st sU = frameP (List.ofFn u) ++ [false]) (hV : ω.st sV = frameP (List.ofFn v) ++ [false])
    (hpos : ω.st sPos = frameP (binary (tabH G) 0) ++ [false])
    (hneg : ω.st sNeg = frameP (binary (tabH G) 0) ++ [false])
    (hX : ω.st sX = List.replicate (8 * G.length + 1) false) (hZ : ω.st sZ = List.replicate (2 * G.length + 1) false)
    (hSp : ω.st sSp = [true])
    (hT5 : ω.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false))
    (hSS : ω.st sSS = []) (hFT : ω.st sFT = flatTable Pl el G.length)
    (hsh : ∀ i, ω.sh i = 0) (hr : ∀ q : Fin 32, q.val < 29 → ω.val q = 0) (hcap : CircCap cap Pl el n G W.length) :
    ∃ ω', WExec cap circA ω ω' (costA (tabH G) n G.length Pl el) ∧
      ω'.st sX = frameP (cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ [false] ∧
      (∃ A B : ℕ, ω'.st sPos = frameP (binary (tabH G) A) ++ [false] ∧
        ω'.st sNeg = frameP (binary (tabH G) B) ++ [false]) ∧
      ω'.st sZ = List.replicate (2 * G.length + 1) false ∧ ω'.st sSS = List.replicate Pl.M false ∧
      (∃ rowsF : ℕ → List Bool, (∀ j ≤ Pl.base.J, (rowsF j).length = G.length) ∧
        ω'.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W rowsF) ∧
      (∀ i : Fin 14, i ≠ sPos → i ≠ sNeg → i ≠ sX → i ≠ sZ → i ≠ sT5 → i ≠ sSS → ω'.st i = ω.st i) ∧
      (∀ i, ω'.sh i = 0) ∧
      ω'.val 26 = flatReportFast Pl el (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v)) ∧
      (∀ q : Fin 32, q.val < 26 → ω'.val q = 0) ∧ (∀ q : Fin 32, 27 ≤ q.val → ω'.val q = ω.val q) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hcap
  set X := cornerWord (G.map NormalizedThresholdGate.eval) c u v with hXdef
  have hXl : X.length = 4 * G.length := by rw [hXdef, cornerWord_length, List.length_map]
  -- stage 2
  obtain ⟨ω1, A1, B1, e1, x1, p1, n1, o1, h1, v1, k1⟩ := cwS_spec cap (tabH G) G c u v ω 0 0 [] [] [] [] [false]
    [false] [] (List.replicate (8 * G.length) false)
    (by rw [hsh sG, hG, List.drop_zero, List.append_nil])
    (by rw [hsh sG, hG, gatesW_length]; omega) (by rw [hC]) (by rw [hU]) (by rw [hV]) (by rw [hpos])
    (by rw [hneg]) (by rw [hX, List.replicate_succ'] <;> rfl) (by simp) (fun i _ _ => hsh i)
    (fun q hq => hr q (by omega)) c1 c2 c3 c4 c5 (tab_hov G)
  -- the + population
  have hw1 : wbit ω1 sSp = true := by
    unfold wbit; rw [o1 sSp (by decide) (by decide) (by decide), h1 sSp, hSp, hsh sSp] <;> rfl
  have e2 := pop_spec cap sX sZ sSp (0 : Fin 32) (by decide) (by decide) (by decide) true G.length X []
    (List.replicate (2 * G.length + 1) false) ω1 hXl (by rw [x1] <;> rfl) (by rw [h1, hsh])
    (by rw [o1 sZ (by decide) (by decide) (by decide), hZ]) (by rw [h1, hsh]) (by simp) hw1
    (by rw [v1, hr 0 (by decide)]) (by omega)
  have hZp : frameP (popBits true X) ++ (List.replicate (2 * G.length + 1) false).drop (2 * G.length) =
      frame (popBits true X) := by
    rw [List.drop_replicate, show 2 * G.length + 1 - 2 * G.length = 1 by omega, frame_eq_frameP]; rfl
  rw [hZp] at e2
  obtain ⟨ω2, hω2⟩ : ∃ y, y = ω1.sets sZ (frame (popBits true X)) := ⟨_, rfl⟩
  rw [← hω2] at e2
  have hpl : (popBits true X).length = G.length := popBits_length true G.length X hXl
  -- the + report
  obtain ⟨ω3, n3, hn3, e3, r3, z3, pt3, ft3, ss3, ⟨rowsF, hrF, t53⟩, sa3, sb3, sc3, sd3, o3, w3⟩ :=
    majS_spec cap Pl el G.length (popBits true X) hpl c6 (fun _ => List.replicate G.length false) (fun _ _ => by simp) 0
      ω2 (by rw [hω2]; simp) (by rw [hω2]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide),
        o1 sT5 (by decide) (by decide) (by decide), hT5])
      (by rw [hω2]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide),
        o1 sSS (by decide) (by decide) (by decide), hSS]; rfl)
      (by rw [hω2]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide),
        o1 sFT (by decide) (by decide) (by decide), hFT])
      ⟨by rw [hω2]; simp [h1, hsh], by rw [hω2]; simp [h1, hsh], by rw [hω2]; simp [h1, hsh],
        by rw [hω2]; simp [h1, hsh]⟩
      (fun q hq => by rw [hω2]; simp only [WState.sets_val]; rw [v1]; exact hr q (by omega))
  have hR3 := flatReportFast_le Pl el (popBits true X)
  have v26 : ω3.val 26 = 0 := by
    rw [w3 26 (by decide), hω2]; simp only [WState.sets_val]; rw [v1]; exact hr 26 (by decide)
  have e4 := wmove_spec cap (18 : Fin 32) 26 (by decide) (ω3.val 18) ω3 rfl (by rw [r3]; omega)
    (by rw [r3, v26]; omega)
  obtain ⟨ω4, hω4⟩ : ∃ y, y = (ω3.setv 18 0).setv 26 (ω3.val 26 + ω3.val 18) := ⟨_, rfl⟩
  rw [← hω4] at e4
  -- blank the population
  have hw4 : wbit ω4 sSp = true := by
    unfold wbit; rw [hω4]; simp only [WState.setv_st, WState.setv_sh]
    rw [(o3 sSp (by decide) (by decide) (by decide) (by decide)).1, (o3 sSp (by decide) (by decide) (by decide)
      (by decide)).2, hω2]
    simp only [WState.sets_st, WState.sets_sh]
    rw [Function.update_of_ne (by decide), o1 sSp (by decide) (by decide) (by decide), h1 sSp, hSp, hsh sSp]; rfl
  have hx4 : ω4.st sX = frameP X ++ false :: [] := by
    rw [hω4]; simp only [WState.setv_st]
    rw [(o3 sX (by decide) (by decide) (by decide) (by decide)).1, hω2]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), x1]
  have e5 := blank_spec cap sX sZ sSp (0 : Fin 32) (by decide) (by decide) (by decide) true G.length X []
    (frame (popBits true X)) ω4 hXl hx4
    (by rw [hω4]; simp only [WState.setv_sh]; rw [(o3 sX (by decide) (by decide) (by decide) (by decide)).2, hω2]
        simp [h1, hsh])
    (by rw [hω4]; simp only [WState.setv_st]; rw [pt3, hω2]; simp)
    (by rw [hω4]; simp only [WState.setv_sh]; exact sa3) (by rw [frame_eq_frameP]; simp [hpl]) hw4
    (by rw [hω4]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact z3 0 (by decide) (by decide)) (by omega)
  have hZb : List.replicate (2 * G.length) false ++ (frame (popBits true X)).drop (2 * G.length) =
      List.replicate (2 * G.length + 1) false := by
    rw [frame_eq_frameP, List.drop_append_of_le_length (by simp [hpl]),
      List.drop_eq_nil_of_le (by simp [hpl]), List.nil_append, ← List.replicate_succ']
  rw [hZb] at e5
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, ?_, ⟨A1, B1, ?_, ?_⟩,
    ?_, ?_, ⟨rowsF, hrF, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have : ω3.val 18 ≤ Pl.M := by rw [r3]; exact hR3
    unfold costA
    omega
  · simp only [WState.sets_st, Function.update_of_ne (show sX ≠ sZ by decide)]
    rw [hx4] <;> rfl
  · simp only [WState.sets_st, Function.update_of_ne (show sPos ≠ sZ by decide)]
    rw [hω4]; simp only [WState.setv_st]
    rw [(o3 sPos (by decide) (by decide) (by decide) (by decide)).1, hω2]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), p1]
  · simp only [WState.sets_st, Function.update_of_ne (show sNeg ≠ sZ by decide)]
    rw [hω4]; simp only [WState.setv_st]
    rw [(o3 sNeg (by decide) (by decide) (by decide) (by decide)).1, hω2]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), n1]
  · simp
  · simp only [WState.sets_st, Function.update_of_ne (show sSS ≠ sZ by decide)]
    rw [hω4]; simp only [WState.setv_st]; rw [ss3]; simp
  · simp only [WState.sets_st, Function.update_of_ne (show sT5 ≠ sZ by decide)]
    rw [hω4]; simp only [WState.setv_st]; exact t53
  · intro i i1 i2 i3 i4 i5 i6
    simp only [WState.sets_st, Function.update_of_ne i4]
    rw [hω4]; simp only [WState.setv_st]
    have i7 : i ≠ sFT ∨ i = sFT := by by_cases h : i = sFT <;> simp [h]
    rcases i7 with i7 | i7
    · rw [(o3 i i4 i5 i6 i7).1, hω2]; simp only [WState.sets_st]
      rw [Function.update_of_ne i4, o1 i i1 i2 i3]
    · subst i7; rw [ft3, hω2]; simp only [WState.sets_st]
      rw [Function.update_of_ne (by decide), o1 sFT (by decide) (by decide) (by decide)]
  · intro i
    simp only [WState.sets_sh]
    rw [hω4]; simp only [WState.setv_sh]
    by_cases hi : i = sZ ∨ i = sT5 ∨ i = sSS ∨ i = sFT
    · rcases hi with rfl | rfl | rfl | rfl
      · exact sa3
      · exact sb3
      · exact sc3
      · exact sd3
    · simp only [not_or] at hi
      rw [(o3 i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2).2, hω2]; simp [h1, hsh]
  · simp only [WState.sets_val]
    rw [hω4]; simp [r3, v26]
  · intro q hq
    simp only [WState.sets_val]
    rw [hω4]; simp only [WState.setv_val, Function.update_apply]
    have hq26 : q ≠ 26 := fun e => by rw [e] at hq; simp at hq
    rw [if_neg hq26]
    split_ifs with h18
    · rfl
    · exact z3 q hq h18
  · intro q hq
    simp only [WState.sets_val]
    rw [hω4]; simp only [WState.setv_val, Function.update_apply]
    have hq26 : q ≠ 26 := fun e => by rw [e] at hq; simp at hq
    have hq18 : q ≠ 18 := fun e => by rw [e] at hq; simp at hq
    rw [if_neg hq26, if_neg hq18, w3 q (by omega), hω2]
    simp only [WState.sets_val]
    rw [v1]

/-- The half-B cost. -/
def costB (g : ℕ) (P : FlatListParams) (e : P.FlatSeed) (W : ℕ) : ℕ :=
  passCost g + 1 + (Maj.majBound P e g + 1 + (7 * P.M + 1 + 1 + (passCost g + 1 + (cost8 g W P.M P.M + 2))))

theorem circB_spec (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (X W : List Bool) (hXl : X.length = 4 * G.length) (p k : ℕ) (hp : p ≤ Pl.M) (rowsT : ℕ → List Bool)
    (hrows : ∀ j ≤ Pl.base.J, (rowsT j).length = G.length) (ω : SS)
    (hX : ω.st sX = frameP X ++ [false]) (hZ : ω.st sZ = List.replicate (2 * G.length + 1) false)
    (hSm : ω.st sSm = []) (hT5 : ω.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W rowsT)
    (hSS : ω.st sSS = List.replicate k false) (hFT : ω.st sFT = flatTable Pl el G.length)
    (hTop : ω.st sTop = frame W) (hsh : ∀ i, ω.sh i = 0) (hr : ∀ q : Fin 32, q.val < 26 → ω.val q = 0)
    (h26 : ω.val 26 = p) (h27 : ω.val 27 = 0) (h28 : ω.val 28 = 0) (hcap : CircCap cap Pl el n G W.length) :
    ∃ ω', WExec cap circB ω ω' (costB G.length Pl el W.length) ∧
      ω'.val 28 = (termOk X W p (flatReportFast Pl el (popBits false X))).toNat ∧
      (∀ q : Fin 32, q.val < 28 → ω'.val q = 0) ∧ (∀ q : Fin 32, 29 ≤ q.val → ω'.val q = ω.val q) ∧
      ω'.st sZ = List.replicate (2 * G.length + 1) false ∧
      ω'.st sSS = List.replicate Pl.M false ++ List.replicate (k - Pl.M) false ∧
      (∃ rowsF : ℕ → List Bool, (∀ j ≤ Pl.base.J, (rowsF j).length = G.length) ∧
        ω'.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W rowsF) ∧
      (∀ i : Fin 14, i ≠ sZ → i ≠ sT5 → i ≠ sSS → ω'.st i = ω.st i) ∧ (∀ i, ω'.sh i = 0) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hcap
  -- the − population
  have hw0 : wbit ω sSm = false := by unfold wbit; rw [hSm, hsh sSm]; rfl
  have e1 := pop_spec cap sX sZ sSm (0 : Fin 32) (by decide) (by decide) (by decide) false G.length X []
    (List.replicate (2 * G.length + 1) false) ω hXl (by rw [hX]) (hsh sX) hZ (hsh sZ) (by simp) hw0
    (hr 0 (by decide)) (by omega)
  have hZp : frameP (popBits false X) ++ (List.replicate (2 * G.length + 1) false).drop (2 * G.length) =
      frame (popBits false X) := by
    rw [List.drop_replicate, show 2 * G.length + 1 - 2 * G.length = 1 by omega, frame_eq_frameP]; rfl
  rw [hZp] at e1
  obtain ⟨ω1, hω1⟩ : ∃ y, y = ω.sets sZ (frame (popBits false X)) := ⟨_, rfl⟩
  rw [← hω1] at e1
  have hpl : (popBits false X).length = G.length := popBits_length false G.length X hXl
  -- the − report
  obtain ⟨ω2, n2, hn2, e2, r2, z2, pt2, ft2, ss2, ⟨rowsF, hrF, t52⟩, sa2, sb2, sc2, sd2, o2, w2⟩ :=
    majS_spec cap Pl el G.length (popBits false X) hpl c6 rowsT hrows k ω1 (by rw [hω1]; simp)
      (by rw [hω1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), hT5])
      (by rw [hω1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), hSS])
      (by rw [hω1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), hFT])
      ⟨by rw [hω1]; simp [hsh], by rw [hω1]; simp [hsh], by rw [hω1]; simp [hsh], by rw [hω1]; simp [hsh]⟩
      (fun q hq => by rw [hω1]; simp only [WState.sets_val]; exact hr q hq)
  have hR2 := flatReportFast_le Pl el (popBits false X)
  have v27 : ω2.val 27 = 0 := by rw [w2 27 (by decide), hω1]; exact h27
  have e3 := wmove_spec cap (18 : Fin 32) 27 (by decide) (ω2.val 18) ω2 rfl (by rw [r2]; omega)
    (by rw [r2, v27]; omega)
  obtain ⟨ω3, hω3⟩ : ∃ y, y = (ω2.setv 18 0).setv 27 (ω2.val 27 + ω2.val 18) := ⟨_, rfl⟩
  rw [← hω3] at e3
  -- blank the population
  have hw3 : wbit ω3 sSm = false := by
    unfold wbit; rw [hω3]; simp only [WState.setv_st, WState.setv_sh]
    rw [(o2 sSm (by decide) (by decide) (by decide) (by decide)).1, (o2 sSm (by decide) (by decide) (by decide)
      (by decide)).2, hω1]
    simp only [WState.sets_st, WState.sets_sh]
    rw [Function.update_of_ne (by decide), hSm, hsh sSm]; rfl
  have hx3 : ω3.st sX = frameP X ++ false :: [] := by
    rw [hω3]; simp only [WState.setv_st]
    rw [(o2 sX (by decide) (by decide) (by decide) (by decide)).1, hω1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), hX]
  have e4 := blank_spec cap sX sZ sSm (0 : Fin 32) (by decide) (by decide) (by decide) false G.length X []
    (frame (popBits false X)) ω3 hXl hx3
    (by rw [hω3]; simp only [WState.setv_sh]; rw [(o2 sX (by decide) (by decide) (by decide) (by decide)).2, hω1]
        simp [hsh])
    (by rw [hω3]; simp only [WState.setv_st]; rw [pt2, hω1]; simp)
    (by rw [hω3]; simp only [WState.setv_sh]; exact sa2) (by rw [frame_eq_frameP]; simp [hpl]) hw3
    (by rw [hω3]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact z2 0 (by decide) (by decide)) (by omega)
  have hZb : List.replicate (2 * G.length) false ++ (frame (popBits false X)).drop (2 * G.length) =
      List.replicate (2 * G.length + 1) false := by
    rw [frame_eq_frameP, List.drop_append_of_le_length (by simp [hpl]),
      List.drop_eq_nil_of_le (by simp [hpl]), List.nil_append, ← List.replicate_succ']
  rw [hZb] at e4
  obtain ⟨ω4, hω4⟩ : ∃ y, y = ω3.sets sZ (List.replicate (2 * G.length + 1) false) := ⟨_, rfl⟩
  rw [← hω4] at e4
  -- stage 8
  have g4 : ∀ q : Fin 32, q ≠ 18 → q ≠ 27 → ω4.val q = ω2.val q := by
    intro q q1 q2; rw [hω4, hω3]; simp [Function.update_apply, q1, q2]
  have hm4 : ω4.val 27 = flatReportFast Pl el (popBits false X) := by rw [hω4, hω3]; simp [r2, v27]
  have hp4 : ω4.val 26 = p := by rw [g4 26 (by decide) (by decide), w2 26 (by decide), hω1]; exact h26
  have hk4 : ω4.val 28 = 0 := by rw [g4 28 (by decide) (by decide), w2 28 (by decide), hω1]; exact h28
  have hst4 : ∀ i : Fin 14, i ≠ sZ → i ≠ sT5 → i ≠ sSS → i ≠ sFT → ω4.st i = ω.st i := by
    intro i i1 i2 i3 i4
    rw [hω4]; simp only [WState.sets_st, Function.update_of_ne i1]
    rw [hω3]; simp only [WState.setv_st]
    rw [(o2 i i1 i2 i3 i4).1, hω1]; simp only [WState.sets_st, Function.update_of_ne i1]
  have hsh4 : ∀ i, ω4.sh i = 0 := by
    intro i
    rw [hω4]; simp only [WState.sets_sh]
    rw [hω3]; simp only [WState.setv_sh]
    by_cases hi : i = sZ ∨ i = sT5 ∨ i = sSS ∨ i = sFT
    · rcases hi with rfl | rfl | rfl | rfl
      · exact sa2
      · exact sb2
      · exact sc2
      · exact sd2
    · simp only [not_or] at hi
      rw [(o2 i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2).2, hω1]; simp [hsh]
  obtain ⟨ω5, e5, k5, p5, m5, z5, s5, sh5, v5, c5'⟩ := termS_spec cap X W G.length p
    (flatReportFast Pl el (popBits false X)) [] [] ω4 hXl
    (by rw [hst4 sX (by decide) (by decide) (by decide) (by decide), hX])
    (by rw [hst4 sTop (by decide) (by decide) (by decide) (by decide), hTop, frame_eq_frameP])
    (hsh4 sX) (hsh4 sTop) hp4 hm4 hk4
    (fun q hq => by
      rw [g4 q (fun e => by rw [e] at hq; simp at hq) (fun e => by rw [e] at hq; simp at hq)]
      exact z2 q (by omega) (fun e => by rw [e] at hq; simp at hq))
    (by unfold capOf8 at c7 ⊢; omega)
  refine ⟨ω5, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, k5, ?_, ?_, ?_, ?_,
    ⟨rowsF, hrF, ?_⟩, ?_, fun i => by rw [sh5 i]; exact hsh4 i⟩
  · have : ω2.val 18 ≤ Pl.M := by rw [r2]; exact hR2
    have hc8 : cost8 G.length W.length p (flatReportFast Pl el (popBits false X)) ≤ cost8 G.length W.length Pl.M Pl.M := by
      unfold cost8; omega
    unfold costB
    omega
  · intro q hq
    by_cases h7 : q.val < 7
    · exact z5 q h7
    · by_cases h26 : q = 26
      · subst h26; exact p5
      · by_cases h27' : q = 27
        · subst h27'; exact m5
        · have hq26 : q.val < 26 := by
            rcases q with ⟨k0, hk0⟩
            simp only [Fin.ext_iff] at h26 h27'
            simp only at hq h26 h27' ⊢
            omega
          rw [v5 q (by omega) h26 h27' (fun e => by rw [e] at hq; simp at hq)]
          by_cases h18 : q = 18
          · subst h18; rw [hω4, hω3]; simp
          · rw [g4 q h18 h27']; exact z2 q hq26 h18
  · intro q hq
    rw [v5 q (by omega) (fun e => by rw [e] at hq; simp at hq) (fun e => by rw [e] at hq; simp at hq)
      (fun e => by rw [e] at hq; simp at hq),
      g4 q (fun e => by rw [e] at hq; simp at hq) (fun e => by rw [e] at hq; simp at hq),
      w2 q (by omega), hω1]
    rfl
  · rw [s5, hω4]; simp
  · rw [s5, hω4]; simp only [WState.sets_st, Function.update_of_ne (show sSS ≠ sZ by decide)]
    rw [hω3]; simp only [WState.setv_st]; exact ss2
  · rw [s5, hω4]; simp only [WState.sets_st, Function.update_of_ne (show sT5 ≠ sZ by decide)]
    rw [hω3]; simp only [WState.setv_st]; exact t52
  · intro i i1 i2 i3
    rw [s5]
    by_cases i4 : i = sFT
    · subst i4; rw [hω4]; simp only [WState.sets_st, Function.update_of_ne (show sFT ≠ sZ by decide)]
      rw [hω3]; simp only [WState.setv_st]; rw [ft2, hω1]; simp only [WState.sets_st]
      rw [Function.update_of_ne (by decide)]
    · exact hst4 i i1 i2 i3 i4

/-- **One circuit's factor at a list seed**: from the gate table, the point, blank accumulators, a blank corner word
and population, the `+` sign, a blank template, the seed's flat table and the top table, the register `28` holds
`[termOk X W R⁺ R⁻]`, every register `0 … 27` is `0`, every head `0`. -/
theorem circS_spec (cap : ℕ) (Pl : FlatListParams) (el : Pl.FlatSeed) {n : ℕ} (G : List (NormalizedThresholdGate n))
    (c u v : BitInput n) (W : List Bool) (ω : SS)
    (hG : ω.st sG = gatesW (tabH G) G) (hC : ω.st sC = frameP (List.ofFn c) ++ [false])
    (hU : ω.st sU = frameP (List.ofFn u) ++ [false]) (hV : ω.st sV = frameP (List.ofFn v) ++ [false])
    (hpos : ω.st sPos = frameP (binary (tabH G) 0) ++ [false])
    (hneg : ω.st sNeg = frameP (binary (tabH G) 0) ++ [false])
    (hX : ω.st sX = List.replicate (8 * G.length + 1) false) (hZ : ω.st sZ = List.replicate (2 * G.length + 1) false)
    (hSp : ω.st sSp = [true]) (hSm : ω.st sSm = [])
    (hT5 : ω.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W (fun _ => List.replicate G.length false))
    (hSS : ω.st sSS = []) (hFT : ω.st sFT = flatTable Pl el G.length) (hTop : ω.st sTop = frame W)
    (hsh : ∀ i, ω.sh i = 0) (hr : ∀ q : Fin 32, q.val < 29 → ω.val q = 0) (hcap : CircCap cap Pl el n G W.length) :
    ∃ ω', WExec cap circS ω ω' (costA (tabH G) n G.length Pl el + 1 + costB G.length Pl el W.length) ∧
      ω'.val 28 = (termOk (cornerWord (G.map NormalizedThresholdGate.eval) c u v) W
        (flatReportFast Pl el (popBits true (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))
        (flatReportFast Pl el (popBits false (cornerWord (G.map NormalizedThresholdGate.eval) c u v)))).toNat ∧
      (∀ q : Fin 32, q.val < 28 → ω'.val q = 0) ∧ (∀ q : Fin 32, 29 ≤ q.val → ω'.val q = ω.val q) ∧
      (∀ i, ω'.sh i = 0) ∧
      ω'.st sX = frameP (cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ [false] ∧
      (∃ A B : ℕ, ω'.st sPos = frameP (binary (tabH G) A) ++ [false] ∧
        ω'.st sNeg = frameP (binary (tabH G) B) ++ [false]) ∧
      ω'.st sZ = List.replicate (2 * G.length + 1) false ∧
      ω'.st sSS = List.replicate Pl.M false ++ List.replicate (Pl.M - Pl.M) false ∧
      (∃ rowsF : ℕ → List Bool, (∀ j ≤ Pl.base.J, (rowsF j).length = G.length) ∧
        ω'.st sT5 = levelWord Pl.M Pl.base.J Pl.base.W rowsF) ∧
      (∀ i : Fin 14, i ≠ sPos → i ≠ sNeg → i ≠ sX → i ≠ sZ → i ≠ sT5 → i ≠ sSS → ω'.st i = ω.st i) := by
  obtain ⟨ω1, e1, x1, ⟨A, B, p1, n1⟩, z1, ss1, ⟨rowsF, hrF, t51⟩, o1, h1, r26, z26, w27⟩ :=
    circA_spec cap Pl el G c u v W ω hG hC hU hV hpos hneg hX hZ hSp hT5 hSS hFT hsh hr hcap
  have hXl : (cornerWord (G.map NormalizedThresholdGate.eval) c u v).length = 4 * G.length := by
    rw [cornerWord_length, List.length_map]
  obtain ⟨ω2, e2, k2, z2, w2, zz2, ss2, ⟨rowsG, hrG, t52⟩, o2, h2⟩ := circB_spec cap Pl el G
    (cornerWord (G.map NormalizedThresholdGate.eval) c u v) W hXl _ Pl.M (flatReportFast_le _ _ _) rowsF hrF ω1 x1 z1
    (by rw [o1 sSm (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSm]) t51 ss1
    (by rw [o1 sFT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hFT])
    (by rw [o1 sTop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hTop]) h1 z26 r26
    (by rw [w27 27 (by decide)]; exact hr 27 (by decide)) (by rw [w27 28 (by decide)]; exact hr 28 (by decide)) hcap
  refine ⟨ω2, WExec.seq e1 e2, k2, z2, fun q hq => by rw [w2 q hq, w27 q (by omega)], h2, ?_, ⟨A, B, ?_, ?_⟩, zz2,
    ss2, ⟨rowsG, hrG, t52⟩, fun i i1 i2 i3 i4 i5 i6 => by rw [o2 i i4 i5 i6, o1 i i1 i2 i3 i4 i5 i6]⟩
  · rw [o2 sX (by decide) (by decide) (by decide), x1]
  · rw [o2 sPos (by decide) (by decide) (by decide), p1]
  · rw [o2 sNeg (by decide) (by decide) (by decide), n1]

end NearCubicWires.WireExponent3_5.PrimT.S3
