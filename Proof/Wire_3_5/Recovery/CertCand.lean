import Proof.Wire_3_5.Recovery.CertCostB

/-! # The candidate test: `[m_a ≤ n/2]` from `a` and `n` (P3:3738-3741, 3818-3822; D1.6, the prefix stage)

Realizes one test of the prefix's scan at a candidate source index `a`: the width `q = q(2^a)` (`widthMachine`),
`L = L(q)` (`lqMachine`), the schedule loop's setup (`setupMachine`), the schedule loop (`schedLoop`, `n`
rounds, which computes `t(q)` once `n ≥ t(q) − 1`), and the core length test (`coreMachine`), composed on one
layout: the candidate `1^a` (tape 0), `1^n` (tape 1), the schedule loop's 33 tapes (2–34, a port block that the test
leaves in the same canonical form), the width machine's other 27 tapes (35–61), the `L` machine's other 19 tapes
(62–80), the setup's other 11 tapes (81–91), and the core test's tapes (from 92).

Paper quantity: the scan's test `[m_a ≤ n/2]`; `innerTapes` (the schedule loop's canonical tapes), `innerTapes_eq` (they
are the loop's input), **`candMachine`** and **`candMachine_ready`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## The schedule loop's canonical tapes -/

/-- The schedule loop's 33 tapes with ports `A, B, E`, the words, drivers, empty (padded) scratch and the counter word. -/
def innerTapes (A B E : List Bool) (p w total capT T capF c : ℕ) : Fin (30 + 2 + 1) → List Bool := fun i =>
  if i.val = 0 then A else if i.val = 1 then B else if i.val = 2 then E
  else if i.val = 3 then CompareMachine.word p else if i.val = 4 then CompareMachine.word w
  else if i.val = 5 then List.replicate total true else if i.val = 6 then List.replicate capT false
  else if i.val < 30 then List.replicate T false else if i.val = 30 then List.replicate T true
  else if i.val = 31 then List.replicate capF false else CompareMachine.word c

theorem scratchCap_round (T : ℕ) (i : Fin 30) :
    scratchCap roundScratch T i = if 7 ≤ i.val then T else 0 := by
  unfold scratchCap
  by_cases h : 7 ≤ i.val
  · rw [if_pos ⟨⟨i.val - 7, by omega⟩, Fin.ext (by simp [roundScratch]; omega)⟩, if_pos h]
  · rw [if_neg (by rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp [roundScratch] at this; omega), if_neg h]

/-- **The canonical tapes are the schedule loop's input** at the padded ports. -/
theorem innerTapes_eq (a b e p w total capT T capF c : ℕ) :
    innerTapes (ZeroPadding.pad total (List.replicate a true)) (ZeroPadding.pad total (List.replicate b true))
      (ZeroPadding.pad total (List.replicate e true)) p w total capT T capF c =
    Fin.addCases (motive := fun _ => List Bool)
      (roundTapes (padScratch roundScratch T (roundInput a b e p w total capT)) T capF)
      (fun _ : Fin 1 => CompareMachine.word c) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i'
    · simp only [roundTapes, Fin.addCases_left, padScratch, scratchCap_round, innerTapes, roundInput, Fin.val_castAdd]
      rcases j with ⟨v, hv⟩
      interval_cases v <;> simp [ZeroPadding.pad]
    · simp only [roundTapes, Fin.addCases_right, innerTapes, Fin.val_castAdd, Fin.val_natAdd]
      fin_cases k <;> simp
  · simp only [Fin.addCases_right, innerTapes, Fin.val_natAdd]
    fin_cases k; simp

/-- Positions of the inner block other than the three ports carry the same tapes for any ports. -/
theorem innerTapes_other (A B E A' B' E' : List Bool) (p w total capT T capF c : ℕ) (j : Fin (30 + 2 + 1))
    (hj : 3 ≤ j.val) :
    innerTapes A B E p w total capT T capF c j = innerTapes A' B' E' p w total capT T capF c j := by
  unfold innerTapes
  simp only [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, show j.val ≠ 2 by omega, if_false]

/-! ## The candidate test's layout -/

section Cand
variable (k A u v D : ℕ)

/-- The candidate test's tape count. -/
def candTapes : ℕ := Clause.tapes D + 110

/-- A fixed position below 92. -/
def cpos (m : ℕ) (h : m < 92 := by decide) : Fin (candTapes D) := ⟨m, by unfold candTapes; omega⟩

/-- The width machine: its tape 0 is the candidate, the others are tapes 35–61. -/
def candW (i : Fin 28) : Fin (candTapes D) :=
  ⟨if i.val = 0 then 0 else 34 + i.val, by have := i.isLt; unfold candTapes; split_ifs <;> omega⟩
/-- The `L` machine: its tape 0 is the width's output (60), the others are tapes 62–80. -/
def candL (i : Fin 20) : Fin (candTapes D) :=
  ⟨if i.val = 0 then 60 else 61 + i.val, by have := i.isLt; unfold candTapes; split_ifs <;> omega⟩
/-- The setup: `L` (77), the three ports (2, 3, 4), the driver (7) and capacity tape (8), then tapes 81–91. -/
def candS (i : Fin 17) : Fin (candTapes D) :=
  ⟨if i.val = 0 then 77 else if i.val = 1 then 2 else if i.val = 2 then 3 else if i.val = 3 then 4
    else if i.val = 4 then 7 else if i.val = 5 then 8 else 75 + i.val,
    by have := i.isLt; unfold candTapes; split_ifs <;> omega⟩
/-- The schedule loop: tapes 2–34. -/
def candI (i : Fin (30 + 2 + 1)) : Fin (candTapes D) :=
  ⟨2 + i.val, by have := i.isLt; unfold candTapes; omega⟩
/-- The core test: `1^q` (60), the counter port (4), `1^n` (1), then tapes from 92. -/
def candC (i : Fin (Clause.tapes D + 18)) : Fin (candTapes D) :=
  ⟨if i.val = 0 then 60 else if i.val = Clause.tapes D then 4 else if i.val = Clause.tapes D + 1 then 1
    else 92 + i.val, by have := i.isLt; unfold candTapes; split_ifs <;> omega⟩
/-- The flag's position. -/
def candFlag : Fin (candTapes D) := candC D (tl D 16)

theorem candW_inj : Function.Injective (candW D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candW, Fin.val_mk] at this; apply Fin.ext
  split_ifs at this <;> omega
theorem candL_inj : Function.Injective (candL D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candL, Fin.val_mk] at this; apply Fin.ext
  split_ifs at this <;> omega
theorem candS_inj : Function.Injective (candS D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candS, Fin.val_mk] at this; apply Fin.ext
  split_ifs at this <;> omega
theorem candI_inj : Function.Injective (candI D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candI, Fin.val_mk] at this; apply Fin.ext; omega
theorem candC_inj : Function.Injective (candC D) := by
  intro a b h; have := congrArg Fin.val h; simp only [candC, Fin.val_mk] at this; apply Fin.ext
  split_ifs at this <;> omega

/-- Close a value goal about the candidate layout. -/
macro "cand_val" : tactic => `(tactic| (simp only [candW, candL, candS, candI, candC, cpos, tl_val, Fin.val_mk,
  Fin.isValue, Fin.coe_ofNat_eq_mod] <;> first | omega | (split_ifs <;> omega)))

/-- The setup's input by values. -/
theorem setupInput_eq (L : ℕ) (A B E : List Bool) (total capT : ℕ) (j : Fin 17) :
    setupInput L A B E total capT j = if j.val = 0 then List.replicate L true else if j.val = 1 then A
      else if j.val = 2 then B else if j.val = 3 then E else if j.val = 4 then List.replicate total true
      else if j.val = 5 then List.replicate capT false else [] := by
  fin_cases j <;> rfl

/-- The candidate test's input: `1^a`, `1^n`, the inner block, and empty tapes. -/
def candInput (a n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) : Fin (candTapes D) → List Bool :=
  fun i => if i.val = 0 then List.replicate a true else if i.val = 1 then List.replicate n true
    else if h : 2 ≤ i.val ∧ i.val < 35 then innerTapes Ap Bp Ep p w total capT T capF c ⟨i.val - 2, by omega⟩
    else []

theorem candInput_fresh (a n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (i : Fin (candTapes D))
    (hi : 35 ≤ i.val) : candInput D a n Ap Bp Ep p w total capT T capF c i = [] := by
  simp only [candInput]; rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem candInput_inner (a n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (j : Fin (30 + 2 + 1)) :
    candInput D a n Ap Bp Ep p w total capT T capF c (candI D j) = innerTapes Ap Bp Ep p w total capT T capF c j := by
  simp only [candInput, candI, Fin.val_mk]
  rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

/-! ## The candidate test -/

/-- `L = L(q(2^a))`, the loop's start `a₀ = L³(v−2u)^{16}`, `b₀ = (2v)^{16}`, and the loop's counter after `c` rounds. -/
def candL0 (a : ℕ) : ℕ := Ledger.Lq (widthAt k A a)
def candA0 (a : ℕ) : ℕ := candL0 k A a * candL0 k A a * candL0 k A a * (v - 2 * u) ^ 16
def candB0 : ℕ := (2 * v) ^ 16
def candT (a p w c : ℕ) : ℕ := roundCount (candA0 k A u v a) (candB0 v) 1 p w c

/-- The schedule loop's cost. -/
def candSchedCost (p w total T c : ℕ) : ℕ :=
  1 + 1 + (c * (roundCostBound p w total + 1 + (2 * T + 4 + 1 + 0) + 2) + c + 3 + 1 + 1)

/-- The candidate test's time bound. -/
def candBound (a n p w total T c : ℕ) : ℕ :=
  candWidthBound k A a + 1 + (candLqBound (widthAt k A a) + 1 +
    (candSetupBound v (candL0 k A a) total + 1 +
      (candSchedCost p w total T c + 1 + candCoreBound D (widthAt k A a) (1 + c) n)))

/-- **The candidate test**: width, `L`, the loop's setup, the schedule loop, the core length test. -/
noncomputable def candMachine :=
  Composition.machine (RecoveryFocus.machine (candW D) (widthMachine k A))
  (Composition.machine (RecoveryFocus.machine (candL D) lqMachine)
  (Composition.machine (RecoveryFocus.machine (candS D) (setupMachine u v))
  (Composition.machine (RecoveryFocus.machine (candI D) schedLoop)
    (RecoveryFocus.machine (candC D) (coreMachine D)))))

theorem candCoreBound_mono (q t t' n : ℕ) (h : t ≤ t') : candCoreBound D q t n ≤ candCoreBound D q t' n := by
  unfold candCoreBound
  have := Nat.mul_le_mul_left (64 * (q + 2 + (q + 2) ^ D)) (show t + 2 ≤ t' + 2 by omega)
  omega

/-- **The candidate test is ready**: from `1^a`, `1^n` and the inner block (stale ports of length `≤ total`) it writes
`[2(q + 1 + cw)(t + 1) ≤ n]` at `q = q(2^a)`, `t` the loop's counter after `c` rounds, keeps `1^a`, `1^n`, and leaves
the inner block in canonical form, within `candBound`. -/
theorem candMachine_run (a n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (hD : 1 ≤ D)
    (hcap : total + 1 ≤ capT) (hA : Ap.length ≤ total) (hB : Bp.length ≤ total) (hE : Ep.length ≤ total)
    (hbound : ∀ i, i ≤ c → candA0 k A u v a * p ^ i ≤ total ∧ candB0 v * w ^ i ≤ total ∧ 1 + i ≤ total)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hTc : roundCostBound p w total + 1 ≤ T) (hcapF : T + 1 ≤ capF) :
    ∃ (cost : ℕ) (out : Fin (candTapes D) → List Bool), cost ≤ candBound k A v D a n p w total T c ∧
      ClockJoin.ReadyRun (candMachine k A u v D) cost (candInput D a n Ap Bp Ep p w total capT T capF c) out ∧
      out (cpos D 0) = List.replicate a true ∧ out (cpos D 1) = List.replicate n true ∧
      (∀ j, out (candI D j) = innerTapes (ZeroPadding.pad total (List.replicate (candA0 k A u v a * p ^ c) true))
        (ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true))
        (ZeroPadding.pad total (List.replicate (candT k A u v a p w c) true)) p w total capT T capF c j) ∧
      out (candFlag D) =
        [decide ((widthAt k A a + 1 + clauseWidth D (widthAt k A a)) * (candT k A u v a p w c + 1) * 2 ≤ n)] := by
  set x := candInput D a n Ap Bp Ep p w total capT T capF c with hx
  set q := widthAt k A a with hq
  -- the width
  obtain ⟨c1, o1, hc1, r1, o10, o126⟩ := widthMachine_run k A a
  have g1 := r1.focus (candW D) (candW_inj D) x (by
    intro j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this
      simp [hx, candInput, candW, widthInput]
    · rw [hx, candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp only [candW, Fin.val_mk]; rw [if_neg hj]; omega)]
      simp [widthInput, hj])
  set a1 := install (candW D) x o1 with ha1
  have a1_0 : a1 (cpos D 0) = List.replicate a true := by
    rw [show cpos D 0 = candW D 0 from Fin.ext (by simp [cpos, candW]), ha1, install_slot _ (candW_inj D), o10]
  have a1_60 : a1 (cpos D 60) = List.replicate q true := by
    rw [show cpos D 60 = candW D 26 from Fin.ext (by simp [cpos, candW]), ha1, install_slot _ (candW_inj D), o126]
  have a1_x : ∀ i : Fin (candTapes D), (1 ≤ i.val ∧ i.val ≤ 34) ∨ 62 ≤ i.val → a1 i = x i := by
    intro i hi; rw [ha1, install_other _ _ _ _ (by
      intro j; have := j.isLt; apply fin_ne; simp only [candW, Fin.val_mk]; split_ifs <;> omega)]
  -- `L`
  obtain ⟨c2, o2, hc2, r2, o20, o216⟩ := lqMachine_run q
  have g2 := r2.focus (candL D) (candL_inj D) a1 (by
    intro j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this
      rw [show candL D 0 = cpos D 60 from Fin.ext (by simp [cpos, candL]), a1_60]; simp [lqInput]
    · rw [a1_x _ (Or.inr (by simp only [candL, Fin.val_mk]; rw [if_neg hj]; omega)),
        hx, candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp only [candL, Fin.val_mk]; rw [if_neg hj]; omega)]
      simp [lqInput, hj])
  set a2 := install (candL D) a1 o2 with ha2
  have a2_77 : a2 (cpos D 77) = List.replicate (candL0 k A a) true := by
    rw [show cpos D 77 = candL D 16 from Fin.ext (by simp [cpos, candL]), ha2, install_slot _ (candL_inj D), o216]
    rfl
  have a2_60 : a2 (cpos D 60) = List.replicate q true := by
    rw [show cpos D 60 = candL D 0 from Fin.ext (by simp [cpos, candL]), ha2, install_slot _ (candL_inj D), o20]
  have a2_x : ∀ i : Fin (candTapes D), (1 ≤ i.val ∧ i.val ≤ 34) ∨ 81 ≤ i.val → a2 i = x i := by
    intro i hi
    rw [ha2, install_other _ _ _ _ (by
      intro j; have := j.isLt; apply fin_ne; simp only [candL, Fin.val_mk]; split_ifs <;> omega), a1_x _ (by omega)]
  have a2_0 : a2 (cpos D 0) = List.replicate a true := by
    rw [ha2, install_other _ _ _ _ (by
      intro j; have := j.isLt; apply fin_ne; simp only [candL, cpos, Fin.val_mk]; split_ifs <;> omega), a1_0]
  -- the loop's setup
  obtain ⟨c3, o3, hc3, r3, o30, o31, o32, o33, o34, o35⟩ :=
    setupMachine_run u v (candL0 k A a) Ap Bp Ep total capT hcap hA hB hE
  have g3 := r3.focus (candS D) (candS_inj D) a2 (by
    intro j
    rw [setupInput_eq]
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show candS D j = cpos D 77 from Fin.ext (by cand_val), a2_77]
    · rw [if_neg h0, a2_x _ (by cand_val), hx]
      by_cases h6 : 6 ≤ j.val
      · rw [candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by cand_val)]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rcases (show j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 by omega) with h | h | h | h | h
        · rw [show candS D j = candI D ⟨0, by decide⟩ from Fin.ext (by cand_val), candInput_inner]
          simp [innerTapes, h]
        · rw [show candS D j = candI D ⟨1, by decide⟩ from Fin.ext (by cand_val), candInput_inner]
          simp [innerTapes, h]
        · rw [show candS D j = candI D ⟨2, by decide⟩ from Fin.ext (by cand_val), candInput_inner]
          simp [innerTapes, h]
        · rw [show candS D j = candI D ⟨5, by decide⟩ from Fin.ext (by cand_val), candInput_inner]
          simp [innerTapes, h]
        · rw [show candS D j = candI D ⟨6, by decide⟩ from Fin.ext (by cand_val), candInput_inner]
          simp [innerTapes, h])
  set a3 := install (candS D) a2 o3 with ha3
  have hloopin : ∀ j : Fin (30 + 2 + 1), a3 (candI D j) =
      innerTapes (ZeroPadding.pad total (List.replicate (candA0 k A u v a) true))
        (ZeroPadding.pad total (List.replicate (candB0 v) true)) (ZeroPadding.pad total (List.replicate 1 true))
        p w total capT T capF c j := by
    intro j
    have hj := j.isLt
    by_cases hp : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 5 ∨ j.val = 6
    · rcases hp with h | h | h | h | h
      · rw [show candI D j = candS D 1 from Fin.ext (by simp [candS, candI, h]), ha3, install_slot _ (candS_inj D),
          o31]
        simp [innerTapes, h, candA0]
      · rw [show candI D j = candS D 2 from Fin.ext (by simp [candS, candI, h]), ha3, install_slot _ (candS_inj D),
          o32]
        simp [innerTapes, h, candB0]
      · rw [show candI D j = candS D 3 from Fin.ext (by simp [candS, candI, h]), ha3, install_slot _ (candS_inj D),
          o33]
        simp [innerTapes, h]
      · rw [show candI D j = candS D 4 from Fin.ext (by simp [candS, candI, h]), ha3, install_slot _ (candS_inj D),
          o34]
        simp [innerTapes, h]
      · rw [show candI D j = candS D 5 from Fin.ext (by simp [candS, candI, h]), ha3, install_slot _ (candS_inj D),
          o35]
        simp [innerTapes, h]
    · rw [ha3, install_other _ _ _ _ (by
          intro i; have := i.isLt; apply fin_ne; simp only [candS, candI, Fin.val_mk]; split_ifs <;> omega),
        a2_x _ (by simp only [candI, Fin.val_mk]; omega), hx, candInput_inner]
      exact innerTapes_other _ _ _ _ _ _ _ _ _ _ _ _ _ j (by omega)
  -- the schedule loop
  have hl := schedLoop_ready (candA0 k A u v a) (candB0 v) 1 p w total capT T capF c hcap hbound hT hTc hcapF
  have e0 : roundState (candA0 k A u v a) (candB0 v) 1 p w total capT 0 =
      roundInput (candA0 k A u v a) (candB0 v) 1 p w total capT := by
    simp [roundState, roundCount]
  have g4 := hl.focus (candI D) (candI_inj D) a3 (by
    intro j
    rw [hloopin, innerTapes_eq, e0])
  set a4 := install (candI D) a3 (Fin.addCases (roundTapes (padScratch roundScratch T
    (roundState (candA0 k A u v a) (candB0 v) 1 p w total capT c)) T capF) (fun _ => CompareMachine.word c))
    with ha4
  have a4_inner : ∀ j, a4 (candI D j) =
      innerTapes (ZeroPadding.pad total (List.replicate (candA0 k A u v a * p ^ c) true))
        (ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true))
        (ZeroPadding.pad total (List.replicate (candT k A u v a p w c) true)) p w total capT T capF c j := by
    intro j
    rw [ha4, install_slot _ (candI_inj D)]
    exact (congrFun (innerTapes_eq (candA0 k A u v a * p ^ c) (candB0 v * w ^ c) (candT k A u v a p w c)
      p w total capT T capF c) j).symm
  have a4_off : ∀ i : Fin (candTapes D), (i.val < 2 ∨ 35 ≤ i.val) → (i.val ≤ 76 ∨ 92 ≤ i.val) →
      i.val ≠ 77 → a4 i = a2 i := by
    intro i h1 h2 h3
    rw [ha4, install_other _ _ _ _ (by
        intro j; have := j.isLt; apply fin_ne; simp only [candI, Fin.val_mk]; omega), ha3,
      install_other _ _ _ _ (by
        intro j; have := j.isLt; apply fin_ne; simp only [candS, Fin.val_mk]; split_ifs <;> omega)]
  have a4_60 : a4 (cpos D 60) = List.replicate q true := by
    rw [a4_off _ (by simp [cpos]) (by simp [cpos]) (by simp [cpos]), a2_60]
  have a4_1 : a4 (cpos D 1) = List.replicate n true := by
    rw [a4_off _ (by simp [cpos]) (by simp [cpos]) (by simp [cpos]), a2_x _ (by simp [cpos])]
    simp [hx, candInput, cpos]
  have a4_0 : a4 (cpos D 0) = List.replicate a true := by
    rw [a4_off _ (by simp [cpos]) (by simp [cpos]) (by simp [cpos]), a2_0]
  have a4_fresh : ∀ i : Fin (candTapes D), 92 ≤ i.val → a4 i = [] := by
    intro i hi
    rw [a4_off _ (by omega) (by omega) (by omega), a2_x _ (by omega), hx,
      candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  -- the core length test
  obtain ⟨c5, o5, hc5, r5, o5t0, o5t1, o5f⟩ := coreMachine_run D q (candT k A u v a p w c) n total hD
  have g5 := r5.focus (candC D) (candC_inj D) a4 (by
    intro j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [show candC D j = cpos D 60 from Fin.ext (by cand_val),
        a4_60]
      simp only [coreInput, if_pos h0]
    · by_cases h1 : j.val = Clause.tapes D
      · rw [show candC D j = candI D 2 from Fin.ext (by cand_val), a4_inner]
        simp only [coreInput, if_neg h0, if_pos h1]
        rfl
      · by_cases h2 : j.val = Clause.tapes D + 1
        · rw [show candC D j = cpos D 1 from Fin.ext (by cand_val), a4_1]
          simp only [coreInput, if_neg h0, if_neg h1, if_pos h2]
        · rw [a4_fresh _ (by cand_val)]
          simp only [coreInput, if_neg h0, if_neg h1, if_neg h2])
  have ht := roundCount_le (candA0 k A u v a) (candB0 v) 1 p w c
  have hcm := candCoreBound_mono D q (candT k A u v a p w c) (1 + c) n ht
  refine ⟨_, _, ?_, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 (ClockJoin.join _ _ _ _ _ _ _ g4 g5))), ?_, ?_, ?_, ?_⟩
  · unfold candBound candSchedCost
    rw [← hq]
    omega
  · rw [install_other _ _ _ _ (by
      intro j; have := j.isLt; apply fin_ne; simp only [candC, cpos, Fin.val_mk]; split_ifs <;> omega), a4_0]
  · rw [show cpos D 1 = candC D (tl D 1) from Fin.ext (by simp [candC, cpos, tl_val]), install_slot _ (candC_inj D), o5t1]
  · intro j
    by_cases h2 : j.val = 2
    · rw [show candI D j = candC D (tl D 0) from Fin.ext (by simp [candC, candI, tl_val, h2, tapes_eq]), install_slot _ (candC_inj D), o5t0]
      simp [innerTapes, h2]
    · have hj := j.isLt
      rw [install_other _ _ _ _ (by
        intro i; have := i.isLt; apply fin_ne; simp only [candC, candI, Fin.val_mk]; split_ifs <;> omega), a4_inner]
  · rw [candFlag, install_slot _ (candC_inj D), o5f]

end Cand

end NearCubicWires.WireExponent3_5.Transfer
