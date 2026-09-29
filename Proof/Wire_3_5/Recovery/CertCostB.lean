import Proof.Wire_3_5.Recovery.CertCostA
import Proof.Wire_3_5.Recovery.CertCore

/-! # The setup and core machines with explicit time bounds (P3:3738-3741, 3818-3822; D1.6, the prefix stage)

Realizes the time part of the schedule loop's setup and of the core length test: both run once per candidate of the
prefix's scan on one reused bank, so their running times must be bounded by explicit functions of the candidate. `setupMachine_ready` and `coreMachine_ready` are restated with the same runs and outputs and a bound on the cost.

Paper quantities: the loop's initial state `(a₀, b₀, 1)` and the core length `m_a`; **`setupMachine_run`** (cost
`≤ candSetupBound v L total = 2 total + 32 (L+1)^3 ((2v)^{16} + 3) + 64`) and **`coreMachine_run`** (cost
`≤ candCoreBound D q t n`, polynomial in `q`, linear in `t + 2` and `n`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes Clause.machine Clause.clause_run Clause.input
  Clause.qSlot Clause.widthSlot)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section SetupCost
variable (u v : ℕ)

/-- The setup machine's time bound. -/
def candSetupBound (L total : ℕ) : ℕ := 2 * total + 32 * (L + 1) ^ 3 * ((2 * v) ^ 16 + 3) + 64

/-- **The setup machine within its time bound.** -/
theorem setupMachine_run (L : ℕ) (A B E : List Bool) (total capT : ℕ) (hcap : total + 1 ≤ capT)
    (hA : A.length ≤ total) (hB : B.length ≤ total) (hE : E.length ≤ total) :
    ∃ (cost : ℕ) (out : Fin 17 → List Bool), cost ≤ candSetupBound v L total ∧
      ClockJoin.ReadyRun (setupMachine u v) cost (setupInput L A B E total capT) out ∧
      out 0 = List.replicate L true ∧
      out 1 = ZeroPadding.pad total (List.replicate (L * L * L * (v - 2 * u) ^ 16) true) ∧
      out 2 = ZeroPadding.pad total (List.replicate ((2 * v) ^ 16) true) ∧
      out 3 = ZeroPadding.pad total [true] ∧
      out 4 = List.replicate total true ∧ out 5 = List.replicate capT false := by
  set x := setupInput L A B E total capT with hx
  have hmax : max capT (total + 1) = capT := max_eq_left hcap
  have he := ready_of_root (RecoveryScratchErase.erase_ready total capT ![A, B, E] (by
    intro i; fin_cases i <;> simpa))
  rw [hmax] at he
  have h1 := he.focus slotsSE (by decide) x (by intro j; fin_cases j <;> rfl)
  set a1 := install slotsSE x (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 3 => List.replicate total false)
    (fun _ : Fin 1 => List.replicate total true)) (fun _ : Fin 1 => List.replicate capT false)) with ha1
  have hfree : ∀ i : Fin 17, 6 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsSE] at this; omega))]
    simp only [hx, setupInput]
    rcases i with ⟨v', hv'⟩
    interval_cases v' <;> rfl
  have a10 : a1 0 = List.replicate L true := by rw [ha1, install_other _ _ _ _ (by decide)]; rfl
  -- the template of `L`
  have h2 := (RepairSource.ProjectionNormalization.DimensionTemplate.ready false L).focus slotsST (by decide) a1 (by
    intro j; fin_cases j
    · exact a10
    · exact hfree 6 (by decide)
    · exact hfree 7 (by decide))
  set a2 := install slotsST a1 (RepairSource.ProjectionNormalization.DimensionTemplate.output false L) with ha2
  have a26 : a2 6 = ZeroPadding.pad (L + 2) (CompareMachine.word L) := by
    rw [ha2, show (6 : Fin 17) = slotsST 1 from rfl, install_slot _ (by decide)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output,
      ← RepairSource.CloseoutCapacity.Power.template_source, UWalkUnary.source]
  have a20 : a2 0 = List.replicate L true := by
    rw [ha2, show (0 : Fin 17) = slotsST 0 from rfl, install_slot _ (by decide)]; rfl
  -- `L²`
  have hp1 := ready_pad _ _ _ _ ![0, L + 2, 0, 0] (UWalkNumbers.product_ready L L)
  have h3 := hp1.focus slotsSP1 (by decide) a2 (by
    intro j; fin_cases j
    · show a2 0 = _; rw [a20]; simp [UWalkNumbers.productInput]
    · show a2 6 = _; rw [a26]; simp [UWalkNumbers.productInput, CompareMachine.word]
    · show a2 8 = _; rw [ha2, install_other _ _ _ _ (by decide), hfree 8 (by decide)]; rfl
    · show a2 9 = _; rw [ha2, install_other _ _ _ _ (by decide), hfree 9 (by decide)]; rfl)
  set a3 := install slotsSP1 a2 (fun i => ZeroPadding.pad (![0, L + 2, 0, 0] i) (UWalkNumbers.productOutput L L i))
    with ha3
  have a38 : a3 8 = List.replicate (L * L) true := by
    rw [ha3, show (8 : Fin 17) = slotsSP1 2 from rfl, install_slot _ (by decide)]; simp [UWalkNumbers.productOutput]
  have a36 : a3 6 = ZeroPadding.pad (L + 2) (CompareMachine.word L) := by
    rw [ha3, show (6 : Fin 17) = slotsSP1 1 from rfl, install_slot _ (by decide)]
    simp [UWalkNumbers.productOutput, CompareMachine.word]
  -- `L³`
  have hp2 := ready_pad _ _ _ _ ![0, L + 2, 0, 0] (UWalkNumbers.product_ready (L * L) L)
  have h4 := hp2.focus slotsSP2 (by decide) a3 (by
    intro j; fin_cases j
    · show a3 8 = _; rw [a38]; simp [UWalkNumbers.productInput]
    · show a3 6 = _; rw [a36]; simp [UWalkNumbers.productInput, CompareMachine.word]
    · show a3 10 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hfree 10 (by decide)]; rfl
    · show a3 11 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hfree 11 (by decide)]; rfl)
  set a4 := install slotsSP2 a3 (fun i => ZeroPadding.pad (![0, L + 2, 0, 0] i)
    (UWalkNumbers.productOutput (L * L) L i)) with ha4
  have hlow : ∀ i : Fin 17, 12 ≤ i.val → a4 i = [] := by
    intro i hi
    have e : ∀ {m : ℕ} (s : Fin m → Fin 17), (∀ j, (s j).val < 12) → ∀ j, s j ≠ i := by
      intro m s hs j hj; have := hs j; rw [hj] at this; omega
    rw [ha4, install_other _ _ _ _ (e _ (by decide)), ha3, install_other _ _ _ _ (e _ (by decide)), ha2,
      install_other _ _ _ _ (e _ (by decide)), hfree _ (by omega)]
  -- the word `(v−2u)^{16}`
  have h5 := (UWalkNumbers.fixed_ready (CompareMachine.word ((v - 2 * u) ^ 16))).focus slotsSQ (by decide) a4 (by
    intro j; fin_cases j
    · exact hlow 12 (by decide)
    · exact hlow 13 (by decide))
  set a5 := install slotsSQ a4 ![CompareMachine.word ((v - 2 * u) ^ 16),
    List.replicate (CompareMachine.word ((v - 2 * u) ^ 16)).length false] with ha5
  -- `a₀ = L³·(v−2u)^{16}` onto the erased port 1
  have hp3 := ready_pad _ _ _ _ ![0, 0, total, 0] (UWalkNumbers.product_ready (L * L * L) ((v - 2 * u) ^ 16))
  have h6 := hp3.focus slotsSP3 (by decide) a5 (by
    intro j; fin_cases j
    · show a5 10 = _
      rw [ha5, install_other _ _ _ _ (by decide), ha4, show (10 : Fin 17) = slotsSP2 2 from rfl,
        install_slot _ (by decide)]
      simp [UWalkNumbers.productOutput, UWalkNumbers.productInput]
    · show a5 12 = _
      rw [ha5, show (12 : Fin 17) = slotsSQ 0 from rfl, install_slot _ (by decide)]
      simp [UWalkNumbers.productInput, CompareMachine.word]
    · show a5 1 = _
      rw [ha5, install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
        install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        show (1 : Fin 17) = slotsSE 0 from rfl, install_slot _ (by decide)]
      rfl
    · show a5 14 = _
      rw [ha5, install_other _ _ _ _ (by decide), hlow 14 (by decide)]; rfl)
  set a6 := install slotsSP3 a5 (fun i => ZeroPadding.pad (![0, 0, total, 0] i)
    (UWalkNumbers.productOutput (L * L * L) ((v - 2 * u) ^ 16) i)) with ha6
  -- `b₀` onto the erased port 2
  have hb := ready_pad _ _ _ _ ![total, 0] (UWalkNumbers.fixed_ready (List.replicate ((2 * v) ^ 16) true))
  have h7 := hb.focus slotsSB (by decide) a6 (by
    intro j; fin_cases j
    · show a6 2 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
        install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
        install_other _ _ _ _ (by decide), ha1, show (2 : Fin 17) = slotsSE 1 from rfl, install_slot _ (by decide)]
      rfl
    · show a6 15 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), hlow 15 (by decide)]; rfl)
  set a7 := install slotsSB a6 (fun i => ZeroPadding.pad (![total, 0] i)
    (![List.replicate ((2 * v) ^ 16) true, List.replicate (List.replicate ((2 * v) ^ 16) true).length false] i))
    with ha7
  -- the counter `1` onto the erased port 3
  have ho := ready_pad _ _ _ _ ![total, 0] (UWalkNumbers.fixed_ready [true])
  have h8 := ho.focus slotsSO (by decide) a7 (by
    intro j; fin_cases j
    · show a7 3 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
        install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        show (3 : Fin 17) = slotsSE 2 from rfl, install_slot _ (by decide)]
      rfl
    · show a7 16 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), hlow 16 (by decide)]; rfl)
  refine ⟨_, _, ?_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 (ClockJoin.join _ _ _ _ _ _ _ h3
    (ClockJoin.join _ _ _ _ _ _ _ h4 (ClockJoin.join _ _ _ _ _ _ _ h5 (ClockJoin.join _ _ _ _ _ _ _ h6
    (ClockJoin.join _ _ _ _ _ _ _ h7 h8)))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hV : (v - 2 * u) ^ 16 ≤ (2 * v) ^ 16 := Nat.pow_le_pow_left (by omega) 16
    have hL1 : L ≤ (L + 1) ^ 3 := by nlinarith [Nat.pow_le_pow_left (show 1 ≤ L + 1 by omega) 2]
    have hL2 : L * L ≤ (L + 1) ^ 3 := by nlinarith [Nat.pow_le_pow_left (show 1 ≤ L + 1 by omega) 2]
    have hL3 : L * L * L ≤ (L + 1) ^ 3 := by nlinarith [Nat.pow_le_pow_left (show 1 ≤ L + 1 by omega) 2]
    have hW1 : 1 ≤ (2 * v) ^ 16 + 3 := by omega
    have e1 := Nat.mul_le_mul hL3 (show 2 * (v - 2 * u) ^ 16 + 3 ≤ 2 * ((2 * v) ^ 16 + 3) by omega)
    have e2 := Nat.mul_le_mul hL2 (show 2 * L + 3 ≤ 3 * (L + 1) by omega)
    have e3 := Nat.mul_le_mul_left ((L + 1) ^ 3) hW1
    have e4 : (L + 1) ^ 3 * (3 * (L + 1)) ≤ 3 * (L + 1) ^ 3 * ((2 * v) ^ 16 + 3) * (L + 1) := by nlinarith
    simp only [CompareMachine.word, List.length_cons, List.length_replicate, List.length_nil,
      UWalkNumbers.productCost, candSetupBound]
    nlinarith
  · rw [install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
      install_other _ _ _ _ (by decide), ha3, show (0 : Fin 17) = slotsSP1 0 from rfl, install_slot _ (by decide)]
    simp [UWalkNumbers.productOutput]
  · rw [install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      show (1 : Fin 17) = slotsSP3 2 from rfl, install_slot _ (by decide)]
    simp [UWalkNumbers.productOutput]
  · rw [install_other _ _ _ _ (by decide), ha7, show (2 : Fin 17) = slotsSB 0 from rfl, install_slot _ (by decide)]
    rfl
  · rw [show (3 : Fin 17) = slotsSO 0 from rfl, install_slot _ (by decide)]; rfl
  · rw [install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
      install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
      install_other _ _ _ _ (by decide), ha1, show (4 : Fin 17) = slotsSE 3 from rfl, install_slot _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
      install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
      install_other _ _ _ _ (by decide), ha1, show (5 : Fin 17) = slotsSE 4 from rfl, install_slot _ (by decide)]
    rfl

end SetupCost

section CoreCost
variable (D : ℕ)

/-- The core length test's time bound. -/
def candCoreBound (q t n : ℕ) : ℕ :=
  (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) * (q + 3) ^ (2 * D + 2) +
    64 * (q + 2 + (q + 2) ^ D) * (t + 2) + 2 * n + 128

/-- The clause machine's budget is polynomial in `q` (as in base's `Width.budget_bound`). -/
theorem clause_budget_le (q : ℕ) :
    RepairSource.CloseoutSchedule.Clause.budget D q ≤
      (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) * (q + 3) ^ (2 * D + 2) := by
  unfold RepairSource.CloseoutSchedule.Clause.budget
  have hp := RepairSource.ProjectionNormalization.DimensionPolynomial.budget_bound D 1 (q + 1)
  have hc := RepairSource.CloseoutSchedule.Clog.budget_bound ((q + 2) ^ D)
  have he : q + 1 + 2 = q + 3 := by omega
  rw [he] at hp
  have hAX : (q + 2) ^ D ≤ (q + 3) ^ (D + 1) := (Nat.pow_le_pow_left (by omega : q + 2 ≤ q + 3) D).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hXP : ((q + 3) ^ (D + 1)) ^ 2 = (q + 3) ^ (2 * D + 2) := by rw [← pow_mul]; congr 1; ring
  have hqP : q + 3 ≤ (q + 3) ^ (2 * D + 2) := Nat.le_self_pow (by omega) _
  have hA2 : ((q + 2) ^ D + 1) ^ 2 ≤ 4 * (q + 3) ^ (2 * D + 2) := by
    have h1 : 1 ≤ (q + 3) ^ (D + 1) := Nat.one_le_pow _ _ (by omega)
    have hs := Nat.pow_le_pow_left (show (q + 2) ^ D + 1 ≤ 2 * (q + 3) ^ (D + 1) by omega) 2
    rw [mul_pow, hXP] at hs
    exact hs
  generalize (q + 3) ^ (2 * D + 2) = P at hp hqP hA2 ⊢
  generalize ((q + 2) ^ D + 1) ^ 2 = Z at hc hA2
  generalize RepairSource.ProjectionNormalization.DimensionPolynomial.budget D 1 (q + 1) = B at hp ⊢
  generalize RepairSource.CloseoutSchedule.Clog.budget ((q + 2) ^ D) = G at hc ⊢
  rw [Nat.add_mul]
  linarith

/-- **The core length test within its time bound.** -/
theorem coreMachine_run (q t n total : ℕ) (hD : 1 ≤ D) : ∃ (cost : ℕ) (out : Fin (Clause.tapes D + 18) → List Bool),
    cost ≤ candCoreBound D q t n ∧
    ClockJoin.ReadyRun (coreMachine D) cost (coreInput D q t n total) out ∧
      out (tl D 0) = ZeroPadding.pad total (List.replicate t true) ∧ out (tl D 1) = List.replicate n true ∧
      out (tl D 16) = [decide ((q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) * (t + 1) * 2 ≤ n)] := by
  set x := coreInput D q t n total with hx
  have htl : ∀ j : Fin 18, 2 ≤ j.val → x (tl D j) = [] := by
    intro j hj; simp only [hx, coreInput, tl_val, tapes_eq]; split_ifs <;> first | rfl | omega
  have htl0 : x (tl D 0) = ZeroPadding.pad total (List.replicate t true) := by
    simp only [hx, coreInput, tl_val, tapes_eq]; split_ifs <;> first | rfl | omega
  have htl1 : x (tl D 1) = List.replicate n true := by
    simp only [hx, coreInput, tl_val, tapes_eq]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by simp)]
  -- the clause machine
  obtain ⟨oc, hc, hcq, hcw⟩ := Clause.clause_run D q hD
  have h1 := hc.focus (cl D) (cl_injective D) x (by
    intro i; simp only [hx, coreInput, cl_val, Clause.input]
    have := i.isLt; split_ifs <;> first | rfl | (rw [tapes_eq] at *; omega))
  set a1 := install (cl D) x oc with ha1
  have a1tl : ∀ j, a1 (tl D j) = x (tl D j) := by
    intro j; rw [ha1, install_other _ _ _ _ (by
      intro i; apply fin_ne; rw [cl_val, tl_val]; have := i.isLt; omega)]
  -- `1^{cw}` from the clause width's word
  have h2 := (UWalkUnary.ready false false 0 (RepairSource.CloseoutLanguage.clauseWidth D q)).focus (slotsCU D)
    (by core_inj) a1 (by
    intro j; fin_cases j
    · show a1 (cl D (Clause.widthSlot D)) = _
      rw [ha1, install_slot _ (cl_injective D), hcw]; simp [UWalkUnary.input, UWalkUnary.source]
    · show a1 (tl D 2) = _; rw [a1tl, htl _ (by decide)]; rfl
    · show a1 (tl D 3) = _; rw [a1tl, htl _ (by decide)]; rfl)
  set a2 := install (slotsCU D) a1 (UWalkUnary.result false false 0 (RepairSource.CloseoutLanguage.clauseWidth D q))
    with ha2
  -- `q + 1 + cw`
  have h3 := (ClockUnarySum.sum_ready (q + 1) (RepairSource.CloseoutLanguage.clauseWidth D q)).focus (slotsCS D)
    (by core_inj) a2 (by
    intro j; fin_cases j
    · show a2 (cl D (Clause.qSlot D)) = _
      rw [ha2, install_other _ _ _ _ (by core_off), ha1, install_slot _ (cl_injective D), hcq]; rfl
    · show a2 (tl D 2) = _
      rw [ha2, show tl D 2 = slotsCU D 1 from rfl, install_slot _ (by core_inj)]
      simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
    · show a2 (tl D 4) = _; rw [ha2, install_other _ _ _ _ (by core_off), a1tl, htl _ (by decide)]; rfl
    · show a2 (tl D 5) = _; rw [ha2, install_other _ _ _ _ (by core_off), a1tl, htl _ (by decide)]; rfl)
  set a3 := install (slotsCS D) a2 ![List.replicate (q + 1) true,
    List.replicate (RepairSource.CloseoutLanguage.clauseWidth D q) true,
    List.replicate (q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) true,
    List.replicate (q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q + 2) false] with ha3
  -- the word of `t + 1` from the padded counter
  have ht := ready_pad _ _ _ _ ![total, 0, 0]
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready true t)
  have h4 := ht.focus (slotsCT D) (by core_inj) a3 (by
    intro j; fin_cases j
    · show a3 (tl D 0) = _
      rw [ha3, install_other _ _ _ _ (by core_off), ha2, install_other _ _ _ _ (by core_off), a1tl, htl0]; rfl
    · show a3 (tl D 6) = _
      rw [ha3, install_other _ _ _ _ (by core_off), ha2, install_other _ _ _ _ (by core_off), a1tl,
        htl _ (by decide)]; rfl
    · show a3 (tl D 7) = _
      rw [ha3, install_other _ _ _ _ (by core_off), ha2, install_other _ _ _ _ (by core_off), a1tl,
        htl _ (by decide)]; rfl)
  set a4 := install (slotsCT D) a3 (fun i => ZeroPadding.pad (![total, 0, 0] i)
    (RepairSource.ProjectionNormalization.DimensionTemplate.output true t i)) with ha4
  -- `m = (q + 1 + cw)(t + 1)`
  have hp := ready_pad _ _ _ _ ![0, t + 1 + 2, 0, 0]
    (UWalkNumbers.product_ready (q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) (t + 1))
  have h5 := hp.focus (slotsCP D) (by core_inj) a4 (by
    intro j; fin_cases j
    · show a4 (tl D 4) = _
      rw [ha4, install_other _ _ _ _ (by core_off), ha3, show tl D 4 = slotsCS D 2 from rfl,
        install_slot _ (by core_inj)]
      simp [UWalkNumbers.productInput]
    · show a4 (tl D 6) = _
      rw [ha4, show tl D 6 = slotsCT D 1 from rfl, install_slot _ (by core_inj)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkNumbers.productInput,
        ← RepairSource.CloseoutCapacity.Power.template_source, UWalkUnary.source, CompareMachine.word]
    · show a4 (tl D 8) = _
      rw [ha4, install_other _ _ _ _ (by core_off), ha3, install_other _ _ _ _ (by core_off), ha2,
        install_other _ _ _ _ (by core_off), a1tl, htl _ (by decide)]; rfl
    · show a4 (tl D 9) = _
      rw [ha4, install_other _ _ _ _ (by core_off), ha3, install_other _ _ _ _ (by core_off), ha2,
        install_other _ _ _ _ (by core_off), a1tl, htl _ (by decide)]; rfl)
  set a5 := install (slotsCP D) a4 (fun i => ZeroPadding.pad (![0, t + 1 + 2, 0, 0] i)
    (UWalkNumbers.productOutput (q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) (t + 1) i)) with ha5
  have hfree : ∀ j : Fin 18, 10 ≤ j.val → a5 (tl D j) = [] := by
    intro j hj
    rw [ha5, install_other _ _ _ _ (by
        intro i; fin_cases i <;> (apply fin_ne; simp [slotsCP, tl]; omega)), ha4,
      install_other _ _ _ _ (by intro i; fin_cases i <;> (apply fin_ne; simp [slotsCT, tl]; omega)), ha3,
      install_other _ _ _ _ (by
        intro i; fin_cases i <;> (apply fin_ne; simp [slotsCS, tl, cl, Clause.qSlot, tapes_eq]; omega)), ha2,
      install_other _ _ _ _ (by
        intro i; fin_cases i <;> (apply fin_ne; simp [slotsCU, tl, cl, width_val, tapes_eq]; omega)),
      a1tl, htl _ (by omega)]
  -- the word `0 1^2`
  have h6 := (UWalkNumbers.fixed_ready (CompareMachine.word 2)).focus (slotsCW D) (by core_inj) a5 (by
    intro j; fin_cases j
    · exact hfree 10 (by decide)
    · exact hfree 11 (by decide))
  set a6 := install (slotsCW D) a5 ![CompareMachine.word 2, List.replicate (CompareMachine.word 2).length false]
    with ha6
  -- `2m`
  have hq := UWalkNumbers.product_ready ((q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) * (t + 1)) 2
  have h7 := hq.focus (slotsCD D) (by core_inj) a6 (by
    intro j; fin_cases j
    · show a6 (tl D 8) = _
      rw [ha6, install_other _ _ _ _ (by core_off), ha5, show tl D 8 = slotsCP D 2 from rfl,
        install_slot _ (by core_inj)]
      simp [UWalkNumbers.productOutput, UWalkNumbers.productInput]
    · show a6 (tl D 10) = _
      rw [ha6, show tl D 10 = slotsCW D 0 from rfl, install_slot _ (by core_inj)]
      simp [UWalkNumbers.productInput, CompareMachine.word]
    · show a6 (tl D 12) = _; rw [ha6, install_other _ _ _ _ (by core_off), hfree 12 (by decide)]; rfl
    · show a6 (tl D 13) = _; rw [ha6, install_other _ _ _ _ (by core_off), hfree 13 (by decide)]; rfl)
  set a7 := install (slotsCD D) a6 (UWalkNumbers.productOutput
    ((q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) * (t + 1)) 2) with ha7
  -- the comparison with `n`
  have h8 := (RepairSource.CloseoutSchedule.RawCompare.compare_run
    ((q + 1 + RepairSource.CloseoutLanguage.clauseWidth D q) * (t + 1) * 2) n).focus (slotsCC D) (by core_inj) a7 (by
    intro j; fin_cases j
    · show a7 (tl D 12) = _
      rw [ha7, show tl D 12 = slotsCD D 2 from rfl, install_slot _ (by core_inj)]
      simp [UWalkNumbers.productOutput, RepairSource.CloseoutSchedule.RawCompare.input]
    · show a7 (tl D 1) = _
      rw [ha7, install_other _ _ _ _ (by core_off), ha6, install_other _ _ _ _ (by core_off), ha5,
        install_other _ _ _ _ (by core_off), ha4, install_other _ _ _ _ (by core_off), ha3,
        install_other _ _ _ _ (by core_off), ha2, install_other _ _ _ _ (by core_off), a1tl, htl1]; rfl
    · show a7 (tl D 14) = _; rw [ha7, install_other _ _ _ _ (by core_off), ha6, install_other _ _ _ _ (by core_off),
        hfree 14 (by decide)]; rfl
    · show a7 (tl D 15) = _; rw [ha7, install_other _ _ _ _ (by core_off), ha6, install_other _ _ _ _ (by core_off),
        hfree 15 (by decide)]; rfl
    · show a7 (tl D 16) = _; rw [ha7, install_other _ _ _ _ (by core_off), ha6, install_other _ _ _ _ (by core_off),
        hfree 16 (by decide)]; rfl
    · show a7 (tl D 17) = _; rw [ha7, install_other _ _ _ _ (by core_off), ha6, install_other _ _ _ _ (by core_off),
        hfree 17 (by decide)]; rfl)
  refine ⟨_, _, ?_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 (ClockJoin.join _ _ _ _ _ _ _ h3
    (ClockJoin.join _ _ _ _ _ _ _ h4 (ClockJoin.join _ _ _ _ _ _ _ h5 (ClockJoin.join _ _ _ _ _ _ _ h6
    (ClockJoin.join _ _ _ _ _ _ _ h7 h8)))))), ?_, ?_, ?_⟩
  · have hcl := clause_budget_le D q
    have hcw : RepairSource.CloseoutLanguage.clauseWidth D q ≤ (q + 2) ^ D :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    set cw := RepairSource.CloseoutLanguage.clauseWidth D q
    set M := q + 2 + (q + 2) ^ D
    have hm : q + 1 + cw + 1 ≤ M := by omega
    have hmin : min ((q + 1 + cw) * (t + 1) * 2) n ≤ n := min_le_right _ _
    have h1 := Nat.mul_le_mul_right (t + 2) hm
    simp only [CompareMachine.word, List.length_cons, List.length_replicate,
      UWalkNumbers.productCost, RepairSource.CloseoutSchedule.RawCompare.budget, candCoreBound]
    nlinarith
  · rw [install_other _ _ _ _ (by core_off), ha7, install_other _ _ _ _ (by core_off), ha6,
      install_other _ _ _ _ (by core_off), ha5, install_other _ _ _ _ (by core_off), ha4,
      show tl D 0 = slotsCT D 0 from rfl, install_slot _ (by core_inj)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output]
  · rw [show tl D 1 = slotsCC D 1 from rfl, install_slot _ (by core_inj)]
    simp [RepairSource.CloseoutSchedule.RawCompare.output]
  · rw [show tl D 16 = slotsCC D 4 from rfl, install_slot _ (by core_inj)]
    simp [RepairSource.CloseoutSchedule.RawCompare.output]

end CoreCost

end NearCubicWires.WireExponent3_5.Transfer
