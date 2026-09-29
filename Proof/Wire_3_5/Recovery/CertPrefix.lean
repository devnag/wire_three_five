import Proof.Wire_3_5.Recovery.CertPrefixPrep

/-! # The prefix of the `E^NP` program: `2^{a(n)}` from the input word (P3:3738-3741, 3758-3759; D1.6)

Realizes "For source lengths `N_a = 2^a`, put `m_a = t(q(N_a))q_0(N_a)`. Choose the largest `a` such that
`m_a ≤ n/2`" (P3:3738-3740) and the first half of "The resulting slice is computable in `E^NP`. Run the fixed refuter
[…] on the source length `N_{a(n)}`" (P3:3758-3759): from the framed input `x` of length `n` the prefix computes
`N = 2^{S}` with `S` the scan's index after `n` rounds (`S = a(n) = sliceIdx n` for `n ≥ n₀`, `S ≤ n` always), in time
polynomial in `2^n`. The preparation (`prepMachine`), the scan (`scanLoop`, focused on the scan block) and base's
`CloseoutCapacity.Power` (`1^S ↦ 1^{2^S}`) run on `prefixTapes D` tapes; `prefixCold` places them on base's cold
layout `Cold.tapes w` (input `frame x` on `Cold.extra w 0`, output on `Cold.port w 2`), the contract of base's
`CloseoutSchedule.Guarded.continuation_run`, so base's onset guard and refuter call apply unchanged.

Paper quantities: `N_{a(n)} = 2^{a(n)}` and the polynomial clock; **`prefixCold`** and **`prefix_cold_run`**: `∃ e₁ e₂ e₃
coef E, ∀ x`, a ready run within `coef·(2^n+1)^E` keeping `frame x` on `Cold.extra w 0` and writing `1^{2^S}` on
`Cold.port w 2`, with `S = scanS … n`; **`prefix_index`**: `S ≤ n`, and `S = sliceIdx n` past `n₀`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CertPrefix
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Prefix
variable (k A u v D : ℕ)

/-- Base's power machine: `1^S` from the scan index (1), `1^{2^S}` onto `scanTapes D + 119`. -/
def slPow (i : Fin 17) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 1 else scanTapes D + 104 + i.val, by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩

theorem slPow_inj : Function.Injective (slPow D) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [slPow, Fin.val_mk] at hv; apply Fin.ext
  split_ifs at hv <;> omega

/-- **The prefix** on its own tapes: the preparation, the scan, `2^S`. -/
noncomputable def prefixCore (e1 e2 e3 : ℕ) :=
  Composition.machine (prepMachine D ((v - u) ^ 16) (v ^ 16) e1 e2 e3)
  (Composition.machine (RecoveryFocus.machine (slS D) (scanLoop k A u v D))
    (RecoveryFocus.machine (slPow D) RepairSource.CloseoutCapacity.Power.machine))

/-- The scan's index after `n` rounds at length `n` with `c = n` rounds of the schedule loop. -/
def prefixS (n : ℕ) : ℕ := scanS k A u v D n ((v - u) ^ 16) (v ^ 16) n n

/-- The scan loop's cost. -/
def scanCost (n p w C1 C2 C3 : ℕ) : ℕ :=
  1 + 1 + (n * (scanRoundBound k A v D n n p w C1 C2 n + 1 + (2 * C3 + 4 + 1 + 0) + 2) + n + 3 + 1 + 1)

/-- The prefix's cost. -/
def prefixCost (e1 e2 e3 : ℕ) (bits : List Bool) : ℕ :=
  prepCostA e1 e2 e3 bits + 1 + prepCostB ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) (pcap e2 bits.length)
    (pcap e3 bits.length) + 1 +
  (scanCost k A v D bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) (pcap e2 bits.length)
    (pcap e3 bits.length) + 1 + RepairSource.CloseoutCapacity.Power.budget (prefixS k A u v D bits.length))

/-- **The prefix is ready** on its own tapes, given the capacities' constraints at `n`. -/
theorem prefixCore_run (e1 e2 e3 : ℕ) (hD : 1 ≤ D) (bits : List Bool)
    (hn : bits.length ≤ pcap e1 bits.length)
    (hvals : ∀ a, a ≤ bits.length → ∀ i, i ≤ bits.length →
      candA0 k A u v a * ((v - u) ^ 16) ^ i ≤ pcap e1 bits.length ∧
      candB0 v * (v ^ 16) ^ i ≤ pcap e1 bits.length ∧ 1 + i ≤ pcap e1 bits.length)
    (hT : max (pcap e1 bits.length + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 bits.length)
    (hTc : roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) + 1 ≤ pcap e2 bits.length)
    (hTs : pcap e2 bits.length + 1 + bits.length + bits.length + 1 ≤ pcap e3 bits.length)
    (hTs' : scanRoundBound k A v D bits.length bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length)
      (pcap e2 bits.length) bits.length + 1 ≤ pcap e3 bits.length) :
    ∃ out : Fin (prefixTapes D) → List Bool,
      ClockJoin.ReadyRun (prefixCore k A u v D e1 e2 e3) (prefixCost k A u v D e1 e2 e3 bits) (prefixInput D bits) out ∧
      out (ppos D 0 (by unfold prefixTapes; omega)) = frame bits ∧
      out (ppos D (scanTapes D + 119) (by unfold prefixTapes; omega)) =
        List.replicate (2 ^ prefixS k A u v D bits.length) true := by
  set n := bits.length with hn'
  set C1 := pcap e1 n with hC1
  set C2 := pcap e2 n with hC2
  set C3 := pcap e3 n with hC3
  have hST := scanTapes_eq D
  obtain ⟨a, ha, hB⟩ := prep_run D ((v - u) ^ 16) (v ^ 16) e1 e2 e3 bits
  have hblock := block_eq D bits ((v - u) ^ 16) (v ^ 16) C1 C2 C3 a hB
  obtain ⟨az, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, atop⟩ := hB
  -- the scan
  have hl := scanLoop_ready k A u v D n n [] [] [] ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n C3 (C3 + 1)
    hD le_rfl hn (by simp) (by simp) (by simp) hvals hT hTc le_rfl hTs hTs' le_rfl
  have g2 := hl.focus (slS D) (slS_inj D) a (fun i => (hblock i).trans rfl)
  set a2 := install (slS D) a (Fin.addCases (roundTapes (padScratch (scanScratch D) C3
    (scanQ k A u v D [] [] [] n ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n n)) C3 (C3 + 1))
    (fun _ => CompareMachine.word n)) with ha2
  have a2S : a2 (slPow D 0) = ZeroPadding.pad C1 (List.replicate (prefixS k A u v D n) true) := by
    rw [show slPow D 0 = slS D ⟨0, by omega⟩ from Fin.ext (by simp [slPow, slS]), ha2, install_slot _ (slS_inj D),
      loopIn_val, dif_pos (by simp; omega)]
    simp only [padScratch]
    rw [scratchCap_scan, if_neg (by simp)]
    simp [scanQ, scanInput, ZeroPadding.pad, prefixS]
  have a2off : ∀ q : Fin (prefixTapes D), (q.val = 0 ∨ scanTapes D + 4 ≤ q.val) → a2 q = a q := by
    intro q hq
    rw [ha2, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [slS, Fin.val_mk]; omega)]
  -- `2^S`
  obtain ⟨po, pr, p15, -⟩ := RepairSource.CloseoutCapacity.Power.power_run (prefixS k A u v D n)
  have hp := ready_pad _ _ _ _ (fun i : Fin 17 => if i.val = 0 then C1 else 0) pr
  have g3 := hp.focus (slPow D) (slPow_inj D) a2 (by
    intro j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this
      rw [a2S]; simp [RepairSource.CloseoutCapacity.Power.input]
    · rw [a2off _ (Or.inr (by simp only [slPow, Fin.val_mk]; rw [if_neg hj]; omega)),
        atop _ (by simp only [slPow, Fin.val_mk]; rw [if_neg hj]; omega)]
      simp [RepairSource.CloseoutCapacity.Power.input, hj, ZeroPadding.pad])
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ ha (ClockJoin.join _ _ _ _ _ _ _ g2 g3), ?_, ?_⟩
  · rw [install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [slPow, ppos, Fin.val_mk]; split_ifs <;> omega),
      a2off _ (Or.inl (by simp [ppos])), az]
  · rw [show ppos D (scanTapes D + 119) _ = slPow D 15 from Fin.ext (by simp [slPow, ppos]),
      install_slot _ (slPow_inj D)]
    simp [p15, ZeroPadding.pad]

/-! ## The polynomial clock -/

/-- The prefix's time coefficient. -/
def prefixCoef (e1 e2 e3 : ℕ) : ℕ :=
  1000 + RepairSource.CloseoutCapacity.coefficient e1 e1 + RepairSource.CloseoutCapacity.coefficient e2 e2 +
    RepairSource.CloseoutCapacity.coefficient e3 e3 + 2 * ((v - u) ^ 16 + v ^ 16) + 8 * (2 ^ e1 + 2 ^ e2 + 2 ^ e3)

theorem prefixS_le (n : ℕ) : prefixS k A u v D n ≤ n := scanSeq_le _ n

/-- **The prefix runs in time polynomial in `2^n`.** -/
theorem prefixCost_le (e1 e2 e3 : ℕ) (bits : List Bool)
    (hTs' : scanRoundBound k A v D bits.length bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length)
      (pcap e2 bits.length) bits.length + 1 ≤ pcap e3 bits.length) :
    prefixCost k A u v D e1 e2 e3 bits ≤
      prefixCoef u v e1 e2 e3 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
  have hx : 1 ≤ 2 ^ bits.length + 1 := Nat.le_add_left 1 _
  have hnx := self_le_x bits.length
  have hp : ∀ a, a ≤ e1 + e2 + e3 + 4 → (2 ^ bits.length + 1) ^ a ≤ (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) :=
    fun a h => Nat.pow_le_pow_right hx h
  have ux : 2 ^ bits.length + 1 ≤ (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
    calc 2 ^ bits.length + 1 = (2 ^ bits.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := hp 1 (by omega)
  have hal := RepairSource.CloseoutCapacity.allocation_budget 1 0 bits
  have hc1 := (RepairSource.CloseoutCapacity.budget_bound e1 e1 bits).trans
    (Nat.mul_le_mul_left _ (hp (e1 + 1) (by omega)))
  have hc2 := (RepairSource.CloseoutCapacity.budget_bound e2 e2 bits).trans
    (Nat.mul_le_mul_left _ (hp (e2 + 1) (by omega)))
  have hc3 := (RepairSource.CloseoutCapacity.budget_bound e3 e3 bits).trans
    (Nat.mul_le_mul_left _ (hp (e3 + 1) (by omega)))
  have hC1 : pcap e1 bits.length ≤ 2 ^ e1 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) :=
    (cap_le_poly e1 bits.length).trans (Nat.mul_le_mul_left (2 ^ e1) (hp e1 (by omega)))
  have hC2 : pcap e2 bits.length ≤ 2 ^ e2 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) :=
    (cap_le_poly e2 bits.length).trans (Nat.mul_le_mul_left (2 ^ e2) (hp e2 (by omega)))
  have hC3x : (2 ^ bits.length + 1) * pcap e3 bits.length ≤ 2 ^ e3 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
    calc (2 ^ bits.length + 1) * pcap e3 bits.length
        ≤ (2 ^ bits.length + 1) * (2 ^ e3 * (2 ^ bits.length + 1) ^ e3) :=
          Nat.mul_le_mul_left _ (cap_le_poly e3 bits.length)
      _ = 2 ^ e3 * (2 ^ bits.length + 1) ^ (e3 + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hp _ (by omega))
  have hC3 : pcap e3 bits.length ≤ 2 ^ e3 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
    have := Nat.le_mul_of_pos_left (pcap e3 bits.length) (show 0 < 2 ^ bits.length + 1 by omega)
    omega
  have hS := prefixS_le k A u v D bits.length
  have hpow : RepairSource.CloseoutCapacity.Power.budget (prefixS k A u v D bits.length) ≤
      384 * (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
    have h1 := RepairSource.CloseoutCapacity.power_budget (prefixS k A u v D bits.length)
    have h2 : 2 ^ prefixS k A u v D bits.length ≤ 2 ^ bits.length := Nat.pow_le_pow_right (by norm_num) hS
    have h3 : 128 * (prefixS k A u v D bits.length + 3) * (2 ^ prefixS k A u v D bits.length + 1) ≤
        128 * (3 * (2 ^ bits.length + 1)) * (2 ^ bits.length + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h4 : (2 ^ bits.length + 1) * (2 ^ bits.length + 1) ≤ (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := by
      rw [← pow_two]; exact hp 2 (by omega)
    nlinarith
  have hscan : bits.length * (scanRoundBound k A v D bits.length bits.length ((v - u) ^ 16) (v ^ 16)
      (pcap e1 bits.length) (pcap e2 bits.length) bits.length + 1 + (2 * pcap e3 bits.length + 4 + 1 + 0) + 2) ≤
      3 * ((2 ^ bits.length + 1) * pcap e3 bits.length) + 7 * (2 ^ bits.length + 1) := by
    calc _ ≤ (2 ^ bits.length + 1) * (3 * pcap e3 bits.length + 7) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  unfold prefixCost prepCostA prepCostB scanCost prefixCoef
  simp only [CompareMachine.word, List.length_cons, List.length_replicate]
  have hX1 : 1 ≤ (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) := hx.trans ux
  generalize (2 ^ bits.length + 1) ^ (e1 + e2 + e3 + 4) = X at *
  have hpX : (v - u) ^ 16 ≤ (v - u) ^ 16 * X := Nat.le_mul_of_pos_right _ hX1
  have hwX : v ^ 16 ≤ v ^ 16 * X := Nat.le_mul_of_pos_right _ hX1
  have hdist : (1000 + RepairSource.CloseoutCapacity.coefficient e1 e1 + RepairSource.CloseoutCapacity.coefficient e2 e2 +
      RepairSource.CloseoutCapacity.coefficient e3 e3 + 2 * ((v - u) ^ 16 + v ^ 16) + 8 * (2 ^ e1 + 2 ^ e2 + 2 ^ e3)) * X =
      1000 * X + RepairSource.CloseoutCapacity.coefficient e1 e1 * X + RepairSource.CloseoutCapacity.coefficient e2 e2 * X +
      RepairSource.CloseoutCapacity.coefficient e3 e3 * X + 2 * ((v - u) ^ 16 * X) + 2 * (v ^ 16 * X) +
      8 * (2 ^ e1 * X) + 8 * (2 ^ e2 * X) + 8 * (2 ^ e3 * X) := by ring
  omega

end Prefix

/-! ## On base's cold layout -/

section Cold
variable (k A u v D : ℕ)

/-- The prefix's tapes on base's cold layout: `frame x` on `Cold.extra w 0`, `1^{2^S}` on `Cold.port w 2`. -/
def coldSlot (i : Fin (prefixTapes D)) : Fin (RepairSource.CloseoutSchedule.Cold.tapes (prefixTapes D)) :=
  ⟨if i.val = 0 then prefixTapes D + 6 else if i.val = scanTapes D + 119 then prefixTapes D + 2 else i.val,
    by have := i.isLt; unfold RepairSource.CloseoutSchedule.Cold.tapes; split_ifs <;> omega⟩

theorem coldSlot_inj : Function.Injective (coldSlot D) := by
  intro a b h; have hv := congrArg Fin.val h; have ha := a.isLt; have hb := b.isLt
  simp only [coldSlot, Fin.val_mk] at hv; apply Fin.ext; split_ifs at hv <;> omega

/-- **The prefix on base's cold layout.** -/
noncomputable def prefixCold (e1 e2 e3 : ℕ) := RecoveryFocus.machine (coldSlot D) (prefixCore k A u v D e1 e2 e3)

/-- **The prefix meets base's cold contract** (`CloseoutSchedule.Guarded.continuation_run`'s hypotheses) with
`N = 2^S`, `S = prefixS … n`, within a polynomial clock. -/
theorem prefix_cold_run (hD : 1 ≤ D) (huv : 2 * u < v) : ∃ e1 e2 e3 coef E : ℕ, ∀ bits : List Bool,
    ∃ out : Fin (RepairSource.CloseoutSchedule.Cold.tapes (prefixTapes D)) → List Bool,
      ClockJoin.ReadyRun (prefixCold k A u v D e1 e2 e3) (coef * (2 ^ bits.length + 1) ^ E)
        (RepairSource.CloseoutSchedule.Cold.input (prefixTapes D) bits) out ∧
      out (RepairSource.CloseoutSchedule.Cold.extra (prefixTapes D) 0) = frame bits ∧
      out (RepairSource.CloseoutSchedule.Cold.port (prefixTapes D) 2) =
        ZeroPadding.pad 0 (List.replicate (2 ^ prefixS k A u v D bits.length) true) := by
  obtain ⟨e1, e2, e3, hcaps⟩ := prefix_caps k A u v D huv
  refine ⟨e1, e2, e3, prefixCoef u v e1 e2 e3, e1 + e2 + e3 + 4, fun bits => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcaps bits.length
  obtain ⟨o, hr, o0, oN⟩ := prefixCore_run k A u v D e1 e2 e3 hD bits h1 h2 h3 h4 h5 h6
  have hcost := prefixCost_le k A u v D e1 e2 e3 bits h6
  have hST := scanTapes_eq D
  have g := (ClockJoin.enlarge _ _ _ _ _ hr hcost).focus (coldSlot D) (coldSlot_inj D)
    (RepairSource.CloseoutSchedule.Cold.input (prefixTapes D) bits) (by
      intro j
      have hj := j.isLt
      by_cases h0 : j.val = 0
      · simp [coldSlot, prefixInput, RepairSource.CloseoutSchedule.Cold.input, h0]
      · have hne : (coldSlot D j).val ≠ prefixTapes D + 6 := by
          simp only [coldSlot, Fin.val_mk]; split_ifs <;> omega
        simp [RepairSource.CloseoutSchedule.Cold.input, prefixInput, h0, hne])
  refine ⟨_, g, ?_, ?_⟩
  · rw [show RepairSource.CloseoutSchedule.Cold.extra (prefixTapes D) 0 = coldSlot D (ppos D 0 (by
        unfold prefixTapes; omega)) from Fin.ext (by
        simp [coldSlot, ppos, RepairSource.CloseoutSchedule.Cold.extra]), install_slot _ (coldSlot_inj D), o0]
  · rw [show RepairSource.CloseoutSchedule.Cold.port (prefixTapes D) 2 = coldSlot D (ppos D (scanTapes D + 119) (by
        unfold prefixTapes; omega)) from Fin.ext (by
        simp [coldSlot, ppos, RepairSource.CloseoutSchedule.Cold.port, RepairSource.CloseoutSchedule.Cold.core]),
      install_slot _ (coldSlot_inj D), oN]
    simp [ZeroPadding.pad]

/-- **The prefix's index is `a(n)`**: `S ≤ n` always, and `S = sliceIdx n = a(n)` past `n₀` (with the words of `ζ`). -/
theorem prefix_index {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) :
    (∀ n, prefixS k A (zu ζ) (zv ζ) D n ≤ n) ∧
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → prefixS k A (zu ζ) (zv ζ) D n = sliceIdx h0 h1 k A D n := by
  refine ⟨fun n => prefixS_le k A _ _ D n, ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_sched_le h0 h1 k A
  exact ⟨n₀, fun n hn => scanSeq_slice h0 h1 k A D n₀ hn₀ n hn⟩

/-- **Consumer check: base's onset guard runs on the prefix unchanged** (`CloseoutSchedule.Guarded`): the guarded
prefix keeps `frame x`, writes the onset flag `[onset ≤ 2^S]` and the framed source word `1^{2^S}`. -/
theorem prefix_guarded (hD : 1 ≤ D) (huv : 2 * u < v) : ∃ e1 e2 e3 coef E : ℕ, ∀ (bits : List Bool) (onset : ℕ),
    ∃ out, ClockJoin.ReadyRun (RepairSource.CloseoutSchedule.Guarded.machine (prefixCold k A u v D e1 e2 e3) onset)
      (coef * (2 ^ bits.length + 1) ^ E + 1 + (6 * onset + 18) + 1 + (6 * 2 ^ prefixS k A u v D bits.length + 15))
      (RepairSource.CloseoutSchedule.Guarded.input (prefixTapes D) bits) out ∧
    out (RepairSource.CloseoutSchedule.Guarded.old (prefixTapes D)
      (RepairSource.CloseoutSchedule.Cold.extra (prefixTapes D) 0)) = frame bits ∧
    out (RepairSource.CloseoutSchedule.Guarded.fresh (prefixTapes D) 4) =
      [decide (onset ≤ 2 ^ prefixS k A u v D bits.length)] ∧
    out (RepairSource.CloseoutSchedule.Guarded.fresh (prefixTapes D) 8) =
      frame (List.replicate (2 ^ prefixS k A u v D bits.length) true) := by
  obtain ⟨e1, e2, e3, coef, E, h⟩ := prefix_cold_run k A u v D hD huv
  refine ⟨e1, e2, e3, coef, E, fun bits onset => ?_⟩
  obtain ⟨out, hr, hx, hN⟩ := h bits
  exact RepairSource.CloseoutSchedule.Guarded.continuation_run _ bits onset 0 _ out hr hx hN

end Cold

end NearCubicWires.WireExponent3_5.Transfer.CertPrefix
