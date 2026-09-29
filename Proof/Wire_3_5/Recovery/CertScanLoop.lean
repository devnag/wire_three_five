import Proof.Wire_3_5.Recovery.CertScan

/-! # The prefix's scan: `n` rounds compute `a(n)` (P3:3738-3741; D1.6, the prefix stage)

Realizes "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3740) as a loop: `n` rounds of `scanWorker` on one reused
bank (the uniform fold), each testing the candidate `S + 1` and adding the bit to `S`. The test at `a` runs the
schedule loop for `c` rounds; its counter is `t(q)` once `t(q) ≤ c + 1` (`roundCount_sched`), and with `c = n`
this holds for every `a ≤ n` once `n` is large, because `t(q) = O(log L)` (P3:3742-3744, `sched_log`) and
`L = ⌈log₂(q+2)⌉` with `q = q(2^a) = O(a log a)`.

Paper quantities: the scan index after `i` rounds, **`scanSeq`**; **`scanSeq_eq_scanUp`** (a monotone test makes the
bit-sum scan the upward scan); **`scanFlag_eq`** (the round's bit is `[m_a ≤ n/2]`); **`eventually_sched_le`**;
**`scanSeq_slice`**: for `n ≥ n₀` the scan's index after `n` rounds is `a(n) = sliceIdx n`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open Filter

/-! ## The bit-sum scan is the upward scan -/

/-- The scan's index after `i` rounds, adding the bit at the next candidate each round. -/
def scanSeq (flag : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => scanSeq flag i + (flag (scanSeq flag i + 1)).toNat

theorem scanSeq_le (flag : ℕ → Bool) (i : ℕ) : scanSeq flag i ≤ i := by
  induction i with
  | zero => simp [scanSeq]
  | succ i ih => simp only [scanSeq]; have := Bool.toNat_le (flag (scanSeq flag i + 1)); omega

/-- Two tests agreeing on `1, …, n` give the same scan for `n` rounds. -/
theorem scanSeq_congr (flag flag' : ℕ → Bool) (n : ℕ) (h : ∀ a, 1 ≤ a → a ≤ n → flag a = flag' a) :
    ∀ i, i ≤ n → scanSeq flag i = scanSeq flag' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have e := ih (by omega)
    have hle := scanSeq_le flag i
    simp only [scanSeq, e, h (scanSeq flag' i + 1) (by omega) (by rw [← e]; omega)]

/-- **With a downward-closed test the bit-sum scan is the upward scan.** -/
theorem scanSeq_eq_scanUp (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    scanSeq (fun a => decide (P a)) n = scanUp P n n 0 := by
  set step : ℕ → ℕ := fun a => a + (decide (P (a + 1))).toNat with hstep
  have hit : ∀ i, scanSeq (fun a => decide (P a)) i = step^[i] 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ← ih]; rfl
  have key : ∀ fuel a, a + fuel ≤ n → step^[fuel] a = scanUp P n fuel a := by
    intro fuel
    induction fuel with
    | zero => intro a _; rfl
    | succ fuel ih =>
      intro a ha
      rw [Function.iterate_succ_apply]
      by_cases hp : P (a + 1)
      · have e : step a = a + 1 := by simp [hstep, hp]
        rw [e, ih (a + 1) (by omega)]
        simp only [scanUp, if_pos (show a < n ∧ P (a + 1) from ⟨by omega, hp⟩)]
      · have e : step a = a := by simp [hstep, hp]
        rw [e, Function.iterate_fixed e]
        simp only [scanUp, if_neg (show ¬ (a < n ∧ P (a + 1)) from fun h => hp h.2)]
  rw [hit, key n 0 (by omega)]

/-! ## Executable twins -/

-- the bit-sum scan and the upward scan agree on a downward-closed test (`a² ≤ 50`, largest `a = 7`)
-- and on a test that is not downward closed they stop at the first failure (`a = 2` alone: index `0`)

/-! ## The round's bit is `[m_a ≤ n/2]` -/

section Correct
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (k A D : ℕ)

/-- **The round's bit is the paper's test** once the schedule loop has run `c ≥ t(q) − 1` rounds. -/
theorem scanFlag_eq (a n c : ℕ) (hc : sched ζ h0 h1 (Ledger.Lq (widthAt k A a)) ≤ c + 1) :
    scanFlag k A (zu ζ) (zv ζ) D a n ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) c =
      decide (coreLen h0 h1 k A D a ≤ n / 2) := by
  unfold scanFlag candT
  have e1 : candA0 k A (zu ζ) (zv ζ) a = schedA ζ (Ledger.Lq (widthAt k A a)) 0 := by
    unfold candA0 candL0 schedA; ring
  have e2 : candB0 (zv ζ) = schedB ζ 0 := by unfold candB0 schedB; ring
  rw [e1, e2, roundCount_sched h0 h1 _ c hc]
  unfold coreLen Ledger.addrWidth
  apply decide_eq_decide.mpr
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  simp only [RepairSource.CloseoutLanguage.clauseWidth]
  constructor <;> intro h <;> linarith

/-- **The schedule fits in `n` rounds eventually**: `t(L(q(2^a))) ≤ n + 1` for every `a ≤ n`, `n ≥ n₀`. -/
theorem eventually_sched_le : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ a, a ≤ n →
    sched ζ h0 h1 (Ledger.Lq (widthAt k A a)) ≤ n + 1 := by
  obtain ⟨J, hJ⟩ := exists_block h0 h1
  set K := (A + 1) * (k + 2) + 3 * A + 2 with hK
  set J' := J + 1 with hJ'
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_poly_le_div16 k A (K * (2 * J')) 1)
  refine ⟨2 * J' * (N₀ + 1), fun n hn a ha => ?_⟩
  set m := n / (2 * J') with hm
  have hm1 : N₀ + 1 ≤ m := by rw [hm]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
  have hnm : n < 2 * J' * (m + 1) := by
    rw [hm]; have := Nat.lt_mul_div_succ n (show 0 < 2 * J' by omega); linarith
  -- `q(2^m) ≥ m`, so the eventual bound at `N = 2^m` controls `n`
  have hN : N₀ ≤ 2 ^ m := by have := Nat.lt_two_pow_self (n := m); omega
  have hpoly := hN₀ (2 ^ m) hN
  rw [← widthAt_eq] at hpoly
  have hwm : m ≤ widthAt k A m := by unfold widthAt; nlinarith
  have hdiv : 2 ^ m / 16 ≤ 2 ^ m := Nat.div_le_self _ _
  -- `q(2^n) + 2 ≤ K (n + 1) ≤ 2^m`
  have hwn : widthAt k A n + 2 ≤ K * (n + 1) := by
    have hc := clog_two_le_self (n * (k + 2) + 2)
    unfold widthAt
    have := Nat.mul_le_mul_left A hc
    rw [hK]; nlinarith
  have hKm : K * (n + 1) ≤ 2 ^ m := by
    have h1' : K * (n + 1) ≤ K * (2 * J') * (m + 1) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by omega)
    have h2' : K * (2 * J') * (m + 1) ≤ K * (2 * J') * (widthAt k A m + 1) ^ 1 := by
      rw [pow_one]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  -- `L ≤ m`
  have hL : Ledger.Lq (widthAt k A a) ≤ m := by
    unfold Ledger.Lq
    exact Nat.clog_le_of_le_pow ((show widthAt k A a + 2 ≤ widthAt k A n + 2 by
      have := widthAt_mono k A ha; omega).trans (hwn.trans hKm))
  have hs := sched_log h0 h1 hJ (Ledger.Lq (widthAt k A a))
  have hlog := Nat.log_le_self 2 (Ledger.Lq (widthAt k A a))
  have h3 : J * (Nat.log 2 (Ledger.Lq (widthAt k A a)) + 1) ≤ J * (m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * J' * m ≤ n := by rw [hm]; exact Nat.mul_div_le n (2 * J')
  nlinarith

/-- **The scan computes `a(n)`**: with `c = n` rounds of the schedule loop, `n ≥ n₀` rounds of the scan end at
`sliceIdx n`. -/
theorem scanSeq_slice (n₀ : ℕ) (hn₀ : ∀ n, n₀ ≤ n → ∀ a, a ≤ n → sched ζ h0 h1 (Ledger.Lq (widthAt k A a)) ≤ n + 1)
    (n : ℕ) (hn : n₀ ≤ n) :
    scanSeq (fun a => scanFlag k A (zu ζ) (zv ζ) D a n ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) n) n =
      sliceIdx h0 h1 k A D n := by
  rw [scanSeq_congr _ (fun a => decide (coreLen h0 h1 k A D a ≤ n / 2)) n
    (fun a _ ha => scanFlag_eq h0 h1 k A D a n n (hn₀ n hn a ha)) n le_rfl]
  exact scanSeq_eq_scanUp _ n

end Correct

/-! ## Monotone time bounds -/

section Bounds
variable (k A u v D : ℕ)

theorem candBound_mono (a a' n p w total T c : ℕ) (h : a ≤ a') :
    candBound k A v D a n p w total T c ≤ candBound k A v D a' n p w total T c := by
  have hw := widthAt_mono k A h
  have hL : candL0 k A a ≤ candL0 k A a' := by unfold candL0 Ledger.Lq; exact Nat.clog_mono_right 2 (by omega)
  unfold candBound candWidthBound candLqBound candSetupBound candCoreBound
  gcongr

theorem scanRoundBound_mono (S S' n p w total T c : ℕ) (h : S ≤ S') :
    scanRoundBound k A v D S n p w total T c ≤ scanRoundBound k A v D S' n p w total T c := by
  unfold scanRoundBound
  have := candBound_mono k A v D (S + 1) (S' + 1) n p w total T c (by omega)
  omega

/-- Every tape of the inner block is at most `capF + c + 1` long. -/
theorem innerTapes_length (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (hA : Ap.length ≤ total)
    (hB : Bp.length ≤ total) (hE : Ep.length ≤ total) (hcap : total + 1 ≤ capT)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hcapF : T + 1 ≤ capF) (j : Fin (30 + 2 + 1)) :
    (innerTapes Ap Bp Ep p w total capT T capF c j).length ≤ capF + c + 1 := by
  have h1 : capT ≤ T := le_of_max_le_left hT
  have h2 : p + 1 ≤ T := le_of_max_le_left (le_of_max_le_right hT)
  have h3 : w + 1 ≤ T := le_of_max_le_right (le_of_max_le_right hT)
  unfold innerTapes
  split_ifs <;> simp [CompareMachine.word] <;> omega

theorem scanInput_length (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (hS : S ≤ total)
    (hA : Ap.length ≤ total) (hB : Bp.length ≤ total) (hE : Ep.length ≤ total) (hcap : total + 1 ≤ capT)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hcapF : T + 1 ≤ capF) (i : Fin (scanTapes D)) :
    (scanInput D S n Ap Bp Ep p w total capT T capF c i).length ≤ capF + c + n + 1 := by
  have h1 : capT ≤ T := le_of_max_le_left hT
  unfold scanInput
  split_ifs with h0 h1' h2
  · rw [pad_length_total _ _ hS]; omega
  · simp; omega
  · have := innerTapes_length Ap Bp Ep p w total capT T capF c hA hB hE hcap hT hcapF ⟨i.val - 2, by omega⟩
    omega
  · simp

end Bounds

/-! ## The scan loop -/

section Loop
variable (k A u v D : ℕ)

/-- The round's scratch: every position from 35 on. -/
def scanScratch (j : Fin (Clause.tapes D + 84)) : Fin (scanTapes D) :=
  ⟨35 + j.val, by have := j.isLt; unfold scanTapes candTapes; omega⟩

theorem scanScratch_inj : Function.Injective (scanScratch D) := by
  intro a b h; have := congrArg Fin.val h; simp only [scanScratch, Fin.val_mk] at this; exact Fin.ext (by omega)

/-- **The scan**: rounds of `scanWorker` on one reused bank. -/
noncomputable def scanLoop :=
  foldLoop (foldBody (scanWorker k A u v D) (scanScratch D) (idleMachine (scanTapes D + 2)))

/-- The scan's index after `i` rounds at length `n`. -/
def scanS (n p w c i : ℕ) : ℕ := scanSeq (fun a => scanFlag k A u v D a n p w c) i

/-- The stale inner ports before round `i`. -/
def scanStA (A0 : List Bool) (n p w total c : ℕ) : ℕ → List Bool
  | 0 => A0
  | i + 1 => ZeroPadding.pad total (List.replicate (candA0 k A u v (scanS k A u v D n p w c i + 1) * p ^ c) true)
def scanStB (B0 : List Bool) (w total c : ℕ) : ℕ → List Bool
  | 0 => B0
  | _ + 1 => ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true)
def scanStE (E0 : List Bool) (n p w total c : ℕ) : ℕ → List Bool
  | 0 => E0
  | i + 1 => ZeroPadding.pad total (List.replicate (candT k A u v (scanS k A u v D n p w c i + 1) p w c) true)

/-- The round's tapes before round `i`. -/
def scanQ (A0 B0 E0 : List Bool) (n p w total capT T capF c i : ℕ) : Fin (scanTapes D) → List Bool :=
  scanInput D (scanS k A u v D n p w c i) n (scanStA k A u v D A0 n p w total c i) (scanStB v B0 w total c i)
    (scanStE k A u v D E0 n p w total c i) p w total capT T capF c

/-- **The scan is ready**: `nr` rounds from `S = 0` end at `S = scanS … nr`, with `1^n` and the inner block kept, given
value capacities for every candidate `a ≤ nr`. -/
theorem scanLoop_ready (n nr : ℕ) (A0 B0 E0 : List Bool) (p w total capT T capF c Ts capFs : ℕ) (hD : 1 ≤ D)
    (hcap : total + 1 ≤ capT) (hnr : nr ≤ total) (hA0 : A0.length ≤ total) (hB0 : B0.length ≤ total)
    (hE0 : E0.length ≤ total)
    (hvals : ∀ a, a ≤ nr → ∀ i, i ≤ c →
      candA0 k A u v a * p ^ i ≤ total ∧ candB0 v * w ^ i ≤ total ∧ 1 + i ≤ total)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hTc : roundCostBound p w total + 1 ≤ T) (hcapF : T + 1 ≤ capF)
    (hTs : capF + c + n + 1 ≤ Ts) (hTs' : scanRoundBound k A v D nr n p w total T c + 1 ≤ Ts)
    (hcapFs : Ts + 1 ≤ capFs) :
    ClockJoin.ReadyRun (scanLoop k A u v D)
      (1 + 1 + (nr * (scanRoundBound k A v D nr n p w total T c + 1 + (2 * Ts + 4 + 1 + 0) + 2) + nr + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch (scanScratch D) Ts (scanQ k A u v D A0 B0 E0 n p w total capT T capF c 0))
        Ts capFs) (fun _ => CompareMachine.word nr))
      (Fin.addCases (roundTapes (padScratch (scanScratch D) Ts (scanQ k A u v D A0 B0 E0 n p w total capT T capF c nr))
        Ts capFs) (fun _ => CompareMachine.word nr)) := by
  set cw := scanRoundBound k A v D nr n p w total T c with hcw
  set Q := scanQ k A u v D A0 B0 E0 n p w total capT T capF c with hQ
  -- the stale ports stay within `total`
  have hst : ∀ i, i ≤ nr → (scanStA k A u v D A0 n p w total c i).length ≤ total ∧
      (scanStB v B0 w total c i).length ≤ total ∧ (scanStE k A u v D E0 n p w total c i).length ≤ total := by
    intro i hi
    cases i with
    | zero => exact ⟨hA0, hB0, hE0⟩
    | succ i =>
      have hSi := scanSeq_le (fun a => scanFlag k A u v D a n p w c) i
      have hv := hvals (scanS k A u v D n p w c i + 1) (by unfold scanS; omega) c le_rfl
      have ht := roundCount_le (candA0 k A u v (scanS k A u v D n p w c i + 1)) (candB0 v) 1 p w c
      refine ⟨?_, ?_, ?_⟩
      · simp only [scanStA]; rw [pad_length_total _ _ hv.1]
      · simp only [scanStB]; rw [pad_length_total _ _ hv.2.1]
      · simp only [scanStE]; rw [pad_length_total _ _ (by unfold candT; omega)]
  -- each round
  have H : ∀ i, i < nr → ∃ out : Fin (scanTapes D) → List Bool,
      ClockJoin.ReadyRun (scanWorker k A u v D) cw (Q i) out ∧
      out (spos D 0) = ZeroPadding.pad total (List.replicate (scanS k A u v D n p w c (i + 1)) true) ∧
      out (spos D 1) = List.replicate n true ∧
      (∀ j, out (sinner D j) = innerTapes (scanStA k A u v D A0 n p w total c (i + 1))
        (scanStB v B0 w total c (i + 1)) (scanStE k A u v D E0 n p w total c (i + 1)) p w total capT T capF c j) := by
    intro i hi
    have hSi := scanSeq_le (fun a => scanFlag k A u v D a n p w c) i
    obtain ⟨hsa, hsb, hse⟩ := hst i hi.le
    obtain ⟨cost, out, hcost, hr, h0, h1, hin⟩ := scanWorker_run k A u v D (scanS k A u v D n p w c i) n
      (scanStA k A u v D A0 n p w total c i) (scanStB v B0 w total c i) (scanStE k A u v D E0 n p w total c i)
      p w total capT T capF c hD hcap (by unfold scanS; omega) hsa hsb hse
      (hvals (scanS k A u v D n p w c i + 1) (by unfold scanS; omega)) hT hTc hcapF
    have hmono := scanRoundBound_mono k A v D (scanS k A u v D n p w c i) nr n p w total T c (by unfold scanS; omega)
    exact ⟨out, ClockJoin.enlarge _ _ _ _ _ hr (hcost.trans hmono), h0, h1, hin⟩
  choose! Q' hQ' using H
  have hlen : ∀ i, i < nr → ∀ j, (Q' i (scanScratch D j)).length ≤ Ts := by
    intro i hi j
    have hSi := scanSeq_le (fun a => scanFlag k A u v D a n p w c) i
    obtain ⟨hsa, hsb, hse⟩ := hst i hi.le
    have hl := ready_lengths (hQ' i hi).1 (capF + c + n + 1) (fun pos =>
      scanInput_length D _ n _ _ _ p w total capT T capF c (by unfold scanS; omega) hsa hsb hse hcap hT hcapF pos)
    have := hl (scanScratch D j)
    omega
  refine uniformFold_ready (scanWorker k A u v D) (scanScratch D) (scanScratch_inj D) (idleMachine (scanTapes D + 2))
    Ts capFs cw 0 nr hcapFs Q Q' (fun i hi => (hQ' i hi).1) hlen (fun i hi => ?_)
  have e : blankScratch (scanScratch D) (Q' i) = Q (i + 1) := by
    funext pos
    obtain ⟨_, h0, h1, hin⟩ := hQ' i hi
    unfold blankScratch
    by_cases hp : 35 ≤ pos.val
    · rw [if_pos ⟨⟨pos.val - 35, by have := pos.isLt; unfold scanTapes candTapes at this; omega⟩,
        Fin.ext (by simp [scanScratch]; omega)⟩]
      rw [hQ]; unfold scanQ; rw [scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp]
    · rw [if_neg (by rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp [scanScratch] at this; omega)]
      by_cases hz : pos.val = 0
      · rw [show pos = spos D 0 from Fin.ext hz, h0, hQ]; unfold scanQ
        simp [scanInput, spos]
      · by_cases ho : pos.val = 1
        · rw [show pos = spos D 1 from Fin.ext ho, h1, hQ]; unfold scanQ
          simp [scanInput, spos]
        · rw [show pos = sinner D ⟨pos.val - 2, by omega⟩ from Fin.ext (by simp [sinner]; omega), hin, hQ]
          unfold scanQ
          simp only [scanInput, sinner, Fin.val_mk]
          rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
          congr 1; apply Fin.ext; simp
  rw [e]
  exact idle_ready _ _

end Loop

end NearCubicWires.WireExponent3_5.Transfer
