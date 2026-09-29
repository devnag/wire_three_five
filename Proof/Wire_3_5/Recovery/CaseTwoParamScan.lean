import Proof.Wire_3_5.Recovery.CertPrefix

/-! # The Case-2 parameters of the selected slice: the index and the XOR schedule (P3:3738-3741, 3818-3822; D1.6 A3a)

Realizes, for the hybrid Case-2 machine, the first half of "put `m_a = t(q(N_a))q_0(N_a)`. Choose the largest `a` such
that `m_a ≤ n/2`" (P3:3738-3740) together with "Choose the least `t` with `e_t ≤ L^{−τ}`" (P3:3818-3822) at that `a`:
from the framed input `x` (`|x| = n`) the machine recomputes the scan index `S` exactly as the program's prefix does
(the preparation and the scan loop), then runs the candidate test at `a = S` itself (not `S + 1`), whose schedule
loop leaves `t(q(2^S))` on its counter. The Case-2 fold needs these as unary words: the copy count `t + 1` and, through
`S`, the padded width `q(2^S)`.

Paper quantities of the main types: **`paramScan_run`** (at the scan's state `S`: `1^S` on the candidate tape and the
schedule counter `candT … S … c` in the inner block) and **`paramCore_run`** (from `frame x`: `1^n`, `1^S` with
`S = prefixS … n` (M21: `= a(n)` past `n₀`), and `candT … S … n`, which is `t(L(q(2^S)))` once `t ≤ n + 1`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamScan
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep
open NearCubicWires.WireExponent3_5.Transfer.CertPrefix
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Scan
variable (k A u v D : ℕ)

/-- **The parameter scan** on the scan's round tapes: the template of `S`, `1^S` onto the candidate tape (base
`UWalkUnary` without the successor), and the candidate test at `a = S`. -/
noncomputable def paramScan :=
  Composition.machine (RecoveryFocus.machine (slotsW1 D)
    (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
  (Composition.machine (RecoveryFocus.machine (slotsW2 D) (UWalkUnary.machine false false))
    (RecoveryFocus.machine (candFocus D) (candMachine k A u v D)))

/-- The parameter scan's cost bound. -/
def paramScanBound (S n p w total T c : ℕ) : ℕ :=
  (2 * S + 8) + 1 + ((2 * S + 6) + 1 + candBound k A v D S n p w total T c)

/-- **The parameter scan is ready**: at the scan's state `S` it leaves `1^S` on the candidate tape, keeps the port `S`
and `1^n`, and its schedule loop leaves `candT … S … c` on the inner counter. -/
theorem paramScan_run (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c : ℕ) (hD : 1 ≤ D)
    (hcap : total + 1 ≤ capT) (hA : Ap.length ≤ total) (hB : Bp.length ≤ total) (hE : Ep.length ≤ total)
    (hbound : ∀ i, i ≤ c → candA0 k A u v S * p ^ i ≤ total ∧ candB0 v * w ^ i ≤ total ∧ 1 + i ≤ total)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hTc : roundCostBound p w total + 1 ≤ T) (hcapF : T + 1 ≤ capF) :
    ∃ (cost : ℕ) (out : Fin (scanTapes D) → List Bool), cost ≤ paramScanBound k A v D S n p w total T c ∧
      ClockJoin.ReadyRun (paramScan k A u v D) cost (scanInput D S n Ap Bp Ep p w total capT T capF c) out ∧
      out (spos D 0) = ZeroPadding.pad total (List.replicate S true) ∧
      out (spos D 35) = List.replicate S true ∧
      out (spos D 1) = List.replicate n true ∧
      (∀ j, out (sinner D j) =
        innerTapes (ZeroPadding.pad total (List.replicate (candA0 k A u v S * p ^ c) true))
          (ZeroPadding.pad total (List.replicate (candB0 v * w ^ c) true))
          (ZeroPadding.pad total (List.replicate (candT k A u v S p w c) true)) p w total capT T capF c j) := by
  set x := scanInput D S n Ap Bp Ep p w total capT T capF c with hx
  have hct := candTapes_ge D
  -- the template of `S`
  have hw1 := ready_pad _ _ _ _ ![total, 0, 0]
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready false S)
  have g1 := hw1.focus (slotsW1 D) (by scan_inj_tac) x (by
    intro j; fin_cases j
    · show x (spos D 0) = _
      simp [hx, scanInput, spos, RepairSource.ProjectionNormalization.DimensionTemplate.input]
    · show x (xpos D 1) = _
      rw [hx, scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.input, ZeroPadding.pad]
    · show x (xpos D 2) = _
      rw [hx, scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.input, ZeroPadding.pad])
  set a1 := install (slotsW1 D) x (fun i => ZeroPadding.pad (![total, 0, 0] i)
    (RepairSource.ProjectionNormalization.DimensionTemplate.output false S i)) with ha1
  have a1_off : ∀ i : Fin (scanTapes D), i.val ≠ 0 → i.val ≠ candTapes D + 1 → i.val ≠ candTapes D + 2 →
      a1 i = x i := by
    intro i h0 h1 h2
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW1, spos, xpos]; omega))]
  -- `1^S` onto the candidate tape
  have g2 := (UWalkUnary.ready false false (S + 2) S).focus (slotsW2 D) (by scan_inj_tac) a1 (by
    intro j; fin_cases j
    · show a1 (xpos D 1) = _
      rw [ha1, show xpos D 1 = slotsW1 D 1 from rfl, install_slot _ (by scan_inj_tac)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input, ZeroPadding.pad,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a1 (spos D 35) = _
      rw [a1_off _ (by spos_tac) (by spos_tac) (by spos_tac), hx,
        scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      rfl
    · show a1 (xpos D 3) = _
      rw [a1_off _ (by spos_tac) (by spos_tac) (by spos_tac), hx,
        scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by spos_tac)]
      rfl)
  set a2 := install (slotsW2 D) a1 (UWalkUnary.result false false (S + 2) S) with ha2
  have a2_35 : a2 (spos D 35) = List.replicate S true := by
    rw [ha2, show spos D 35 = slotsW2 D 1 from rfl, install_slot _ (by scan_inj_tac)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  have a2_off : ∀ i : Fin (scanTapes D), i.val ≠ 0 → i.val ≠ 35 → i.val ≤ candTapes D ∨ candTapes D + 4 ≤ i.val →
      a2 i = x i := by
    intro i h0 h35 hr
    rw [ha2, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW2, spos, xpos]; omega)),
      a1_off _ h0 (by omega) (by omega)]
  have a2_0 : a2 (spos D 0) = ZeroPadding.pad total (List.replicate S true) := by
    rw [ha2, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (apply fin_ne; simp [slotsW2, spos, xpos])),
      ha1, show spos D 0 = slotsW1 D 0 from rfl, install_slot _ (by scan_inj_tac)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output]
  -- the candidate test at `S`
  obtain ⟨c3, o3, hc3, r3, o3a, o3n, o3in, _⟩ :=
    candMachine_run k A u v D S n Ap Bp Ep p w total capT T capF c hD hcap hA hB hE hbound hT hTc hcapF
  have g3 := r3.focus (candFocus D) (candFocus_inj D) a2 (by
    intro i
    have hi := i.isLt
    by_cases h0 : i.val = 0
    · rw [show candFocus D i = spos D 35 from Fin.ext (by simp [candFocus, spos, h0]), a2_35]
      simp [candInput, h0]
    · by_cases h35 : i.val < 35
      · have hv : (candFocus D i).val = i.val := by simp [candFocus, h0, h35]
        rw [a2_off _ (by omega) (by omega) (by omega), hx]
        simp only [scanInput, candInput, hv, if_neg h0]
      · have hv : (candFocus D i).val = i.val + 1 := by simp [candFocus, h0, h35]
        rw [a2_off _ (by omega) (by omega) (by omega), hx,
          scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
          candInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)])
  set a3 := install (candFocus D) a2 o3 with ha3
  have a3_away : ∀ i : Fin (scanTapes D), (∀ j : Fin (candTapes D), (candFocus D j).val ≠ i.val) → a3 i = a2 i := by
    intro i h
    rw [ha3, install_other _ _ _ _ (fun j => fin_ne (h j))]
  refine ⟨_, _, le_refl _, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.enlarge _ _ _ _ _ g3 hc3)), ?_, ?_, ?_, ?_⟩
  · rw [a3_away _ (by intro j; simp only [candFocus, spos, Fin.val_mk]; split_ifs <;> omega), a2_0]
  · rw [show spos D 35 = candFocus D (cpos D 0) from Fin.ext (by simp [spos, candFocus, cpos]), ha3,
      install_slot _ (candFocus_inj D), o3a]
  · rw [show spos D 1 = candFocus D (cpos D 1) from Fin.ext (by simp [spos, candFocus, cpos]), ha3,
      install_slot _ (candFocus_inj D), o3n]
  · intro j
    have hj := j.isLt
    rw [show sinner D j = candFocus D (candI D j) from Fin.ext (by
      simp only [sinner, candFocus, candI, Fin.val_mk]; split_ifs <;> omega), ha3, install_slot _ (candFocus_inj D),
      o3in]

end Scan

section Core
variable (k A u v D : ℕ)

/-- The parameter scan's slots in the prefix layout: the scan block's first `scanTapes D` tapes. -/
def slP (i : Fin (scanTapes D)) : Fin (prefixTapes D) := slS D (Fin.castAdd (2 + 1) i)

theorem slP_inj : Function.Injective (slP D) := fun _ _ h => Fin.castAdd_injective _ _ (slS_inj D h)
theorem slP_val (i : Fin (scanTapes D)) : (slP D i).val = 1 + i.val := rfl

/-- **The parameter core**: the preparation, the scan loop, then the parameter scan at the scan's index. -/
noncomputable def paramCore (e1 e2 e3 : ℕ) :=
  Composition.machine (prepMachine D ((v - u) ^ 16) (v ^ 16) e1 e2 e3)
  (Composition.machine (RecoveryFocus.machine (slS D) (scanLoop k A u v D))
    (RecoveryFocus.machine (slP D) (paramScan k A u v D)))

/-- The stale inner ports stay within the value capacity through the scan. -/
theorem scanSt_length (n nr : ℕ) (p w total c : ℕ)
    (hvals : ∀ a, a ≤ nr → ∀ i, i ≤ c →
      candA0 k A u v a * p ^ i ≤ total ∧ candB0 v * w ^ i ≤ total ∧ 1 + i ≤ total) :
    ∀ i, i ≤ nr → (scanStA k A u v D [] n p w total c i).length ≤ total ∧
      (scanStB v [] w total c i).length ≤ total ∧ (scanStE k A u v D [] n p w total c i).length ≤ total := by
  intro i hi
  cases i with
  | zero => simp [scanStA, scanStB, scanStE]
  | succ i =>
    have hSi := scanSeq_le (fun a => scanFlag k A u v D a n p w c) i
    have hv := hvals (scanS k A u v D n p w c i + 1) (by unfold scanS; omega) c le_rfl
    have ht := roundCount_le (candA0 k A u v (scanS k A u v D n p w c i + 1)) (candB0 v) 1 p w c
    refine ⟨?_, ?_, ?_⟩
    · simp only [scanStA]; rw [pad_length_total _ _ hv.1]
    · simp only [scanStB]; rw [pad_length_total _ _ hv.2.1]
    · simp only [scanStE]; rw [pad_length_total _ _ (by unfold candT; omega)]

/-- The parameter core's cost. -/
def paramCost (e1 e2 e3 : ℕ) (bits : List Bool) : ℕ :=
  prepCostA e1 e2 e3 bits + 1 + prepCostB ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) (pcap e2 bits.length)
    (pcap e3 bits.length) + 1 +
  (scanCost k A v D bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) (pcap e2 bits.length)
    (pcap e3 bits.length) + 1 +
    paramScanBound k A v D (prefixS k A u v D bits.length) bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length)
      (pcap e2 bits.length) bits.length)

/-- **The parameter core is ready**: from `frame x` it leaves `frame x`, `1^n`, the index `1^S` (`S = prefixS … n`,
`false`-padded to the scan capacity) and the schedule counter `candT … S … n` (`false`-padded to the value capacity). -/
theorem paramCore_run (e1 e2 e3 : ℕ) (hD : 1 ≤ D) (bits : List Bool)
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
      ClockJoin.ReadyRun (paramCore k A u v D e1 e2 e3) (paramCost k A u v D e1 e2 e3 bits) (prefixInput D bits) out ∧
      out (ppos D 0 (by unfold prefixTapes; omega)) = frame bits ∧
      out (ppos D 2 (by unfold prefixTapes; omega)) = List.replicate bits.length true ∧
      out (ppos D 36 (by have := scanTapes_eq D; unfold prefixTapes; omega)) =
        ZeroPadding.pad (pcap e3 bits.length) (List.replicate (prefixS k A u v D bits.length) true) ∧
      out (ppos D 5 (by unfold prefixTapes; omega)) =
        ZeroPadding.pad (pcap e1 bits.length) (List.replicate
          (candT k A u v (prefixS k A u v D bits.length) ((v - u) ^ 16) (v ^ 16) bits.length) true) := by
  set n := bits.length with hn'
  set C1 := pcap e1 n with hC1
  set C2 := pcap e2 n with hC2
  set C3 := pcap e3 n with hC3
  have hST := scanTapes_eq D
  obtain ⟨a, ha, hB⟩ := prep_run D ((v - u) ^ 16) (v ^ 16) e1 e2 e3 bits
  have hblock := block_eq D bits ((v - u) ^ 16) (v ^ 16) C1 C2 C3 a hB
  obtain ⟨az, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB
  -- the scan
  have hl := scanLoop_ready k A u v D n n [] [] [] ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n C3 (C3 + 1)
    hD le_rfl hn (by simp) (by simp) (by simp) hvals hT hTc le_rfl hTs hTs' le_rfl
  have g2 := hl.focus (slS D) (slS_inj D) a (fun i => (hblock i).trans rfl)
  set a2 := install (slS D) a (Fin.addCases (roundTapes (padScratch (scanScratch D) C3
    (scanQ k A u v D [] [] [] n ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n n)) C3 (C3 + 1))
    (fun _ => CompareMachine.word n)) with ha2
  have a2P : ∀ i : Fin (scanTapes D), a2 (slP D i) = ZeroPadding.pad (scratchCap (scanScratch D) C3 i)
      (scanQ k A u v D [] [] [] n ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n n i) := by
    intro i
    rw [slP, ha2, install_slot _ (slS_inj D), loopIn_val, dif_pos (by simp only [Fin.val_castAdd]; exact i.isLt)]
    rfl
  have a2off : ∀ q : Fin (prefixTapes D), (q.val = 0 ∨ scanTapes D + 4 ≤ q.val) → a2 q = a q := by
    intro q hq
    rw [ha2, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [slS, Fin.val_mk]; omega)]
  -- the parameter scan at the scan's index
  set S := prefixS k A u v D n with hS
  have hSn : S ≤ n := prefixS_le k A u v D n
  have hst := scanSt_length k A u v D n n ((v - u) ^ 16) (v ^ 16) C1 n hvals n le_rfl
  obtain ⟨c3, o3, hc3, r3, o30, o335, o31, o3in⟩ := paramScan_run k A u v D S n
    (scanStA k A u v D [] n ((v - u) ^ 16) (v ^ 16) C1 n n) (scanStB v [] (v ^ 16) C1 n n)
    (scanStE k A u v D [] n ((v - u) ^ 16) (v ^ 16) C1 n n) ((v - u) ^ 16) (v ^ 16) C1 (C1 + 1) C2 (C2 + 1) n
    hD le_rfl hst.1 hst.2.1 hst.2.2 (fun i hi => hvals S hSn i hi) hT hTc le_rfl
  have hp := ready_pad _ _ _ _ (scratchCap (scanScratch D) C3) r3
  have g3 := hp.focus (slP D) (slP_inj D) a2 (fun i => (a2P i).trans rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ ha (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.enlarge _ _ _ _ _ g3 hc3)), ?_, ?_, ?_, ?_⟩
  · rw [install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [slP_val, ppos, Fin.val_mk]; omega),
      a2off _ (Or.inl (by simp [ppos])), az]
  · rw [show ppos D 2 _ = slP D (spos D 1) from Fin.ext (by simp [slP_val, ppos, spos]),
      install_slot _ (slP_inj D)]
    show ZeroPadding.pad (scratchCap (scanScratch D) C3 (spos D 1)) (o3 (spos D 1)) = _
    rw [scratchCap_scan, if_neg (by simp [spos]), ZeroPadding.pad_zero, o31]
  · rw [show ppos D 36 _ = slP D (spos D 35) from Fin.ext (by simp [slP_val, ppos, spos]),
      install_slot _ (slP_inj D)]
    show ZeroPadding.pad (scratchCap (scanScratch D) C3 (spos D 35)) (o3 (spos D 35)) = _
    rw [scratchCap_scan, if_pos (by simp [spos]), o335]
  · rw [show ppos D 5 _ = slP D (sinner D 2) from Fin.ext (by simp [slP_val, ppos, sinner]),
      install_slot _ (slP_inj D)]
    show ZeroPadding.pad (scratchCap (scanScratch D) C3 (sinner D 2)) (o3 (sinner D 2)) = _
    rw [scratchCap_scan, if_neg (by simp [sinner]), ZeroPadding.pad_zero, o3in]
    rfl

end Core

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamScan
