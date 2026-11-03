import Proof.Packets.PacketsMetaStageKinds

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge
open NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

namespace Stage
open Lev Setup Tail Prog Spec Bounds StageRun

/-! ## Size facts -/

theorem fields_le_input (a : DecompositionAlgorithm) (r : Request) :
    (Request.nativeWord r).length + (Request.topWord a r).length ≤ (r.input a).length := by
  unfold Request.input
  simp only [List.length_append, RepairOrdinary.frame_length]
  omega

theorem reqW_le (a : DecompositionAlgorithm) (r : Request) : reqW a r + 1 ≤ 32 * r.smallSize a := by
  have h1 := fields_le_input a r
  have h2 := NearCubicWires.PacketsGlue.RequestMeta.input_le_small a r
  unfold reqW
  omega

theorem walk_le_small (a : DecompositionAlgorithm) (r : Request) :
    2 ^ canonicalWalkLength (r.denominator a) ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x5 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem max_sq_le (x y : ℕ) : max x y ^ 2 ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

theorem cut_le_small (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target ≤ 40000 * (Request.smallSize a (.thr r four L target)) ^ 3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hF, _, _⟩ := thr_width a r four L target
  have hS := walk_le_small a (.thr r four L target)
  have hW := reqW_le a (.thr r four L target)
  rw [← thrW_eq a r four L target] at hW
  set S := Request.smallSize a (.thr r four L target) with hSdef
  set W := thrW a r four L target with hWdef
  -- the exponent
  have he : Nat.clog 2 (Fv (dsOf a r) + 1) + 1 ≤ 32 * S := by
    have h1 : Fv (dsOf a r) + 1 ≤ 2 ^ W := by omega
    have h2 : Nat.clog 2 (Fv (dsOf a r) + 1) ≤ W := Nat.clog_le_of_le_pow h1
    omega
  -- the denominator
  have hden : Request.denominator a (.thr r four L target) =
      modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) *
        (2 * Cv (dsOf a r) * (target + 1) + 1) := by
    rw [Cv_eq a r four]
    rfl
  set den := Request.denominator a (.thr r four L target) with hdendef
  have hd1 : 2 * Cv (dsOf a r) * (target + 1) + 1 ≤ den := by
    rw [hden]
    have : 1 ≤ modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) := by
      unfold modulusDigitCount; omega
    exact Nat.le_mul_of_pos_left _ this
  have hc := Nat.le_pow_clog (by norm_num : 1 < 2) (den + 1)
  have hsq : (2 * Cv (dsOf a r) * (target + 1) + 1) ^ 2 ≤ S := by
    have h1 : (2 * Cv (dsOf a r) * (target + 1) + 1) ^ 2 ≤ (2 ^ Nat.clog 2 (den + 1)) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h2 : (2 ^ Nat.clog 2 (den + 1)) ^ 2 ≤ 2 ^ canonicalWalkLength den := by
      unfold canonicalWalkLength
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold cutOf canonicalPrimeCutoff canonicalPrimeScale
  have hm := max_sq_le 24 (6 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1))
  have e1 : (6 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1)) ^ 2 =
      36 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) ^ 2 * (2 * Cv (dsOf a r) * (target + 1) + 1) ^ 2 := by ring
  have h3 : (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) ^ 2 ≤ (32 * S) ^ 2 := Nat.pow_le_pow_left he 2
  have h4 : 36 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) ^ 2 * (2 * Cv (dsOf a r) * (target + 1) + 1) ^ 2 ≤
      36 * (32 * S) ^ 2 * S := Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) hsq
  have e2 : 36 * (32 * S) ^ 2 * S = 36864 * S ^ 3 := by ring
  have hS1 : 1 ≤ S := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a _
  have hS3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS1
  omega

/-! ## Step-count bounds -/

theorem tailCost_le (W F C T : ℕ) :
    Tail.tailCost W F C T ≤ 300 * (W + 1) ^ 2 +
      (Nat.clog 2 (F + 1) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2) +
      (cutOf F C T + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2) := by
  unfold Tail.tailCost
  have e : 300 * (W + 1) ^ 2 = 300 * (W * W) + 600 * W + 300 := by ring
  have e2 : 13 * W * W = 13 * (W * W) := by ring
  omega

theorem thrPC_le (W : ℕ) (nw : List Bool) (ds : List CD) (nT : ℕ) (hW1 : 1 ≤ W)
    (hW : W = 32 * (nw.length + (twOf ds).length)) (hpay : ∀ c, (pay (dOf ds c)).length ≤ W) :
    thrPC W nw (twOf ds) ds nT ≤ 2400 * (W + 1) ^ 6 + nT := by
  have hL := loopsCost_le W hW1 (dOf ds) hpay
  have hp := pay_pad_len
  have h6 : W + 1 ≤ (W + 1) ^ 6 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold thrPC thrCost hdrCost extCost
  omega

theorem pow6 (X S : ℕ) (h : X ≤ 32 * S) : X ^ 6 ≤ 2 ^ 30 * S ^ 6 := by
  have h1 : X ^ 6 ≤ (32 * S) ^ 6 := Nat.pow_le_pow_left h 6
  have e : (32 * S) ^ 6 = 2 ^ 30 * S ^ 6 := by ring
  omega

/-- **The cutoff program's step count.** -/
def cutPC (a : DecompositionAlgorithm) : Request → ℕ := pc a (fun W F C T => Tail.tailCost W F C T) tailM

/-- **The `|Sel|` program's step count.** -/
def selPC (a : DecompositionAlgorithm) : Request → ℕ := pc a (fun W _ C _ => selTailCost W C) selTailM

theorem small_pc (a : DecompositionAlgorithm) (r : Request) (x : ℕ) (hx : x ≤ 100 * (reqW a r + 1)) :
    x ≤ 2 ^ 42 * (r.smallSize a) ^ 6 := by
  have hW := reqW_le a r
  have hS1 := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a r
  have h1 : r.smallSize a ≤ (r.smallSize a) ^ 6 := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ (r.smallSize a) ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  omega

theorem thr_pay (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (c : Fin 4) :
    (pay (dOf (dsOf a r) c)).length ≤ thrW a r four L target := by
  have hN := nw_ge r four L target
  unfold thrW
  by_cases hj : c.val < (dsOf a r).length
  · rw [dOf_lt _ c hj]
    have := pay_le_tw (dsOf a r) c.val hj
    omega
  · rw [dOf_ge _ c (by omega), pay_pad_len]
    omega

theorem cutPC_le (a : DecompositionAlgorithm) (r : Request) : cutPC a r ≤ 2 ^ 42 * (r.smallSize a) ^ 6 := by
  cases r with
  | terminal =>
    apply small_pc
    show hdrCost _ _ _ + 1 + _ ≤ _
    unfold hdrCost reqW
    omega
  | sym r four L target =>
    apply small_pc
    show hdrCost _ _ _ + 1 + _ ≤ _
    unfold hdrCost reqW
    omega
  | thr r four L target =>
    obtain ⟨h2, _, _, _, _, _, _, _, _, hF, _, _⟩ := thr_width a r four L target
    have hW := reqW_le a (.thr r four L target)
    rw [← thrW_eq a r four L target] at hW
    have hcut := cut_le_small a r four L target
    have hS1 := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a (.thr r four L target)
    show thrPC _ _ _ _ (Tail.tailCost _ _ _ _) ≤ _
    have hP := thrPC_le (thrW a r four L target) (Request.nativeWord (.thr r four L target)) (dsOf a r)
      (Tail.tailCost (thrW a r four L target) (Fv (dsOf a r)) (Cv (dsOf a r)) target) (by omega) rfl
      (thr_pay a r four L target)
    have hT := tailCost_le (thrW a r four L target) (Fv (dsOf a r)) (Cv (dsOf a r)) target
    set S := Request.smallSize a (.thr r four L target) with hSdef
    set W := thrW a r four L target with hWdef
    have hk : Nat.clog 2 (Fv (dsOf a r) + 1) ≤ W := Nat.clog_le_of_le_pow (by omega)
    have hX6 := pow6 (W + 1) S (by omega)
    have hX2 : (W + 1) ^ 2 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkX : (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2) ≤
        6 * (W + 1) ^ 2 + 6 * (W + 1) := by
      have := Nat.mul_le_mul_right ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2) (show
        Nat.clog 2 (Fv (dsOf a r) + 1) + 1 ≤ W + 1 by omega)
      have e : (W + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + (2 * W + 3)) + 2) = 6 * (W + 1) ^ 2 + 6 * (W + 1) := by
        ring
      omega
    have hX1 : W + 1 ≤ (W + 1) ^ 6 := by
      calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
        _ ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hcX : (cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2) ≤
        (40000 * S ^ 3 + 1) * (320 * S) := by
      apply Nat.mul_le_mul (by omega)
      omega
    have e3 : (40000 * S ^ 3 + 1) * (320 * S) = 12800000 * (S ^ 3 * S) + 320 * S := by ring
    have e4 : S ^ 3 * S = S ^ 4 := by ring
    have h46 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have h16 : S ≤ S ^ 6 := by
      calc S = S ^ 1 := (pow_one _).symm
        _ ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    omega

theorem Cv_le_poly (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    Cv (dsOf a r) ≤ ((twOf (dsOf a r)).length + 1) ^ 4 := by
  have hl : ∀ i : Fin 4, (tab (dOf (dsOf a r) i)).length ≤ (twOf (dsOf a r)).length + 1 := by
    intro i
    rw [tab_eq a r four, tw_eq a r four L target]
    exact T_length_le a r four L target i.val
  unfold Cv
  have e : ((twOf (dsOf a r)).length + 1) ^ 4 = ((twOf (dsOf a r)).length + 1) * (((twOf (dsOf a r)).length + 1) *
      (((twOf (dsOf a r)).length + 1) * (((twOf (dsOf a r)).length + 1) * 1))) := by ring
  rw [e]
  exact Nat.mul_le_mul (hl 0) (Nat.mul_le_mul (hl 1) (Nat.mul_le_mul (hl 2) (Nat.mul_le_mul (hl 3) (le_refl 1))))

theorem selPC_le (a : DecompositionAlgorithm) (r : Request) : selPC a r ≤ 2 ^ 42 * (r.smallSize a) ^ 6 := by
  cases r with
  | terminal =>
    apply small_pc
    show hdrCost _ _ _ + 1 + _ ≤ _
    unfold hdrCost reqW
    omega
  | sym r four L target =>
    apply small_pc
    show hdrCost _ _ _ + 1 + _ ≤ _
    unfold hdrCost reqW
    omega
  | thr r four L target =>
    obtain ⟨h2, _, _, _, _, _, _, _, _, _, _, _⟩ := thr_width a r four L target
    have hW := reqW_le a (.thr r four L target)
    rw [← thrW_eq a r four L target] at hW
    have hS1 := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a (.thr r four L target)
    have hC := Cv_le_poly a r four L target
    show thrPC _ _ _ _ (selTailCost _ _) ≤ _
    have hP := thrPC_le (thrW a r four L target) (Request.nativeWord (.thr r four L target)) (dsOf a r)
      (selTailCost (thrW a r four L target) (Cv (dsOf a r))) (by omega) rfl (thr_pay a r four L target)
    set S := Request.smallSize a (.thr r four L target) with hSdef
    set W := thrW a r four L target with hWdef
    have hR : (twOf (dsOf a r)).length + 1 ≤ W + 1 := by
      unfold thrW at hWdef
      omega
    have hC4 : Cv (dsOf a r) + 1 ≤ (W + 1) ^ 4 + 1 := by
      have := Nat.pow_le_pow_left hR 4
      omega
    have hX6 := pow6 (W + 1) S (by omega)
    have h45 : (W + 1) ^ 4 * (W + 1) = (W + 1) ^ 5 := by ring
    have h56 : (W + 1) ^ 5 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h16 : W + 1 ≤ (W + 1) ^ 6 := by
      calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
        _ ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hsel : selTailCost W (Cv (dsOf a r)) ≤ 30 * (W + 1) ^ 6 := by
      unfold selTailCost
      have h1 : (Cv (dsOf a r) + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2) ≤
          ((W + 1) ^ 4 + 1) * (10 * (W + 1)) := Nat.mul_le_mul hC4 (by omega)
      have e : ((W + 1) ^ 4 + 1) * (10 * (W + 1)) = 10 * ((W + 1) ^ 4 * (W + 1)) + 10 * (W + 1) := by ring
      omega
    omega

/-! ## The two stages -/

theorem scan_fields (a : DecompositionAlgorithm) (r : Request) :
    NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57
      (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 4))
      (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 0)) =
    NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (Request.topWord a r))
      (RepairOrdinary.frame (Request.nativeWord r)) := rfl

/-- Rewriting a `Step`'s entry bank without abstracting over the machine (whose state count is a large term). -/
theorem step_scan {t s : ℕ} {P : Machine t s} {n m : ℕ} {H H' : Fin t → ℕ} {X Y A' : Fin t → List Bool}
    (h : Step P n H X H' A') (e : X = Y) (hnm : n = m) : Step P m H Y H' A' := by
  subst e hnm
  exact h

theorem cut_step0 (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog tailM) (cutPC a r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (Request.topWord a r))
          (RepairOrdinary.frame (Request.nativeWord r))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (NearCubicWires.PacketsGlue.RequestMeta.cutoffOf a r) true := by
  cases r with
  | terminal => exact step_of_lruns (prog tailM) _ _ _ _ 0 (term_run a tailM)
  | sym r four L target => exact step_of_lruns (prog tailM) _ _ _ _ 0 (sym_run a tailM r four L target)
  | thr r four L target =>
    obtain ⟨H1, A1, hs, h1⟩ := step_of_lruns _ _ _ _ _ _ (thr_cut a r four L target)
    refine ⟨H1, A1, step_scan hs (by rw [tw_eq a r four L target]) rfl, ?_⟩
    rw [h1, cut_eq a r four target]
    rfl

theorem sel_step0 (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog selTailM) (selPC a r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame (Request.topWord a r))
          (RepairOrdinary.frame (Request.nativeWord r))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (RowsInit.Count.thrSelOf a r) true := by
  cases r with
  | terminal => exact step_of_lruns (prog selTailM) _ _ _ _ 0 (term_run a selTailM)
  | sym r four L target => exact step_of_lruns (prog selTailM) _ _ _ _ 0 (sym_run a selTailM r four L target)
  | thr r four L target =>
    obtain ⟨H1, A1, hs, h1⟩ := step_of_lruns _ _ _ _ _ _ (thr_sel a r four L target)
    refine ⟨H1, A1, step_scan hs (by rw [tw_eq a r four L target]) rfl, ?_⟩
    rw [h1, Cv_eq a r four, RowsInit.Count.thrSelOf_card a r four L target]

theorem cut_step (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog tailM) (cutPC a r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 4))
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 0))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (NearCubicWires.PacketsGlue.RequestMeta.cutoffOf a r) true := by
  obtain ⟨H1, A1, hs, h1⟩ := cut_step0 a r
  exact ⟨H1, A1, step_scan hs (scan_fields a r).symm rfl, h1⟩

theorem sel_step (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step (prog selTailM) (selPC a r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 4))
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 0))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (RowsInit.Count.thrSelOf a r) true := by
  obtain ⟨H1, A1, hs, h1⟩ := sel_step0 a r
  exact ⟨H1, A1, step_scan hs (scan_fields a r).symm rfl, h1⟩

theorem stage_cost_le (a : DecompositionAlgorithm) (r : Request) (n : ℕ) (hn : n ≤ 2 ^ 42 * (r.smallSize a) ^ 6) :
    6 * (r.input a).length + 17 + 1 + (2 * n + 2) ≤ 2 ^ 45 * (r.smallSize a) ^ 6 := by
  have hI := NearCubicWires.PacketsGlue.RequestMeta.input_le_small a r
  have hS1 := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a r
  have h16 : r.smallSize a ≤ (r.smallSize a) ^ 6 := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ (r.smallSize a) ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  omega

end Stage

theorem run_gen (a : DecompositionAlgorithm) {s : ℕ} (M : Machine (3 + 57) s) (v pcf : Request → ℕ)
    (h : ∀ r, ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step M (pcf r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 4))
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 0))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (v r) true) (r : Request) :
    ∃ (H' : Fin (2 + (13 + 57 + 1)) → ℕ) (A' : Fin (2 + (13 + 57 + 1)) → List Bool),
      Step (NearCubicWires.PacketsGlue.RequestMeta.fieldMachine2 M 4 0)
        (6 * (r.input a).length + 17 + 1 + (2 * pcf r + 2)) (fun _ => 0)
        (NearCubicWires.PacketFamilyParent.inBank (2 + (13 + 57 + 1)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate (v r) true ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨H1, A1, hs, h1⟩ := h r
  exact NearCubicWires.PacketsGlue.RequestMeta.field_run2 M 4 0 (by decide) a r (v r) (pcf r) H1 A1 hs h1

/-- A stage from a program on PG's two-field bank (`topWord`, `nativeWord`). -/
def mkStage (a : DecompositionAlgorithm) {s : ℕ} (M : Machine (3 + 57) s) (v pcf : Request → ℕ)
    (hc : ∀ r, pcf r ≤ 2 ^ 42 * (r.smallSize a) ^ 6)
    (h : ∀ r, ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step M (pcf r) (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 4))
          (RepairOrdinary.frame (NearCubicWires.PacketsGlue.RequestMeta.fields a r 0))) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate (v r) true) :
    NearCubicWires.PacketsGlue.RequestMeta.UnaryStage a v where
  extra := 13 + 57 + 1
  states := _
  machine := NearCubicWires.PacketsGlue.RequestMeta.fieldMachine2 M 4 0
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * pcf r + 2)
  coefficient := 2 ^ 45
  degree := 6
  cost_le := fun r => Stage.stage_cost_le a r _ (hc r)
  run := run_gen a M v pcf h

/-- **`cutoffStage`**: the THR prime cutoff `primeCutoff a r target` (`0` off THR) in unary, by ONE fixed machine
(PG's `fieldMachine2` on the `topWord`/`nativeWord` fields around `Prog.prog Tail.tailM`). -/
def cutoffStage (a : DecompositionAlgorithm) :
    NearCubicWires.PacketsGlue.RequestMeta.UnaryStage a (NearCubicWires.PacketsGlue.RequestMeta.cutoffOf a) :=
  mkStage a (Prog.prog Tail.tailM) _ (Stage.cutPC a) (Stage.cutPC_le a) (Stage.cut_step a)

/-- **`thrSelStage`**: the THR selection count `card (ThresholdRows.Selection a r)` (`0` off THR) in unary, by ONE
fixed machine (the same program with the `|Sel|` tail). -/
def thrSelStage (a : DecompositionAlgorithm) :
    NearCubicWires.PacketsGlue.RequestMeta.UnaryStage a (RowsInit.Count.thrSelOf a) :=
  mkStage a (Prog.prog Tail.selTailM) _ (Stage.selPC a) (Stage.selPC_le a) (Stage.sel_step a)

end
end NearCubicWires.PacketsMeta

