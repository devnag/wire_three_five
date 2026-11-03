import Proof.Packets.PacketsMetaCutoffStage
import Proof.Packets.PacketsWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta.Seed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## 1. `x ↦ ⌊x/2⌋` (bespoke: skip a cell, copy a cell) -/

namespace Halve

/-- States: 0 skip a cell, 1 copy a cell, 2 halt. Tape 0 the input `1^x`, tape 1 the output. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then
      if b 0 then some ⟨0, fun i => if i.val = 1 then some true else none, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else none

def cfg (x : ℕ) (q : Fin 3) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![List.replicate x true, List.replicate o true]⟩

theorem skip (x i o : ℕ) (hi : i < x) : step machine (cfg x 0 i o) = some (cfg x 1 (i + 1) o) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem copy (x i o : ℕ) (hi : i < x) : step machine (cfg x 1 i o) = some (cfg x 0 (i + 1) (o + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stopA (x o : ℕ) : step machine (cfg x 0 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stopB (x o : ℕ) : step machine (cfg x 1 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem pairs (x j i o : ℕ) (h : i + 2 * j ≤ x) :
    Timed machine (2 * j) (cfg x 0 i o) (cfg x 0 (i + 2 * j) (o + j)) := by
  induction j generalizing i o with
  | zero => exact Timed.refl _ _
  | succ j ih =>
    have e : 2 * (j + 1) = 1 + (1 + 2 * j) := by ring
    have h2 := ih (i + 1 + 1) (o + 1) (by omega)
    have e2 : i + 1 + 1 + 2 * j = i + 2 * (j + 1) := by ring
    have e3 : o + 1 + j = o + (j + 1) := by ring
    rw [e2, e3] at h2
    have h := (Timed.single (p := machine) (by rfl) (skip x i o (by omega))).trans
      ((Timed.single (p := machine) (by rfl) (copy x (i + 1) o (by omega))).trans h2)
    rw [← e] at h
    exact h

theorem timed (x : ℕ) : Timed machine (x + 1) (cfg x 0 0 0) (cfg x 2 x (x / 2)) := by
  have hp := pairs x (x / 2) 0 0 (by omega)
  rw [Nat.zero_add, Nat.zero_add] at hp
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e1 : 2 * (x / 2) = x := by omega
    rw [e1] at hp
    exact hp.trans (Timed.single (by rfl) (stopA x (x / 2)))
  · have e1 : 2 * (x / 2) + 1 = x := by omega
    have h1 := Timed.single (p := machine) (by rfl) (skip x (2 * (x / 2)) (x / 2) (by omega))
    rw [e1] at h1
    have h := (hp.trans h1).trans (Timed.single (by rfl) (stopB x (x / 2)))
    have e : 2 * (x / 2) + 1 + 1 = x + 1 := by omega
    rw [e] at h
    exact h

theorem run (x : ℕ) :
    Step machine (x + 1) (fun _ => 0) ![List.replicate x true, []] ![x, x / 2]
      ![List.replicate x true, List.replicate (x / 2) true] := by
  obtain ⟨r, hr, hf, _⟩ := (timed x).run (by rfl)
  have hc : cfg x 0 0 0 = (⟨machine.start, fun _ => 0, ![List.replicate x true, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end Halve

/-- **`x ↦ ⌊x/2⌋`** as PG's `UnaryMap` (masked reset, log entering empty). -/
def halfMap : UnaryMap (fun x => x / 2) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine Halve.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := fun x => by
    obtain ⟨k, hm⟩ := step_mask0 (Halve.run x) (fun _ => true) (fun _ _ => rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, rfl, rfl⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]

theorem half_cost (x : ℕ) : halfMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ _
  rw [pow_one]; omega

/-! ## 2. The value: `seedCount = 2^(⌊t/2⌋·320 + ⌊3·rank/2⌋·2)` (`paper.tex:2597`) -/

/-- The seed exponent `160(t-1) + 2 r_0`, in the form the machine computes it. -/
def seedExp (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  walkLength a r / 2 * 320 + rank a r * 3 / 2 * 2

theorem seed_eq (a : DecompositionAlgorithm) (r : Request) : seedCount a r = 2 ^ seedExp a r := by
  have hw : walkLength a r / 2 = Nat.clog 2 (Request.denominator a r + 1) := by
    unfold walkLength canonicalWalkLength
    omega
  have hs : rank a r * 3 / 2 = toeplitzWalkSideBits (rank a r) := by
    unfold toeplitzWalkSideBits toeplitzSeedBits
    omega
  have hc := card_positiveSample (m := 2 ^ toeplitzWalkSideBits (rank a r))
    (n := 2 * Nat.clog 2 (Request.denominator a r + 1))
  have hv : Fintype.card (MargulisVertex (2 ^ toeplitzWalkSideBits (rank a r))) =
      2 ^ toeplitzWalkSideBits (rank a r) * 2 ^ toeplitzWalkSideBits (rank a r) := by
    simp [MargulisVertex, ZMod.card]
  rw [hv, card_poweredMargulisLabel] at hc
  have hl : seedCount a r = Fintype.card (MargulisWalkSample (2 ^ toeplitzWalkSideBits (rank a r))
      (2 * Nat.clog 2 (Request.denominator a r + 1)).succ) := by
    unfold seedCount Packets.seedList
    rw [List.length_ofFn]
    rfl
  rw [hl, hc]
  unfold seedExp
  rw [hw, hs]
  have e : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
  rw [e, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-! ## 3. Size: the seed count is a fixed power of `smallSize` -/

theorem walk_le_small (a : DecompositionAlgorithm) (r : Request) : 2 ^ walkLength a r ≤ r.smallSize a := by
  have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, x7 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
    intros; omega
  unfold walkLength Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem depth_pow_le_small (a : DecompositionAlgorithm) (r : Request) :
    (pop a r + 2) ^ (depth a r + 1) ≤ r.smallSize a := by
  have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, x8 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
    intros; omega
  unfold pop depth touch Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem two_rank_le (a : DecompositionAlgorithm) (r : Request) : 2 ^ rank a r ≤ 2 * r.smallSize a := by
  have hs := one_le_small a r
  rw [rank_eq]
  rcases le_total (depth a r) (Nat.clog 2 (pop a r)) with h | h
  · rw [max_eq_right h]
    rcases Nat.eq_zero_or_pos (pop a r) with h0 | h0
    · rw [h0]; simp; omega
    · have h1 := two_pow_clog_two_le_two_mul (pop a r) h0
      have h2 := pop_le_small a r
      omega
  · rw [max_eq_left h]
    have h1 : 2 ^ depth a r ≤ 2 ^ (depth a r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (depth a r + 1) ≤ (pop a r + 2) ^ (depth a r + 1) := Nat.pow_le_pow_left (by omega) _
    have h3 := depth_pow_le_small a r
    omega

theorem seed_le_small (a : DecompositionAlgorithm) (r : Request) :
    2 ^ seedExp a r ≤ 8 * (r.smallSize a) ^ 163 := by
  unfold seedExp
  set s := r.smallSize a
  have hw := walk_le_small a r
  have hr := two_rank_le a r
  -- the label part: `(2^⌊t/2⌋)^2 ≤ 2^t ≤ s`
  have hL : 2 ^ (walkLength a r / 2 * 320) ≤ s ^ 160 := by
    have h1 : (2 ^ (walkLength a r / 2)) ^ 2 ≤ s := by
      rw [← pow_mul]
      exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hw
    calc 2 ^ (walkLength a r / 2 * 320) = ((2 ^ (walkLength a r / 2)) ^ 2) ^ 160 := by
          rw [← pow_mul, ← pow_mul]
      _ ≤ s ^ 160 := Nat.pow_le_pow_left h1 _
  -- the vertex part: `2^(2⌊3 rank/2⌋) ≤ (2^rank)^3 ≤ 8 s^3`
  have hV : 2 ^ (rank a r * 3 / 2 * 2) ≤ 8 * s ^ 3 := by
    calc 2 ^ (rank a r * 3 / 2 * 2) ≤ 2 ^ (rank a r * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ rank a r) ^ 3 := by rw [← pow_mul]
      _ ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left hr _
      _ = 8 * s ^ 3 := by ring
  calc 2 ^ (walkLength a r / 2 * 320 + rank a r * 3 / 2 * 2)
      = 2 ^ (walkLength a r / 2 * 320) * 2 ^ (rank a r * 3 / 2 * 2) := by rw [pow_add]
    _ ≤ s ^ 160 * (8 * s ^ 3) := Nat.mul_le_mul hL hV
    _ = 8 * s ^ 163 := by ring

theorem seedCount_le_small (a : DecompositionAlgorithm) (r : Request) :
    seedCount a r ≤ 8 * (r.smallSize a) ^ 163 := by
  rw [seed_eq]; exact seed_le_small a r

/-! ## 4. The stage -/

/-- `⌊t/2⌋·320 = 160(t-1)` in unary. -/
def labelS (a : DecompositionAlgorithm) : UnaryStage a (fun r => walkLength a r / 2 * 320) :=
  ((walkStage a (cutoffStage a) (thrSelStage a)).thenMapP halfMap 4 1 half_cost).thenMapP (scaleMap 320)
    (4 * 320 + 12) 2 (scale_cost 320)

/-- `⌊3·rank/2⌋·2 = 2 r_0` in unary. -/
def vertexS (a : DecompositionAlgorithm) : UnaryStage a (fun r => rank a r * 3 / 2 * 2) :=
  (((rankStage a).thenMapP (scaleMap 3) (4 * 3 + 12) 2 (scale_cost 3)).thenMapP halfMap 4 1 half_cost).thenMapP
    (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2)

/-- The seed exponent in unary. -/
def expS (a : DecompositionAlgorithm) : UnaryStage a (seedExp a) :=
  ((labelS a).pairP (vertexS a) addMap2 6 1 add_cost).ofEq (fun _ => rfl)

theorem pow_cost_le (a : DecompositionAlgorithm) (r : Request) :
    powMap.cost (seedExp a r) ≤ 16200 * (r.smallSize a) ^ 326 := by
  have h := power_budget_le (seedExp a r)
  have h2 := seed_le_small a r
  have hs := one_le_small a r
  have hp : 1 ≤ (r.smallSize a) ^ 163 := Nat.one_le_pow _ _ (by omega)
  change RepairSource.CloseoutCapacity.Power.budget (seedExp a r) ≤ _
  have h3 : (2 ^ seedExp a r + 1) ^ 2 ≤ (9 * (r.smallSize a) ^ 163) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc RepairSource.CloseoutCapacity.Power.budget (seedExp a r)
      ≤ 200 * (2 ^ seedExp a r + 1) ^ 2 := h
    _ ≤ 200 * (9 * (r.smallSize a) ^ 163) ^ 2 := Nat.mul_le_mul_left _ h3
    _ = 16200 * (r.smallSize a) ^ 326 := by ring

def seedCountStage (a : DecompositionAlgorithm) : UnaryStage a (seedCount a) :=
  ((expS a).thenMap powMap 16200 326 (pow_cost_le a)).ofEq (fun r => (seed_eq a r).symm)

end
end NearCubicWires.PacketsMeta.Seed

