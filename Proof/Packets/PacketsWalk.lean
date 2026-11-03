import Proof.Packets.PacketsGate
import Proof.Rows.RowsInitCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierPipeline
open RowsInit.Count (thrSelOf thrSelOf_card)
noncomputable section

/-! ## The values -/

/-- `|circuits|` (`0` on the terminal sentinel): natWord 4 of `nativeWord`. -/
def circN : Request → ℕ
  | .terminal => 0
  | .sym r _ _ _ => r.circuits.length
  | .thr r _ _ _ => r.circuits.length

/-- The target denominator (`0` on the terminal sentinel): natWord 3 of `nativeWord`. -/
def targetOf : Request → ℕ
  | .terminal => 0
  | .sym _ _ _ t => t
  | .thr _ _ _ t => t

/-- SYM's `|circuits|`, `0` otherwise. -/
def symCirc (r : Request) : ℕ := (1 - thrFlag r) * circN r

/-- The target's multiplier in the denominator is nonzero iff this is. -/
def targetGate (a : DecompositionAlgorithm) (r : Request) : ℕ := symCirc r + thrSelOf a r

/-- The gated target. -/
def targetG (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  if targetGate a r = 0 then 0 else targetOf r

/-- The denominator in stage form. -/
def denOf (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  symCirc r * (targetG a r + 1) +
    thrFlag r * (Nat.clog 2 (cutoffOf a r + 1) * (thrSelOf a r * (targetG a r + 1) * 2 + 1))

theorem cutoff_pos (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (target : ℕ) : 1 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
  have h := canonicalPrimeCutoff_ge_563 (familyMagnitudeExponent (ThresholdRows.equation a r))
    (CloseoutFinalC10ThresholdRows.primeDenominator a r target)
  unfold CloseoutFinalC10ThresholdRows.primeCutoff
  omega

/-- **The denominator, exactly, for every request.** -/
theorem den_eq (a : DecompositionAlgorithm) (r : Request) : Request.denominator a r = denOf a r := by
  cases r with
  | terminal => simp [Request.denominator, denOf, symCirc, circN, thrFlag]
  | sym r four L target =>
    simp only [Request.denominator, symmetricListDenominator, denOf, symCirc, thrFlag, circN, targetG,
      targetGate, thrSelOf, targetOf]
    by_cases h : r.circuits.length = 0
    · simp [h]
    · simp [h]
  | thr r four L target =>
    have hc := cutoff_pos a r target
    have hm : modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =
        Nat.clog 2 (CloseoutFinalC10ThresholdRows.primeCutoff a r target + 1) := by
      unfold modulusDigitCount
      exact log_succ_eq_clog _ hc
    have hs := thrSelOf_card a r four L target
    simp only [Request.denominator, CloseoutFinalC10ThresholdRows.listDenominator,
      CloseoutFinalC10ThresholdRows.primeDenominator, reciprocalUnionDenominator, denOf, symCirc, thrFlag,
      circN, targetG, targetGate, targetOf, cutoffOf]
    rw [hm, ← hs]
    by_cases h : thrSelOf a (.thr r four L target) = 0
    · simp [h]
    · simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add, if_neg h, Nat.one_mul]
      ring

theorem walk_eq (a : DecompositionAlgorithm) (r : Request) :
    walkLength a r = Nat.clog 2 (denOf a r + 1) * 2 + 1 := by
  unfold walkLength canonicalWalkLength
  rw [den_eq]
  ring

/-- Where the gate is open, the target is paid by `smallSize`: `target + 1 ≤ den < 2^walkLength ≤ smallSize`. -/
theorem target_lt_small (a : DecompositionAlgorithm) (r : Request) (hg : targetGate a r ≠ 0) :
    targetOf r + 1 ≤ r.smallSize a := by
  have hw := walk_pow_le a r
  have hden : targetOf r + 1 ≤ Request.denominator a r := by
    cases r with
    | terminal => simp [targetGate, symCirc, circN, thrFlag, thrSelOf] at hg
    | sym r four L target =>
      have h1 : 1 ≤ r.circuits.length := by
        simp only [targetGate, symCirc, circN, thrFlag, thrSelOf, Nat.sub_zero, Nat.one_mul,
          Nat.add_zero] at hg
        omega
      simp only [Request.denominator, symmetricListDenominator, targetOf]
      nlinarith
    | thr r four L target =>
      have h1 : 1 ≤ thrSelOf a (.thr r four L target) := by
        simp only [targetGate, symCirc, circN, thrFlag, Nat.sub_self, Nat.zero_mul, Nat.zero_add] at hg
        omega
      have hs := thrSelOf_card a r four L target
      rw [hs] at h1
      simp only [Request.denominator, CloseoutFinalC10ThresholdRows.listDenominator,
        CloseoutFinalC10ThresholdRows.primeDenominator, reciprocalUnionDenominator, modulusDigitCount, targetOf]
      have hm : 1 ≤ (Nat.log 2 (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).succ := Nat.succ_pos _
      have hA : target + 1 ≤ 2 * Fintype.card (ThresholdRows.Selection a r) * (target + 1) + 1 := by nlinarith
      calc target + 1 ≤ 2 * Fintype.card (ThresholdRows.Selection a r) * (target + 1) + 1 := hA
        _ ≤ (Nat.log 2 (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).succ *
            (2 * Fintype.card (ThresholdRows.Selection a r) * (target + 1) + 1) := Nat.le_mul_of_pos_left _ hm
  have hc : Request.denominator a r + 1 ≤ 2 ^ Nat.clog 2 (Request.denominator a r + 1) :=
    Nat.le_pow_clog (by norm_num) _
  have hp : 2 ^ Nat.clog 2 (Request.denominator a r + 1) ≤ 2 ^ walkLength a r := by
    apply Nat.pow_le_pow_right (by norm_num)
    unfold walkLength canonicalWalkLength
    omega
  omega

/-! ## The kind flags that the formulas need -/

/-- `1` unless THR: bit 2 of `nativeWord` is `0` (`native_bit2`). -/
def notThrStage (a : DecompositionAlgorithm) : UnaryStage a (fun r => 1 - thrFlag r) :=
  bitStage a 5 false (fun r => 1 - thrFlag r) (by
    intro r
    have e : fields a r 0 = r.nativeWord := rfl
    rw [e, native_bit2]
    have := thrFlag_le r
    rcases (show thrFlag r = 0 ∨ thrFlag r = 1 by omega) with h | h <;> simp [h])

/-! ## Header scalars -/

/-- **`|circuits|`**: natWord 4, gated by the live flag (the sentinel has no natWord 4). -/
def circStage (a : DecompositionAlgorithm) : UnaryStage a circN :=
  ((liveFlagStage a).gate (natAtGated a 4 (fun r => liveFlag r) circN
    (by
      intro r hr
      cases r with
      | terminal => exact absurd rfl hr
      | sym r four L target =>
        refine ⟨[0, r.q, L, target], r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c)), rfl, ?_⟩
        simp [Request.nativeWord, circN, List.append_assoc]
      | thr r four L target =>
        refine ⟨[1, r.q, L, target], r.circuits.flatMap (fun c => RepairOrdinary.frame (thrWord c)), rfl, ?_⟩
        simp [Request.nativeWord, circN, List.append_assoc])
    4 0
    (by
      intro r _
      rw [pow_zero, Nat.mul_one]
      cases r with
      | terminal => simp [circN]
      | sym r four L target => exact four
      | thr r four L target => exact four))).ofEq
    (by intro r; cases r <;> simp [liveFlag, circN])

/-- **The gated target** (natWord 3, where its multiplier `symCirc + |Sel|` is nonzero). -/
def targetStage (a : DecompositionAlgorithm) (thrSel : UnaryStage a (thrSelOf a)) : UnaryStage a (targetG a) :=
  (((notThrStage a).pairP (circStage a) mulMap2 8 2 mul_cost).pairP thrSel addMap2 6 1 add_cost).gate
    (natAtGated a 3 (targetGate a) targetOf
      (by
        intro r hr
        cases r with
        | terminal => simp [targetGate, symCirc, circN, thrFlag, thrSelOf] at hr
        | sym r four L target =>
          refine ⟨[0, r.q, L], natWord r.circuits.length ++
            r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c)), rfl, ?_⟩
          simp [Request.nativeWord, targetOf, List.append_assoc]
        | thr r four L target =>
          refine ⟨[1, r.q, L], natWord r.circuits.length ++
            r.circuits.flatMap (fun c => RepairOrdinary.frame (thrWord c)), rfl, ?_⟩
          simp [Request.nativeWord, targetOf, List.append_assoc])
      1 1
      (by
        intro r hr
        have := target_lt_small a r hr
        rw [pow_one, Nat.one_mul]
        omega))

/-- The denominator stage. -/
def denStage (a : DecompositionAlgorithm) (cutS : UnaryStage a (cutoffOf a))
    (thrSel : UnaryStage a (thrSelOf a)) : UnaryStage a (denOf a) :=
  let tp1 := (targetStage a thrSel).thenMapP (plusMap 1) 6 1 (plus_cost 1)
  let symS := (notThrStage a).pairP (circStage a) mulMap2 8 2 mul_cost
  let A := symS.pairP tp1 mulMap2 8 2 mul_cost
  let B2 := ((thrSel.pairP tp1 mulMap2 8 2 mul_cost).thenMapP (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2)).thenMapP
    (plusMap 1) 6 1 (plus_cost 1)
  let M := (cutS.thenMapP (plusMap 1) 6 1 (plus_cost 1)).thenMapP clogMap 62 1 clog_cost
  let B := (thrFlagStage a).pairP (M.pairP B2 mulMap2 8 2 mul_cost) mulMap2 8 2 mul_cost
  (A.pairP B addMap2 6 1 add_cost).ofEq (fun _ => rfl)

/-- **`walkLength` stage** (Contract field), from PM's `cutoffStage` and `|Sel|`. -/
def walkStage (a : DecompositionAlgorithm) (cutS : UnaryStage a (cutoffOf a))
    (thrSel : UnaryStage a (thrSelOf a)) : UnaryStage a (walkLength a) :=
  ((((denStage a cutS thrSel).thenMapP (plusMap 1) 6 1 (plus_cost 1)).thenMapP clogMap 62 1 clog_cost).thenMapP
    (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2) |>.thenMapP (plusMap 1) 6 1 (plus_cost 1)).ofEq
    (fun r => (walk_eq a r).symm)

end
end NearCubicWires.PacketsGlue.RequestMeta

