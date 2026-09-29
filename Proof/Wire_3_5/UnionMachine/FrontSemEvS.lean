import Proof.Wire_3_5.UnionMachine.FrontSemEv

/-! # C6 front, the semantic core (9): the pinned setup's facts past an onset (P3:3632-3691)

Past an onset `N₁` at the pinned setup: the setup's width is the ledger's `q(N)`, above the PCPP's minimum arity; the
star hypotheses and the ledger's fits hold at `q(N)`; `q(N)` and every oracle within the size cap are small against
`N` (**`sue_ev`**). Phase 1's input facts follow (**`ph1ok`**), and the capacity stage's (**`hcap_of`**).

Paper quantity of the main types: the front's width `q(N)` and its oracle within `q^G`, against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEvS
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open Filter

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

theorem bu_q (N : ℕ) : (BU l F e coef A).q N = nativeWidth (kE l e) (gateApad l) N := rfl

/-- **The pinned setup's facts past an onset.** -/
theorem sue_ev : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
    (SUE l F e coef A L hL).pcp.nativeWidth N = (BU l F e coef A).q N ∧
    (gatePCPP l).minimumArity ≤ (BU l F e coef A).q N ∧
    (IUE l F e coef A).StarAt ((BU l F e coef A).q N) ∧ (BU l F e coef A).FitsAt ((BU l F e coef A).q N) ∧
    4 * ((BU l F e coef A).q N + 1) ≤ N ∧ 3 * natBitLength ((BU l F e coef A).q N) ≤ (BU l F e coef A).q N ∧
    (∀ o, o ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l) ((BU l F e coef A).q N) → o + 5 ≤ N) ∧
    16 ≤ N := by
  obtain ⟨N0, hN0⟩ := setupF_width l F (kE l e) coef A (aE l e) (haE l e) L hL
  have hq : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  have e1 := hq.eventually (eventually_ge_atTop (gatePCPP l).minimumArity)
  have e2 := hq.eventually (eventually_star F.cr F.cr_pos 2 le_rfl)
  have e3 := FrontSemEv.polyq_le (kE l e) (gateApad l) 4 1
  have e4 := hq.eventually (FrontSemEv.eventually_nbl 3)
  have e5 := FrontSemEv.polyq_le (kE l e) (gateApad l) 5 (2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (eventually_ge_atTop 16))))))
  refine ⟨max (max N0 N1) (BU l F e coef A).onset, fun N hN => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hN1 N (by omega)
  refine ⟨hN0 N (by omega), a1, a2, (BU l F e coef A).fits N (by omega), by rw [pow_one] at a3; exact a3, a4,
    fun o ho => ?_, a6⟩
  have h1 := oracleSize_le (recOracleDeg l) _ o ho
  have h2 : 1 ≤ ((BU l F e coef A).q N + 1) ^ 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) :=
    Nat.one_le_pow _ _ (by omega)
  rw [bu_q] at h1 h2
  omega

/-- **Phase 1's input facts** past the onset. -/
theorem ph1ok {N : ℕ} (x : BitInput N) (w : List Bool) (hw : w.length = N / 16) (h16 : 16 ≤ N)
    (hq4 : 4 * (nativeWidth (kE l e) (gateApad l) N + 1) ≤ N)
    (hnb : 3 * natBitLength (nativeWidth (kE l e) (gateApad l) N) ≤ nativeWidth (kE l e) (gateApad l) N) :
    FrontTop.Ph1OK (kE l e) (gateApad l) (List.ofFn x) w := by
  have hl : (List.ofFn x).length = N := List.length_ofFn
  have hb := FrontSemEv.nbl_le_self (nativeWidth (kE l e) (gateApad l) N)
  have hwl : w.length ≤ N / 16 := by omega
  have hd16 : 16 * (N / 16) ≤ N := Nat.mul_div_le N 16
  have hpay : ∀ c : BooleanCircuit (nativeWidth (kE l e) (gateApad l) (List.ofFn x).length),
      CanonicalWitnessCodec.decodeBooleanCircuit (nativeWidth (kE l e) (gateApad l) (List.ofFn x).length)
        (value (payload w.tail)) = some c → c.size ≤ N / 16 + 2 := by
    intro c hc
    have h1 := FrontSize.size_le_code hc
    have h2 : (payload w.tail).length ≤ w.length := by
      unfold payload; rw [List.length_take]; have := List.length_drop (l := w.tail) (i := FrontWalkRef.ones w.tail + 1)
      have : w.tail.length ≤ w.length := by simp
      omega
    by_cases hp : payload w.tail = []
    · rw [hp] at h1; simp [RepairOrdinary.RadixSemantics.value, natBitLength] at h1; omega
    · have := FrontSize.nbl_value_le _ hp; omega
  refine ⟨by omega, by omega, by rw [hl]; omega, by rw [hl]; omega, fun c hc => ?_, fun c hc => ?_⟩
  · have := hpay c hc; omega
  · have h1 := hpay c hc
    have h2 := FrontSemEv.nbl_le_self c.size
    have ew : nativeWidth (kE l e) (gateApad l) (List.ofFn x).length = nativeWidth (kE l e) (gateApad l) N := by
      rw [hl]
    have e2 : natBitLength (nativeWidth (kE l e) (gateApad l) (List.ofFn x).length) =
        natBitLength (nativeWidth (kE l e) (gateApad l) N) := by rw [ew]
    omega

/-- The capacity stage's room for an oracle within the size cap. -/
theorem hcap_of {N : ℕ} (x : BitInput N) (q s : ℕ) (hs : s + 5 ≤ N) :
    64 * (s + q + 4) + 1 ≤ FrontCapStage.capOf (List.ofFn x) q :=
  FrontCapStage.cap_enough _ q s (by rw [List.length_ofFn]; exact hs)

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEvS
