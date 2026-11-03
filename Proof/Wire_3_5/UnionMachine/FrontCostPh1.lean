import Proof.Wire_3_5.UnionMachine.FrontCostKit

/-! # C6 front, the time (2): phase 1's cost is `O((N+2)^{25})` (P3:3632-3640)

**`ph1C_le`**: phase 1 (the input's framing, the width `q(N)` in unary (base's hierarchy width stages, the `⌈log₂⌉`
program, the tail), the oracle field (the walker, the arity, v8's cold oracle call: base's
`CloseoutWitness.Oracle.budget_polynomial`, `(N+2)^{25}`), the size stage) costs at most `c·(N+2)^{25}`, `c` fixed
by `k`, `A_pad` and the oracle degree.

Paper quantity of the main type: the front's preprocessing time against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostPh1
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit

theorem clog_le (x : ℕ) : Nat.clog 2 x ≤ x := FrontSemEv.clog_le_self x

/-- The hierarchy width stages: `≤ c_k·(N+2)^3`. -/
theorem hfi_le (D C : ℕ) (xs : List Bool) :
    HierarchyFromInput.budget D C xs ≤ (600 * (HierarchyReduction.shortCoefficient D C + 1) ^ 2) * (xs.length + 2) ^ 3 := by
  have h1 := HierarchyReduction.count_budget xs
  have h2 := HierarchyReduction.width_budget D C xs.length
  have h3 := HierarchyReduction.bound_budget D C xs.length
  have hl : PCPResourceLedger.ell xs.length + 1 ≤ xs.length + 2 := by
    unfold PCPResourceLedger.ell; have := clog_le (xs.length + 1); omega
  set n := xs.length + 2 with hn
  set s := HierarchyReduction.shortCoefficient D C with hs
  have a1 : 42 * (xs.length + 1) * (PCPResourceLedger.ell xs.length + 1) ≤ 42 * (n * n) := by
    have := Nat.mul_le_mul (show xs.length + 1 ≤ n by omega) hl; nlinarith
  have a2 : 32 * s * (PCPResourceLedger.ell xs.length + 1) ≤ 32 * s * n := Nat.mul_le_mul_left _ hl
  have a3 : 512 * s ^ 2 * (PCPResourceLedger.ell xs.length + 1) ^ 2 ≤ 512 * s ^ 2 * n ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl 2)
  have hn2 : 2 ≤ n := by omega
  have b1 : n * n ≤ n ^ 3 := by rw [show n ^ 3 = n * n * n by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
  have b2 : n ≤ n ^ 3 := by rw [show n ^ 3 = n * n * n by ring]; nlinarith
  have b3 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have b0 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
  have c1 : 32 * s * n ≤ 32 * (s + 1) ^ 2 * n ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by nlinarith)) b2
  have c2 : 512 * s ^ 2 * n ^ 2 ≤ 512 * (s + 1) ^ 2 * n ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by nlinarith)) b3
  have c3 : 42 * (n * n) ≤ 42 * (s + 1) ^ 2 * n ^ 3 := by
    have : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have c4 : 2 ≤ 2 * (s + 1) ^ 2 * n ^ 3 := by
    have : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have e : 600 * (s + 1) ^ 2 * n ^ 3 = 42 * (s + 1) ^ 2 * n ^ 3 + 32 * (s + 1) ^ 2 * n ^ 3 + 512 * (s + 1) ^ 2 * n ^ 3 +
      2 * (s + 1) ^ 2 * n ^ 3 + 12 * (s + 1) ^ 2 * n ^ 3 := by ring
  unfold HierarchyFromInput.budget
  omega

/-- **Phase 1's cost** is at most `10^{31}·(N+2)^{26}` once `N` covers phase 1's constants. -/
theorem ph1C_le (k Ap G N : ℕ) (xs w : List Bool) (hx : xs.length = N) (hw : w.length ≤ N) (hN : 2 ≤ N)
    (hpay : 16 * (FrontWalkRef.payload w.tail).length ≤ N) (hq : Ledger.nativeWidth k Ap N ≤ N)
    (hk : k + 2 ≤ N + 2) (hsc : HierarchyReduction.shortCoefficient (k + 2) 1 + 1 ≤ N + 2) (hA : Ap + 1 ≤ N + 2)
    (hG : 2 ^ RecoveryScheduleEnvelope.oracleDepth G ≤ N + 2) :
    FrontTop.ph1C k Ap G xs w ≤ 10 ^ 31 * (N + 2) ^ 26 := by
  have hn : 1 ≤ N + 2 := by omega
  have a1 : xs.length ≤ N + 2 := by omega
  have a2 : w.length ≤ N + 2 := by omega
  have aN : N ≤ N + 2 := by omega
  have aA : Ap ≤ N + 2 := by omega
  have aell : PCPResourceLedger.ell xs.length ≤ N + 2 := by
    unfold PCPResourceLedger.ell; have := clog_le (xs.length + 1); omega
  have ab1 : (Nat.bits 1).length ≤ N + 2 := by
    have : (Nat.bits 1).length = 1 := by decide
    omega
  have b1 := hfi_le (k + 2) 1 xs
  have hy := FrontSemEv.clog_pow_le xs.length (k + 2)
  have hcl : Nat.clog 2 xs.length ≤ N + 2 := by have := clog_le xs.length; omega
  have hy2 : Nat.clog 2 (Nat.clog 2 (xs.length ^ (k + 2)) + 2) ≤ Nat.clog 2 (xs.length ^ (k + 2)) + 2 := clog_le _
  have hwA : (Transfer.wordA Ap).length ≤ N + 2 := by unfold Transfer.wordA; simp only [List.length_cons, List.length_replicate]; omega
  have hw2 : Transfer.wordTwo.length ≤ N + 2 := by unfold Transfer.wordTwo; simp
  have hvq : value (SignedSortKey.binary (natBitLength (Ledger.nativeWidth k Ap xs.length))
      (Ledger.nativeWidth k Ap xs.length)) = Ledger.nativeWidth k Ap xs.length :=
    SignedSortKey.binary_value _ _ (CompilerMachine.Pool.lt_pow_natBitLength _)
  have bor := CloseoutWitness.Oracle.budget_polynomial xs (FrontWalkRef.payload w.tail)
    (SignedSortKey.binary (natBitLength (Ledger.nativeWidth k Ap xs.length)) (Ledger.nativeWidth k Ap xs.length))
    (by omega) (by omega) (by rw [hvq, hx]; omega)
  have hnb : natBitLength (Ledger.nativeWidth k Ap xs.length) ≤ N + 2 := by
    have := FrontSemEv.nbl_le_self (Ledger.nativeWidth k Ap xs.length); rw [hx] at this ⊢; omega
  have hq' : Ledger.nativeWidth k Ap xs.length ≤ N + 2 := by rw [hx]; omega
  have hDg : 2 ^ RecoveryScheduleEnvelope.oracleDepth G ≤ N + 2 := hG
  unfold FrontTop.ph1C FrontWidthCost.qCost FrontClog.clogCost FrontClog.mkCost FrontWidthCost.tailCost
    RepairSource.CloseoutSchedule.Clog.budget UWalkNumbers.productCost HierarchyBinary.width FrontOracle.osCost
    FrontOracleField.walkCost FrontArity.arCost CloseoutWitness.OracleCall.budget CloseoutWitness.OracleCall.prepareBudget
    FrontSizeStage.ssCost FrontSize.sizeCost
  rw [hvq, SignedSortKey.binary_length]
  c6npf

section Ph2
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.RepairRepresentation

end Ph2

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostPh1
