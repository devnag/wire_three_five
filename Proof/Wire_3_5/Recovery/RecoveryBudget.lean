import Lean
import Proof.Wire_3_5.Recovery.RecoveryFacts
import Proof.Wire_3_5.Recovery.RecoveryEnvelope
import Bindings.Williams14_Corollary4_4
import Proof.PCP.PCPPQueryBounds
import Proof.Packets.BudgetReaderCaps
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import W3.Joins.Cases


noncomputable section


/-! # The clause degree at the substituted outer verifier (paper v2 (58); Lemma H.7(b))

Paper v2 (58): "the branch-independent integer `d_G = a_p e_H` bounds all PCPP clause counts by `(q+2)^{d_G}`". The
clause degree is the anchor constant `recDG l = e_H·a_p + 1` (`WireExponent3_5GateUnion`), with `e_H` the size
exponent of `H_Γ` (Lemma H.7(b)). The size statements of the earlier outer step (the substituted request of a native
PCP oracle, `recSigma`) are not used: the request is `H_Γ` itself. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer

open _root_.NearCubicGates.Close
open _root_.NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open _root_.NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)

variable (l : Literals)

theorem capExp_pos : 1 ≤ capExp l := Nat.one_le_two_pow

/-- **Lemma H.7(b) at the gate**: `|H_B| + 1 ≤ K_s (q+1)^{e_H}` for every pair `B` whose proof circuit has at most
`q^G` gates, at every source index `1 ≤ ν ≤ q`, `q = q(N)`. -/
theorem datSize_le : ∃ Ks : ℕ, ∀ (ν N : ℕ) (B : Outer.OuterGuess (gateWidth l N)), 1 ≤ ν → ν ≤ gateWidth l N →
    B.pf.size ≤ oracleSizeBound (oracleDeg l) (gateWidth l N) →
    (Outer.Dat (gateMW l) (gateSV l) ν B).D.size + 1 ≤ Ks * (gateWidth l N + 1) ^ eH l := by
  obtain ⟨M, hM⟩ := Outer.natBitLength_T_le (gateSV l)
  set eC' := (Outer.alg (gateMW l) (gateSV l)).sizeExp with heC
  set cA := (Outer.alg (gateMW l) (gateSV l)).coefficient with hcA
  have hcap1 := capExp_pos l
  refine ⟨cA * (M + kclk + 4) ^ eC' + 3, fun ν N B hν1 hνq hpf => ?_⟩
  have hD := Outer.Dat_size_le (gateMW l) (gateSV l) ν B
  have hC := Outer.outC_size_le (gateMW l) (gateSV l) ν hν1 B.src
  have hT := hM ν
  have hpf1 := oracleSize_le l _ _ hpf
  have hq1 : 1 ≤ gateWidth l N + 1 := by omega
  have hlen : lenG l + 2 = capExp l + 1 := by unfold lenG; omega
  have hX : 1 ≤ (gateWidth l N + 1) ^ (lenG l + 2) := Nat.one_le_pow _ _ hq1
  have hlam : Outer.instLength (lenG l) ν ≤ (gateWidth l N + 1) ^ (lenG l + 2) := by
    unfold Outer.instLength; exact Nat.pow_le_pow_left (by omega) _
  have hlin : gateWidth l N + 1 ≤ (gateWidth l N + 1) ^ (lenG l + 2) := Nat.le_self_pow (by omega) _
  have hin : Outer.instLength (lenG l) ν + natBitLength ((gateSV l).T (Outer.instLength (lenG l) ν)) + 1 ≤
      (M + kclk + 4) * (gateWidth l N + 1) ^ (lenG l + 2) := by nlinarith
  have hC2 : (Outer.outC (gateMW l) (gateSV l) ν B.src).circuit.size ≤
      cA * ((M + kclk + 4) ^ eC' * (gateWidth l N + 1) ^ ((lenG l + 2) * eC')) := by
    refine hC.trans (Nat.mul_le_mul_left _ ?_)
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left hin _
  set Y := (gateWidth l N + 1) ^ ((lenG l + 2) * eC') with hY
  set Z := (gateWidth l N + 1) ^ capExp l with hZ
  have hYZ : Y * Z ≤ (gateWidth l N + 1) ^ eH l := by
    rw [hY, hZ, ← pow_add]
    refine Nat.pow_le_pow_right hq1 ?_
    unfold eH eC
    rw [hlen]
    nlinarith
  have hq3 : gateWidth l N + 3 ≤ 3 * (gateWidth l N + 1) ^ eH l := by
    have : gateWidth l N + 1 ≤ (gateWidth l N + 1) ^ eH l := Nat.le_self_pow (by unfold eH; omega) _
    omega
  have hCpf : (Outer.outC (gateMW l) (gateSV l) ν B.src).circuit.size * (B.pf.size + 1) ≤
      cA * (M + kclk + 4) ^ eC' * (Y * Z) := by
    calc (Outer.outC (gateMW l) (gateSV l) ν B.src).circuit.size * (B.pf.size + 1)
        ≤ (cA * ((M + kclk + 4) ^ eC' * Y)) * Z := Nat.mul_le_mul hC2 hpf1
      _ = cA * (M + kclk + 4) ^ eC' * (Y * Z) := by ring
  have h5 : cA * (M + kclk + 4) ^ eC' * (Y * Z) ≤ cA * (M + kclk + 4) ^ eC' * (gateWidth l N + 1) ^ eH l :=
    Nat.mul_le_mul_left _ hYZ
  have hD' : (Outer.Dat (gateMW l) (gateSV l) ν B).D.size ≤
      (Outer.outC (gateMW l) (gateSV l) ν B.src).circuit.size * (B.pf.size + 1) + gateWidth l N + 2 := hD
  have e : (cA * (M + kclk + 4) ^ eC' + 3) * (gateWidth l N + 1) ^ eH l =
      cA * (M + kclk + 4) ^ eC' * (gateWidth l N + 1) ^ eH l + 3 * (gateWidth l N + 1) ^ eH l := by ring
  clear hD
  omega

/-- **The clause bound at `d_G`** ((58)): past a width onset, the PCPP output of the request at `H_B` has at most
`⌈d_G log₂(gateWidth l N+2)⌉` clause bits, for every pair `B` within the cap and every `1 ≤ ν ≤ gateWidth l N`, `d_G = recDG l = e_H a_p + 1`. -/
theorem clauseBits_le : ∃ q₀ : ℕ, ∀ (ν N : ℕ) (B : Outer.OuterGuess (gateWidth l N)), 1 ≤ ν → ν ≤ gateWidth l N →
    q₀ ≤ gateWidth l N → B.pf.size ≤ oracleSizeBound (oracleDeg l) (gateWidth l N) →
    ((gatePCPP l).output
      (W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l) ν B)).clauseBits ≤
      clauseWidth (recDG l) (gateWidth l N) := by
  obtain ⟨Ks, hKs⟩ := datSize_le l
  set K₀ := (gatePCPP l).coefficient * Ks ^ (gatePCPP l).degree with hK₀
  refine ⟨K₀ + (gatePCPP l).minimumArity, fun ν N B hν1 hνq hq0 hpf => ?_⟩
  have hmin : (gatePCPP l).minimumArity ≤ Outer.width (gateMW l) (gateSV l) N := by
    show (gatePCPP l).minimumArity ≤ gateWidth l N; omega
  rw [W3.NearCubicWires.RepairSource.Outer3.requestAt_of (gateMW l) (gateSV l) (gatePCPP l) ν B hmin]
  have hcc := (gatePCPP l).clauseCountBound
    (W3.NearCubicWires.RepairSource.Outer3.requestOf (gateMW l) (gateSV l) (gatePCPP l) ν B hmin)
  have hsz : (W3.NearCubicWires.RepairSource.Outer3.requestOf (gateMW l) (gateSV l) (gatePCPP l) ν B hmin).circuit.size
      + 1 ≤ Ks * (gateWidth l N + 1) ^ eH l := hKs ν N B hν1 hνq hpf
  have hb : 2 ^ ((gatePCPP l).output
      (W3.NearCubicWires.RepairSource.Outer3.requestOf (gateMW l) (gateSV l) (gatePCPP l) ν B hmin)).clauseBits ≤
      (gateWidth l N + 2) ^ recDG l := by
    calc _ ≤ _ := hcc
      _ ≤ (gatePCPP l).coefficient * (Ks * (gateWidth l N + 1) ^ eH l) ^ (gatePCPP l).degree :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz _)
      _ = K₀ * (gateWidth l N + 1) ^ (eH l * (gatePCPP l).degree) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ (gateWidth l N + 2) * (gateWidth l N + 2) ^ (eH l * (gatePCPP l).degree) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      _ = (gateWidth l N + 2) ^ recDG l := by unfold recDG; ring
  have hc := Nat.le_pow_clog (by norm_num : 1 < 2) ((gateWidth l N + 2) ^ recDG l)
  unfold clauseWidth
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hb.trans hc)

end NearCubicWires.WireExponent3_5.Transfer

end
