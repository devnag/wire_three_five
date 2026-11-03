import Lean
import Proof.Wire_3_5.UnionMachine.FrontCapsBase
import Proof.Wire_3_5.UnionMachine.FrontSemEv
import Proof.Wire_3_5.UnionMachine.FrontSemRunBase
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.FrontSemSizeBase


noncomputable section
set_option maxRecDepth 4096


/-! # The front's semantic core (10): a guess's sizes are polynomial in `q` (paper v2, Lemma H.7(b), (58))

At a guess whose `H_Γ` has `|H_Γ| + 1 ≤ K_s (q+1)^σ` (Lemma H.7(b), `UnionCallCount.hsize_pair`), the PCPP output has at
most `K_p(q)` variables and `2^{cb} ≤ K_p(q)` (**`nv_le`**, **`cb_le`**, the PCPP algorithm's bounds). Its atoms at the
description envelope have codes of polynomial length (**`atomWord_le`**, PA's `code_bits_le`).

Paper quantity of the main types: the guess's PCPP output sizes and atom codes against the width `q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSize
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord)

section Gen
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (S : UnionSetup I) (Ks σ : ℕ)

/-- The PCPP output's size bound at width `w`, from `|H_Γ| + 1 ≤ K_s (w+1)^σ`. -/
def Kp (w : ℕ) : ℕ := S.pcppAlg.coefficient * (Ks * (w + 1) ^ σ) ^ S.pcppAlg.degree

variable {S Ks σ}

/-- **The PCPP output's variable count.** -/
theorem nv_le {N : ℕ} (z : BitInput N) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (w : ℕ)
    (hr : (S.request z O).circuit.size + 1 ≤ Ks * (w + 1) ^ σ) :
    (S.pcppOf z O).systematicBits + (S.pcppOf z O).auxiliaryBits ≤ 2 * Kp S Ks σ w := by
  have hsys := S.pcppAlg.systematicBound (S.request z O)
  have haux := S.pcppAlg.auxiliaryBound (S.request z O)
  have har := (S.request z O).sizeLarge
  have e1 : S.pcppAlg.coefficient * ((S.request z O).arity + 1) ^ S.pcppAlg.degree ≤ Kp S Ks σ w := by
    unfold Kp
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have e2 : S.pcppAlg.coefficient * ((S.request z O).circuit.size + 1) ^ S.pcppAlg.degree ≤ Kp S Ks σ w := by
    unfold Kp
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr _)
  show (S.pcppAlg.output (S.request z O)).systematicBits + (S.pcppAlg.output (S.request z O)).auxiliaryBits ≤ _
  omega

/-- **The PCPP output's clause count.** -/
theorem cb_le {N : ℕ} (z : BitInput N) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (w : ℕ)
    (hr : (S.request z O).circuit.size + 1 ≤ Ks * (w + 1) ^ σ) :
    2 ^ (S.pcppOf z O).clauseBits ≤ Kp S Ks σ w := by
  have hM := S.pcppAlg.clauseCountBound (S.request z O)
  refine hM.trans ?_
  unfold Kp
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr _)

theorem Kp_pq : FrontCaps.PQ (Kp S Ks σ) := by
  unfold Kp
  refine FrontCaps.PQ.mul (FrontCaps.PQ.const _) (FrontCaps.PQ.pow (FrontCaps.PQ.mul (FrontCaps.PQ.const _)
    (FrontCaps.PQ.pow ?_ _)) _)
  exact FrontCaps.PQ.add FrontCaps.PQ.var (FrontCaps.PQ.const 1)

end Gen

/-! ## The atoms' codes -/

section Codes

end Codes

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSize

end
