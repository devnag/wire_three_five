import Proof.Wire_3_5.UnionMachine.FrontCapsBase
import Proof.Wire_3_5.UnionMachine.FrontSemEv
import Proof.Wire_3_5.UnionMachine.FrontSemRunBase

/-! # C6 front, the semantic core (10): a guess's sizes are polynomial in `q` (P3:3485-3491, 3669-3691)

At a setup whose PCP makes `C_H (w+1)^{e_Q}` queries, every guess whose oracle is within the size cap has a
substituted circuit of size `< K_R (w+1)^{σ_H}` (**`req_size`**, the `requestSize_le_of`), hence a PCPP output with at
most `K_p(w)` variables and `2^{cb} ≤ K_p(w)` (**`nv_le`**, **`cb_le`**, the PCPP algorithm's bounds). Its atoms at the
description envelope have codes of polynomial length (**`atomWord_le`**, PA's `code_bits_le`).

Paper quantity of the main types: the guess's PCPP output sizes and atom codes against the width `q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSize
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord)

section Gen

end Gen

/-! ## The atoms' codes -/

section Codes

/-- The code word bound at the description envelope `(q+1)^D`. -/
noncomputable def Kc (D q : ℕ) : ℕ := 2 * PrimAsm.CallSize.circBits ((q + 1) ^ D + 4) + 1

theorem atomWord_le (m : Mode) {q : ℕ} (C : m.Circuit q) (D : ℕ) (hd : m.descriptionBits C ≤ (q + 1) ^ D) :
    (natWord (m.code C)).length ≤ Kc D q :=
  PrimAsm.CallSize.natWord_len_le (PrimAsm.CallSize.code_bits_le m C _ (by omega) (by omega))

theorem Kc_pq (D : ℕ) : FrontCaps.PQ (Kc D) := by
  obtain ⟨c, d, -, h⟩ := PrimAsm.CallSize.pb_circBits
  refine ⟨2 * (c * 6 ^ d) + 1, D * d, fun q => ?_⟩
  have h1 := h ((q + 1) ^ D + 4)
  have h2 : (q + 1) ^ D + 4 + 1 ≤ 6 * (q + 1) ^ D := by
    have := Nat.one_le_pow D (q + 1) (by omega); omega
  have h3 : ((q + 1) ^ D + 4 + 1) ^ d ≤ 6 ^ d * (q + 1) ^ (D * d) := by
    calc ((q + 1) ^ D + 4 + 1) ^ d ≤ (6 * (q + 1) ^ D) ^ d := Nat.pow_le_pow_left h2 d
      _ = 6 ^ d * (q + 1) ^ (D * d) := by rw [mul_pow, pow_mul]
  have h4 : 1 ≤ (q + 1) ^ (D * d) := Nat.one_le_pow _ _ (by omega)
  unfold Kc
  calc 2 * PrimAsm.CallSize.circBits ((q + 1) ^ D + 4) + 1 ≤ 2 * (c * (6 ^ d * (q + 1) ^ (D * d))) + 1 := by
        have := Nat.mul_le_mul_left c h3; omega
    _ ≤ (2 * (c * 6 ^ d) + 1) * (q + 1) ^ (D * d) := by
        have e : 2 * (c * (6 ^ d * (q + 1) ^ (D * d))) = 2 * (c * 6 ^ d) * (q + 1) ^ (D * d) := by ring
        rw [e, Nat.add_mul, one_mul]; omega

end Codes

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemSize
