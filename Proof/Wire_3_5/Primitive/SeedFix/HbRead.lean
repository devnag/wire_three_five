import Proof.Wire_3_5.Primitive.SeedFix.HbCopy

/-! # C4.Hb, machine part 4: reading the odometer's positions and the populations' gates (P3:2253-2262)

"`δ_{a,j}^{2t} = Σ_{i_1,…,i_{2t}} Z_{a,i_1}⋯Z_{a,i_{2t}} A_{i_1,j}⋯A_{i_{2t},j}`" (P3:2255-2258): a cell's moment tuple
`ι` sits in the odometer's word as `2t` fields of `ℓ₀` bits (low bit first), and position `ι_r` of population `p`
names pool gate `gi = gis_p[ι_r]`. This module reads a raw field into a register (**`readRawW_spec`**, PA's payload
round `ParseNat.bitRound_spec` in C6's counted loop `wloop`) and walks the populations' records (`popsWord`):
a record is `T sgn`, its gates `T 1^{gi} F`, then `F`.

Paper quantities of the main types: the tuple's positions `ι_r` (`bitsValue (binary ℓ₀ ι_r) = ι_r`) and the gates
`gi` of a population. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem bitsValue_binary : ∀ (w x : ℕ), CanonicalBinary.bitsValue (binary w x) = x % 2 ^ w
  | 0, x => by simp [binary, CanonicalBinary.bitsValue, Nat.mod_one]
  | w + 1, x => by
    simp only [binary, CanonicalBinary.bitsValue, bitsValue_binary w (x / 2)]
    rw [pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem bitsValue_take_lt : ∀ (bs : List Bool) (k : ℕ), CanonicalBinary.bitsValue (bs.take k) < 2 ^ k
  | [], k => by simp [CanonicalBinary.bitsValue]
  | b :: bs, 0 => by simp [CanonicalBinary.bitsValue]
  | b :: bs, k + 1 => by
    simp only [List.take_succ_cons, CanonicalBinary.bitsValue, pow_succ]
    have := bitsValue_take_lt bs k
    cases b <;> simp <;> omega

section Read
variable {ns nr : ℕ} (cap : ℕ)

/-- **Read `c` raw bits** of stream `i` (low bit first) into `v`, through the power `p` and the scratch `t`. -/
def readRawW (i : Fin (ns + 1)) (c v p t : Fin nr) : WM ns nr :=
  .seq (.inc p) (.seq (.whr c (.seq (.dec c) (bitBody false i v p t))) (WM.clear p))

theorem readRawW_spec (i : Fin (ns + 1)) (c v p t : Fin nr) (hcv : c ≠ v) (hcp : c ≠ p) (hct : c ≠ t) (hpv : p ≠ v)
    (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr) (bs : List Bool) (hc : σ.val c = bs.length) (hp : σ.val p = 0)
    (ht : σ.val t = 0) (hread : ∀ m < bs.length, readTapeBit (σ.st i) (σ.sh i + m) = bs.getD m false)
    (hcap : σ.val v + 2 ^ (bs.length + 1) ≤ cap) :
    WExec cap (readRawW i c v p t) σ
      (((σ.seth i (σ.sh i + bs.length)).setv v (σ.val v + CanonicalBinary.bitsValue bs)).setv c 0)
      (1 + 3 + 1 + (bs.length * (36 * 2 ^ bs.length + 12 + 4) + 1 + 1 + (3 * 2 ^ bs.length + 1))) := by
  set L := bs.length with hL
  set v₀ := σ.val v with hv₀
  have hpow : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hpow2 : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hLlt : L < 2 ^ L := Nat.lt_two_pow_self
  have s1 := WExec.inc (cap := cap) p σ (by rw [hp]; omega)
  rw [hp, Nat.zero_add] at s1
  let S : ℕ → WState ns nr := fun k => payState false σ i c v p L v₀ bs k
  have hS0 : S 0 = σ.setv p 1 := by
    simp only [S, payState, stp, Nat.mul_zero, Nat.add_zero, List.take_zero, Nat.sub_zero, pow_zero]
    wgen_eq [hc, hL, hv₀, CanonicalBinary.bitsValue, hcv, hcp, hpv]
  have hloop := UnionMachine.Round.wloop cap c (bitBody false i v p t) (36 * 2 ^ L + 12) L S
    (fun k _ => by simp [S, payState, Function.update_apply, hcv, hcp, Ne.symm hcv, Ne.symm hcp])
    (by omega)
    (fun k hk => bitRound_spec cap false i c v p t hcv hcp hct hpv hpt hvt σ L v₀ bs rfl ht
      (fun m hm => by simpa [stp, off] using hread m hm) (by omega)
      (fun k _ => bitsValue_take_lt bs k) k hk)
  rw [hS0] at hloop
  have hSL : (S L).val p = 2 ^ L := by simp [S, payState]
  have s3 := wclear_spec cap p (2 ^ L) (S L) hSL (by rw [hSL]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq hloop s3)) ?_ (by omega)
  simp only [S, payState, stp, Nat.one_mul, List.take_length, Nat.sub_self]
  wgen_eq [hc, hL, hv₀, hp, hcv, hcp, hpv]

end Read

end NearCubicWires.WireExponent3_5.PrimT.HbM
