import CheckedPCPP.EmitNat
import Platform.RegArith
import Proof.MachineModel.OrdinaryRadixSemantics
import NearCubicGates.PublishedSources.PCPP

/-!
# R3.h9, the shared literal decoder (used by the hard table and by the weak worker W3d)

imp:three-pcpp (the near-cubic-gates paper) outputs three-literal clauses; J8 writes a literal `l` as the framed binary
code `frame (literalCode l).bits` (`literalCode (+i) = 2i`, `literalCode (−i) = 2i + 1`, `Nat.bits` little endian).
The hard table (the near-cubic-gates paper) and the worker read the underlying coordinate and the sign of each literal.

* `binW`: from a framed little-endian word `frame w` at the head of a stream, `X += value w` (proof 1's
  `RadixSemantics.value`), the head past the frame, every scratch register back at `0` (`binW_exec`).
* `binK`: the same for `K` marked bits `marks w` (no end marker), `K` back at `0` (`binK_exec`).
* `litW`: `binW` then `EmitNat.halve`: `V := (literalVar l).val`, `NEG := (literalNeg l).toNat` (**`litW_exec`**).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP.LitDecode

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_append value_lt)
open NearCubicWires.SourceInterfaces

/-! ## Pure facts -/

theorem value_bits (n : ℕ) : value n.bits = n := by
  refine Nat.binaryRec' (by simp [value]) (fun b m hm ih => ?_) n
  rw [Nat.bits_append_bit m b hm]
  simp only [value, ih]
  cases b
  · simp [Nat.bit]
  · simp [Nat.bit]; omega

theorem rtb_off (pre r : List Bool) (k : ℕ) : readTapeBit (pre ++ r) (pre.length + k) = readTapeBit r k := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    rw [List.cons_append, List.length_cons, show pre.length + 1 + k = (pre.length + k) + 1 by omega]
    exact ih

theorem rtb_off0 (pre r : List Bool) : readTapeBit (pre ++ r) pre.length = readTapeBit r 0 := by
  simpa using rtb_off pre r 0

variable {ns nr : ℕ} {cap : ℕ}

/-! ## One marked bit -/

theorem setv_setv (σ : WState ns nr) (r : Fin nr) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  apply WState.eq <;> try rfl
  funext q; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl

/-! ## Framed words -/


/-! ## A counted run of marked bits -/

/-! ## The literal decoder -/

/-! ## Cost classes (rule M4) -/

theorem bits_len_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self

end NearCubicGates.Close.CheckedPCPP.LitDecode
