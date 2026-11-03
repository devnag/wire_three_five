import Joins.Transfer
import CheckedPCPP.LitDecode

/-!
# R3.h9, the table bit as a function of words (the near-cubic-gates paper)

The padded hard table of J9 (`Transfer.hardTable`) at an address `(x, a, j)` reads clause `a mod 2^{rb}` of the J8
clause word and entry `j mod 5` of `(X_{a,1}, X_{a,2}, X_{a,3}, Y_a, Y_a)` under the honest assignment
`(sysEnc x, honest proof)`. `tableBit raw asg a j` computes that value from the clause list `raw` and the assignment
as a bit list `asg` (`hardTable_eq`); the producer's machine computes `tableBit`. `natOfBits_eq_value`: the address
fields are little-endian numbers (proof 1's `RadixSemantics.value`). `clog_eq_size`: the clause width
`clog 2 ((q+2)^d)` is the bit length of `(q+2)^d − 1`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.TableSem

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.CheckedPCPP.LitDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_append value_lt)

/-! ## Numbers -/

theorem clog_eq_size (v : ℕ) : Nat.clog 2 v = (v - 1).size := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_size_self (v - 1)
    omega
  · rw [Nat.size_le]
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp
    · have := Nat.le_pow_clog (b := 2) (by decide) v
      omega

/-! ## The table bit -/

/-! The old-world `gateCore_point` (proof 1's projection PCP, single oracle) is not used:
its only consumer, the Case 2 producer, proves the pair form in its own module. -/

end NearCubicGates.Close.Recovery.TableSem
