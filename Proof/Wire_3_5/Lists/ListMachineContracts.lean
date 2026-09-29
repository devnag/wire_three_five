import Proof.Wire_3_5.Lists.ListMachineNormal
import Proof.Wire_3_5.Foundations.Contracts

/-! # C2d: the machine contract of the repaired count list (P3:1419-1488), with its certified reference

Realizes the C2 sub-contract for `list:repair`'s explicit lists (P3:1482-1488): "The explicit monomial lists have at
most `2^{O((Σ_j H_j) log(M+2))}` occurrences and are constructible within that bound times a polynomial in the
description size." The machine reads a finite list description (`ListTable`: the output range `M`, the depth `J`, the
population `L`, the windows `W_j`, and the level-membership table of the nested hash, C2a's output) and prints the
repaired states `P_0, …, P_M` (P3:1463-1477) as reduced monomial lists.

Main quantities: `ListTable.printed` (the reference output, `Ref.stateRefN` at `s = 0, …, M`), `ListTable.Correct`
(the error field, the P3 type anchor: every printed state IS the paper's `P_s` on every Boolean input, of degree at
most `Σ_{j<J}(H_j − 1)`, on the population's coordinates only, with at most `(L+1)^{Σ_j(H_j−1)}` monomials),
`encodePolys` (the output tape encoding), and the contract **`c2d`** (class `preprocessing`, P3:3108). Result:
**`printed_correct`**, the `Certified.err` field of `c2d`: the reference meets the error field on every admissible
request. A useless output (for example the unrepaired recurrence) fails `Correct` (see `mut/`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.ListMachine.Ref Finset

/-- The finite list description the C2d machine reads (the nested hash as its level-membership table). -/
structure ListTable where
  /-- the states are `P_0, …, P_M` -/
  M : ℕ
  /-- the depth `J` -/
  J : ℕ
  /-- the population: coordinates `Z_0, …, Z_{L−1}` -/
  L : ℕ
  /-- the windows `W_0, …, W_{J−1}` -/
  windows : List ℕ
  /-- `cells[j][i]`: coordinate `i` lies in `𝓛_j` (`j ≤ J`) -/
  cells : List (List Bool)

namespace ListTable

end ListTable

/-! ## Tape encodings -/

end NearCubicWires.WireExponent3_5.ListMachine
