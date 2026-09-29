import Proof.MachineModel.CaseTwoBlockOccurrenceProgram

namespace NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CaseTwoBlockOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RuntimeLeftShiftProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The numeral packet and its accessors -/

/-! ## 2. The block window of the requested point code

Register ABI as in the frozen adapters, with `r15` the packet cursor: `r2` the
leading field of the request, `r3` its trailing field, `r4` the block arity read
from the packet, `r5` the assembled callee request. -/

/-! ## 3. The native occurrence code of one block window

The four adapters of the occurrence-code assembly, each reading its own
numerals from the packet.  Register `r15` is the packet cursor throughout and
`r16`/`r17` hold the two summands of a width that the frozen adapters carried
as a single immediate. -/

/-! ## 4. The occurrence call frame -/

/-! ## 5. The stages, unchanged except for their prologues -/

/-! ### The native occurrence code chain -/

/-! ## 6. The assembled per-block occurrence callee -/

/-! ## 7. Entering the callee at a computed packet

The callee of §6 runs at a packet-valued public length, while the Case-2 block
list calls its per-block parameter at the *target's* public length with the
bare `pair block pointCode`.  The three adapters below close that gap without
touching either ABI: reload the public length, run a packet producer on it,
frame the result as a native context call, and project the returned bit.  The
packet producer is a parameter here; §2 of the closure module supplies it. -/

end NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
