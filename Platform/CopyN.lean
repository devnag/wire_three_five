import Platform.Arr
import Platform.OutX

/-! # Copy a range of records by index

**`copyN A Wk O …`**: append records `c₀, …, c₀ + K − 1` of the record stream on `A` (any tail) to the output
stream `O`, the cursor register `CUR` advancing from `c₀` to `c₀ + K` (`copyN_spec`). Built from `getAt` (read by
index) and `appendRec`. Cost `K · (copyStep L N + 8) + 7K + 3`, `N` the record count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StablePartition.Workspace (overlay)

end NearCubicGates.Close.Platform
