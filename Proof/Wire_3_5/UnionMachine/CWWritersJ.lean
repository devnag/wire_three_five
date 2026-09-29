import Proof.Wire_3_5.UnionMachine.CWParReady
import Proof.Wire_3_5.UnionMachine.CWThr
import Proof.Wire_3_5.UnionMachine.CWConst

/-! # C6 front, U5, the code writers: the three writers of both class modes

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094), and the union call names its carriers: the union front writes, per variable, the codes of
the calls' named carriers, of the encoding parity atom and of the constant atom. **`writersJ : CWIface.WritersJ`**:
the carrier writers (`CWThr.carrierWriters`), the parity writers (`CWParReady.parityWriters`) and FP's constant
writers (`CWConst.constWriter`), for both class modes.

Paper quantity of the main type: the codes of the calls' named carriers and of the setup's atoms. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWWritersJ

/-- **The three writers for both class modes.** -/
noncomputable def writersJ : CWIface.WritersJ where
  carrier := CWThr.carrierWriters
  parity := CWParReady.parityWriters
  const := CWConst.constWriter

end NearCubicWires.WireExponent3_5.UnionMachine.CWWritersJ
