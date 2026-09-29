import Proof.Wire_3_5.UnionMachine.RadSetupB5
import Proof.Wire_3_5.UnionMachine.ThrUnitIface

/-! # The producer statement over the RADIX setup v5 (follow-up)

`ThrUnit.ThrUnitOf2` takes the RADIX setups as `RadSetupB4.RadSetupSpecB4`, whose measure misses the star row at
`G = 0`; the v5 setup `RadSetupB5.RadSetupSpecB5` adds it. The consumer types (`ThrUnitSpec2`, `ThrUnitU2`,
`ThrLeafOfU2`) are unchanged.

* `radDeg5`, `radCf5`, **`ThrUnitOf3 l`**: the uniform decode fronts, the uniform RADIX setups v5, the FILTER setup and its
  pipe bound give the unit machines v2.

Paper quantity of the main type: the THR tape's units within the preprocessing class `2^{O(Ψ)}` (P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

/-- The RADIX setup v5's exponents and coefficients. -/
def radDeg5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ :=
  max (max R.Dn R.Db) R.Dp

def radCf5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ := R.Kn + R.Kb + R.Kp

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
