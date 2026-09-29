import Proof.Supplier.EquationHeaderBoot

/-! Actual weight-count production from the parsed d template and odd bit.
The result is the sentinel driver for 2*d-odd.toNat. -/
namespace NearCubicWires.RepairOrdinary.EquationWeightCount
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bs =>
    if q.val=0 then some ⟨1,![none,none,some false],![.right,.stay,.right]⟩
    else if q.val=1 then some
      (if bs 0 then
        if bs 1 then ⟨3,![none,none,some true],![.right,.stay,.right]⟩
        else ⟨2,![none,none,some true],![.stay,.stay,.right]⟩
      else ⟨4,fun _ => none,fun _ => .stay⟩)
    else if q.val=2 then some ⟨3,![none,none,some true],![.right,.stay,.right]⟩
    else if q.val=3 then some
      (if bs 0 then ⟨2,![none,none,some true],![.stay,.stay,.right]⟩
      else ⟨4,fun _ => none,fun _ => .stay⟩)
    else none

def ticks (n : ℕ) (odd : Bool) := 2*n+2-(if n=0 then 0 else odd.toNat)
def machine := Rewind.machine raw

end NearCubicWires.RepairOrdinary.EquationWeightCount
