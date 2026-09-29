import Proof.MachineModel.Machine

/-! The original incidence machine with a retained false prefix on its
physically produced row counter. The machine is unchanged; this strengthens
its configuration invariant to the normalizer's ready counter encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeMaskCount
open NearCubicWires NearCubicWires.ExtIncidence
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
abbrev machine := ExtIncidence.machine

@[simp] theorem halted_six : machine.halted 6 = true := rfl

/-! ## One transition per rule branch. Input reads are stated by the scanned bit. -/


/-! ## Reading inside appended words -/

/-! ## Loops -/

/-! ## One block, all blocks of a monomial, one monomial -/

/-! ## The whole ordered stream -/

/-! ## Coarse cost: linear in the stream length, times the child count -/


end PCJ9eff70d512234a4c_Fixed.Materializer.NativeMaskCount
