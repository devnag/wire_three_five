import Proof.MachineModel.OrdinaryWitnessPrefixBody

/-! The bounded witness loop consumes precisely B supplied bits, with a
small binary comparison per bit. Its source suffix is retained and unread. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefixLoop
open LocalBitMultitape
open RecordController (code test stop)
open WitnessPrefixBody (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.WitnessPrefixLoop
