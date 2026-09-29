import Proof.CaseAnalysis.WitnessSourceSize

/-! The exact coefficient policy needs the bit length of its cap, not the
numeric power of two. Reuse the checked dyadic shift and fixed polynomial
producer; the remaining clause-bit addition is performed once per source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def factor (delta : ℚ) (copies : ℕ):=64*delta.den^(3*copies+2)

end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
