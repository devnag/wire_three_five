import Proof.CaseAnalysis.RowsSharedInput

/-! Coarse preparation bounds for the actual positional enumerator and
cut consumer. Only the digit exponent contains the monomial population;
native cache and matrix widths occur polynomially outside that exponent. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scale (n p F w N Q : ℕ) := n+p+F+w+N+Q+1
def capacity (n p F w N Q : ℕ) :=
  4096*(scale n p F w N Q)^4*2^(w*(Q+1))

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationBounds
