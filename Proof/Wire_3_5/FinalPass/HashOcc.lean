import Lean
import Proof.Wire_3_5.FinalPass.HashPre1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashOccBase


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH printer's occurrence count against `Ψ_aux` (the numbers)

alg:eq-occurrences (P3:1887-1888) at the HASH child request: the charged occurrence count
`max(1,A)·2^m·Q'(P_ex+1)^{Q'd}` is at most `2^{log A + m + Q' + Q'd·log(P_ex+1)}` (**`occP_le_of`**, generic in the
request), and at a HASH call (`log A ≤ k + c_V X²`, `m = 2t + 1`, `Q' = d_Q(L³ + k + L)`, `d = d_D L²`,
`log(P_ex+1) ≤ k + c_{Da} L`) this exponent is at most `C₁·S_aux` with `S_aux = k + L² + (k+L³)L²(k+L)` the auxiliary
load's factor (`Ψ_aux = C_D·S_aux`, P3:3101-3102) (**`occS_num`**).

Paper quantities of the main types: the HASH child request's occurrence count against `Ψ_aux`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine

/-- The HASH budget's linear constant. -/
noncomputable def C1H (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) (c : FinalPass.SymFr.SymC) : ℕ :=
  4 * cV l + 4 * cT l + 3 * c.dQ + 2 * c.dQ * c.dD * (FinalPass.SymFr.cDa alg + 1) + 3

/-- **The load-constant floor of the HASH printer's budget** (chosen before `F`). -/
noncomputable def occCDH (l : Literals) (alg : RepairRepresentation.DecompositionAlgorithm) (c : FinalPass.SymFr.SymC) : ℕ :=
  160 * C1H l alg c + 2

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
