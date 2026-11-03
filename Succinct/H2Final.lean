import Succinct.H2Run
import Succinct.H2Pre
import Succinct.T8H2End
import Succinct.H2Post
import Succinct.L10Kind1
import Succinct.T8H2Dock

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

/-- `C`'s input nodes in the emission loop (the near-cubic-gates paper's fixed weak machine, `D_B`: an input gate of `C` is copied). -/
theorem kind1OK (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) : Kind1OK (capH o B) o B :=
  fun _ _ _ h j hk => kind1 h j hk

theorem h2Run : H2RunSpec := h2Run_of preSpec (postSpec_of endOutSpec) costSpec kind1OK

theorem h2Ready : H2ReadySpec := h2Ready_of_run h2Run

end NearCubicGates.Close.Succinct.H2
