import Proof.Circuits.CallableRelocation

namespace NearCubicWires.AmbientLinkEntry

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The linked program's register span -/

/-! ## 2. The first stage at an ambient register background -/

def firstStageStateAt (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) : NPOracleState where
  pc := layout.firstBase + state.pc
  registers := fun candidate =>
    if candidate < layout.firstSpan then state.registers candidate
    else ambient candidate

@[simp] theorem firstStageStateAt_pc (layout : LinkLayout) (ambient : ℕ → ℕ)
    (state : NPOracleState) :
    (firstStageStateAt layout ambient state).pc =
      layout.firstBase + state.pc := rfl

/-! ## 3. The reset block as an equation -/

/-! ## 4. The linked program at an arbitrary entry state -/

end NearCubicWires.AmbientLinkEntry
