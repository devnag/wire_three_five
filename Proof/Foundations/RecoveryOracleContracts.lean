import Proof.Foundations.RecoveryOracleSemantics

/-! Actual ordinary-oracle execution and the LOCAL recovery realization targets.
Finite query-control rules extend the existing local finite-tape machine. A
query is made from head zero on its fresh query tape; the framed query's
literal length plus one is charged. This conservative query convention is
polynomially equivalent to ordinary SAT-oracle time and is used only in the
refuter/recovery branches, never to justify the ordinary fast competitor.
-/
namespace NearCubicWires.RepairSource
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true









/-- Literal ordinary exponential time with an NP oracle. The max convention
only fixes the finite zero-length cost; it changes no asymptotic class. -/
def OrdinaryInENP (language : Language) : Prop :=
  ∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
    Nonempty (OrdinaryENPCertificate oracle language)

theorem OrdinaryOracleRuns.enlarge {oracle : ℕ → Bool} {program : OrdinaryOracleProgram}
    {input output : List Bool} {budget larger : ℕ}
    (run : OrdinaryOracleRuns oracle program input output budget) (h : budget ≤ larger) :
    OrdinaryOracleRuns oracle program input output larger := by
  obtain ⟨cost, final, hcost, trace, halted, result⟩ := run
  exact ⟨cost, final, hcost.trans h, trace, halted, result⟩

end NearCubicWires.RepairSource
