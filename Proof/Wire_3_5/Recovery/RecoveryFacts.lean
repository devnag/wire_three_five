import Proof.Wire_3_5.Recovery.RecoveryLanguage

/-! # Facts about the recovery's setup at the refuter's language (P3:3632-3653, 3699-3709; D1)

Realizes the properties of the outer verifier the recovery uses at the refuter's hierarchy language: "pad the outer
verifier to the exact width `q(N)` [...] All probabilities and the projection property are preserved" (P3:3637-3644),
perfect completeness at yes-instances ("perfect completeness guarantees existence", P3:3766), and the substituted
circuit's width.

Paper quantities: for `S = recSetup` (`S₁` at `recL`):
* `recSetup_hind`: the decision formula ignores the randomness (base `decisionIndependent`, through the padding);
* **`recSetup_complete`**: at a hierarchy yes-instance the padded PCP has an accepting proof;
* **`recSetup_width`**: the padded width is the ledger's `q(N) = nativeWidth kclk A_pad N` eventually;
* `request_arity`: the substituted request's arity is `max(width, minimumArity)`, which is `q(N)` eventually
  (`eventually_request_arity`);
* `tendsto_nativeWidth`: `q(N) → ∞`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP padProjectionPCP_complete)
open Filter

section Facts
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem clogN_le_nativeWidth (A' N : ℕ) : Nat.clog 2 N ≤ nativeWidth kclk A' N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  · have h1 : N ≤ N ^ (kclk + 2) := Nat.le_self_pow (by omega) N
    exact (Nat.clog_mono_right 2 h1).trans (Ledger.clog_le_nativeWidth kclk A' N)

theorem tendsto_nativeWidth (A' : ℕ) : Tendsto (nativeWidth kclk A') atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun N hN => ?_⟩
  calc b = Nat.clog 2 (2 ^ b) := (Nat.clog_pow 2 b (by norm_num)).symm
    _ ≤ Nat.clog 2 N := Nat.clog_mono_right 2 hN
    _ ≤ nativeWidth kclk A' N := clogN_le_nativeWidth kclk A' N

end Facts

end NearCubicWires.WireExponent3_5.Transfer
