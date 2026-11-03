import Recovery.C1Sem
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/C1Sem.lean with the copies schedule (Stage35.WQ).

/-!
# Case 1 semantics: both hard functions are cyclic tables ((a′) form)

the near-cubic-gates paper's extraction of the hard table (three-way Case 1, decision F2): (i) `X_z` (`WQ.srcFn`) and (iii) `O*` (`Transfer.pfFn`) are
`cycFn` instances (`srcFn_eq`, `pfFn_eq`), so `gateCore`'s two Case 1 values are the amplified padded `cycFn`
(`gateCore_caseOne_i`, `gateCore_caseOne_iii`; the uniform recovery "run the general amplifier"). `table_cycFn`: the truth table of
`cycFn a w q` (low address bit first, `boolFunctionTable`) is `w` read cyclically, `2^q` entries — what the Case 1
machine writes before calling the amplifier.
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.C1Sem

open Stage35 _root_.NearCubicGates.Close

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces NearCubicGates.Close.Transfer NearCubicGates.Close.Recovery
open NearCubicGates.Close.Gadget

open NearCubicGates.Close.Recovery.C1Sem

/-- Case 1 (i): `X_z` is the cyclic function of `z`. -/
theorem srcFn_eq (s : WS35) (g : WQ) (ν : ℕ) (z : BitInput (2 ^ ν)) :
    g.srcFn s ν z = cycFn ν z (g.width s ν) := by
  funext r
  unfold WQ.srcFn W3.NearCubicWires.RepairSource.Outer3.srcFn cycFn
  congr 2
  funext j
  rw [dif_pos (lt_of_lt_of_le j.isLt (g.nu_lt_width s ν).le)]
  rfl

/-- **Case 1 (i)** (the near-cubic-gates paper's extraction of the hard table–the uniform recovery): without a CHECK-passing source circuit, the gate core is the amplified
padded cyclic function of the source input `z`. -/
theorem gateCore_caseOne_i (s : WS35) (g : WQ) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) {c : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c g.degree) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h : ¬g.SrcExists s ν z) :
    g.gateCore s P amplifier ν z cl pl target =
      Transfer.GateParams.amplified amplifier (g.width s ν) (cycFn ν z (g.width s ν)) target := by
  unfold WQ.gateCore W3.NearCubicWires.RepairSource.Outer3.coreC
  rw [dif_neg h, ← srcFn_eq]

/-- **Case 1 (iii)** (the near-cubic-gates paper's extraction of the hard table–the uniform recovery): with `B*_src` and `O*` but no `q^G`-gate circuit answering as `O*`, the gate
core is the amplified padded cyclic function of the first honest table `O*`. -/
theorem gateCore_caseOne_iii (s : WS35) (g : WQ) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) {c : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c g.degree) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl pl target : ℕ)
    (h1 : g.SrcExists s ν z) (h2 : g.AcceptedOracle s ν z h1)
    (h : ¬g.IsCaseTwo s ν z) :
    g.gateCore s P amplifier ν z cl pl target =
      Transfer.GateParams.amplified amplifier (g.width s ν)
        (cycFn _ (Classical.choice (existsFirstTable _ h2)).table (g.width s ν)) target := by
  unfold WQ.gateCore W3.NearCubicWires.RepairSource.Outer3.coreC
  rw [dif_pos h1, dif_pos h2]
  simp only []
  rw [dif_neg h]
  rfl

/-- **The Case 1 fit** (the near-cubic-gates paper's uniform recovery: "pad the function in either case to exactly `m(q) = K_amp q₀(q)` inputs"):
with `copies(q) ≥ a_G` (`AfterReady.ampLarge`, past its onset), the amplified function on `q = q(N_ν)` inputs has at most `m(q)`
(`WQ.coreArity`) inputs, so it fits every final length `n ≥ m(q)`. -/
theorem arity_fit (s : WS35) (g : WQ) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (ν : ℕ) (hK : amplifier.arityCoefficient ≤ g.copies (g.width s ν)) (f : BoolFunction (g.width s ν)) :
    (amplifier.output (g.width s ν) f).arity ≤ g.coreArity s ν := by
  have hq : 1 ≤ g.width s ν := by have := g.nu_lt_width s ν; omega
  refine (amplifier.arityBound _ f hq).trans ?_
  unfold WQ.coreArity WQ.tableArity
  exact Nat.mul_le_mul hK (by omega)

end NearCubicGates.Close.Recovery3.C1Sem

