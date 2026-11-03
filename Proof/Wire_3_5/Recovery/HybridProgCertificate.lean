import Lean
import Proof.Wire_3_5.Recovery.HybridLeaf
import Proof.Wire_3_5.Recovery.RecoveryBudget
import Proof.Wire_3_5.Stage35.Common
import Proof.Wire_3_5.Stage35.KitMain
import Proof.Wire_3_5.Stage35.ExecCost


/-!
# The recovered language is in `E^NP` (the recovery leaf's certificate)

Paper v2, §H.6 "Exact lengths and canonical recovery": "The resulting slice is computable in `E^NP`. Run the fixed
refuter to obtain `z`, and then make the case decision of §H.5 in three stages. Each stage is a SAT query of size
`2^{O(q)}` followed by prefix self-reduction […] No formula contains the algorithm `A_G`. […] Since `q = O(n)`, this is
`2^{O(n)}` overall." (stages in the near-cubic-wires order: source circuit, first accepted oracle `O*`, proof circuit
with `O_{B_pf} = O*`).

At the literals `l`: the composed program (`NearCubicGates.Close.Recovery3.Common.existsCertificate` at `ws l`: this
proof's scan prefix and the after-prefix program) with the Case-2 kit (`Stage35.KitMain.kit_of`: the Case-2
execution with the XOR schedule `t(q)+1`, the clause bound at `d_G` from `clauseBits_le`). The execution's cost class
(`ExecCost.FoldNeedCap`, `ExecCost.HtwoCostPoly`) is the input `CostAt l`.

* `certGen_of_cost : CostAt l → Split.CertGen l`, `costAt l : CostAt l` (`Stage35.ExecCost`), and
  **`certGen : ∀ l, Split.CertGen l`**.
-/

set_option autoImplicit false


namespace NearCubicWires.RepairSource.HybridProgram
open _root_.NearCubicWires _root_.NearCubicWires.RepairSource _root_.NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open _root_.NearCubicWires.WireExponent3_5.Transfer (zu zv)

/-- The Case-2 execution's cost class at the literals `l` (the budget statements of `Stage35.ExecCostSpec`). -/
def CostAt (l : Literals) : Prop :=
  Stage35.ExecCost.FoldNeedCap (gateMW l) (gateSV l) (gatePCPP l) (oracleDeg l) (recDG l) ∧
  ∀ e1 e2 e3 e4 : ℕ, Stage35.ExecCost.HtwoCostPoly (gateMW l) (gateSV l) (gatePCPP l) (oracleDeg l) (recDG l) kclk
    (gateApad l) (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) e1 e2 e3 e4

theorem recDG_pos (l : Literals) : 1 ≤ recDG l := by unfold recDG; omega

/-- **D1.6 from the cost class**: the recovered language is in `E^NP` at every weak machine within `o(N^{kclk+2})`. -/
theorem certGen_of_cost (l : Literals) (hc : CostAt l) : Split.CertGen l := by
  intro M hM
  have hkit := Stage35.KitMain.kit_of (gateMW l) (gateSV l) (gatePCPP l)
    l.eightSources.amplification.schedule (recDG l)
    (gateZeta_pos l) (gateZeta_lt l) (recDG_pos l) (clauseBits_le l) hc.1 hc.2
  obtain ⟨kit⟩ := hkit
  obtain ⟨onset, -, hcert⟩ := NearCubicGates.Close.Recovery3.Common.existsCertificate (ws l) (gatePCPP l)
    l.eightSources.amplification.schedule (recDG l) (gateZeta_pos l) (gateZeta_lt l) (recDG_pos l) kit 0 M hM
  exact ⟨onset, hcert⟩

/-- The cost class holds at every literal set (`Stage35.ExecCost`). -/
theorem costAt (l : Literals) : CostAt l :=
  ⟨Stage35.ExecCost.foldNeedCap _ _ _ _ _,
    fun e1 e2 e3 e4 => Stage35.ExecCost.htwoCostPoly _ _ _ _ _ _ _ _ _ e1 e2 e3 e4⟩

/-- **`CertGen l`**, the recovery leaf's certificate: the recovered language is in `E^NP` at every weak machine within
`o(N^{kclk+2})`. -/
theorem certGen (l : Literals) : Split.CertGen l := certGen_of_cost l (costAt l)

end NearCubicWires.RepairSource.HybridProgram

