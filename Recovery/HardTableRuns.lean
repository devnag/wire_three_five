import CheckedPCPP.Composite
import Proof.MachineModel.ClockJoin
import Proof.Foundations.OuterPCPRecovery

/-!
# The Case 2 producer (`HardTableRuns`), (a′) form

The near-cubic-gates paper's uniform recovery (sec:all-lengths, "all canonical choices are recoverable in E^NP"): "In the small-oracle branch, the
honest PCPP proof and each AND helper are computable in polynomial time once the oracle is known" — after the (a′)
repair (the extraction of the hard table, canonical Case 2 of the three-way split; coordinator decision F2) the "oracle" is the selected pair
`B* = (B*_src, B*_pf)`: `B*_src` the first CHECK-passing source circuit, `O*` the first honest oracle of
`C_{⟨B*_src⟩_ν}`, `B*_pf` the first `q^G`-gate circuit answering as `O*` (`Transfer.GateParams.selectedPair`). The E^NP
program holds, for a Case 2 source input `z`, exactly the five words of `portInput`:
* port 0: the word of `C_{⟨B*_src⟩_ν}` that the imported constructor returns (`CheckedPCPP.mwWord`, imp:short-pcp);
* port 1: the framed canonical description of `B*_pf` (stage 3's prefix self-reduction, proof 1's canonical order);
* port 2: the framed final address; ports 3, 4: `1^q` and `1^B` (`q = q(N_ν)`, `B = oracleSizeBound G q`).
One fixed machine started there returns the Case 2 value of `gateCore` at the address: the padded five-entry hard table
of `D_{B*}` (J9, `Transfer.hardTable`; the near-cubic-gates paper's extraction of the hard table, "Substituting `O_{B_pf}` for every oracle gate and negating the output
gives the outer verifier ... Apply imp:three-pcpp").

Seam (GR's common program): the producer is used only through its tape count, its machine, the five input
ports `j ↦ j` and one output port of index at least `5`; every non-port tape starts empty; the run is a
`ClockJoin.ReadyRun` within `C·(2^n+1)^E`; the output port holds the framed bit.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicGates.Close.Gadget
open NearCubicGates.Close.Transfer

/-- The five input words of the Case 2 producer: the word of `C_{⟨B*_src⟩_ν}`, the recovered description of `B*_pf`,
the final address, unary `q`, unary `B`. -/
def fiveWords (word description address : List Bool) (R B : ℕ) : Fin 5 → List Bool :=
  ![word, description, address, List.replicate R true, List.replicate B true]

/-- The producer's entry bank: the five words on the ports `j ↦ j`, every other tape empty. -/
def portInput (t : ℕ) (word description address : List Bool) (R B : ℕ) : Fin t → List Bool :=
  fun i => if h : i.val < 5 then fiveWords word description address R B ⟨i.val, h⟩ else []

end NearCubicGates.Close.Recovery
