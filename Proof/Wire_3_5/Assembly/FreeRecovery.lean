import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Recovery.HybridLeaf

/-! # Leaf R of the split with free constants, from D1.6

Realizes the end of the transfer (P3:3740-3742, 3831-3852) at every choice of the gate's free constants: "By
Lemma tr:soundness this machine is one-sided. Once its clock is $o(T(N))$, the refuter consequently returns a rejected
hierarchy yes-instance" (P3:3699-3701), for the machine built at `gate0 l F`, and the recovered slice's `E^NP`
certificate. `recoveryLeaf2` needs the gate relation `GateRel` (true at `gate0 l F` for every
`F`, `gateRel_gate0`) and the certificate `cert2`; so leaf R needs no relation on `F`.

Paper quantities:
* **`Cert2At l F`**: the certificate of the recovered language `recLanguageCut2` for the union machine built at
  `gate0 l F`, i.e. `recoveryLeaf2`'s `cert2` at that gate. It depends on `F` only through the machine: the language
  reads the gate only through `A_pad` (`recLanguageCut2_gate0`, by `rfl`).
* **`CertGen l`**: D1.6 in a form free of `F`: for every clock and every weak machine within `o(T(N))`, a cutoff and
  an `E^NP` certificate of the recovered language at that machine (the refuter's program is correct on exactly such
  machines, `HierarchyRefuterAlgorithm.eventual`). `cert2At_of_certGen` gives `Cert2At l F` at every `F`, the clock
  bound coming from the union leaf's `tr:time` (`Runtime3.littleO`).
* `recoveryLeafF_of_cert2`, `recoveryLeafF_of_certGen`, and `rowB_of_leavesF_certGen` (row B from leaves P and U and
  D1.6). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Transfer

variable (l : Literals)

/-- **D1.6, free of the gate's free constants**: for every clock `N^{kclk+2}` and every weak machine within
`o(T(N))`, a cutoff and an `E^NP` certificate of the recovered language at that machine. -/
def CertGen : Prop :=
  ∀ (kclk : ℕ) (M : OrdinaryWeakMachine), OrdinaryLittleO M (fun n => n ^ (kclk + 2)) →
    ∃ cutoff : ℕ, Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
      (recLanguageCut2 l (gate0 l (freeSat l)) kclk M cutoff))

end NearCubicWires.WireExponent3_5.Split
