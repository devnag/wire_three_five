import Proof.Wire_3_5.Assembly.FreeRecovery
import Proof.Wire_3_5.Recovery.HybridLeafOk

/-! # Leaf R with free constants for union leaves with the atom test, from D1.6

"By Lemma tr:soundness this machine is one-sided. Once its clock is `o(T(N))`, the refuter consequently returns a
rejected hierarchy yes-instance" (P3:3699-3701), for the union machine that "rejects … oversized atoms" (P3:3670), whose
completeness is at the accepting guesses passing the atom test (`UnionLeafAt2`). D1.6's input `CertGen l` quantifies over
machines only, so it is UNCHANGED:
* `Cert2AtOk l F` (the certificate at the machine of a `UnionLeafAt2`), `recoveryLeafF2_of_cert2`;
* `cert2AtOk_of_certGen` (the clock bound from the leaf's `tr:time`, `Runtime3.littleO`);
* **`recoveryLeafF2_of_certGen : CertGen l → RecoveryLeafF2 l`**;
* `literals_parts_of_certGen2`: `Parts` from leaves P, U (with the atom test) and D1.6.

Paper quantity of the main type: leaf R (the recovered language, its `E^NP` certificate, both hardnesses). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Transfer

variable (l : Literals)

/-- **D1.6 at the concrete gate** for the union machine of a leaf with the atom test. -/
def Cert2AtOk (F : GateFree l) : Prop :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (U : UnionLeafAt2 ((gate0 l F).inputs kclk coef A a ha) (setupF l F kclk coef A a ha))
    (P : FusedPrimitive ((gate0 l F).inputs kclk coef A a ha)),
    ∃ cutoff : ℕ, Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
      (recLanguageCut2 l (gate0 l F) kclk (recMachine2Ok l (gate0 l F) U P) cutoff))

/-- **Leaf R from D1.6** at every choice of the free constants, for union leaves with the atom test. -/
noncomputable def recoveryLeafF2_of_cert2 (cert : ∀ F, GateFreeOK l F → Cert2AtOk l F) : RecoveryLeafF2 l :=
  fun F hF => recoveryLeaf2Ok l (gate0 l F) (gateRel_gate0 l F) (cert F hF)

/-- The F-free certificate gives `Cert2AtOk` at every choice of the free constants: the machine's clock bound is the
union leaf's `tr:time` through `Runtime3.littleO`. -/
theorem cert2AtOk_of_certGen (h : CertGen l) (F : GateFree l) : Cert2AtOk l F := fun kclk _ _ _ _ U P =>
  h kclk (recMachine2Ok l (gate0 l F) U P) (U.toUnionConstruction.runtime3 P (recL l kclk)).littleO

/-- **Leaf R from the F-free D1.6**, for union leaves with the atom test. -/
noncomputable def recoveryLeafF2_of_certGen (h : CertGen l) : RecoveryLeafF2 l :=
  recoveryLeafF2_of_cert2 l fun F _ => cert2AtOk_of_certGen l h F

end NearCubicWires.WireExponent3_5.Split
