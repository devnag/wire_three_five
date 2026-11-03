import Proof.Wire_3_5.Primitive.Writers.HashFamBase
import Proof.Wire_3_5.Primitive.Writers.HashReady4

/-! # PA2: the HASH writer's family budgets over the v4 data stage

`HashFam`'s run and budget (`hash_fam_run`, `hash_fam_cost`, at the base constants `HB`) with the v4 data stage
(`ThrData.ThrDataStage4`): the machine `hashM4` (the v4 shell `ShellT.shellMGH4` with PA's HASH unit), the run
through `ShellT.hash_ready4`; the data stage's `cost3`, `need`, `Cc3`, `Dc3`, `Kn`, `Dn` are v3's verbatim, so every
numeric step is `HashFam`'s.

* `hashM4`, **`hash_fam_run4`**, **`hash_fam_cost4`**.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline

/-- **The HASH writer's machine over the v4 data stage** at the base constants. -/
noncomputable def hashM4 {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (S : ThrData.ThrDataStage4 alg Dexp capT) (W : PrimT.WalkBank.WalkBankProducer) (FS : FiltSetup.FiltSetupSpec5 W)
    (h : HB) :=
  ShellT.shellMGH4 S W.x (CellUnit.unitM W (SymDec.hdecW W FS h.cr)) h.D h.Kr h.D2 h.C2 3 h.Cv 1 5
    (NumsXH.numsMH 0 h.KH h.cr)

section Run
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.HashCall NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.Records

end Run

/-! ## The budget's class link -/

section Cost
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive


end Cost

end NearCubicWires.WireExponent3_5.PrimAsm.HashFam
