import Proof.Wire_3_5.Assembly.ThrStage3
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.WalkStage

/-!
# The thr leaf's closure join

The thr leaf's finish term, stated from EXACTLY the producers still open at 09-28, with every other
argument supplied by verified code: the v4 data stage `thrStage4U` (PrimTTS4W), the unit machines `thrUnitOf5`
at the walk bank `walkBank`, C6's FILTER setup `fsSpec` and pipe bound `filtPipe_le2`, and the RADIX
setups as a uniform family `radStage` (RadSetupRun). The open producers, one binder each:

* `tail`: THRTAIL, the THR writer's leaf from the unit machines v4 (`ThrLeafOfU4`: T-A's dimension stage
  `ThrDim.thrDimStage_of` with T-A2's bounds, the T-B run and class link, the dock), with the pre-link available;
* `xF`, `hx`: the unit cells (at least the walk bank's streams);
* `dec`: the decode fronts as a uniform family at the cells `xF`.

The finish instantiates `thrClose` at the producers once they are verified. Paper quantity of the main type: the THR
tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3011-3016, 3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrClose

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The thr leaf from exactly its open producers.** -/
noncomputable def thrClose
    (tail : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → UnionMachine.ThrUnit.ThrLeafOfU4 l)
    (xF : ∀ l : Literals, GateFree l → ℕ) (hx : ∀ (l : Literals) (F : GateFree l), UnionMachine.WalkStage.walkBank.x ≤ xF l F)
    (dec : ∀ l : Literals, FinalPass.Seams.StageU l (fun F _ _ _ _ _ => UnionMachine.ThrDec.ThrDecFront (xF l F) l F)
      (fun D => UnionMachine.ThrUnit.decDeg D) (fun D => UnionMachine.ThrUnit.decCf D)) :
    ThrStage3.StageT :=
  fun l pre => tail l pre (PrimT.TS4.thrStage4U l)
    (UnionMachine.ThrUnitOf.thrUnitOf5 l UnionMachine.WalkStage.walkBank (xF l) (hx l)
      (UnionMachine.FsSpec.fsSpec UnionMachine.WalkStage.walkBank) UnionMachine.FiltPipeLe.filtPipe_le2 (dec l)
      (UnionMachine.RadSetupRun.radStage l (xF l)))

end NearCubicWires.WireExponent3_5.ThrClose
