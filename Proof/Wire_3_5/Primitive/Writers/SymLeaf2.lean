import Lean
import Proof.Wire_3_5.Primitive.Writers.SymLeaf
import Proof.Wire_3_5.Primitive.Writers.SymFamRun2
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymFamCost
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.PopSetupSpecB2
import Proof.Wire_3_5.Primitive.Writers.SymFamRun2Base
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (POP setup): the SYM writer's leaf over `PopSetupSpecB2`

**`symLeaf2 : SymLeafOf2 l`**: `SymLeaf.symLeaf` with the POP setup `Q : PopSetupSpecB2 W` (the need's measure reads
the row offset `r4`): the same floors (`sbE2 … .EW`, `1`), coefficient (`sbF2 … .cWr`), the machine
`SymFam.symWM2`, the run `sym_fam_run2` within `c_W·classBound` (`sym_fam_cost`, which reads no POP setup field).

* `sbF2`, `sbE2`, `sbF2_cpsi`; **`symLeaf2`**.

Paper quantity of the main type: the SYM tape `symTape` (C4's `BAT` word of the call, P3:3011-3016) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

variable (l : Literals) {W : PrimT.WalkBank.WalkBankProducer} (FS : FiltSetup.FiltSetupSpec5 W)
  (Q : PopSetup.PopSetupSpecB2 W) (hfp : BudgetIface.FiltPipeLe2) (hpp : PopPipeLe)

/-- **All the base constants** (after `F`), over `PopSetupSpecB2`. -/
noncomputable def sbF2 (F : GateFree l) : SB :=
  ⟨wbC, wbD, nwC, nwD, Data.symCc, Data.symDc, FS.Cn, FS.Dn, FS.Cb, FS.Db, Q.Kn, Q.Dn, Q.Kb, Q.Db, fpK hfp, fpD hfp,
    ppK hpp, ppD hpp, CallIndexR.capZR l, 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32, gateCsp l,
    SymSizes.schedJ l, SymSizes.cXg l, SymSizes.KLam l, CallIndexR.capK F.cr, F.cr, F.filterErrDeg,
    CapNum.cMain (gateCap l) .sym⟩

/-- **The exponents** (with the floors: `capK`, `c_r`, `fe` not yet chosen). -/
noncomputable def sbE2 : SB :=
  ⟨wbC, wbD, nwC, nwD, Data.symCc, Data.symDc, FS.Cn, FS.Dn, FS.Cb, FS.Db, Q.Kn, Q.Dn, Q.Kb, Q.Db, fpK hfp, fpD hfp,
    ppK hpp, ppD hpp, CallIndexR.capZR l, 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32, gateCsp l,
    SymSizes.schedJ l, SymSizes.cXg l, SymSizes.KLam l, 0, 0, 0, CapNum.cMain (gateCap l) .sym⟩

/-- The budget's exponent reads the exponents only: `c_ψ` of the floor envelope covers every `F`. -/
theorem sbF2_cpsi (F : GateFree l) :
    (sbF2 l FS Q hfp hpp F).Etot * SymSizes.cSOf (sbF2 l FS Q hfp hpp F).Z 26 ≤ (sbE2 l FS Q hfp hpp).EW.cpsi := by
  rw [SB.Etot_eq (sbF2 l FS Q hfp hpp F) (sbE2 l FS Q hfp hpp) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
  exact le_refl _

/-! ## The leaf -/

/-- **The SYM writer's leaf over `PopSetupSpecB2`.** -/
noncomputable def symLeaf2 : SymLeafOf2 l := fun W FS Q hfp hpp _fe =>
  ⟨(sbE2 l FS Q hfp hpp).EW, 1, fun F _hF _hE hCD =>
    ⟨(sbF2 l FS Q hfp hpp F).cWr, fun kclk coef A a ha =>
      { t := _
        s := _
        M := symWM2 l F W FS Q (sbF2 l FS Q hfp hpp F)
        inS := _
        outS := _
        hio := ShellX.shellInX_ne_out
        ready := fun n a' ha' Cs carriers translation hcall hs => by
          refine WritersJoin.writerRun_mono (sym_fam_run2 l F kclk coef A a ha W FS Q (sbF2 l FS Q hfp hpp F)
            rfl rfl rfl rfl rfl rfl rfl rfl wb_spec nw_spec (fp_spec hfp) (pp_spec hpp) rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl ha' Cs carriers translation hcall hs) ?_
          exact sym_fam_cost l F kclk coef A a ha (sbF2 l FS Q hfp hpp F) wb_spec nw_spec rfl rfl rfl rfl rfl rfl rfl rfl
            hCD _ (sbF2_cpsi l FS Q hfp hpp F) ha' Cs carriers translation hcall hs }⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf

end
