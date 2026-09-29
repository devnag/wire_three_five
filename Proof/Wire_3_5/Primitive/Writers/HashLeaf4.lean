import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.Writers.HashLeafIface4
import Proof.Wire_3_5.Primitive.Writers.HashFam4

/-! # The HASH writer's leaf over the v4 data stage

**`hashLeaf4 : HashLeafOf4 l`** ('s type): `HashLeaf.hashLeaf` with the v4 data stage family
(`ThrData.ThrStage4U l`): the same floors (`envMax E₀ E_H`, `max CD₀ 1`) and coefficient (`HB.cW`), the
machine `HashFam.hashM4` (the v4 shell on `STx + x3 + 1` tapes), the run `hash_fam_run4` within `c_W·classBound`
(`hash_fam_cost4`).

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline

/-- **The HASH writer's leaf over the v4 data stage.** -/
noncomputable def hashLeaf4 (l : Literals) : HashLeafOf4 l := fun SU W FS hfp hT fe =>
  ⟨envMax (SU fe).2.1 (hbE wbD nwD (tnD hT) (SU fe).1 (fpD hfp) FS.Dn FS.Db (CallIndexR.capZR l)).EW,
    max (SU fe).2.2.1 1, fun F hF hE hCD =>
    ⟨(hbF wbC wbD nwC nwD (tnK hT (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F) (tnD hT)
        ((SU fe).2.2.2 F hF (Plan.classLE_trans (Plan.classLE_envMax_left _ _) hE) (le_trans (le_max_left _ _) hCD)).1
        (SU fe).1 (fpK hfp) (fpD hfp) FS.Cn FS.Dn FS.Cb FS.Db (CallIndexR.capZR l)
        (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F.cr).cW,
      fun kclk coef A a ha =>
        { t := _
          s := _
          M := hashM4 (((SU fe).2.2.2 F hF (Plan.classLE_trans (Plan.classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).1 W FS
            (hbF wbC wbD nwC nwD (tnK hT (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F) (tnD hT)
              ((SU fe).2.2.2 F hF (Plan.classLE_trans (Plan.classLE_envMax_left _ _) hE) (le_trans (le_max_left _ _) hCD)).1
              (SU fe).1 (fpK hfp) (fpD hfp) FS.Cn FS.Dn FS.Cb FS.Db (CallIndexR.capZR l)
              (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F.cr)
          inS := _
          outS := _
          hio := ShellT.shellInX4_ne_out _ _ _ _ _ _
          ready := fun n a' ha' Cs carriers translation hcall hs => by
            obtain ⟨hdeg, hcf⟩ := (((SU fe).2.2.2 F hF (Plan.classLE_trans (Plan.classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2
            refine WritersJoin.writerRun_mono (hash_fam_run4 l F kclk coef A a ha _ W FS _
              (le_trans (le_max_left _ _) hdeg) (le_trans (le_max_right _ _) hdeg) (le_trans (Nat.le_add_right _ _) hcf)
              (le_trans (Nat.le_add_left _ _) hcf) rfl rfl rfl rfl wb_spec nw_spec
              (fun n hs a' Cs carriers capT h1 h2 h3 h4 =>
                tn_spec hT (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F kclk coef A a ha n hs Cs carriers capT
                  h1 h2 h3 h4)
              (fp_spec hfp) rfl rfl rfl ha' Cs carriers translation hcall hs) ?_
            refine hash_fam_cost4 l F kclk coef A a ha _ _ (le_trans (le_max_left _ _) hdeg)
              (le_trans (Nat.le_add_right _ _) hcf) wb_spec nw_spec (le_trans (le_max_right _ _) hCD) _ ?_ ha' Cs
              carriers translation hcall hs
            rw [hbF_Etot]
            exact le_max_right _ _ }⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
