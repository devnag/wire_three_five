import Proof.Wire_3_5.UnionMachine.RadLink
import Proof.Wire_3_5.FinalPass.RadPreBase
import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadBW6

/-! # RADIX: the setup at a THR call (stages 2 to 6 and the value links; P3:2585-2623, P3:2150-2157; #170,
#183)

At a THR call, from the setup's entry `RadSetupB3.RsIn4` (the request and the fixed hash's bits on `0`, W6's words on
`130 … 132`, the payloads on `133 … 136`, the twenty values in `410 …`), **`radixW`** = C1's digit program
(`RadDigs.digsP`, stage 2) ; `RadAsm.radixB` at the block writer `FinalPass.RadB.radBlockW3` (stages 3 to 6) ends in
**`RadSetupB3.RadReadyB2`** for Route B's request `qC = reqB (radReqOf …) G ((4row+4)G) (4S₁+1) (M+2+S₂+(J+1)G)`:

* the value links: the call's majorant `mpC` is W6's `thrMP M A B_* K` (`mpC_eq`), its level records are the window
  records, its seed word and rows are the table builder's (`HashSeed.revWord_eq`, `Hash4.rowF_eq`), the list data is
  `thrCallD = dataBits mpC hashBits`, `listBound = 4S₁+1`;
* the record (`RadLink.record_frame`), the admissibility (`radPre`), the capacities (`radCaps` with
  `RadBnd.thrDigs_caps` and the table word's length `lw`);
* `RunCaps` (the capacity premises of `RadAsm.radixB_run`, as one structure), **`radix_call`**.

Paper quantity of the main type: the RADIX row's C2 request `radReqOf … g pr s row` at Route B's capacities, on the
record stream (`RadReadyB2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires.RepairOrdinary.SignedSortKey

/-! ## The capacity premises of stages 3 to 6, as one structure -/

/-- **The capacity premises of `RadAsm.radixB_run`.** -/
structure RunCaps (cap : ℕ) (Wb : RadSpec3.RadBlockW3) (A l : List Bool) (t ℓ pm J G row M p s : ℕ)
    (prs : List (ℕ × ℕ)) (Wf : ℕ → ℕ) (ls : List (List ℕ)) (Dl : ListData) (all : List ℕ) (C cd : ℕ) : Prop where
  c0 : 2 * (M + ls.length + G + J + p + row + 1) ≤ cap
  c1 : (RadScan.recsW prs).length + (prs.map Prod.fst).sum + (prs.map Prod.snd).sum + G + row + M + ls.length + J +
    p ≤ cap
  c2 : (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45 + 1048576 + 4 * row + J + 8 ≤ cap
  c3 : RadFieldsP.fieldsLen ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) M ls.length p ≤ cap
  c4 : 2 * (A ++ frame l).length + 2 * t * (2 * ℓ + 2) + 4 * (t * ℓ) + ℓ + t + 2 ≤ cap
  c5 : 2 * ℓ + 1 ≤ cap
  c6 : M + G + J + (RadScan.recsW prs).length + 4 ≤ cap
  cS : (FinalPass.Hash4.seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap
  cW : (FinalPass.Hash4.winWord M G J Wf).length ≤ cap
  cO : (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length + 1 ≤ cap
  hC : ∀ j ≤ J, FinalPass.Hash4.levelCost ℓ G M all.length j
    (FinalPass.ListEval.pow (FinalPass.ListEval.topW J Wf j)) (FinalPass.ListEval.topW J Wf j) ≤ C
  c8 : G + row + 3 * (4 * (prs.map Prod.snd).sum + 1) + M + ls.length ≤ cap
  c9 : ∀ gis ∈ ls, (gis.flatMap RadCnt.itemW).length ≤ cap
  c11 : ∀ gis ∈ ls, capC Dl gis.length ≤ cap
  need : ∀ gis ∈ ls, ∀ t' ≤ Dl.M, ∀ sgn : Bool, ∀ olen ≤ (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length,
    Wb.need (blkSize Dl gis G row t' sgn olen) ≤ cap
  c12 : (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length + 3 ≤ cap
  cost : ∀ gis ∈ ls, RadDig.digCost cap Wb Dl gis G ≤ cd

theorem radixB_run' (cap x : ℕ) (Wb : RadSpec3.RadBlockW3) (σ : WState (LNS x) LNR) (A l : List Bool)
    (t ℓ pm J G row M p s : ℕ) (prs : List (ℕ × ℕ)) (Wf : ℕ → ℕ) (ls : List (List ℕ)) (Dl : ListData)
    (all : List ℕ) (C cd : ℕ)
    (h0 : σ.st (sk x 0) = frame (A ++ frame l)) (h0h : σ.sh (sk x 0) = 0)
    (h131 : σ.st (sk x 131) = RadScan.recsW prs) (h131h : σ.sh (sk x 131) = 0)
    (hprs : RadScan.recsW prs = (FinalPass.ListEval.levels J).flatMap (FinalPass.Hash4.winRec J Wf))
    (h132 : σ.st (sk x 132) = frame (binary ℓ pm)) (h132h : σ.sh (sk x 132) = 0)
    (h137 : σ.st (sk x 137) = ls.flatMap gisWord) (h137h : σ.sh (sk x 137) = 0)
    (hbl : ∀ k : Fin 161, (k.val = 3 ∨ (138 ≤ k.val ∧ k.val ≤ 148) ∨ k.val = 150) →
      σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0)
    (hG : σ.val (rIn 4) = G) (hrow : σ.val (rIn 3) = row) (hM : σ.val (rIn 13) = M)
    (hτ : σ.val (rIn 12) = ls.length) (hJ : σ.val (rIn 16) = J) (hp : σ.val (rIn 1) = p) (hs : σ.val (rIn 2) = s)
    (ht : σ.val (rIn 17) = t) (hℓ : σ.val (rIn 18) = ℓ)
    (zQ : ∀ i, σ.val (rQ i) = 0) (zF : ∀ i, σ.val (rF i) = 0) (zY : ∀ i, σ.val (rY i) = 0)
    (zT : ∀ i, σ.val (rT i) = 0) (zB : ∀ i, σ.val (rB i) = 0) (zZ : ∀ i, σ.val (rZ i) = 0)
    (zG : ∀ i, σ.val (rG i) = 0)
    (hl : l.length = 2 * t * ℓ) (hℓ1 : 1 ≤ ℓ)
    (hseed : FinalPass.HashSeed.revWord l ℓ (2 * t) = FinalPass.Hash4.seedWord ℓ all)
    (hDM : Dl.M = M) (hDJ : Dl.J = J) (hDW : Dl.W = Wf)
    (hrowF : FinalPass.Hash4.rowF pm ℓ M G all = FinalPass.ListEval.rowsOf Dl G)
    (hlb : ListMachine.listBound Dl = 4 * (prs.map Prod.snd).sum + 1)
    (hLG : ∀ gis ∈ ls, gis.length ≤ G) (hτ1 : 1 ≤ ls.length) (hp2 : 2 ≤ p) (hsp : s < p)
    (hc : RunCaps cap Wb A l t ℓ pm J G row M p s prs Wf ls Dl all C cd) :
    ∃ σR : WState (LNS x) LNR, WExec cap (radixB x Wb) σ σR
        (radCostB cap (RadScan.recsW prs).length (prs.map Prod.snd).sum G row M ls.length J p s t ℓ
          (A ++ frame l).length C (FinalPass.Hash4.winWord M G J Wf).length
          (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length cd
          (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length)) ∧
      σR.st (sk x 3) = RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) ++ [true, false, false] ∧
      σR.sh (sk x 3) = 0 ∧ σR.st (sk x 150) = [true] ∧ σR.sh (sk x 150) = 0 ∧
      Keep σ σR (fun i => i.val = 3 ∨ i.val = 150 ∨ 130 ≤ i.val) (fun _ => True) :=
  radixB_run cap x Wb σ A l t ℓ pm J G row M p s prs Wf ls Dl all h0 h0h h131 h131h hprs h132 h132h h137 h137h hbl
    hG hrow hM hτ hJ hp hs ht hℓ zQ zF zY zT zB zZ zG hl hℓ1 hseed hDM hDJ hDW hrowF hlb hLG hτ1 hp2 hsp hc.c0 hc.c1
    hc.c2 hc.c3 hc.c4 hc.c5 hc.c6 hc.cS hc.cW hc.cO C hc.hC hc.c8 hc.c9 hc.c11 hc.need hc.c12 cd hc.cost

/-! ## The setup at a THR call -/

section Call

end Call

/-- **The RADIX setup program** (stages 2 to 6). -/
noncomputable def radixW (x : ℕ) : WM (LNS x) LNR := .seq (RadDigs.digsP x) (radixB x FinalPass.RadB.radBlockW3)


section CallLemmas

end CallLemmas

end NearCubicWires.WireExponent3_5.UnionMachine.RadCall
