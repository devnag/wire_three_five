import Proof.Wire_3_5.UnionMachine.RadAsm4

/-! # RADIX assembly (5): the digit loop on the cell, the record's end, stages 3 to 6 composed (P3:2585-2623)

* `run8910` / **`run8910_spec`**: the digit loop's registers (`ph8`), the digit loop (`RadDigL.digLoop`, block writer
  `Wb`, entry `RadDig.DigIn` on the cell), the record's end and the RADIX flag (`ph10`);
* `radixB` = `run23 ; run456 ; ph7 ; run8910`, `radCostB`, **`radixB_run`**: from the state after stage 2 the record
  stream `3` ends as `fieldsWordB R Lg M τ₀ p s cap ++ ls.flatMap (digBlocks D · G row) ++ [true, false, false]`
  (head `0`) with `R = U^40`, `Lg = U^40 + 1`, `cap = U^45`, the flag `[true]` on `150` (head `0`); every stream but
  `3`, `150` and those `≥ 130` as at the entry.

Paper quantity of the main type: the RADIX row's framed record (setup fields, factor blocks in store order). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

variable (cap : ℕ) (x : ℕ)

/-! ## The digit loop and the record's end -/

def run8910 (Wb : RadSpec3.RadBlockW3) : WM (LNS x) LNR :=
  .seq (ph8 x) (.seq (RadDigL.digLoop rZ rG Wb (sk x 3) (sk x 138) (sk x 142) (sk x 137) (scK x) (rY 0) (rY 17))
    (ph10 x))

theorem run8910_spec (Wb : RadSpec3.RadBlockW3) (σ : WState (LNS x) LNR) (G row M lb : ℕ) (ls : List (List ℕ))
    (Dl : ListData) (fW : List Bool)
    (h3 : σ.st (sk x 3) = fW) (h3h : σ.sh (sk x 3) = fW.length) (hOP : σ.val (rY 0) = fW.length)
    (h142 : σ.st (sk x 142) = FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl G))
    (h142h : σ.sh (sk x 142) = 0)
    (h137 : σ.st (sk x 137) = ls.flatMap gisWord) (h137h : σ.sh (sk x 137) = 0)
    (hbl : ∀ k : Fin 161, ((138 ≤ k.val ∧ k.val ≤ 140) ∨ k.val = 150) → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0)
    (hG : σ.val (rIn 4) = G) (hrow : σ.val (rIn 3) = row) (hM : σ.val (rIn 13) = M)
    (hτ : σ.val (rIn 12) = ls.length) (hlb : σ.val (rQ 8) = lb)
    (zZ : ∀ i, σ.val (rZ i) = 0) (zG : ∀ i, σ.val (rG i) = 0) (hy4 : σ.val (rY 4) = 0) (hy17 : σ.val (rY 17) = 0)
    (hy18 : σ.val (rY 18) = 0)
    (hDM : Dl.M = M) (hlbD : ListMachine.listBound Dl = lb) (hLG : ∀ gis ∈ ls, gis.length ≤ G)
    (c8 : G + row + 3 * lb + M + ls.length ≤ cap) (c9 : ∀ gis ∈ ls, (gis.flatMap RadCnt.itemW).length ≤ cap)
    (c10 : G < cap) (c10' : (FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl G)).length ≤ cap)
    (c11 : ∀ gis ∈ ls, capC Dl gis.length ≤ cap) (cM : M + 1 ≤ cap)
    (hneed : ∀ gis ∈ ls, ∀ t' ≤ Dl.M, ∀ sgn : Bool,
      ∀ olen ≤ fW.length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length,
        Wb.need (blkSize Dl gis G row t' sgn olen) ≤ cap)
    (c12 : fW.length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length + 3 ≤ cap)
    (cd : ℕ) (hcost : ∀ gis ∈ ls, RadDig.digCost cap Wb Dl gis G ≤ cd) :
    ∃ σR : WState (LNS x) LNR, WExec cap (run8910 x Wb) σ σR
        (ph8Cost G row lb M ls.length + 1 + ((ls.length * (cd + 4) + 1) + 1 +
          (8 * 3 + 1 + ((5 * ((fW ++ ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length + 3) + 1) + 1 +
            (8 + 1 + (5 + 1)))))) ∧
      σR.st (sk x 3) = fW ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) ++ [true, false, false] ∧
      σR.sh (sk x 3) = 0 ∧ σR.st (sk x 150) = [true] ∧ σR.sh (sk x 150) = 0 ∧
      Keep σ σR (fun i => i.val = 3 ∨ i.val = 137 ∨ i.val = 138 ∨ i.val = 150) (fun _ => True) := by
  have b138 := hbl 138 (Or.inl ⟨by decide, by decide⟩)
  have b139 := hbl 139 (Or.inl ⟨by decide, by decide⟩)
  have b140 := hbl 140 (Or.inl ⟨by decide, by decide⟩)
  have b150 := hbl 150 (Or.inr rfl)
  have e8 := ph8_spec cap x σ G row lb M ls.length hG hrow hlb hM hτ (zG 1) (zG 2) (zG 5) (zZ 9) hy17 hy4 c8
  set σ8 := ((((σ.setv (rG 1) G).setv (rG 2) row).setv (rG 5) (3 * lb)).setv (rZ 9) M).setv (rY 17)
    ls.length with hσ8
  have K8 : Keep σ σ8 (fun _ => False) (fun r => r = rG 1 ∨ r = rG 2 ∨ r = rG 5 ∨ r = rZ 9 ∨ r = rY 17) := by
    refine ⟨fun i _ => ⟨rfl, rfl⟩, fun r hr => ?_⟩
    simp only [not_or] at hr
    simp [σ8, Function.update_apply, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
  have hZR : ∀ i j, rZ i ≠ rG j := ZG
  have st3 : σ8.st (sk x 3) = fW := by rw [K8.st (by rad_ne)]; exact h3
  have sh3 : σ8.sh (sk x 3) = fW.length := by rw [K8.sh (by rad_ne)]; exact h3h
  have v0 : σ8.val (rY 0) = fW.length := by rw [K8.val (by rad_ne)]; exact hOP
  have hin : RadDig.DigIn rZ rG (sk x 3) (sk x 138) (sk x 142) (sk x 137) (scK x) (rY 0) Dl G row σ8 := by
    refine ⟨by rad_ne, by rad_ne, by rad_ne, by rad_ne, ?_, fun i => ?_, fun j => ?_, fun i => ?_, hZR,
      ⟨[], by rw [K8.st (by rad_ne), K8.sh (by rad_ne), h142, h142h, List.drop_zero, List.append_nil]⟩,
      by rw [st3, sh3], ?_, fun i => ?_, ?_, ?_, ?_, fun j h1 h2 h5 => ?_, ?_, fun i h9 => ?_⟩
    · intro a b h
      have e := congrArg Fin.val h
      rw [scK_val, scK_val] at e
      exact Fin.ext (by omega)
    · have hi := i.isLt
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
        · have := congrArg Fin.val e; rw [scK_val] at this; simp [sk_val] at this; omega
    · rad_ne
    · rad_ne
    · rw [K8.st (by rad_ne), K8.sh (by rad_ne), b138.1, b138.2]; rfl
    · fin_cases i
      · show σ8.st (sk x 139) = [] ∧ σ8.sh (sk x 139) = 0
        rw [K8.st (by rad_ne), K8.sh (by rad_ne)]; exact b139
      · show σ8.st (sk x 140) = [] ∧ σ8.sh (sk x 140) = 0
        rw [K8.st (by rad_ne), K8.sh (by rad_ne)]; exact b140
    · simp [σ8, Function.update_apply, Fin.ext_iff, rG_val, rZ_val, rY_val, RadSpec.radBlkK]
    · simp [σ8, Function.update_apply, Fin.ext_iff, rG_val, rZ_val, rY_val, RadSpec.radBlkK]
    · simp [σ8, Function.update_apply, Fin.ext_iff, rG_val, rZ_val, rY_val, RadSpec.radBlkK, hlbD]
    · have n1 : rG j ≠ rG 1 := rG.injective.ne h1
      have n2 : rG j ≠ rG 2 := rG.injective.ne h2
      have n5 : rG j ≠ rG 5 := rG.injective.ne h5
      have nz : rG j ≠ rZ 9 := fun e => ZG 9 j e.symm
      have ny : rG j ≠ rY 17 := fun e => YG 17 j e.symm
      simp only [σ8, WState.setv_val, Function.update_apply, if_neg n1, if_neg n2, if_neg n5, if_neg nz, if_neg ny]
      exact zG j
    · simp [σ8, Function.update_apply, Fin.ext_iff, rG_val, rZ_val, rY_val, RadSpec.radBlkK, hDM]
    · have n9 : rZ i ≠ rZ 9 := rZ.injective.ne h9
      have ng1 : rZ i ≠ rG 1 := ZG i 1
      have ng2 : rZ i ≠ rG 2 := ZG i 2
      have ng5 : rZ i ≠ rG 5 := ZG i 5
      have ny : rZ i ≠ rY 17 := fun e => YZ 17 i e.symm
      simp only [σ8, WState.setv_val, Function.update_apply, if_neg n9, if_neg ng1, if_neg ng2, if_neg ng5, if_neg ny]
      exact zZ i
  have e9 := RadDigL.digLoop_spec cap rZ rG Wb (sk x 3) (sk x 138) (sk x 142) (sk x 137) (scK x) (rY 0) (rY 17) Dl G
    row ls σ8 hin (by rad_ne) (by rad_ne) (fun i => fun e => YZ 17 i e.symm) (fun j => fun e => YG 17 j e.symm)
    (by rad_ne) (by simp [σ8]) [] (by rw [K8.st (by rad_ne), K8.sh (by rad_ne), h137, h137h, List.drop_zero,
      List.append_nil]) hLG c9 c10 c10' c11 (by rw [hDM]; exact cM) (by omega)
    (fun gis hg t' ht' sgn olen hol => hneed gis hg t' ht' sgn olen (by rw [st3] at hol; exact hol))
    (by rw [v0]; omega) cd hcost
  set σ9 := (RadDigL.post (sk x 3) (sk x 138) (sk x 137) (rY 0) σ8 (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) (ls.flatMap fun gis => RadDig.tdW Dl gis.length)
    (ls.flatMap gisWord).length).setv (rY 17) 0 with hσ9
  have K9 : Keep σ8 σ9 (fun i => i = sk x 3 ∨ i = sk x 138 ∨ i = sk x 137) (fun r => r = rY 0 ∨ r = rY 17) :=
    ((keep_post (sk x 3) (sk x 138) (sk x 137) (rY 0) σ8 (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) _ _).trans (keep_setv _ (rY 17) 0)).mono
      (fun i h => by rcases h with h | h; exact h; exact h.elim) (fun r h => h)
  have n3_138 : sk x 3 ≠ sk x 138 := by rad_ne
  have n3_137 : sk x 3 ≠ sk x 137 := by rad_ne
  have u3 : σ9.st (sk x 3) = fW ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) := by
    simp [σ9, RadDigL.post, Function.update_apply, n3_138, st3]
  have u3h : σ9.sh (sk x 3) = (fW ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length := by
    simp [σ9, RadDigL.post, Function.update_apply, n3_138, n3_137, sh3]
  have u0 : σ9.val (rY 0) = (fW ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length := by
    simp [σ9, RadDigL.post, Function.update_apply, v0, rY.injective.eq_iff]
  obtain ⟨σ10, e10, K10, r3, r3h, r150, r150h⟩ := ph10_spec cap x σ9 (fW ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)) u3 u3h u0
    (by rw [K9.st (by rad_ne), K8.st (by rad_ne)]; exact b150.1)
    (by rw [K9.sh (by rad_ne), K8.sh (by rad_ne)]; exact b150.2)
    (by rw [K9.val (by rad_ne), K8.val (by rad_ne)]; exact hy18) (by rw [List.length_append]; omega)
  refine ⟨σ10, WExec.seq e8 (WExec.seq e9 e10), ?_, r3h, r150, r150h, ?_⟩
  · rw [r3, List.append_assoc]
  · exact ((K8.trans K9).trans K10).mono (fun i h => by
      simp [Fin.ext_iff, sk_val] at h
      omega) (fun _ _ => trivial)

/-! ## Stages 3 to 6 -/

/-- **Stages 3 to 6.** -/
def radixB (Wb : RadSpec3.RadBlockW3) : WM (LNS x) LNR :=
  .seq (run23 x) (.seq (run456 x) (.seq (ph7 x) (run8910 x Wb)))

/-- Stages 3 to 6's cost. -/
def radCostB (S2 S1 G row M τ J p s t ℓ la C lwin lo c lu U : ℕ) : ℕ :=
  (ph2Cost S2 S1 G row M τ J p cap + 1 + ph3Cost cap (U ^ 40) (U ^ 40 + 1) (U ^ 45) M τ p s) + 1 +
    ((((18 * t + 3) + 1 + ((18 * ℓ + 3) + 1 + RadSeed.hashSeedCost t ℓ la)) + 1 +
      (((18 * ℓ + 3) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + (60 * ℓ + 40))))) + 1 +
      ((18 * M + 3) + 1 + ((18 * G + 3) + 1 + ((18 * J + 3) + 1 + ((18 * S2 + 3) + 1 + RadWin.winCost M G J S2)))))) +
    1 + (FinalPass.Hash4.buildCost M G J C lwin lo + 1 +
      (ph8Cost G row (4 * S1 + 1) M τ + 1 + ((τ * (c + 4) + 1) + 1 +
        (8 * 3 + 1 + ((5 * (lu + 3) + 1) + 1 + (8 + 1 + (5 + 1))))))))

theorem radixB_run (Wb : RadSpec3.RadBlockW3) (σ : WState (LNS x) LNR) (A l : List Bool) (t ℓ pm J G row M p s : ℕ)
    (prs : List (ℕ × ℕ)) (Wf : ℕ → ℕ) (ls : List (List ℕ)) (Dl : ListData) (all : List ℕ)
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
    (c0 : 2 * (M + ls.length + G + J + p + row + 1) ≤ cap)
    (c1 : (RadScan.recsW prs).length + (prs.map Prod.fst).sum + (prs.map Prod.snd).sum + G + row + M + ls.length + J +
      p ≤ cap)
    (c2 : (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45 + 1048576 + 4 * row + J + 8 ≤ cap)
    (c3 : RadFieldsP.fieldsLen ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) M ls.length p ≤ cap)
    (c4 : 2 * (A ++ frame l).length + 2 * t * (2 * ℓ + 2) + 4 * (t * ℓ) + ℓ + t + 2 ≤ cap)
    (c5 : 2 * ℓ + 1 ≤ cap) (c6 : M + G + J + (RadScan.recsW prs).length + 4 ≤ cap)
    (cS : (FinalPass.Hash4.seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap)
    (cW : (FinalPass.Hash4.winWord M G J Wf).length ≤ cap)
    (cO : (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length + 1 ≤ cap)
    (C : ℕ) (hC : ∀ j ≤ J, FinalPass.Hash4.levelCost ℓ G M all.length j
      (FinalPass.ListEval.pow (FinalPass.ListEval.topW J Wf j)) (FinalPass.ListEval.topW J Wf j) ≤ C)
    (c8 : G + row + 3 * (4 * (prs.map Prod.snd).sum + 1) + M + ls.length ≤ cap)
    (c9 : ∀ gis ∈ ls, (gis.flatMap RadCnt.itemW).length ≤ cap)
    (c11 : ∀ gis ∈ ls, capC Dl gis.length ≤ cap)
    (hneed : ∀ gis ∈ ls, ∀ t' ≤ Dl.M, ∀ sgn : Bool, ∀ olen ≤ (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length,
      Wb.need (blkSize Dl gis G row t' sgn olen) ≤ cap)
    (c12 : (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length + 3 ≤ cap)
    (cd : ℕ) (hcost : ∀ gis ∈ ls, RadDig.digCost cap Wb Dl gis G ≤ cd) :
    ∃ σR : WState (LNS x) LNR, WExec cap (radixB x Wb) σ σR
        (radCostB cap (RadScan.recsW prs).length (prs.map Prod.snd).sum G row M ls.length J p s t ℓ
          (A ++ frame l).length C (FinalPass.Hash4.winWord M G J Wf).length
          (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length cd
          (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length)) ∧
      σR.st (sk x 3) = RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row) ++ [true, false, false] ∧
      σR.sh (sk x 3) = 0 ∧ σR.st (sk x 150) = [true] ∧ σR.sh (sk x 150) = 0 ∧
      Keep σ σR (fun i => i.val = 3 ∨ i.val = 150 ∨ 130 ≤ i.val) (fun _ => True) := by
  have b3 := hbl 3 (by decide)
  obtain ⟨σ3, e3, K3, f3, f3h, f3v, q7, q8⟩ := run23_spec cap x σ prs G row M ls.length J p s h131 h131h b3.1 b3.2
    hG hrow hM hτ hJ hp hs zQ zF zY hτ1 hp2 hsp c0 c1 c2 c3
  obtain ⟨σ6, e6, K6, g142, g142h, g143, g143h, g144, g144h, g145⟩ := run456_spec cap x σ3 A l t ℓ M G J
    (RadScan.recsW prs) hl (by rw [K3.st (by rad_ne)]; exact h0) (by rw [K3.sh (by rad_ne)]; exact h0h)
    (fun k h1 h2 => by
      rw [K3.st (by rad_ne), K3.sh (by rad_ne)]
      exact hbl k (Or.inr (Or.inl ⟨by omega, h2⟩)))
    (by rw [K3.st (by rad_ne)]; exact h131) (by rw [K3.sh (by rad_ne)]; exact h131h)
    (by rw [K3.val (by rad_ne)]; exact ht) (by rw [K3.val (by rad_ne)]; exact hℓ)
    (by rw [K3.val (by rad_ne)]; exact hM) (by rw [K3.val (by rad_ne)]; exact hG)
    (by rw [K3.val (by rad_ne)]; exact hJ) q7 (fun i => by rw [K3.val (by rad_ne)]; exact zT i)
    (fun i h1 h2 => by rw [K3.val (by rad_ne)]; exact zY i) c4 c5 c6
  have hwin : σ6.st (sk x 143) = FinalPass.Hash4.winWord M G J Wf := by
    rw [g143, hprs]; unfold FinalPass.Hash4.winWord; simp [List.append_assoc]
  obtain ⟨σ7, e7, K7, g142', g142h'⟩ := ph7_spec cap x σ6 pm ℓ M G J Wf all hℓ1 cS cW cO (by omega) (by omega)
    (by omega) C hC hwin g142 (by rw [g144, hseed]) (by rw [(K3.trans K6).st (by rad_ne)]; exact h132)
    (fun k h1 h2 => ⟨0, by rw [(g145 k h1 h2).1, FinalPass.Tm.binary_zero]⟩)
    (fun k => by
      fin_cases k
      · exact g142h
      · exact g143h
      · exact g144h
      · show σ6.sh (sk x 132) = 0
        rw [(K3.trans K6).sh (by rad_ne)]; exact h132h
      · exact (g145 145 (by decide) (by decide)).2
      · exact (g145 146 (by decide) (by decide)).2
      · exact (g145 147 (by decide) (by decide)).2
      · exact (g145 148 (by decide) (by decide)).2)
    (fun r => by rw [(K3.trans K6).val (by rad_ne)]; exact zB r)
  have K67 := K6.trans K7
  have K37 := K3.trans K67
  obtain ⟨σR, eR, r3, r3h, r150, r150h, KR⟩ := run8910_spec cap x Wb σ7 G row M (4 * (prs.map Prod.snd).sum + 1) ls
    Dl (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)) (by rw [K67.st (by rad_ne)]; exact f3) (by rw [K67.sh (by rad_ne)]; exact f3h)
    (by rw [K67.val (by rad_ne)]; exact f3v) (by rw [g142', hrowF, hDM, hDJ, hDW]) g142h'
    (by rw [K37.st (by rad_ne)]; exact h137) (by rw [K37.sh (by rad_ne)]; exact h137h)
    (fun k hk => by
      rw [K37.st (by rad_ne), K37.sh (by rad_ne)]
      exact hbl k (by omega))
    (by rw [K37.val (by rad_ne)]; exact hG) (by rw [K37.val (by rad_ne)]; exact hrow)
    (by rw [K37.val (by rad_ne)]; exact hM) (by rw [K37.val (by rad_ne)]; exact hτ)
    (by rw [K67.val (by rad_ne)]; exact q8) (fun i => by rw [K37.val (by rad_ne)]; exact zZ i)
    (fun i => by rw [K37.val (by rad_ne)]; exact zG i) (by rw [K37.val (by rad_ne)]; exact zY 4)
    (by rw [K37.val (by rad_ne)]; exact zY 17) (by rw [K37.val (by rad_ne)]; exact zY 18)
    hDM hlb hLG c8 c9 (by omega) (by rw [hDM, hDJ, hDW, ← hrowF]; omega) c11 (by omega) hneed c12 cd hcost
  refine ⟨σR, WExec.seq e3 (WExec.seq e6 (WExec.seq e7 eR)), r3, r3h, r150, r150h, ?_⟩
  exact (K37.trans KR).mono (fun i h => by
    simp [Fin.ext_iff, sk_val] at h
    omega) (fun _ _ => trivial)

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
