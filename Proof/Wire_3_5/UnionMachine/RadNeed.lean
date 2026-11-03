import Proof.Wire_3_5.UnionMachine.RadCallBase
import Proof.Wire_3_5.UnionMachine.PopPipeLe

/-! # RADIX, Route B: the setup's word lengths and costs, bounded (the `RadSetupSpecB5` instance, part 1)

Every capacity premise of the RADIX setup at a THR call (`RadCall.RunCaps`, the digit program's need) and its cost
(`RadAsm.radCostB`) is bounded by a polynomial in one number `X` that dominates the row's explicit numbers (the
Route-B measure `xOf`, the star row, `t`, the request's length, `ℓ₀`); the pipe's bound `q.bound` likewise.

* the words: a factor block `RadBlk.bw` (`bw_len_le`, via PA's `PopRec.blockE_eq`), a digit's blocks, the setup
  fields (`fieldsWordB_len`), the seed, window and index words;
* the costs without lists: `digACost`, `digCCost`, `digCost` (`digCost_le`), the level cost (`levelCost_mono`),
  `radCostB` (`radCostB_mono`).

Paper quantity: the RADIX row's capacities and running time, polynomial in the row's explicit capacity
(prim:runtime P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadNeed
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.WireExponent3_5.UnionMachine.RadAsm

/-! ## Lists -/

theorem sum_map_le {α : Type} (f : α → ℕ) (B : ℕ) : ∀ l : List α, (∀ x ∈ l, f x ≤ B) → (l.map f).sum ≤ l.length * B
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x List.mem_cons_self
    have h2 := sum_map_le f B l (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem len_le_flatMap {α β : Type} (f : α → List β) : ∀ (l : List α) (x : α), x ∈ l →
    (f x).length ≤ (l.flatMap f).length
  | [], x, h => by simp at h
  | a :: l, x, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := len_le_flatMap f l x h; omega

theorem fst_snd_le (prs : List (ℕ × ℕ)) :
    (prs.map Prod.fst).sum + (prs.map Prod.snd).sum ≤ (RadScan.recsW prs).length := by
  induction prs with
  | nil => simp [RadScan.recsW]
  | cons ab prs ih =>
    simp only [RadScan.recsW, List.flatMap_cons, List.length_append, RadScan.recW_length, List.map_cons,
      List.sum_cons] at ih ⊢
    omega

theorem mem_levels (J j : ℕ) (hj : j ≤ J) : j ∈ levels J := by
  simp [levels, List.mem_reverse, List.mem_range]; omega

theorem le_of_mem_levels (J j : ℕ) (hj : j ∈ levels J) : j ≤ J := by
  simp [levels, List.mem_reverse, List.mem_range] at hj; omega

/-- A level's modulus and window are at most the window records' length. -/
theorem win_le (J : ℕ) (Wf : ℕ → ℕ) (prs : List (ℕ × ℕ))
    (hprs : RadScan.recsW prs = (levels J).flatMap (FinalPass.Hash4.winRec J Wf)) (j : ℕ) (hj : j ≤ J) :
    pow (topW J Wf j) + topW J Wf j + 3 ≤ (RadScan.recsW prs).length := by
  have h := len_le_flatMap (FinalPass.Hash4.winRec J Wf) (levels J) j (mem_levels J j hj)
  rw [← hprs] at h
  simp only [FinalPass.Hash4.winRec, unary, List.length_cons, List.length_append, List.length_replicate,
    List.length_singleton] at h
  omega

/-! ## Word lengths -/

theorem itemW_len_le (gis : List ℕ) (V : ℕ) (hL : gis.length ≤ V) (hg : ∀ gi ∈ gis, gi ≤ V) :
    (gis.flatMap RadCnt.itemW).length ≤ V * (V + 2) := by
  have h := PopPipeLe.len_flatMap_le' gis RadCnt.itemW (V + 2) (fun gi hgi => by
    have := hg gi hgi
    simp only [RadCnt.itemW, List.length_cons, List.length_append, List.length_replicate, List.length_singleton,
      List.length_nil]
    omega)
  exact le_trans h (Nat.mul_le_mul_right _ hL)

theorem gisWord_len_le (gis : List ℕ) (V : ℕ) (hL : gis.length ≤ V) (hg : ∀ gi ∈ gis, gi ≤ V) :
    (RadSpec.gisWord gis).length ≤ V * (V + 2) + 1 := by
  have h := itemW_len_le gis V hL hg
  have e : RadSpec.gisWord gis = gis.flatMap RadCnt.itemW ++ [false] := rfl
  rw [e, List.length_append, List.length_singleton]
  omega

theorem cntCost_le (gis : List ℕ) (V : ℕ) (hL : gis.length ≤ V) (hg : ∀ gi ∈ gis, gi ≤ V) :
    RadCnt.cntCost gis ≤ V * (7 * V + 19) + 1 := by
  unfold RadCnt.cntCost
  have h := sum_map_le (fun gi => 7 * gi + 19) (7 * V + 19) gis (fun gi hgi => by have := hg gi hgi; omega)
  have := Nat.mul_le_mul_right (7 * V + 19) hL
  omega

theorem seedWord_len (ℓ : ℕ) (all : List ℕ) :
    (FinalPass.Hash4.seedWord ℓ all).length = all.length * (2 * ℓ + 2) + 1 := by
  unfold FinalPass.Hash4.seedWord
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  have e : ∀ c : ℕ, (true :: frame (RepairOrdinary.SignedSortKey.binary ℓ c)).length = 2 * ℓ + 2 := fun c => by
    rw [List.length_cons, frame_length, RepairOrdinary.SignedSortKey.binary_length]
  simp only [e, List.map_const', List.sum_replicate, smul_eq_mul]

theorem winWord_len (M L J : ℕ) (Wf : ℕ → ℕ) :
    (FinalPass.Hash4.winWord M L J Wf).length = M + L + J + ((levels J).flatMap (FinalPass.Hash4.winRec J Wf)).length + 4 := by
  simp only [FinalPass.Hash4.winWord, unary, List.length_append, List.length_replicate, List.length_singleton]
  omega

/-- The level word at `L` points. -/
theorem lw_len (Dl : ListData) (L : ℕ) :
    (levelWord Dl.M Dl.J Dl.W (rowsOf Dl L)).length =
      Dl.M + 2 + ((levels Dl.J).flatMap (FinalPass.Hash4.winRec Dl.J Dl.W)).length + (Dl.J + 1) * L :=
  RadScan.levelWord_length _ _ _ _ L (RadDig.rowsOf_len Dl L)

theorem capC_eq (Dl : ListData) (L : ℕ) :
    capC Dl L = 4 * ((levelWord Dl.M Dl.J Dl.W (rowsOf Dl L)).length + L + 1) := rfl

/-- **A factor block's length** (`RadBlk.bw`) at the block's numbers at most `V`. -/
theorem bw_len_le (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) (t V : ℕ) (hL : gis.length ≤ V)
    (hlb : listBound Dl ≤ V) (ht : t ≤ V) (hlw : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl gis.length)).length ≤ V)
    (hlab : ∀ lab ∈ CompilerMachine.Pool.labsOf G row gis, lab ≤ V) :
    (RadBlk.bw Dl gis G row sgn t).length ≤ 2000 * (V + 1) ^ 2 := by
  unfold RadBlk.bw
  rw [PopRec.blockE_eq, PopBlockW.blockE_length, PopPipeLe.pieceA_len, PopPipeLe.pieceB_len,
    PopBlockW.pieceP_length, PopPipeLe.m2_flat_len]
  have hn : (CompilerMachine.Pool.labsOf G row gis).length = 4 * gis.length := RadBnd.labsOf_length G row gis
  have hE := PopPipeLe.len_flatMap_le' (CompilerMachine.Pool.labsOf G row gis) labE (4 * V + 4) (fun lab h => by
    have := hlab lab h
    simp only [labE, reps_length, m2, List.length_append, List.length_cons, List.length_nil]
    omega)
  have hS : labSum (CompilerMachine.Pool.labsOf G row gis) ≤ 5 + (CompilerMachine.Pool.labsOf G row gis).length * (2 * V + 10) := by
    unfold labSum
    have := sum_map_le (fun lab => 2 * lab + 10) (2 * V + 10) (CompilerMachine.Pool.labsOf G row gis)
      (fun lab h => by have := hlab lab h; omega)
    omega
  have hc1 : cap1C gis.length (CompilerMachine.Pool.labsOf G row gis) ≤
      2 * (4 * gis.length) + 1 + labSum (CompilerMachine.Pool.labsOf G row gis) := by
    unfold cap1C
    have h1 : labCost (4 * gis.length) (CompilerMachine.Pool.labsOf G row gis) = labSum (CompilerMachine.Pool.labsOf G row gis) := by
      rw [← hn]; exact labCost_eq _
    rw [h1]
    exact max_le (by omega) (by omega)
  have hcc := capC_eq Dl gis.length
  have m1 : (CompilerMachine.Pool.labsOf G row gis).length * (4 * V + 4) ≤ (4 * V) * (4 * V + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have m2' : (CompilerMachine.Pool.labsOf G row gis).length * (2 * V + 10) ≤ (4 * V) * (2 * V + 10) :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : (4 * V) * (4 * V + 4) = 16 * (V * V) + 16 * V := by ring
  have e2 : (4 * V) * (2 * V + 10) = 8 * (V * V) + 40 * V := by ring
  have e3 : (V + 1) ^ 2 = V * V + 2 * V + 1 := by ring
  omega

/-- **A digit's blocks.** -/
theorem digBlocks_len_le (Dl : ListData) (gis : List ℕ) (G row V : ℕ) (hL : gis.length ≤ V)
    (hlb : listBound Dl ≤ V) (hM : Dl.M ≤ V) (hlw : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl gis.length)).length ≤ V)
    (hlab : ∀ lab ∈ CompilerMachine.Pool.labsOf G row gis, lab ≤ V) :
    (RadBlk.digBlocks Dl gis G row).length ≤ 4000 * (V + 1) ^ 3 := by
  have hb : ∀ sgn : Bool, (RadBlk.bws Dl gis G row sgn (Dl.M + 1)).length ≤ (Dl.M + 1) * (2000 * (V + 1) ^ 2) :=
    fun sgn => by
      have h := PopPipeLe.len_flatMap_le' (List.range (Dl.M + 1)) (RadBlk.bw Dl gis G row sgn) (2000 * (V + 1) ^ 2)
        (fun t ht => bw_len_le Dl gis G row sgn t V hL hlb (by simp at ht; omega) hlw hlab)
      simpa [RadBlk.bws] using h
  have h1 := hb true
  have h2 := hb false
  have m : (Dl.M + 1) * (2000 * (V + 1) ^ 2) ≤ (V + 1) * (2000 * (V + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have e : (V + 1) * (2000 * (V + 1) ^ 2) = 2000 * (V + 1) ^ 3 := by ring
  unfold RadBlk.digBlocks
  rw [List.length_append]
  omega

/-- **The setup fields' length** is within `fieldsLen`. -/
theorem fieldsWordB_len (R Lg M τ p s cp : ℕ) (hτ : 1 ≤ τ) (hp : 1 ≤ p) (hs : s < p) :
    (RadFieldsP.fieldsWordB R Lg M τ p s cp).length ≤ RadFieldsP.fieldsLen R Lg cp M τ p := by
  rw [RadFieldsP.fieldsWordB_eq]
  simp only [List.length_append]
  rw [RadFieldsP.len_rep, RadFieldsP.len_rep, RadFieldsP.len_enc, RadFieldsP.len_zW M (2 * τ) (by omega),
    RadFieldsP.len_patT p s (2 * τ) hs, RadFieldsP.len_rep]
  have h := RadFieldsP.len_cons M p τ hp
  have h' := Nat.mul_le_mul_left τ (show 2 * ((M + 1) * (4 * p + 4)) ≤ 2 * ((M + 1) * (4 * p + 4)) + 5 * p + 2 by omega)
  have e1 : (fieldE [true]).length = 6 := rfl
  have e2 : (fieldE []).length = 2 := rfl
  rw [e1, e2]
  unfold RadFieldsP.fieldsLen
  omega

/-! ## Costs without lists -/

/-- A truncation record's cost bound. -/
def recB (V : ℕ) : ℕ := (8 + 1 + (5 + 1 + ((16 * V + 17) + 1 + (16 * V + 17)))) + 1 +
    ((18 * V + 3) + 1 + ((V * 19 + 1) + 1 + ((18 * V + 3) + 1 + (V * 9 + 1))))

theorem recCost_le (a b L G V : ℕ) (ha : a ≤ V) (hb : b ≤ V) (hL : L ≤ V) (hG : G ≤ V) :
    RadTrunc.recCost a b L G ≤ recB V := by
  unfold RadTrunc.recCost recB; omega

theorem loopCost_le (a b : ℕ → ℕ) (L G V : ℕ) (js : List ℕ) (hab : ∀ j ∈ js, a j ≤ V ∧ b j ≤ V) (hL : L ≤ V)
    (hG : G ≤ V) : RadTrunc.loopCost a b L G js ≤ js.length * (recB V + 2) + 1 := by
  unfold RadTrunc.loopCost
  have := sum_map_le (fun j => RadTrunc.recCost (a j) (b j) L G + 2) (recB V + 2) js (fun j hj => by
    have := recCost_le (a j) (b j) L G V (hab j hj).1 (hab j hj).2 hL hG; omega)
  omega

/-- The digit's front cost bound. -/
def DA (V : ℕ) : ℕ :=
  (V * (7 * V + 19) + 1 + 1 + (5 * (V * (V + 2)) + 1)) + 1 +
    ((18 * V + 3 + 1 + (18 * V + 3 + 1 + (5 * V + 1))) + 1 +
      (((16 * V + 17) + 1 + (((V + 1) * (recB V + 2) + 1) + 1 + (8 + 1 + (5 + 1 + (5 * V + 1))))) + 1 +
        (RadTrunc2.capWCost V V + 1 + ((18 * V + 3) + 1 + (5 * V + 1)))))

theorem digACost_le (Dl : ListData) (gis : List ℕ) (G V : ℕ) (hG : G ≤ V) (hL : gis.length ≤ G)
    (hg : ∀ gi ∈ gis, gi ≤ V) (hJ : Dl.J ≤ V) (hM : Dl.M ≤ V)
    (hw : ∀ j ≤ Dl.J, pow (topW Dl.J Dl.W j) ≤ V ∧ topW Dl.J Dl.W j ≤ V)
    (hlw : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length ≤ V)
    (htd : (RadDig.tdW Dl gis.length).length ≤ V) : RadDig.digACost Dl gis G ≤ DA V := by
  have h1 := cntCost_le gis V (by omega) hg
  have h2 := itemW_len_le gis V (by omega) hg
  have h3 := loopCost_le (fun j => pow (topW Dl.J Dl.W j)) (fun j => topW Dl.J Dl.W j) gis.length G V (levels Dl.J)
    (fun j hj => hw j (le_of_mem_levels _ _ hj)) (by omega) hG
  have hlv : (levels Dl.J).length = Dl.J + 1 := by simp [levels]
  have m : (levels Dl.J).length * (recB V + 2) ≤ (V + 1) * (recB V + 2) := Nat.mul_le_mul_right _ (by omega)
  have hc : RadTrunc2.capWCost (RadDig.tdW Dl gis.length).length gis.length ≤ RadTrunc2.capWCost V V := by
    unfold RadTrunc2.capWCost; omega
  unfold RadDig.digACost RadTrunc2.truncCost DA
  omega

/-- The digit's closing cost bound. -/
def DC (V : ℕ) : ℕ :=
  (5 * V + 1) + 1 + ((3 * (4 * (V + V + 1)) + 1) + 1 + ((3 * V + 1) + 1 + ((3 * V + 1) + 1 +
    ((V * (7 * V + 19) + 1) + 1 + (1 + 1 + ((3 * (V * (V + 2)) + 1) + 1 + (3 * V + 1)))))))

theorem digCCost_le (gis : List ℕ) (G tl cc V : ℕ) (hG : G ≤ V) (hL : gis.length ≤ V) (hg : ∀ gi ∈ gis, gi ≤ V)
    (htl : tl ≤ V) (hcc : cc ≤ 4 * (V + V + 1)) : RadDig.digCCost gis G tl cc ≤ DC V := by
  have h1 := cntCost_le gis V hL hg
  have h2 := itemW_len_le gis V hL hg
  unfold RadDig.digCCost DC
  omega

theorem tCost_mono (M V c : ℕ) (h : M ≤ V) : RadBlk.tCost M c ≤ RadBlk.tCost V c := by
  unfold RadBlk.tCost; gcongr

/-- **A digit's cost bound** at the capacity (`RunCaps.cost`'s `cd`). -/
def cdB (V : ℕ) : ℕ :=
  DA V + 1 + ((3 + 1 + (RadBlk.tCost V (FinalPass.RadB.radBlockW3.bound V) + 1 + (1 + 1 +
    RadBlk.tCost V (FinalPass.RadB.radBlockW3.bound V)))) + 1 + DC V)

theorem digCost_le (cap : ℕ) (Dl : ListData) (gis : List ℕ) (G : ℕ) (hG : G ≤ cap) (hL : gis.length ≤ G)
    (hg : ∀ gi ∈ gis, gi ≤ cap) (hJ : Dl.J ≤ cap) (hM : Dl.M ≤ cap)
    (hw : ∀ j ≤ Dl.J, pow (topW Dl.J Dl.W j) ≤ cap ∧ topW Dl.J Dl.W j ≤ cap)
    (hlw : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length ≤ cap)
    (htd : (RadDig.tdW Dl gis.length).length ≤ cap) :
    RadDig.digCost cap FinalPass.RadB.radBlockW3 Dl gis G ≤ cdB cap := by
  have hA := digACost_le Dl gis G cap hG hL hg hJ hM hw hlw htd
  have hC := digCCost_le gis G (RadDig.tdW Dl gis.length).length (capC Dl gis.length) cap hG (by omega) hg htd
    (by show 4 * ((RadDig.tdW Dl gis.length).length + gis.length + 1) ≤ _; omega)
  have hT := tCost_mono Dl.M cap (FinalPass.RadB.radBlockW3.bound cap) hM
  unfold RadDig.digCost cdB
  omega

/-- **The level cost bound** (`RunCaps.hC`'s `C`). -/
def Cb (V : ℕ) : ℕ := FinalPass.Hash4.levelCost V V V V V V V

theorem levelCost_mono (ℓ L M n j pw w V : ℕ) (h1 : ℓ ≤ V) (h2 : L ≤ V) (h3 : M ≤ V) (h4 : n ≤ V) (h5 : j ≤ V)
    (h6 : pw ≤ V) (h7 : w ≤ V) : FinalPass.Hash4.levelCost ℓ L M n j pw w ≤ Cb V := by
  unfold Cb FinalPass.Hash4.levelCost FinalPass.Hash4.stepCost FinalPass.Hash4.hornerCost FinalPass.Hash4.recCost
    FinalPass.Tm.mulStepCost
  gcongr

theorem radCostB_mono (cap S2 S1 G row M τ J p s t ℓ la C lwin lo c lu U : ℕ) (h1 : S2 ≤ cap) (h2 : S1 ≤ cap)
    (h3 : G ≤ cap) (h4 : row ≤ cap) (h5 : M ≤ cap) (h6 : τ ≤ cap) (h7 : J ≤ cap) (h8 : p ≤ cap) (h9 : s ≤ cap)
    (h10 : t ≤ cap) (h11 : ℓ ≤ cap) (h12 : la ≤ cap) (h13 : lwin ≤ cap) (h14 : lo ≤ cap) (h15 : lu ≤ cap)
    (h16 : U ≤ cap) :
    radCostB cap S2 S1 G row M τ J p s t ℓ la C lwin lo c lu U ≤
      radCostB cap cap cap cap cap cap cap cap cap cap cap cap cap C cap cap c cap cap := by
  unfold radCostB ph2Cost ph3Cost RadFieldsP.fieldsCost RadFields2.digitCost RadSeed.hashSeedCost RadSeed.tailCost
    FinalPass.HashSeed.seedCost RadWin.winCost FinalPass.Hash4.buildCost ph8Cost
  gcongr

/-! ## The need and the bound -/

/-- The quadratic part. -/
def nT2 (X : ℕ) : ℕ := 100 * (X + 1) ^ 2

/-- The scale part `U^45`. -/
def nT3 (X : ℕ) : ℕ := (1048576 * X) ^ 45 + 1048576 * X + 1048576

/-- The setup fields. -/
def nT4 (X : ℕ) : ℕ := RadFieldsP.fieldsLen ((1048576 * X) ^ 40) ((1048576 * X) ^ 40 + 1) ((1048576 * X) ^ 45) X X X

/-- The factor blocks. -/
def nT5 (X : ℕ) : ℕ := 4000 * X * (X + 1) ^ 3

/-- The block writer's need. -/
def nT6 (X : ℕ) : ℕ := 300 * (nT4 X + nT5 X + 3000 * (X + 1) ^ 2 + 1)

/-- **The RADIX setup's need** at the row's measure `X`. -/
noncomputable def needF (X : ℕ) : ℕ :=
  FinalPass.DigsBody.digsWImpl.C * (X + 1) ^ FinalPass.DigsBody.digsWImpl.D + nT2 X + nT3 X + nT4 X + nT5 X + nT6 X

/-- **The RADIX setup's cost bound** at the capacity. -/
noncomputable def bnd (cap : ℕ) : ℕ :=
  FinalPass.DigsBody.digsWImpl.C * (cap + 1) ^ FinalPass.DigsBody.digsWImpl.D + 1 +
    radCostB cap cap cap cap cap cap cap cap cap cap cap cap cap (Cb cap) cap cap (cdB cap) cap cap

/-- **The pipe's bound** at the row's measure. -/
def pipeF (X : ℕ) : ℕ := X * (128 * (nT4 X + nT5 X + 4) ^ 2)

theorem nT2_eq (X : ℕ) : nT2 X = 100 * (X * X) + 200 * X + 100 := by unfold nT2; ring

/-! ## The call's numbers, bounded by one `X` -/

/-- The hypotheses: the Route-B measure `xOf`, the star row, `J`, `t`, the request's length and `ℓ₀` at most `X`
(`ℓ₀ ≤ 2X+1`), and the call's structural facts (those of `RadAsm.radixB_run`). -/
structure Bd (X : ℕ) (A l : List Bool) (t ℓ pm J G row M p s : ℕ) (prs : List (ℕ × ℕ)) (Wf : ℕ → ℕ)
    (ls : List (List ℕ)) (Dl : ListData) (all : List ℕ) : Prop where
  hx : xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length ≤ X
  hrow : row ≤ X
  hJ : J ≤ X
  ht : t ≤ X
  hla : (A ++ frame l).length ≤ X
  hℓ : ℓ ≤ 2 * X + 1
  hall : all.length = 2 * t
  hsp : s < p
  hp1 : 1 ≤ p
  hτ1 : 1 ≤ ls.length
  hprs : RadScan.recsW prs = (levels J).flatMap (FinalPass.Hash4.winRec J Wf)
  hDM : Dl.M = M
  hDJ : Dl.J = J
  hDW : Dl.W = Wf
  hrowF : FinalPass.Hash4.rowF pm ℓ M G all = rowsOf Dl G
  hlb : listBound Dl = 4 * (prs.map Prod.snd).sum + 1
  hLG : ∀ gis ∈ ls, gis.length ≤ G
  hgi : ∀ gis ∈ ls, ∀ gi ∈ gis, gi < G

theorem xOf_ge (G row M τ J p S1 S2 : ℕ) :
    M + τ + G + (4 * row + 4) * G + (4 * S1 + 1) + (M + 2 + S2 + (J + 1) * G) + p ≤ xOf G row M τ J p S1 S2 := by
  unfold xOf RadSpec.radX; omega

theorem blkSize_eq (Dl : ListData) (gis : List ℕ) (G row t : ℕ) (sgn : Bool) (olen : ℕ) :
    RadSpec.blkSize Dl gis G row t sgn olen = olen + (RadBlk.bw Dl gis G row sgn t).length +
      (levelWord Dl.M Dl.J Dl.W (rowsOf Dl gis.length)).length + (RadSpec.gisWord gis).length +
      (G + 1) * (4 * row + 4) + t + 3 * listBound Dl + capC Dl gis.length := rfl

section Bd
variable {X : ℕ} {A l : List Bool} {t ℓ pm J G row M p s : ℕ} {prs : List (ℕ × ℕ)} {Wf : ℕ → ℕ}
  {ls : List (List ℕ)} {Dl : ListData} {all : List ℕ}

theorem Bd.lwL (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) (L : ℕ) (hL : L ≤ G) :
    (levelWord Dl.M Dl.J Dl.W (rowsOf Dl L)).length ≤ X := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  rw [lw_len, h.hDM, h.hDJ, h.hDW, ← h.hprs]
  have := Nat.mul_le_mul_left (J + 1) hL
  omega

theorem Bd.lo_le (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) :
    (levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length ≤ X := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  rw [RadScan.levelWord_length M J Wf _ G (fun j => by simp [FinalPass.Hash4.rowF]), ← h.hprs]
  omega

theorem Bd.fields_le (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) :
    RadFieldsP.fieldsLen ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) M ls.length p ≤ nT4 X := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  have hM : M ≤ X := by omega
  have hτ : ls.length ≤ X := by omega
  have hp : p ≤ X := by omega
  unfold nT4 RadFieldsP.fieldsLen
  gcongr

theorem Bd.lu_le (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) :
    (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length ≤ nT4 X + nT5 X := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  have hf := fieldsWordB_len ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) h.hτ1 h.hp1 h.hsp
  have hf2 := h.fields_le
  have hb := PopPipeLe.len_flatMap_le' ls (fun gis => RadBlk.digBlocks Dl gis G row) (4000 * (X + 1) ^ 3)
    (fun gis hgis => digBlocks_len_le Dl gis G row X (le_trans (h.hLG gis hgis) (by omega)) (by rw [h.hlb]; omega)
      (by rw [h.hDM]; omega) (h.lwL _ (h.hLG gis hgis))
      (fun lab hlab => le_trans (RadBnd.labsOf_le G row gis (h.hgi gis hgis) lab hlab) (by omega)))
  have m : ls.length * (4000 * (X + 1) ^ 3) ≤ X * (4000 * (X + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
  have e : X * (4000 * (X + 1) ^ 3) = nT5 X := by unfold nT5; ring
  omega

/-- **The capacity premises of stages 3 to 6 from the need.** -/
theorem runCaps_of (cap : ℕ) (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) (hcap : needF X ≤ cap) :
    RadCall.RunCaps cap FinalPass.RadB.radBlockW3 A l t ℓ pm J G row M p s prs Wf ls Dl all (Cb cap) (cdB cap) := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  have hrow := h.hrow
  have hJ := h.hJ
  have ht := h.ht
  have hla := h.hla
  have hℓ := h.hℓ
  have hsp := h.hsp
  have hfs := fst_snd_le prs
  have e2 := nT2_eq X
  have hT : nT2 X + nT3 X + nT4 X + nT5 X + nT6 X ≤ cap := by unfold needF at hcap; omega
  have hlu := h.lu_le
  have hc3 := h.fields_le
  have hU : (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ≤ 1048576 * X := Nat.mul_le_mul_left _ hx
  have hU45 : (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45 ≤ (1048576 * X) ^ 45 := Nat.pow_le_pow_left hU 45
  have e3 : nT3 X = (1048576 * X) ^ 45 + 1048576 * X + 1048576 := rfl
  have m1 : 2 * t * (2 * ℓ + 2) ≤ 2 * X * (2 * (2 * X + 1) + 2) := by gcongr
  have m2 : t * ℓ ≤ X * (2 * X + 1) := Nat.mul_le_mul ht hℓ
  have e4 : 2 * X * (2 * (2 * X + 1) + 2) = 8 * (X * X) + 8 * X := by ring
  have e5 : X * (2 * X + 1) = 2 * (X * X) + X := by ring
  have e6 : X * (X + 2) = X * X + 2 * X := by ring
  have e7 : (X + 1) ^ 2 = X * X + 2 * X + 1 := by ring
  have e8 : nT6 X = 300 * (nT4 X + nT5 X + 3000 * (X + 1) ^ 2 + 1) := rfl
  have hw := win_le J Wf prs h.hprs
  have hlo := h.lo_le
  refine ⟨?_, ?_, ?_, le_trans hc3 (by omega), ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [seedWord_len, h.hall]; omega
  · rw [winWord_len, ← h.hprs]; omega
  · intro j hj
    have := hw j hj
    exact levelCost_mono _ _ _ _ _ _ _ cap (by omega) (by omega) (by omega) (by rw [h.hall]; omega) (by omega)
      (by omega) (by omega)
  · omega
  · intro gis hgis
    have := itemW_len_le gis X (le_trans (h.hLG gis hgis) (by omega))
      (fun gi hgi => by have := h.hgi gis hgis gi hgi; omega)
    omega
  · intro gis hgis
    rw [capC_eq]
    have := h.lwL gis.length (h.hLG gis hgis)
    have := h.hLG gis hgis
    omega
  · intro gis hgis t' ht' sgn olen holen
    show 300 * (RadSpec.blkSize Dl gis G row t' sgn olen + 1) ≤ cap
    rw [blkSize_eq]
    have hlL := h.hLG gis hgis
    have hbw := bw_len_le Dl gis G row sgn t' X (by omega) (by rw [h.hlb]; omega) (by rw [h.hDM] at ht'; omega)
      (h.lwL _ hlL) (fun lab hlab => le_trans (RadBnd.labsOf_le G row gis (h.hgi gis hgis) lab hlab) (by omega))
    have hgw := gisWord_len_le gis X (by omega) (fun gi hgi => by have := h.hgi gis hgis gi hgi; omega)
    have hcc := capC_eq Dl gis.length
    have hlw' := h.lwL gis.length hlL
    have e9 : (G + 1) * (4 * row + 4) = (4 * row + 4) * G + 4 * row + 4 := by ring
    have hlb := h.hlb
    have hM' := h.hDM
    omega
  · intro gis hgis
    have hlL := h.hLG gis hgis
    exact digCost_le cap Dl gis G (by omega) hlL (fun gi hgi => by have := h.hgi gis hgis gi hgi; omega)
      (by rw [h.hDJ]; omega) (by rw [h.hDM]; omega)
      (fun j hj => by
        rw [h.hDJ, h.hDW] at *
        have := hw j hj
        exact ⟨by omega, by omega⟩)
      (by have := h.lwL G le_rfl; omega)
      (by have := h.lwL gis.length hlL; unfold RadDig.tdW; omega)

/-- **The cost of stages 2 to 6 is within the bound.** -/
theorem cost_le (cap : ℕ) (h : Bd X A l t ℓ pm J G row M p s prs Wf ls Dl all) (hcap : needF X ≤ cap) (N : ℕ)
    (hN : N ≤ X) :
    FinalPass.DigsBody.digsWImpl.bound N + 1 +
      radCostB cap (RadScan.recsW prs).length (prs.map Prod.snd).sum G row M ls.length J p s t ℓ (A ++ frame l).length
        (Cb cap) (FinalPass.Hash4.winWord M G J Wf).length (levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length
        (cdB cap) (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ≤ bnd cap := by
  have hx := h.hx
  have hg := xOf_ge G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length
  have hrow := h.hrow
  have hJ := h.hJ
  have ht := h.ht
  have hla := h.hla
  have hℓ := h.hℓ
  have hsp := h.hsp
  have hfs := fst_snd_le prs
  have e2 := nT2_eq X
  have hT : FinalPass.DigsBody.digsWImpl.C * (X + 1) ^ FinalPass.DigsBody.digsWImpl.D + nT2 X + nT3 X + nT4 X + nT5 X + nT6 X ≤ cap := hcap
  have hlu := h.lu_le
  have hU : (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ≤ 1048576 * X := Nat.mul_le_mul_left _ hx
  have e3 : nT3 X = (1048576 * X) ^ 45 + 1048576 * X + 1048576 := rfl
  have hlo := h.lo_le
  have hd := FinalPass.DigsBody.digsWImpl.bound_le N
  have hd2 : FinalPass.DigsBody.digsWImpl.C * (N + 1) ^ FinalPass.DigsBody.digsWImpl.D ≤
      FinalPass.DigsBody.digsWImpl.C * (cap + 1) ^ FinalPass.DigsBody.digsWImpl.D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hR := radCostB_mono cap (RadScan.recsW prs).length (prs.map Prod.snd).sum G row M ls.length J p s t ℓ
    (A ++ frame l).length (Cb cap) (FinalPass.Hash4.winWord M G J Wf).length
    (levelWord M J Wf (FinalPass.Hash4.rowF pm ℓ M G all)).length (cdB cap) (RadFieldsP.fieldsWordB ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40) ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M ls.length p s ((1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ++ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)).length (1048576 * xOf G row M ls.length J p (prs.map Prod.snd).sum (RadScan.recsW prs).length)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [winWord_len, ← h.hprs]; omega) (by omega) (by rw [List.length_append]; omega)
    (by omega)
  unfold bnd
  omega

/-- **The pipe's bound**: the Route-B row cost at the record `frame record = fields ++ blocks ++ [t,f,f]`. -/
theorem bound_le (q : RadSetupB.RadReqB) (X : ℕ) (h1 : (q.r.D.M + 1) ^ (2 * q.r.digs.length) ≤ X)
    (h2 : q.record.length ≤ nT4 X + nT5 X + 3) : q.bound ≤ pipeF X := by
  unfold RadSetupB.RadReqB.bound pipeF
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

end Bd

/-! ## Polynomial -/

theorem PolyB.pow' {f : ℕ → ℕ} (hf : FinalPass.DigsBody.PolyB f) (n : ℕ) :
    FinalPass.DigsBody.PolyB fun U => f U ^ n := by
  induction n with
  | zero => simpa using FinalPass.DigsBody.PolyB.const 1
  | succ n ih => simpa [pow_succ] using FinalPass.DigsBody.PolyB.mul ih hf

/-- The closure tactic: sums, products, powers, the identity and constants. -/
macro "polyc" : tactic => `(tactic| repeat' (first | with_reducible exact FinalPass.DigsBody.PolyB.id | with_reducible exact FinalPass.DigsBody.PolyB.const _ | with_reducible apply PolyB.pow' | with_reducible apply FinalPass.DigsBody.PolyB.add | with_reducible apply FinalPass.DigsBody.PolyB.mul))

theorem nT4_poly : FinalPass.DigsBody.PolyB nT4 := by
  unfold nT4 RadFieldsP.fieldsLen
  polyc

theorem nT5_poly : FinalPass.DigsBody.PolyB nT5 := by
  unfold nT5
  polyc

theorem needF_poly : FinalPass.DigsBody.PolyB needF := by
  have h1 : FinalPass.DigsBody.PolyB fun X =>
      FinalPass.DigsBody.digsWImpl.C * (X + 1) ^ FinalPass.DigsBody.digsWImpl.D := ⟨_, _, fun _ => le_rfl⟩
  have h2 : FinalPass.DigsBody.PolyB nT2 := by
    unfold nT2
    polyc
  have h3 : FinalPass.DigsBody.PolyB nT3 := by
    unfold nT3
    polyc
  have h6 : FinalPass.DigsBody.PolyB nT6 := by
    unfold nT6
    exact FinalPass.DigsBody.PolyB.mul (FinalPass.DigsBody.PolyB.const _)
      (FinalPass.DigsBody.PolyB.add (FinalPass.DigsBody.PolyB.add (FinalPass.DigsBody.PolyB.add nT4_poly nT5_poly)
        (FinalPass.DigsBody.PolyB.mul (FinalPass.DigsBody.PolyB.const _)
          (PolyB.pow' (FinalPass.DigsBody.PolyB.add FinalPass.DigsBody.PolyB.id (FinalPass.DigsBody.PolyB.const _)) 2)))
        (FinalPass.DigsBody.PolyB.const _))
  unfold needF
  exact FinalPass.DigsBody.PolyB.add (FinalPass.DigsBody.PolyB.add (FinalPass.DigsBody.PolyB.add
    (FinalPass.DigsBody.PolyB.add (FinalPass.DigsBody.PolyB.add h1 h2) h3) nT4_poly) nT5_poly) h6

theorem pipeF_poly : FinalPass.DigsBody.PolyB pipeF := by
  unfold pipeF
  exact FinalPass.DigsBody.PolyB.mul FinalPass.DigsBody.PolyB.id (FinalPass.DigsBody.PolyB.mul
    (FinalPass.DigsBody.PolyB.const _) (PolyB.pow' (FinalPass.DigsBody.PolyB.add
      (FinalPass.DigsBody.PolyB.add nT4_poly nT5_poly) (FinalPass.DigsBody.PolyB.const _)) 2))

theorem bnd_poly : FinalPass.DigsBody.PolyB bnd := by
  have hRB : FinalPass.DigsBody.PolyB fun c => FinalPass.RadB.radBlockW3.bound c :=
    ⟨_, _, FinalPass.RadB.radBlockW3.bound_le⟩
  unfold bnd radCostB ph2Cost ph3Cost RadFieldsP.fieldsCost RadFields2.digitCost RadSeed.hashSeedCost RadSeed.tailCost
    FinalPass.HashSeed.seedCost RadWin.winCost FinalPass.Hash4.buildCost ph8Cost RadNums.numsCost UnaryPow.sq Cb
    FinalPass.Hash4.levelCost FinalPass.Hash4.stepCost FinalPass.Hash4.hornerCost FinalPass.Hash4.recCost
    FinalPass.Tm.mulStepCost cdB DA recB RadTrunc2.capWCost RadBlk.tCost DC
  polyc
  all_goals exact hRB

end NearCubicWires.WireExponent3_5.UnionMachine.RadNeed
