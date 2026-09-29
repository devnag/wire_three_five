import Proof.Wire_3_5.Primitive.Writers.GeoColsLoop

/-! # PA (d): the columns writer for the C4.L (`C4Geo.colsField P`)

P3:1212-1216 (star:partition): "Assign `r/2` whole blocks to each side. Each contributes exactly `b−s` free center bits
[...] A fixed linear basis of each code gives polynomial-time encoding"; the `C4Geo.colsField P` is C3's
column header of `φ` (the dense width `natWord width`, then every column as `binary width`, framed). The writer:

* `preW` (PA's verified numbers `p1W`/`p2W`/`p3W`, with `b` and `r/2` carried past them by **`frameR`**);
* `colsE`: the marks of `natWord width` (PA's `writeNatM`), the blocks (`GeoColsLoop.blkLoop`), the unit columns
  (`GeoColsLoop.uLoop`), the closing `0`;
* **`colsW_spec`**: from the writer's start state, the output stream is `C4Geo.colsField P` (through
  `GeoColsV.colsField_emit`), the input stream kept;
* **`colsEC_le`**: the emission's cost is at most `2000·(n+2)^4`;
* **`cols_run`**: `WriterRun (geoM (colsW c_r) Dv Cv) … w (C4Geo.colsField P)` (`GeoFront.geo_run`).

Paper quantity of the main type: the columns of `φ` (P3:1212-1216) in C3's column header. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoColsRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
open NearCubicWires.WireExponent3_5.PrimAsm.GeoColsV NearCubicWires.WireExponent3_5.PrimAsm.GeoColsCw
open NearCubicWires.WireExponent3_5.PrimAsm.GeoColsLoop
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.BlockPlatform

/-! ## Carrying a register past a program that never names it -/

section Frame
variable {ns nr : ℕ} (cap : ℕ)

theorem setv_commC (σ : WState ns nr) (r r' : Fin nr) (h : r' ≠ r) (x y : ℕ) :
    (σ.setv r x).setv r' y = (σ.setv r' y).setv r x :=
  WState.eq rfl rfl (by simp only [WState.setv_val]; exact (Function.update_comm h y x σ.val).symm) rfl

theorem setv_sethC (σ : WState ns nr) (r : Fin nr) (i : Fin (ns + 1)) (x y : ℕ) :
    (σ.setv r x).seth i y = (σ.seth i y).setv r x := rfl

theorem setv_setsC (σ : WState ns nr) (r : Fin nr) (i : Fin (ns + 1)) (x : ℕ) (l : List Bool) :
    (σ.setv r x).sets i l = (σ.sets i l).setv r x := rfl

theorem setv_setcC (σ : WState ns nr) (r : Fin nr) (x : ℕ) (c : Bool) :
    (σ.setv r x).setc c = (σ.setc c).setv r x := rfl

/-- **Carrying a register**: a program that never names `r` runs the same with any value in `r`. -/
theorem frameR {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (r : Fin nr)
    (hP : namesR r P = false) (x : ℕ) : WExec cap P (σ.setv r x) (τ.setv r x) n := by
  induction h with
  | skip σ => exact WExec.skip _
  | inc r' σ hc =>
    have hr : r' ≠ r := by simpa [namesR] using hP
    have e : ((σ.setv r' (σ.val r' + 1)).setv r x) = ((σ.setv r x).setv r' ((σ.setv r x).val r' + 1)) := by
      rw [wsetv_val_ne _ _ hr, setv_commC σ r r' hr]
    rw [e]
    exact WExec.inc r' _ (by rw [wsetv_val_ne _ _ hr]; exact hc)
  | dec r' σ hc =>
    have hr : r' ≠ r := by simpa [namesR] using hP
    have e : ((σ.setv r' (σ.val r' - 1)).setv r x) = ((σ.setv r x).setv r' ((σ.setv r x).val r' - 1)) := by
      rw [wsetv_val_ne _ _ hr, setv_commC σ r r' hr]
    rw [e]
    exact WExec.dec r' _ (by rw [wsetv_val_ne _ _ hr]; exact hc)
  | fwd i σ => rw [← setv_sethC]; exact WExec.fwd i _
  | bwd i σ => rw [← setv_sethC]; exact WExec.bwd i _
  | wr i b σ => rw [← setv_setsC]; exact WExec.wr i b _
  | setc v σ => rw [← setv_setcC]; exact WExec.setc v _
  | seq h1 h2 ih1 ih2 =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact WExec.seq (ih1 hP.1) (ih2 hP.2)
  | ifrT hv h1 ih =>
    simp only [namesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.ifrT (by rw [wsetv_val_ne _ _ hP.1.1]; exact hv) (ih hP.1.2)
  | ifrF hv h1 ih =>
    simp only [namesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.ifrF (by rw [wsetv_val_ne _ _ hP.1.1]; exact hv) (ih hP.2)
  | ifsT hv h1 ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact WExec.ifsT hv (ih hP.1)
  | ifsF hv h1 ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact WExec.ifsF hv (ih hP.2)
  | whrF hv =>
    simp only [namesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP
    exact WExec.whrF (by rw [wsetv_val_ne _ _ hP.1]; exact hv)
  | whrT hv h1 h2 ih1 ih2 =>
    have hP' := hP
    simp only [namesR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hP'
    exact WExec.whrT (by rw [wsetv_val_ne _ _ hP'.1]; exact hv) (ih1 hP'.2) (ih2 hP)
  | whsF hv => exact WExec.whsF hv
  | whsT hv h1 h2 ih1 ih2 =>
    have hP' := hP
    simp only [namesR] at hP'
    exact WExec.whsT hv (ih1 hP') (ih2 hP)
  | mono h1 hle ih => exact WExec.mono (ih hP) hle

end Frame

/-! ## The numbers, with `b` and `r/2` kept -/

/-- `rB := b`, `rR2 := r/2` (from the star block). -/
def copiesW : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR (SG 5) rB rT2) (FinalPass.Hash4.wcopyR (SG 6) rR2 rT2)

/-- **The columns writer's numbers**: PA's `p1W`, the copies, `p2W`, `p3W`. -/
def preW (cr : ℕ) : WM GS GR := .seq (p1W cr) (.seq copiesW (.seq p2W p3W))

theorem p3W_names (r : Fin GR) (h1 : 32 ≤ r.val) (h2 : r.val ≠ 40) (h3 : r.val ≠ 41) : namesR r p3W = false := by
  revert r
  decide

theorem preW_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (preW cr) (σG w P.n W) σF c ∧ σF.val rA = aOf P ∧ σF.val rH = hLv P ∧
      σF.val rWd = aOf P + hLv P ∧ σF.val rOP = 0 ∧ σF.val rK = 0 ∧ σF.val rT = 0 ∧ σF.val rB = P.b ∧
      σF.val rR2 = P.r / 2 ∧
      (∀ r : Fin GR, 32 ≤ r.val → r.val ≠ 40 → r.val ≠ 41 → r ≠ rB → r ≠ rR2 → σF.val r = 0) ∧
      σF.st = (σG w P.n W).st ∧ σF.sh gOUT = 0 ∧ c ≤ numsGCostE P cr + 40 * P.n + 20 := by
  have hbn := b_le P
  have hr4 := P.four_r_le_n
  have hrb := P.r_mul_b_le
  have hrs := rb_eq P
  obtain ⟨σ1, c1, e1, f5, f6, f7, fz, fst, fsh, fc1⟩ := part1_spec cr W P hrP sfx w hw hW
  have s5 : SG 5 = (5 : Fin GR) := rfl
  have s6 : SG 6 = (6 : Fin GR) := rfl
  have ec1 := FinalPass.Hash4.wcopyR_spec (2 * W + 2) (SG 5) rB rT2 (by rw [s5]; decide) (by rw [s5]; decide)
    (by decide) σ1 (fz _ (by decide)) (fz _ (by decide)) (by rw [f5]; omega)
  rw [f5] at ec1
  have v6 : (σ1.setv rB P.b).val (SG 6) = P.r / 2 := by
    rw [wsetv_val_ne _ _ (by rw [s6]; decide)]; exact f6
  have ec2 := FinalPass.Hash4.wcopyR_spec (2 * W + 2) (SG 6) rR2 rT2 (by rw [s6]; decide) (by rw [s6]; decide)
    (by decide) (σ1.setv rB P.b) (by rw [wsetv_val_ne _ _ (by decide)]; exact fz _ (by decide))
    (by rw [wsetv_val_ne _ _ (by decide)]; exact fz _ (by decide)) (by rw [v6]; omega)
  rw [v6] at ec2
  have hrhb : P.r / 2 * P.b ≤ P.n := by unfold aOf at hrs; omega
  obtain ⟨σ2, c2, e2, gA, gH, g7, gz, gst, gsh, gc2⟩ := part2_spec (2 * W + 2) P.b (P.r / 2) (P.n - P.r * P.b) σ1
    f5 f6 f7 fz (by omega)
  obtain ⟨σ3, c3, e3, hA3, hH3, hW3, hR3, hOP, hK, hT, hst3, hsh3, hc3⟩ := part3_spec (2 * W + 2) (P.r / 2 * P.b)
    ((P.n - P.r * P.b + 1) / 2) (P.n - P.r * P.b) σ2 gA gH g7 gz (by omega)
  have e2' := frameR (2 * W + 2) (frameR (2 * W + 2) e2 rB (by decide) P.b) rR2 (by decide) (P.r / 2)
  have e3' := frameR (2 * W + 2) (frameR (2 * W + 2) e3 rB (by decide) P.b) rR2 (by decide) (P.r / 2)
  have hne : ∀ r : Fin GR, r ≠ rB → r ≠ rR2 → ((σ3.setv rB P.b).setv rR2 (P.r / 2)).val r = σ3.val r :=
    fun r a b => by rw [wsetv_val_ne _ _ b, wsetv_val_ne _ _ a]
  refine ⟨(σ3.setv rB P.b).setv rR2 (P.r / 2), _, WExec.seq e1 (WExec.seq (WExec.seq ec1 ec2) (WExec.seq e2' e3')),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hne _ (by decide) (by decide), hA3]; rfl
  · rw [hne _ (by decide) (by decide), hH3]; rfl
  · rw [hne _ (by decide) (by decide), hW3]; rfl
  · rw [hne _ (by decide) (by decide), hOP]
  · rw [hne _ (by decide) (by decide), hK]
  · rw [hne _ (by decide) (by decide), hT]
  · rw [wsetv_val_ne _ _ (by decide)]; simp
  · simp
  · intro r h1 h2 h3 h4 h5
    rw [hne r h4 h5, val_keep (2 * W + 2) e3 r (p3W_names r h1 h2 h3)]
    exact gz r (by omega) (fun e => by subst e; revert h1; decide) (fun e => by subst e; revert h1; decide)
      (fun e => by subst e; revert h1; decide) (fun e => by subst e; revert h1; decide)
  · show σ3.st = _; rw [hst3, gst, fst]
  · show σ3.sh gOUT = 0; rw [hsh3, gsh, fsh]
  · rw [fc1, gc2, hc3]
    unfold numsGCostE
    omega

/-! ## The emission -/

/-- The width writer's registers: `rWd` (kept), scratch `32..37`, the output counter. -/
def WN : Fin 8 ↪ Fin GR := ⟨![28, 32, 33, 34, 35, 36, 37, 30], by decide⟩

/-- `rQU −= rA` (through `rT2`, `rZ`). -/
def QB : Fin 4 ↪ Fin GR := ⟨![62, 24, 44, 63], by decide⟩

/-- The blocks' start: `post := width − b`, `K1 := r/2`. -/
def blkInit : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR rWd rPost rT2) (.seq (UnaryArith.subW PB) (FinalPass.Hash4.wcopyR rR2 rK1 rT2))

/-- The unit columns' start: `pre := A`, `post := width − A − 1`, `U := h`. -/
def uInit : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR rA rPU rT2) (.seq (FinalPass.Hash4.wcopyR rWd rQU rT2)
    (.seq (UnaryArith.subW QB) (.seq (.dec rQU) (FinalPass.Hash4.wcopyR rH rU rT2))))

/-- **The emission**: the marks of `natWord width`, the blocks, the unit columns, the closing `0`. -/
def colsE : WM GS GR :=
  .seq (writeNatM gOUT WN) (.seq blkInit (.seq blkLoop (.seq uInit (.seq uLoop (emitW gOUT rOP [false])))))

/-- **The columns writer's program.** -/
def colsW (cr : ℕ) : WM GS GR := .seq (preW cr) colsE

/-- The emission's cost. -/
def colsEC (P : StarParams) : ℕ :=
  (natBitLength (aOf P + hLv P) + 10) * (100 * (aOf P + hLv P) + 200) + 1 +
    ((18 * (aOf P + hLv P) + 3 + 1 + (30 * P.b + 10 + 1 + (18 * (P.r / 2) + 3))) + 1 +
      ((P.r / 2) * (bCost (aOf P + hLv P) (aOf P + hLv P) P.b + 4) + 1 + 1 +
        ((18 * aOf P + 3 + 1 + (18 * (aOf P + hLv P) + 3 + 1 + (30 * aOf P + 10 + 1 + (1 + 1 + (18 * hLv P + 3))))) +
          1 + (hLv P * (uCost (aOf P + hLv P) + 4) + 1 + 1 + 8))))

theorem width_le_n (P : StarParams) : aOf P + hLv P ≤ P.n := by
  have hrs := rb_eq P
  have hrb := P.r_mul_b_le
  have hr4 := P.four_r_le_n
  have hr2 := P.two_le_r
  unfold hLv
  omega

theorem cap_total (n w L : ℕ) (hw : w ≤ n) (hL : L ≤ w + 1) :
    2 * (2 * L + 1) + w * (4 * w + 2) + 1 ≤ 5 * ((n + 2) * (n + 2)) := by
  have : w * (4 * w + 2) ≤ n * (4 * n + 2) := Nat.mul_le_mul hw (by omega)
  nlinarith

theorem colsE_spec (cap : ℕ) (P : StarParams) (σ : WState GS GR) (hA : σ.val rA = aOf P) (hH : σ.val rH = hLv P)
    (hWd : σ.val rWd = aOf P + hLv P) (hOP : σ.val rOP = 0) (hK : σ.val rK = 0) (hT : σ.val rT = 0)
    (hB : σ.val rB = P.b) (hR2 : σ.val rR2 = P.r / 2)
    (hz : ∀ r : Fin GR, 32 ≤ r.val → r.val ≠ 40 → r.val ≠ 41 → r ≠ rB → r ≠ rR2 → σ.val r = 0)
    (hO : σ.st gOUT = []) (hsh : σ.sh gOUT = 0) (hcap : 5 * ((P.n + 2) * (P.n + 2)) ≤ cap) :
    ∃ τ c, WExec cap colsE σ τ c ∧ τ.st gOUT = PrimT.C4Geo.colsField P ∧ τ.st gIN = σ.st gIN ∧
      c ≤ colsEC P := by
  have hwn := width_le_n P
  have hbn := b_le P
  have hr4 := P.four_r_le_n
  have hr2 := P.two_le_r
  have hrs := rb_eq P
  have hsq : 2 * (P.n + 2) ≤ (P.n + 2) * (P.n + 2) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨w, hwd⟩ : ∃ x, x = aOf P + hLv P := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ x, x = aOf P := ⟨_, rfl⟩
  obtain ⟨h, hhd⟩ : ∃ x, x = hLv P := ⟨_, rfl⟩
  obtain ⟨nb, hnbd⟩ : ∃ x, x = P.r / 2 := ⟨_, rfl⟩
  have hAh : A + h = w := by rw [hAd, hhd, hwd]
  have hnbA : nb * P.b = A := by rw [hnbd, hAd]; rfl
  have hwn' : w ≤ P.n := by rw [hwd]; exact hwn
  have hbw : P.b ≤ w := by
    have : 1 ≤ nb := by rw [hnbd]; omega
    have := Nat.mul_le_mul_right P.b this
    omega
  have hnbn : nb ≤ P.n := by rw [hnbd]; omega
  rw [← hAd] at hA
  rw [← hhd] at hH
  rw [← hwd] at hWd
  rw [← hnbd] at hR2
  have zz : ∀ r : Fin GR, 32 ≤ r.val → r.val ≠ 40 → r.val ≠ 41 → r ≠ rB → r ≠ rR2 → σ.val r = 0 := hz
  -- 1: the width's natWord
  have wn0 : WN 0 = rWd := rfl
  have wn7 : WN 7 = rOP := rfl
  have e1 := writeNatM_spec cap gOUT WN σ (zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (zz _ (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [hsh, hO]; rfl)
    (by
      rw [wn0, wn7, hWd, hOP]
      have := CopyNat.natBitLength_le_self_succ w
      omega)
  rw [wn0, wn7, hWd] at e1
  obtain ⟨σ1, h1⟩ : ∃ x, x = appendO σ gOUT rOP (marks (RepairRepresentation.natWord w)) := ⟨_, rfl⟩
  rw [← h1] at e1
  obtain ⟨a1, a2, a3, a4, a5⟩ := appO σ (marks (RepairRepresentation.natWord w))
  rw [← h1] at a1 a2 a3 a4 a5
  have hLw := CopyNat.natBitLength_le_self_succ w
  have lenM : (marks (RepairRepresentation.natWord w)).length = 2 * (2 * natBitLength w + 1) := by
    rw [RepairOrdinary.Streaming.marks_length, natWord_length]
  have o1 : σ1.val rOP = 2 * (2 * natBitLength w + 1) := by rw [a3, hOP, lenM]; ring
  have ho1 : σ1.sh gOUT = (σ1.st gOUT).length := by rw [a2, a1, hsh, hO]; simp
  have z1 : ∀ r : Fin GR, 32 ≤ r.val → r.val ≠ 40 → r.val ≠ 41 → r ≠ rB → r ≠ rR2 → σ1.val r = 0 :=
    fun r a b c d e => by
      rw [a5 r (fun h => by rw [h] at a; revert a; decide)]; exact zz r a b c d e
  -- 2: the blocks' start
  have c1 := FinalPass.Hash4.wcopyR_spec cap rWd rPost rT2 (by decide) (by decide) (by decide) σ1
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [a5 _ (by decide), hWd]; omega)
  rw [a5 rWd (by decide), hWd] at c1
  obtain ⟨σ2, h2⟩ : ∃ x, x = σ1.setv rPost w := ⟨_, rfl⟩
  rw [← h2] at c1
  have k2 : ∀ r, r ≠ rPost → σ2.val r = σ1.val r := fun r hr => by rw [h2]; simp [Function.update_of_ne hr]
  have p0 : PB 0 = rPost := rfl
  have p1 : PB 1 = rB := rfl
  have p2 : PB 2 = rT2 := rfl
  have p3 : PB 3 = rZ := rfl
  have c2 := UnaryArith.subW_spec cap PB σ2
    (by rw [p2, k2 _ (by decide)]; exact z1 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [p3, k2 _ (by decide)]; exact z1 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [p0, h2]; simp; omega) (by rw [p1, k2 _ (by decide), a5 _ (by decide), hB]; omega)
  rw [p0, p1, k2 rB (by decide), a5 rB (by decide), hB, show σ2.val rPost = w by rw [h2]; simp] at c2
  obtain ⟨σ3, h3⟩ : ∃ x, x = σ2.setv rPost (w - P.b) := ⟨_, rfl⟩
  rw [← h3] at c2
  have k3 : ∀ r, r ≠ rPost → σ3.val r = σ1.val r := fun r hr => by
    rw [h3]; simp [Function.update_of_ne hr]; exact k2 r hr
  have c3 := FinalPass.Hash4.wcopyR_spec cap rR2 rK1 rT2 (by decide) (by decide) (by decide) σ3
    (by rw [k3 _ (by decide)]; exact z1 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [k3 _ (by decide)]; exact z1 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [k3 _ (by decide), a5 _ (by decide), hR2]; omega)
  rw [k3 rR2 (by decide), a5 rR2 (by decide), hR2] at c3
  obtain ⟨σ4, h4⟩ : ∃ x, x = σ3.setv rK1 nb := ⟨_, rfl⟩
  rw [← h4] at c3
  have k4 : ∀ r, r ≠ rPost → r ≠ rK1 → σ4.val r = σ1.val r := fun r a b => by
    rw [h4]; simp [Function.update_of_ne b]; exact k3 r a
  have st4 : σ4.st = σ1.st := by rw [h4, h3, h2]; rfl
  have sh4 : σ4.sh = σ1.sh := by rw [h4, h3, h2]; rfl
  have z4 : ∀ r : Fin GR, 32 ≤ r.val → r.val ≠ 40 → r.val ≠ 41 → r ≠ rB → r ≠ rR2 → r ≠ rPost → r ≠ rK1 →
      σ4.val r = 0 := fun r a b c d e f g => by rw [k4 r f g]; exact z1 r a b c d e
  have v4B : σ4.val rB = P.b := by rw [k4 _ (by decide) (by decide), a5 _ (by decide), hB]
  -- 3: the blocks
  have hB0 : blocksWord P w 0 = [] := rfl
  have inv0 : bInv P w σ4 0 σ4 := by
    refine ⟨by rw [hB0, List.append_nil], by rw [st4, sh4]; exact ho1, by rw [hB0]; rfl, fun s _ => rfl,
      fun r _ _ _ _ => rfl, ?_, ?_⟩
    · rw [z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp
    · rw [h4]; simp [Function.update_apply, Fin.ext_iff, GR]; rw [h3]; simp
  have hK1 : σ4.val rK1 = nb := by rw [h4]; simp
  have hbl := blocksWord_length_le P w nb (by omega)
  have hmul : nb * (P.b * (4 * w + 2)) + h * (4 * w + 2) = w * (4 * w + 2) := by
    rw [← Nat.mul_assoc, hnbA, ← Nat.add_mul, hAh]
  have htot := cap_total P.n w (natBitLength w) hwn' hLw
  obtain ⟨τB, eB, invB, hKB⟩ := UnionMachine.Round.wloopE cap rK1 blkBody (bCost w w P.b) nb (bInv P w σ4)
    (by omega)
    (blkLoop_step cap P w nb (by omega) σ4 v4B
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [k4 _ (by decide) (by decide), a5 _ (by decide), hK])
      (by rw [k4 _ (by decide) (by decide), a5 _ (by decide), hT])
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (z4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [k4 _ (by decide) (by decide), o1]; omega) (by omega) (by omega))
    σ4 inv0 hK1
  obtain ⟨bS, bSh, bOP, bO, bF, -, -⟩ := invB
  have fB : ∀ r, r ≠ rPre → r ≠ rPost → r ≠ rOP → r ≠ rK1 → τB.val r = σ.val r := fun r a b c d => by
    rw [bF r a b c d, k4 r b d, a5 r c]
  -- 4: the unit columns' start
  have d1 := FinalPass.Hash4.wcopyR_spec cap rA rPU rT2 (by decide) (by decide) (by decide) τB
    (by rw [fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [fB _ (by decide) (by decide) (by decide) (by decide), hA]; omega)
  rw [fB rA (by decide) (by decide) (by decide) (by decide), hA] at d1
  obtain ⟨υ1, g1⟩ : ∃ x, x = τB.setv rPU A := ⟨_, rfl⟩
  rw [← g1] at d1
  have j1 : ∀ r, r ≠ rPU → υ1.val r = τB.val r := fun r hr => by rw [g1]; simp [Function.update_of_ne hr]
  have d2 := FinalPass.Hash4.wcopyR_spec cap rWd rQU rT2 (by decide) (by decide) (by decide) υ1
    (by rw [j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide), hWd]; omega)
  rw [j1 rWd (by decide), fB rWd (by decide) (by decide) (by decide) (by decide), hWd] at d2
  obtain ⟨υ2, g2⟩ : ∃ x, x = υ1.setv rQU w := ⟨_, rfl⟩
  rw [← g2] at d2
  have j2 : ∀ r, r ≠ rQU → υ2.val r = υ1.val r := fun r hr => by rw [g2]; simp [Function.update_of_ne hr]
  have q0 : QB 0 = rQU := rfl
  have q1 : QB 1 = rA := rfl
  have q2 : QB 2 = rT2 := rfl
  have q3 : QB 3 = rZ := rfl
  have vA2 : υ2.val rA = A := by
    rw [j2 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide), hA]
  have d3 := UnaryArith.subW_spec cap QB υ2
    (by rw [q2, j2 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [q3, j2 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [q0, g2]; simp; omega) (by rw [q1, vA2]; omega)
  rw [q0, q1, vA2, show υ2.val rQU = w by rw [g2]; simp] at d3
  obtain ⟨υ3, g3⟩ : ∃ x, x = υ2.setv rQU (w - A) := ⟨_, rfl⟩
  rw [← g3] at d3
  have d4 := WExec.dec (cap := cap) rQU υ3 (by rw [g3]; simp; omega)
  obtain ⟨υ4, g4⟩ : ∃ x, x = υ3.setv rQU (υ3.val rQU - 1) := ⟨_, rfl⟩
  rw [← g4] at d4
  have j4 : ∀ r, r ≠ rQU → υ4.val r = υ1.val r := fun r hr => by
    rw [g4, g3]; simp [Function.update_of_ne hr]; exact j2 r hr
  have d5 := FinalPass.Hash4.wcopyR_spec cap rH rU rT2 (by decide) (by decide) (by decide) υ4
    (by rw [j4 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [j4 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide)]
        exact zz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [j4 _ (by decide), j1 _ (by decide), fB _ (by decide) (by decide) (by decide) (by decide), hH]; omega)
  rw [j4 rH (by decide), j1 rH (by decide), fB rH (by decide) (by decide) (by decide) (by decide), hH] at d5
  obtain ⟨υ5, g5⟩ : ∃ x, x = υ4.setv rU h := ⟨_, rfl⟩
  rw [← g5] at d5
  have j5 : ∀ r, r ≠ rU → r ≠ rQU → r ≠ rPU → υ5.val r = τB.val r := fun r a b c => by
    rw [g5]; simp [Function.update_of_ne a]; rw [j4 r b, j1 r c]
  have st5 : υ5.st = τB.st := by rw [g5, g4, g3, g2, g1]; rfl
  have sh5 : υ5.sh = τB.sh := by rw [g5, g4, g3, g2, g1]; rfl
  -- 5: the unit columns
  have hU0 : unitsWord A w 0 = [] := rfl
  have inv0' : uInv A w υ5 0 υ5 := by
    refine ⟨by rw [hU0, List.append_nil], by rw [st5, sh5]; exact bSh, by rw [hU0]; rfl, fun s _ => rfl,
      fun r _ _ _ _ => rfl, ?_, ?_⟩
    · rw [g5, wsetv_val_ne _ _ (by decide), j4 _ (by decide), g1]; simp
    · rw [g5, wsetv_val_ne _ _ (by decide), g4, g3]; simp
  have hU : υ5.val rU = h := by rw [g5]; simp
  have oU : υ5.val rOP = 2 * (2 * natBitLength w + 1) + (blocksWord P w nb).length := by
    rw [j5 _ (by decide) (by decide) (by decide), bOP, k4 _ (by decide) (by decide), o1]
  obtain ⟨τU, eU, invU, -⟩ := UnionMachine.Round.wloopE cap rU uStep (uCost w) h (uInv A w υ5)
    (by omega)
    (uLoop_step cap A w h (by omega) υ5
      (by rw [j5 _ (by decide) (by decide) (by decide), fB _ (by decide) (by decide) (by decide) (by decide), hK])
      (by rw [j5 _ (by decide) (by decide) (by decide), fB _ (by decide) (by decide) (by decide) (by decide), hT])
      (by rw [oU]; omega) (by omega))
    υ5 inv0' hU
  obtain ⟨uS, uSh, uOP, uO, -, -, -⟩ := invU
  have hul := unitsWord_length A w h (by omega)
  -- 6: the closing `0`
  have e6 := emitW_spec cap gOUT rOP [false] τU uSh (by rw [uOP, oU, hul]; simp; omega)
  obtain ⟨f1, -, -, f4, -⟩ := appO τU [false]
  refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.seq c1 (WExec.seq c2 c3)) (WExec.seq eB
    (WExec.seq (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 d5)))) (WExec.seq eU e6)))), ?_, ?_, ?_⟩
  · rw [f1, uS, st5, bS, st4, a1, hO, colsField_emit]
    rw [hwd, hAd, hhd, hnbd]
    rfl
  · have hIO : gIN ≠ gOUT := by decide
    rw [f4 _ hIO, uO _ hIO, st5, bO _ hIO, st4, a4 _ hIO]
  · unfold colsEC
    rw [← hwd, ← hAd, ← hhd, ← hnbd]
    simp only [List.length_cons, List.length_nil]
    omega

/-! ## The cost is polynomial -/

/-- **The emission's cost is at most `2000·(n+2)^4`.** -/
theorem colsEC_le (P : StarParams) : colsEC P ≤ 2000 * (P.n + 2) ^ 4 := by
  have hwn := width_le_n P
  have hbn := b_le P
  have hr4 := P.four_r_le_n
  have hr2 := P.two_le_r
  have hL := CopyNat.natBitLength_le_self_succ (aOf P + hLv P)
  obtain ⟨M, hM⟩ : ∃ x, x = P.n + 2 := ⟨_, rfl⟩
  rw [← hM]
  have aw : aOf P + hLv P ≤ M := by omega
  have ab : P.b ≤ M := by omega
  have anb : P.r / 2 ≤ M := by omega
  have aA : aOf P ≤ M := by omega
  have ah : hLv P ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have u1 : cwCost P.b ≤ cwCost M := by
    unfold cwCost
    have := Nat.mul_le_mul ab (show 150 * P.b + 200 + 4 ≤ 150 * M + 200 + 4 by omega)
    omega
  have u2 : colCost (aOf P + hLv P) (aOf P + hLv P) P.b ≤ colCost M M M := by
    unfold colCost; omega
  have u3 : iCost (aOf P + hLv P) (aOf P + hLv P) P.b ≤ iCost M M M := by
    unfold iCost; omega
  have u4 : bCost (aOf P + hLv P) (aOf P + hLv P) P.b ≤ bCost M M M := by
    unfold bCost
    have := Nat.mul_le_mul ab (show iCost (aOf P + hLv P) (aOf P + hLv P) P.b + 4 ≤ iCost M M M + 4 by omega)
    omega
  have u5 : P.r / 2 * (bCost (aOf P + hLv P) (aOf P + hLv P) P.b + 4) ≤ M * (bCost M M M + 4) :=
    Nat.mul_le_mul anb (by omega)
  have u6 : hLv P * (uCost (aOf P + hLv P) + 4) ≤ M * (uCost M + 4) :=
    Nat.mul_le_mul ah (by unfold uCost; omega)
  have u7 : (natBitLength (aOf P + hLv P) + 10) * (100 * (aOf P + hLv P) + 200) ≤ (M + 10) * (100 * M + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsum : colsEC P ≤ (M + 10) * (100 * M + 200) + M * (bCost M M M + 4) + M * (uCost M + 4) + 200 * M + 200 := by
    unfold colsEC; omega
  have p2 : 2 * M ≤ M ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hM2
  have p3 : 2 * M ^ 2 ≤ M ^ 3 :=
    calc 2 * M ^ 2 ≤ M * M ^ 2 := Nat.mul_le_mul_right _ hM2
      _ = M ^ 3 := by ring
  have p4 : 2 * M ^ 3 ≤ M ^ 4 :=
    calc 2 * M ^ 3 ≤ M * M ^ 3 := Nat.mul_le_mul_right _ hM2
      _ = M ^ 4 := by ring
  refine le_trans hsum ?_
  unfold bCost iCost colCost cwCost uCost
  nlinarith [p2, p3, p4, hM2]

/-! ## The writer -/

theorem colsW_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W)
    (hW2 : 5 * ((P.n + 2) * (P.n + 2)) ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (colsW cr) (σG w P.n W) σF c ∧ σF.st gOUT = PrimT.C4Geo.colsField P ∧
      σF.st gIN = RepairOrdinary.frame w ∧ c ≤ numsGCostE P cr + 40 * P.n + 21 + 2000 * (P.n + 2) ^ 4 := by
  obtain ⟨σ0, c0, e0, hA, hH, hWd, hOP, hK, hT, hB, hR2, hz, hst, hsh, hc0⟩ := preW_spec cr W P hrP sfx w hw hW
  have hO : σ0.st gOUT = [] := by rw [hst]; simp [σG, gOUT, gIN, gNT, gCT, gAUX]
  obtain ⟨τ, c1, e1, hOut, hIn, hc1⟩ := colsE_spec (2 * W + 2) P σ0 hA hH hWd hOP hK hT hB hR2 hz hO hsh
    (by omega)
  have hle := colsEC_le P
  refine ⟨τ, _, WExec.seq e0 e1, hOut, ?_, by omega⟩
  rw [hIn, hst]
  simp [σG]

/-- **The columns writer's run**: `frame w ↦ C4Geo.colsField P` (C4.L's column header of `φ`). -/
theorem cols_run (cr Dv Cv Bud : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ UnaryCalc.value Dv Cv P.n)
    (hW2 : 5 * ((P.n + 2) * (P.n + 2)) ≤ UnaryCalc.value Dv Cv P.n)
    (hB : 2 * (frontCost w P.n Dv Cv + (numsGCostE P cr + 40 * P.n + 21 + 2000 * (P.n + 2) ^ 4)) + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (geoM (colsW cr) Dv Cv) Bud (gInP Dv) (gOutP Dv) w (PrimT.C4Geo.colsField P) := by
  obtain ⟨σF, c, hx, hO, hI, hc⟩ := colsW_spec cr (UnaryCalc.value Dv Cv P.n) P hrP sfx w hw hW hW2
  exact geo_run (colsW cr) Dv Cv P.n c Bud w sfx _ hw σF hx hI hO (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.GeoColsRun
