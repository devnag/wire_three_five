import Proof.Wire_3_5.UnionMachine.RadBlk

/-! # RADIX, stage 5a (8): one digit (P3:2596-2604)

Digit `d` of row `(g, p)`: its pool indices `gis_d` are read in place on `GS` (`DigsW`'s word); the table word at
`L_d = |gis_d|` is cut from the table at `G` on `TS` and appended to `T`; the block writer then appends the digit's
`2(M+1)` factor blocks to the record `O`; `T`'s head returns to its end and `GS`'s moves past the digit.

* `digA` / **`digA_spec`**: `Rg 0 := L_d`, `Gl := G − L_d`, `T_d` appended to `T` (`RadTrunc2.truncP_spec`),
  `Rg 6 := capC D L_d`, `Tq := |T_d|`, `T`'s head back at `T_d`'s start;
* `digC` / **`digC_spec`**: `T`'s head forward, `Rg 6`, `Gl`, `Rg 0` cleared, `GS` past the digit;
* `digBody` / **`digBody_spec`**: the digit (`digA ; RadBlk.sgnP ; digC`): the record gets `digBlocks`, `T` gets
  `T_d` (head at its end), `GS` moves past `gisWord gis_d`; every register as at the entry.

Paper quantity of the main type: the RADIX row's factor blocks of one digit (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadDig
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

variable {ns nr : ℕ} (cap : ℕ)

/-- Digit `d`'s table word (at `L_d = |gis|`). -/
def tdW (Dl : ListData) (L : ℕ) : List Bool := levelWord Dl.M Dl.J Dl.W (rowsOf Dl L)

theorem tdW_take (Dl : ListData) (L G : ℕ) (h : L ≤ G) :
    levelWord Dl.M Dl.J Dl.W (fun j => (rowsOf Dl G j).take L) = tdW Dl L := by
  unfold tdW
  congr 1
  funext j
  exact RadTrunc.rowsOf_take Dl L G j h

theorem rowsOf_len (Dl : ListData) (G j : ℕ) : (rowsOf Dl G j).length = G := by simp [rowsOf]

section Dig
variable (Z : Fin 11 ↪ Fin nr) (Rg : Fin radBlkK ↪ Fin nr)

/-- The digit's preparation: count, `G − L`, the cut table, `capC`, `|T_d|` kept, `T` back. -/
def digA (T TS GS : Fin (ns + 1)) : WM ns nr :=
  .seq (RadCnt.cntP GS (Z 0) (Rg 0)) (.seq (RadTrunc2.glW (Rg 1) (Rg 0) (Z 1) (Z 6) (Z 7))
    (.seq (RadTrunc2.truncP T TS (Z 2) (Z 3) (Z 4) (Z 5) (Rg 0) (Z 1))
      (.seq (RadTrunc2.capW (Z 2) (Rg 0) (Rg 6) (Z 6)) (.seq (wcopyR (Z 2) (Z 8) (Z 6)) (WM.rewind T (Z 2))))))

/-- The state after the preparation. -/
def digAOut (T : Fin (ns + 1)) (σ : WState ns nr) (Dl : ListData) (gis : List ℕ) (G : ℕ) : WState ns nr :=
  ((((σ.sets T (σ.st T ++ tdW Dl gis.length)).setv (Rg 0) gis.length).setv (Z 1) (G - gis.length)).setv (Rg 6)
    (capC Dl gis.length)).setv (Z 8) (tdW Dl gis.length).length

/-- The preparation's cost. -/
def digACost (Dl : ListData) (gis : List ℕ) (G : ℕ) : ℕ :=
  (RadCnt.cntCost gis + 1 + (5 * (gis.flatMap RadCnt.itemW).length + 1)) + 1 +
    ((18 * G + 3 + 1 + (18 * gis.length + 3 + 1 + (5 * gis.length + 1))) + 1 +
      (RadTrunc2.truncCost Dl.M (fun j => pow (topW Dl.J Dl.W j)) (fun j => topW Dl.J Dl.W j) gis.length G
        (levels Dl.J) (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length + 1 +
        (RadTrunc2.capWCost (tdW Dl gis.length).length gis.length + 1 +
          ((18 * (tdW Dl gis.length).length + 3) + 1 + (5 * (tdW Dl gis.length).length + 1)))))

theorem digA_spec (T TS GS : Fin (ns + 1)) (hTS : T ≠ TS) (hZR : ∀ i j, Z i ≠ Rg j)
    (σ : WState ns nr) (Dl : ListData) (gis : List ℕ) (G : ℕ) (restS restG : List Bool)
    (hLG : gis.length ≤ G)
    (hS : (σ.st TS).drop (σ.sh TS) = levelWord Dl.M Dl.J Dl.W (rowsOf Dl G) ++ restS)
    (hG : (σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG) (hT : σ.sh T = (σ.st T).length)
    (h0 : σ.val (Rg 0) = 0) (h1 : σ.val (Rg 1) = G) (h6 : σ.val (Rg 6) = 0)
    (hz : ∀ i : Fin 11, i.val ≤ 8 → σ.val (Z i) = 0)
    (hc1 : (gis.flatMap RadCnt.itemW).length ≤ cap) (hc2 : G < cap)
    (hc3 : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length ≤ cap)
    (hc4 : capC Dl gis.length ≤ cap) :
    WExec cap (digA Z Rg T TS GS) σ (digAOut Z Rg T σ Dl gis G) (digACost Dl gis G) := by
  have hRZ : ∀ i j, Rg j ≠ Z i := fun i j e => hZR i j e.symm
  have hcc : capC Dl gis.length = 4 * ((tdW Dl gis.length).length + gis.length + 1) := rfl
  have hc4' : 4 * ((tdW Dl gis.length).length + gis.length + 1) ≤ cap := hcc ▸ hc4
  have z0 := hz 0 (by decide)
  have z1 := hz 1 (by decide)
  have z2 := hz 2 (by decide)
  have z3 := hz 3 (by decide)
  have z4 := hz 4 (by decide)
  have z5 := hz 5 (by decide)
  have z6 := hz 6 (by decide)
  have z7 := hz 7 (by decide)
  have z8 := hz 8 (by decide)
  -- 1: the count
  have s1 := RadCnt.cntP_spec cap GS (Z 0) (Rg 0) (hZR 0 0) gis restG σ hG z0 hc1 (by rw [h0]; omega)
  rw [h0, Nat.zero_add] at s1
  -- 2: G − L
  have s2 := RadTrunc2.glW_spec cap (Rg 1) (Rg 0) (Z 1) (Z 6) (Z 7) (by simp [hZR, hRZ])
    (σ.setv (Rg 0) gis.length) (by simp [hZR, z1]) (by simp [hZR, z6]) (by simp [hZR, z7])
    (by simp [h1]; omega) (by simp; omega)
  have v1 : (σ.setv (Rg 0) gis.length).val (Rg 1) = G := by simp [h1]
  have v0 : (σ.setv (Rg 0) gis.length).val (Rg 0) = gis.length := by simp
  rw [v1, v0] at s2
  -- 3: the cut table
  set σ2 := (σ.setv (Rg 0) gis.length).setv (Z 1) (G - gis.length) with hσ2
  have s3 := RadTrunc2.truncP_spec cap T TS hTS (Z 2) (Z 3) (Z 4) (Z 5) (Rg 0) (Z 1) (by simp [hZR, hRZ]) σ2
    Dl.M Dl.J Dl.W (rowsOf Dl G) gis.length G restS hLG (rowsOf_len Dl G) (by simpa [σ2] using hS)
    (by simpa [σ2] using hT) (by simp [hZR, hRZ, σ2, hZR, hRZ, z4]) (by simp [hZR, hRZ, σ2, hZR, hRZ, z5]) (by simp [hZR, hRZ, σ2, hZR, hRZ])
    (by simp [hZR, hRZ, σ2]) (by simp [hZR, hRZ, σ2, hZR, hRZ, z3])
    (by rw [tdW_take Dl gis.length G hLG]; simp [hZR, hRZ, σ2, hZR, hRZ, z2]; omega) hc3
  rw [tdW_take Dl gis.length G hLG] at s3
  -- 4: capC
  set σ3 := appendO σ2 T (Z 2) (tdW Dl gis.length) with hσ3
  have s4 := RadTrunc2.capW_spec cap (Z 2) (Rg 0) (Rg 6) (Z 6) (hZR 2 6) (Z.injective.ne (by decide))
    (Rg.injective.ne (by decide)) (hRZ 6 0) (hRZ 6 6) σ3 (by simp [hZR, hRZ, σ3, σ2, hRZ, h6]) (by simp [hZR, hRZ, σ3, σ2, z6])
    (by simp [hZR, hRZ, σ3, σ2, hRZ, z2]; omega)
  have w2 : σ3.val (Z 2) = (tdW Dl gis.length).length := by simp [hZR, hRZ, σ3, σ2, z2]
  have w0 : σ3.val (Rg 0) = gis.length := by simp [hZR, hRZ, σ3, σ2, hRZ]
  rw [w2, w0, ← hcc] at s4
  -- 5: |T_d| kept
  set σ4 := σ3.setv (Rg 6) (capC Dl gis.length) with hσ4
  have s5 := wcopyR_spec cap (Z 2) (Z 8) (Z 6) (Z.injective.ne (by decide)) (Z.injective.ne (by decide))
    (Z.injective.ne (by decide)) σ4 (by simp [hZR, hRZ, σ4, σ3, σ2, hRZ, z8]) (by simp [hZR, hRZ, σ4, σ3, σ2, hRZ, z6])
    (by simp [hZR, hRZ, σ4, σ3, σ2, hRZ, z2]; omega)
  have w2' : σ4.val (Z 2) = (tdW Dl gis.length).length := by simp [hZR, hRZ, σ4, hZR, w2]
  rw [w2'] at s5
  -- 6: T back
  set σ5 := σ4.setv (Z 8) (tdW Dl gis.length).length with hσ5
  have s6 := wrewind_spec cap T (Z 2) (tdW Dl gis.length).length σ5 (by simp [hZR, hRZ, σ5, σ4, hZR, w2])
    (by simp [hZR, hRZ, σ5, σ4, hZR, w2]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_ ?_
  · simp only [σ5, σ4, σ3, σ2, digAOut]
    apply WState.eq
    · funext j
      by_cases hj : j = T
      · subst hj; simp [hT]
      · simp [Function.update_apply, hj]
    · simp
    · funext q
      by_cases hq2 : q = Z 2
      · subst hq2; simp [Function.update_apply, hZR, z2]
      · simp [Function.update_apply, hq2]
    · simp
  · unfold digACost; omega

/-- The digit's cleanup: `T`'s head forward by `Tq`, `Rg 6`, `Gl`, `Rg 0` cleared, `GS` past the digit. -/
def digC (T GS : Fin (ns + 1)) : WM ns nr :=
  .seq (RadTrunc2.fwdN T (Z 8)) (.seq (WM.clear (Rg 6)) (.seq (WM.clear (Z 1)) (.seq (WM.clear (Rg 0))
    (RadCnt.skipG GS (Z 0) (Rg 0)))))

/-- The cleanup's cost. -/
def digCCost (gis : List ℕ) (G tl cc : ℕ) : ℕ :=
  (5 * tl + 1) + 1 + ((3 * cc + 1) + 1 + ((3 * (G - gis.length) + 1) + 1 + ((3 * gis.length + 1) + 1 +
    (RadCnt.cntCost gis + 1 + (1 + 1 + ((3 * (gis.flatMap RadCnt.itemW).length + 1) + 1 + (3 * gis.length + 1)))))))

theorem digC_spec (T GS : Fin (ns + 1)) (hTG : T ≠ GS) (hZR : ∀ i j, Z i ≠ Rg j) (τ : WState ns nr)
    (gis : List ℕ) (G tl cc : ℕ) (restG : List Bool)
    (hG : (τ.st GS).drop (τ.sh GS) = gisWord gis ++ restG)
    (h8 : τ.val (Z 8) = tl) (h6 : τ.val (Rg 6) = cc) (h1 : τ.val (Z 1) = G - gis.length)
    (h0 : τ.val (Rg 0) = gis.length) (hz0 : τ.val (Z 0) = 0)
    (hc1 : (gis.flatMap RadCnt.itemW).length ≤ cap) (hc2 : gis.length < cap) (hc3 : tl ≤ cap) (hc4 : cc ≤ cap)
    (hc5 : G ≤ cap) :
    WExec cap (digC Z Rg T GS) τ
      (((((((τ.setv (Z 8) 0).seth T (τ.sh T + tl)).setv (Rg 6) 0).setv (Z 1) 0).setv (Rg 0) 0).seth GS
        (τ.sh GS + (gisWord gis).length))) (digCCost gis G tl cc) := by
  have hRZ : ∀ i j, Rg j ≠ Z i := fun i j e => hZR i j e.symm
  have s1 := RadTrunc2.fwdN_spec cap T (Z 8) tl τ h8 (by omega)
  have s2 := wclear_spec cap (Rg 6) cc ((τ.setv (Z 8) 0).seth T (τ.sh T + tl)) (by simp [hRZ, h6])
    (by simp [hRZ, h6]; omega)
  have s3 := wclear_spec cap (Z 1) (G - gis.length) ((((τ.setv (Z 8) 0).seth T (τ.sh T + tl))).setv (Rg 6) 0)
    (by simp [hZR, hRZ, h1]) (by simp [hZR, hRZ, h1]; omega)
  have s4 := wclear_spec cap (Rg 0) gis.length
    (((((τ.setv (Z 8) 0).seth T (τ.sh T + tl))).setv (Rg 6) 0).setv (Z 1) 0) (by simp [hZR, hRZ, h0])
    (by simp [hZR, hRZ, h0]; omega)
  have s5 := RadCnt.skipG_spec cap GS (Z 0) (Rg 0) (hZR 0 0) gis restG
    ((((((τ.setv (Z 8) 0).seth T (τ.sh T + tl))).setv (Rg 6) 0).setv (Z 1) 0).setv (Rg 0) 0)
    (by simp [Function.update_apply, Ne.symm hTG]; exact hG) (by simp [hZR, hRZ, hz0]) (by simp) hc1 hc2
  have eG : ((((((τ.setv (Z 8) 0).seth T (τ.sh T + tl))).setv (Rg 6) 0).setv (Z 1) 0).setv (Rg 0) 0).sh GS =
      τ.sh GS := by simp [Function.update_apply, Ne.symm hTG]
  rw [eG] at s5
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
  unfold digCCost; omega

/-- **One digit.** -/
def digBody (Wb : RadSpec3.RadBlockW3) (O T TS GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (OP : Fin nr) :
    WM ns nr :=
  .seq (digA Z Rg T TS GS) (.seq (RadBlk.sgnP Wb O T GS Sc Rg OP (Z 9) (Z 10) (Z 6)) (digC Z Rg T GS))

/-- The state after one digit: the record gets the digit's blocks, `T` gets `T_d` (head at its end), `GS`'s head
passes the digit. -/
def digOut (O T GS : Fin (ns + 1)) (OP : Fin nr) (σ : WState ns nr) (Dl : ListData) (gis : List ℕ) (G row : ℕ) :
    WState ns nr :=
  ((((appendO σ O OP (RadBlk.digBlocks Dl gis G row)).sets T (σ.st T ++ tdW Dl gis.length)).seth T
    (σ.sh T + (tdW Dl gis.length).length)).seth GS (σ.sh GS + (gisWord gis).length))

/-- One digit's cost. -/
def digCost (Wb : RadSpec3.RadBlockW3) (Dl : ListData) (gis : List ℕ) (G : ℕ) : ℕ :=
  digACost Dl gis G + 1 + ((3 + 1 + (RadBlk.tCost Dl.M (Wb.bound cap) + 1 + (1 + 1 + RadBlk.tCost Dl.M (Wb.bound cap))))
    + 1 + digCCost gis G (tdW Dl gis.length).length (capC Dl gis.length))

/-- **The digit's entry**: the streams (the record's head at its end, `T`'s at its end, the table at `G` read in
place on `TS`, the digit's indices read in place on `GS`, the block writer's scratch blank), the registers (the
block writer's fixed inputs `G`, `row`, `3·listBound D`, `M` in `Z 9`, the rest `0`). -/
structure DigIn (O T TS GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (OP : Fin nr) (Dl : ListData) (G row : ℕ)
    (σ : WState ns nr) : Prop where
  OT : O ≠ T
  OG : O ≠ GS
  TG : T ≠ GS
  TTS : T ≠ TS
  ScI : Function.Injective Sc
  ScN : ∀ i, Sc i ≠ O ∧ Sc i ≠ T ∧ Sc i ≠ GS
  RgOP : ∀ j, Rg j ≠ OP
  ZOP : ∀ i, Z i ≠ OP
  ZR : ∀ i j, Z i ≠ Rg j
  S : ∃ restS, (σ.st TS).drop (σ.sh TS) = levelWord Dl.M Dl.J Dl.W (rowsOf Dl G) ++ restS
  ho : σ.sh O = (σ.st O).length
  hT : σ.sh T = (σ.st T).length
  Sc0 : ∀ i, σ.st (Sc i) = [] ∧ σ.sh (Sc i) = 0
  r1 : σ.val (Rg 1) = G
  r2 : σ.val (Rg 2) = row
  r5 : σ.val (Rg 5) = 3 * ListMachine.listBound Dl
  rz : ∀ j : Fin radBlkK, j ≠ 1 → j ≠ 2 → j ≠ 5 → σ.val (Rg j) = 0
  z9 : σ.val (Z 9) = Dl.M
  zz : ∀ i : Fin 11, i ≠ 9 → σ.val (Z i) = 0

theorem digBody_spec (Wb : RadSpec3.RadBlockW3) (O T TS GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (OP : Fin nr)
    (Dl : ListData) (gis : List ℕ) (G row : ℕ) (σ : WState ns nr) (hin : DigIn Z Rg O T TS GS Sc OP Dl G row σ)
    (restG : List Bool) (hG : (σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG) (hLG : gis.length ≤ G)
    (hc1 : (gis.flatMap RadCnt.itemW).length ≤ cap) (hc2 : G < cap)
    (hc3 : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length ≤ cap) (hc4 : capC Dl gis.length ≤ cap)
    (hcM : Dl.M + 1 ≤ cap)
    (hneed : ∀ t ≤ Dl.M, ∀ sgn : Bool, ∀ olen ≤ (σ.st O).length + (RadBlk.digBlocks Dl gis G row).length,
      Wb.need (blkSize Dl gis G row t sgn olen) ≤ cap)
    (hop : σ.val OP + (RadBlk.digBlocks Dl gis G row).length ≤ cap) :
    WExec cap (digBody Z Rg Wb O T TS GS Sc OP) σ (digOut O T GS OP σ Dl gis G row) (digCost cap Wb Dl gis G) := by
  have hZR := hin.ZR
  have hRZ : ∀ i j, Rg j ≠ Z i := fun i j e => hZR i j e.symm
  have hZO := hin.ZOP
  have hRO := hin.RgOP
  have hOZ : ∀ i, OP ≠ Z i := fun i e => hZO i e.symm
  have hOR : ∀ j, OP ≠ Rg j := fun j e => hRO j e.symm
  obtain ⟨restS, hS⟩ := hin.S
  have hcc : capC Dl gis.length = 4 * ((tdW Dl gis.length).length + gis.length + 1) := rfl
  have hc4' : 4 * ((tdW Dl gis.length).length + gis.length + 1) ≤ cap := hcc ▸ hc4
  have sA := digA_spec cap Z Rg T TS GS hin.TTS hZR σ Dl gis G restS restG hLG hS hG hin.hT
    (hin.rz 0 (by decide) (by decide) (by decide)) hin.r1 (hin.rz 6 (by decide) (by decide) (by decide))
    (fun i hi => hin.zz i (fun e => by subst e; exact absurd hi (by decide))) hc1 hc2 hc3 hc4
  set τ1 := digAOut Z Rg T σ Dl gis G with hτ1
  have eO : τ1.st O = σ.st O := by simp [τ1, digAOut, Function.update_apply, hin.OT]
  have eOh : τ1.sh O = σ.sh O := by simp [τ1, digAOut]
  have eOP : τ1.val OP = σ.val OP := by simp [τ1, digAOut, hOZ, hOR]
  have hB : RadBlk.BlkIn O T GS Sc Rg OP Dl gis G row τ1 := by
    refine ⟨hin.OT, hin.OG, hin.TG, hin.ScI, hin.ScN, hRO, ⟨[], ?_⟩, ⟨restG, ?_⟩, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_,
      fun j hj => ?_⟩
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hin.hT]; rfl
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, Function.update_apply, Ne.symm hin.TG, hG]
    · rw [eO, eOh]; exact hin.ho
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, Function.update_apply, (hin.ScN i).2.1, hin.Sc0 i]
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ]
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.r1]
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.r2]
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.r5]
    · simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ]
    · have j0 : j ≠ 0 := fun e => by subst e; exact absurd hj (by decide)
      have j1 : j ≠ 1 := fun e => by subst e; exact absurd hj (by decide)
      have j2 : j ≠ 2 := fun e => by subst e; exact absurd hj (by decide)
      have j5 : j ≠ 5 := fun e => by subst e; exact absurd hj (by decide)
      have j6 : j ≠ 6 := fun e => by subst e; exact absurd hj (by decide)
      simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, j0, j6, hin.rz j j1 j2 j5]
  have sB := RadBlk.sgnP_spec cap Wb O T GS Sc Rg OP (Z 9) (Z 10) (Z 6) (Z.injective.ne (by decide))
    (Z.injective.ne (by decide)) (Z.injective.ne (by decide)) (hZO 10) (hZO 9) (hZO 6) (fun j => hRZ 10 j)
    (fun j => hRZ 6 j) (fun j => hRZ 9 j) Dl gis G row τ1 hB (by simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.z9])
    (by simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.zz 10 (by decide)]) (by simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.zz 6 (by decide)])
    (by simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.rz 3 (by decide) (by decide) (by decide)])
    (by simp [hZO, hOZ, hRO, hOR, τ1, digAOut, hZR, hRZ, hin.rz 4 (by decide) (by decide) (by decide)])
    (fun t ht sgn olen hol => hneed t ht sgn olen (by rw [eO] at hol; exact hol)) (by rw [eOP]; exact hop) hcM
  set τ2 := appendO τ1 O OP (RadBlk.digBlocks Dl gis G row) with hτ2
  have eG : (τ2.st GS).drop (τ2.sh GS) = gisWord gis ++ restG := by
    simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, Function.update_apply, Ne.symm hin.TG, Ne.symm hin.OG, hG]
  have sC := digC_spec cap Z Rg T GS hin.TG hZR τ2 gis G (tdW Dl gis.length).length (capC Dl gis.length) restG eG
    (by simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, hZR, hRZ, hOZ]) (by simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, hZR, hRZ, hOR])
    (by simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, hZR, hRZ, hOZ]) (by simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, hZR, hRZ, hOR])
    (by simp [hZO, hOZ, hRO, hOR, τ2, τ1, digAOut, hZR, hRZ, hOZ, hin.zz 0 (by decide)]) hc1 (by omega) (by omega) hc4 (by omega)
  refine WExec.cast cap (WExec.seq sA (WExec.seq sB sC)) ?_ le_rfl
  simp only [τ2, τ1, digAOut, digOut]
  apply WState.eq
  · funext j
    by_cases hjG : j = GS
    · subst hjG; simp [hZO, hOZ, hRO, hOR, Function.update_apply, Ne.symm hin.TG, Ne.symm hin.OG]
    · by_cases hjT : j = T
      · subst hjT; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hjG, Ne.symm hin.OT]
      · simp [hZO, hOZ, hRO, hOR, Function.update_apply, hjG, hjT]
  · funext j
    by_cases hjT : j = T
    · subst hjT; simp [hZO, hOZ, hRO, hOR, Function.update_apply, Ne.symm hin.OT]
    · simp [hZO, hOZ, hRO, hOR, Function.update_apply, hjT, hin.OT]
  · funext q
    by_cases h8 : q = Z 8
    · subst h8; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hZR, hRZ, hZO, hin.zz 8 (by decide)]
    · by_cases h6 : q = Rg 6
      · subst h6; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hZR, hRZ, hRO, hin.rz 6 (by decide) (by decide) (by decide)]
      · by_cases h1 : q = Z 1
        · subst h1; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hZR, hRZ, hZO, hin.zz 1 (by decide)]
        · by_cases h0 : q = Rg 0
          · subst h0; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hZR, hRZ, hRO, hin.rz 0 (by decide) (by decide) (by decide)]
          · by_cases hO : q = OP
            · subst hO; simp [hZO, hOZ, hRO, hOR, Function.update_apply, hOZ, hOR]
            · simp [hZO, hOZ, hRO, hOR, Function.update_apply, h8, h6, h1, h0, hO]
  · simp

end Dig

end NearCubicWires.WireExponent3_5.UnionMachine.RadDig
