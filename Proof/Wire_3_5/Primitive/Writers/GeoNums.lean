import Proof.Wire_3_5.Primitive.Writers.GeoFront

/-! # PA (d): the halves' and width's numbers, as one register-language program

P3:1188-1189 and P3:1213-1215 (star:partition): "Assign `r/2` whole blocks to each side [...] Split the remaining
`n−rb` coordinates as evenly as possible". From the request word, the program `numsG` computes the call's star
numbers (PA's verified `StarNums`, `r = rowBr c_r n`) and then `A = (r/2)·b` (the left blocks' coordinates),
`h = ⌈(n−rb)/2⌉` (the left unblocked ones), `A + h` (the printer's dense width) and `(n−rb) − h`; the writers
`widthW` and `sideW` then emit `1^(A+h)` and the marks of `1^A 0^A 1^h 0^rest` (`GeoSide` identifies these with
`C4Geo.width` / `C4Geo.sideField`).

* `aOf`, `hLv`, `numsG`, **`numsG_spec`**, `numsGExact`, `numsGExact_le`;
* `widthW`/**`widthW_spec`**, `sideW`/**`sideW_spec`**, **`width_runG`**, **`side_runG`** (`GeoFront.geo_run`).

Paper quantities of the main types: `A = (r/2)·b`, `h = ⌈(n−rb)/2⌉` (P3:1213-1215). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The numbers -/

/-- `A = (r/2)·b`, the left blocks' coordinates. -/
def aOf (P : StarParams) : ℕ := P.r / 2 * P.b

/-- `h = ⌈(n−rb)/2⌉`, the left half's unblocked coordinates. -/
def hLv (P : StarParams) : ℕ := (P.n - P.r * P.b + 1) / 2

theorem rb_eq (P : StarParams) : P.r * P.b = 2 * aOf P := by
  obtain ⟨q, hq⟩ := P.r_even
  unfold aOf
  rw [hq, show (q + q) / 2 = q by omega]
  ring

theorem frame_marksG (u : List Bool) : RepairOrdinary.frame u = marks u ++ [false] := by
  have := RepairOrdinary.Streaming.frame_append u []
  simpa [RepairOrdinary.frame] using this

/-! ## The numbers program -/

/-- The star block. -/
def SG : Fin 20 ↪ Fin GR := Fin.castLEEmb (by norm_num)

abbrev rF : Fin GR := 20
abbrev rC : Fin GR := 21
abbrev rP : Fin GR := 22
abbrev rT : Fin GR := 23
abbrev rA : Fin GR := 24
abbrev rX : Fin GR := 25
abbrev rTwo : Fin GR := 26
abbrev rH : Fin GR := 27
abbrev rWd : Fin GR := 28
abbrev rRst : Fin GR := 29
abbrev rOP : Fin GR := 30
abbrev rK : Fin GR := 31

/-- `rA += (r/2)·b`. -/
def MA : Fin 5 ↪ Fin GR := ⟨![6, 5, 24, 38, 39], by decide⟩
/-- `rH := rX / 2`. -/
def DV : Fin 9 ↪ Fin GR := ⟨![25, 26, 27, 32, 33, 34, 35, 36, 37], by decide⟩
/-- `rRst −= rH`. -/
def SB : Fin 4 ↪ Fin GR := ⟨![29, 27, 40, 41], by decide⟩

/-- Part 1: `n` and the star numbers. -/
def p1W (cr : ℕ) : WM GS GR := .seq (readNatM true gIN rF rC (SG 0) rP rT) (StarNums.starNumsM cr 0 SG)

/-- Part 2: `A = (r/2)·b` and `h = ⌈(n−rb)/2⌉`. -/
def p2W : WM GS GR :=
  .seq (UnaryArith.mulAddW MA) (.seq (addTo (SG 7) rX rT) (.seq (.inc rX) (.seq (.inc rTwo) (.seq (.inc rTwo)
    (UnaryArith.divW DV)))))

/-- Part 3: `width = A + h`, `rest = (n−rb) − h`. -/
def p3W : WM GS GR :=
  .seq (addTo rA rWd rT) (.seq (addTo rH rWd rT) (.seq (addTo (SG 7) rRst rT) (UnaryArith.subW SB)))

/-- **The numbers program**. -/
def numsG (cr : ℕ) : WM GS GR := .seq (p1W cr) (.seq p2W p3W)

theorem frame_splitG (x sfx : List Bool) :
    RepairOrdinary.frame (x ++ sfx) = [] ++ ParseNat.enc true x ++ (marks sfx ++ [false]) := by
  have h1 := RepairOrdinary.Streaming.frame_append x sfx
  rw [h1, frame_marksG]
  simp [ParseNat.enc]

theorem starOut_hiG (σ : WState GS GR) (P : StarParams) (fe : ℕ) (r : Fin GR) (hr : 20 ≤ r.val) :
    (StarNums.starOut σ SG P fe).val r = σ.val r := by
  have h : ∀ i, r ≠ SG i := fun i e => by
    have := congrArg Fin.val e
    have hi := i.isLt
    simp only [SG, Fin.castLEEmb_apply, Fin.val_castLE] at this
    omega
  simp [StarNums.starOut, Function.update_apply, h]

theorem b_le (P : StarParams) : P.b ≤ P.n := by
  have := P.r_mul_b_le; have := P.two_le_r; nlinarith

theorem part1_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σ' c, WExec (2 * W + 2) (p1W cr) (σG w P.n W) σ' c ∧ σ'.val (SG 5) = P.b ∧ σ'.val (SG 6) = P.r / 2 ∧
      σ'.val (SG 7) = P.n - P.r * P.b ∧ (∀ r : Fin GR, 20 ≤ r.val → σ'.val r = 0) ∧ σ'.st = (σG w P.n W).st ∧
      σ'.sh gOUT = 0 ∧ c = (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 + StarNums.starCost P.n cr 0 := by
  have hpow := CopyNat.two_pow_natBitLength_le P.n
  have r1 := readNatM_spec (2 * W + 2) true gIN rF rC (SG 0) rP rT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false]) (σG w P.n W)
    (by simp only [σG, if_pos rfl]; rw [hw]; exact frame_splitG _ _) (by rfl) rfl rfl rfl rfl
    (by simp only [σG]; rw [pow_succ]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ σ, σ = ((σG w P.n W).seth gIN (([] : List Bool).length + stp true *
      (RepairRepresentation.natWord P.n).length)).setv (SG 0) ((σG w P.n W).val (SG 0) + P.n) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have v1 : ∀ r : Fin GR, r ≠ SG 0 → σ1.val r = 0 := by
    intro r hr
    simp [hσ1, Function.update_apply, hr, σG]
  have v10 : σ1.val (SG 0) = P.n := by simp [hσ1, σG]
  have r2 := StarNums.starNums_spec (2 * W + 2) cr 0 SG P hrP σ1 v10 (fun i hi => v1 _ (fun e => hi (SG.injective e)))
    (by omega)
  obtain ⟨-, -, -, o5, o6, o7, -, -, -⟩ := StarNums.starOut_val σ1 SG P 0
  refine ⟨_, _, WExec.seq r1 r2, o5, o6, o7, ?_, ?_, ?_, rfl⟩
  · intro r hr
    rw [starOut_hiG _ _ _ _ hr]
    exact v1 _ (fun e => by rw [e] at hr; simp [SG] at hr)
  · simp [StarNums.starOut, hσ1]
  · have hOI : gOUT ≠ gIN := by decide
    simp [StarNums.starOut, hσ1, σG, Function.update_apply, hOI]

theorem part2_spec (cap b rh m : ℕ) (σ : WState GS GR) (h5 : σ.val (SG 5) = b) (h6 : σ.val (SG 6) = rh)
    (h7 : σ.val (SG 7) = m) (hz : ∀ r : Fin GR, 20 ≤ r.val → σ.val r = 0) (hc : rh * b + m + rh + b + 3 ≤ cap) :
    ∃ σ' c, WExec cap p2W σ σ' c ∧ σ'.val rA = rh * b ∧ σ'.val rH = (m + 1) / 2 ∧ σ'.val (SG 7) = m ∧
      (∀ r : Fin GR, 20 ≤ r.val → r ≠ rA → r ≠ rX → r ≠ rTwo → r ≠ rH → σ'.val r = 0) ∧ σ'.st = σ.st ∧
      σ'.sh = σ.sh ∧ c = b * (18 * rh + 8) + 18 * b + 10 + 1 + (18 * m + 3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 +
        (m + 1 + 2) * (90 * (m + 1) + 90 * 2 + 60))))) := by
  have e60 : MA 0 = SG 6 := rfl
  have e51 : MA 1 = SG 5 := rfl
  have r3 := UnaryArith.mulAddW_spec cap MA σ (hz _ (by decide)) (hz _ (by decide)) (by rw [e51, h5]; omega)
    (by rw [e60, e51, h6, h5, hz (MA 2) (by decide)]; omega) (by rw [e60, h6]; omega)
  rw [e60, e51, h6, h5, hz (MA 2) (by decide), show MA 2 = rA from rfl] at r3
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ.setv rA (0 + rh * b) := ⟨_, rfl⟩
  rw [← hσ3] at r3
  have v3 : ∀ r : Fin GR, 20 ≤ r.val → r ≠ rA → σ3.val r = 0 := by
    intro r hr hA
    rw [hσ3]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg hA]
    exact hz r hr
  have v37 : σ3.val (SG 7) = m := by
    rw [hσ3]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide)]
    exact h7
  have r4 := addTo_spec cap (SG 7) rX rT (by decide) (by decide) (by decide) σ3 (v3 _ (by decide) (by decide))
    (by rw [v37]; omega) (by rw [v37, v3 _ (by decide) (by decide)]; omega)
  rw [v37, v3 rX (by decide) (by decide)] at r4
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setv rX (0 + m) := ⟨_, rfl⟩
  rw [← hσ4] at r4
  have v4X : σ4.val rX = m := by rw [hσ4]; simp
  have r5 := WExec.inc (cap := cap) rX σ4 (by rw [v4X]; omega)
  rw [v4X] at r5
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setv rX (m + 1) := ⟨_, rfl⟩
  rw [← hσ5] at r5
  have v5T : σ5.val rTwo = 0 := by
    rw [hσ5, hσ4]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]
    exact v3 _ (by decide) (by decide)
  have r6 := WExec.inc (cap := cap) rTwo σ5 (by rw [v5T]; omega)
  rw [v5T] at r6
  obtain ⟨σ6, hσ6⟩ : ∃ τ, τ = σ5.setv rTwo (0 + 1) := ⟨_, rfl⟩
  rw [← hσ6] at r6
  have v6T : σ6.val rTwo = 1 := by rw [hσ6]; simp
  have r7 := WExec.inc (cap := cap) rTwo σ6 (by rw [v6T]; omega)
  rw [v6T] at r7
  obtain ⟨σ7, hσ7⟩ : ∃ τ, τ = σ6.setv rTwo (1 + 1) := ⟨_, rfl⟩
  rw [← hσ7] at r7
  have v7 : ∀ r : Fin GR, 20 ≤ r.val → r ≠ rA → r ≠ rX → r ≠ rTwo → σ7.val r = 0 := by
    intro r hr h1 h2 h3
    rw [hσ7, hσ6, hσ5, hσ4]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg h3, if_neg h3, if_neg h2, if_neg h2]
    exact v3 r hr h1
  have v7X : σ7.val rX = m + 1 := by
    rw [hσ7, hσ6, hσ5]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_true]
  have v7T : σ7.val rTwo = 2 := by rw [hσ7]; simp
  have v7A : σ7.val rA = rh * b := by
    rw [hσ7, hσ6, hσ5, hσ4, hσ3]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_true]
    omega
  have v77 : σ7.val (SG 7) = m := by
    rw [hσ7, hσ6, hσ5, hσ4]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact v37
  have e0 : DV 0 = rX := rfl
  have e1 : DV 1 = rTwo := rfl
  have e2 : DV 2 = rH := rfl
  have r8 := UnaryArith.divW_spec cap DV σ7 (by rw [e1, v7T]; omega) (v7 _ (by decide) (by decide) (by decide) (by decide))
    (v7 _ (by decide) (by decide) (by decide) (by decide)) (v7 _ (by decide) (by decide) (by decide) (by decide))
    (v7 _ (by decide) (by decide) (by decide) (by decide)) (v7 _ (by decide) (by decide) (by decide) (by decide))
    (by rw [e0, v7X]; omega) (by rw [e1, v7T]; omega)
    (by rw [e2, e0, v7X, v7 _ (by decide) (by decide) (by decide) (by decide)]; omega) (by omega)
  rw [e0, e1, e2, v7X, v7T, v7 rH (by decide) (by decide) (by decide) (by decide)] at r8
  refine ⟨_, _, WExec.seq r3 (WExec.seq r4 (WExec.seq r5 (WExec.seq r6 (WExec.seq r7 r8)))), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]
    exact v7A
  · simp
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]
    exact v77
  · intro r hr h1 h2 h3 h4
    simp only [WState.setv_val, Function.update_apply]
    rw [if_neg h4, if_neg h2]
    exact v7 r hr h1 h2 h3
  · rw [hσ7, hσ6, hσ5, hσ4, hσ3]; simp
  · rw [hσ7, hσ6, hσ5, hσ4, hσ3]; simp

theorem part3_spec (cap A h m : ℕ) (σ : WState GS GR) (hA : σ.val rA = A) (hH : σ.val rH = h) (h7 : σ.val (SG 7) = m)
    (hz : ∀ r : Fin GR, 20 ≤ r.val → r ≠ rA → r ≠ rX → r ≠ rTwo → r ≠ rH → σ.val r = 0) (hc : A + h + m ≤ cap) :
    ∃ σ' c, WExec cap p3W σ σ' c ∧ σ'.val rA = A ∧ σ'.val rH = h ∧ σ'.val rWd = A + h ∧ σ'.val rRst = m - h ∧
      σ'.val rOP = 0 ∧ σ'.val rK = 0 ∧ σ'.val rT = 0 ∧ σ'.st = σ.st ∧ σ'.sh = σ.sh ∧
      c = 18 * A + 3 + 1 + (18 * h + 3 + 1 + (18 * m + 3 + 1 + (30 * h + 10))) := by
  have zT : σ.val rT = 0 := hz _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have zW : σ.val rWd = 0 := hz _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have r9 := addTo_spec cap rA rWd rT (by decide) (by decide) (by decide) σ zT (by rw [hA]; omega) (by rw [hA, zW]; omega)
  rw [hA, zW] at r9
  obtain ⟨σ9, hσ9⟩ : ∃ τ, τ = σ.setv rWd (0 + A) := ⟨_, rfl⟩
  rw [← hσ9] at r9
  have v9H : σ9.val rH = h := by
    rw [hσ9]; simp only [WState.setv_val, Function.update_apply]; rw [if_neg (by decide)]; exact hH
  have v9W : σ9.val rWd = A := by rw [hσ9]; simp
  have v9T : σ9.val rT = 0 := by
    rw [hσ9]; simp only [WState.setv_val, Function.update_apply]; rw [if_neg (by decide)]; exact zT
  have r10 := addTo_spec cap rH rWd rT (by decide) (by decide) (by decide) σ9 v9T (by rw [v9H]; omega)
    (by rw [v9H, v9W]; omega)
  rw [v9H, v9W] at r10
  obtain ⟨σ10, hσ10⟩ : ∃ τ, τ = σ9.setv rWd (A + h) := ⟨_, rfl⟩
  rw [← hσ10] at r10
  have v107 : σ10.val (SG 7) = m := by
    rw [hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]; exact h7
  have v10R : σ10.val rRst = 0 := by
    rw [hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]; exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have v10T : σ10.val rT = 0 := by
    rw [hσ10]; simp only [WState.setv_val, Function.update_apply]; rw [if_neg (by decide)]; exact v9T
  have r11 := addTo_spec cap (SG 7) rRst rT (by decide) (by decide) (by decide) σ10 v10T (by rw [v107]; omega)
    (by rw [v107, v10R]; omega)
  rw [v107, v10R] at r11
  obtain ⟨σ11, hσ11⟩ : ∃ τ, τ = σ10.setv rRst (0 + m) := ⟨_, rfl⟩
  rw [← hσ11] at r11
  have s0 : SB 0 = rRst := rfl
  have s1 : SB 1 = rH := rfl
  have v11H : σ11.val rH = h := by
    rw [hσ11, hσ10]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide)]; exact v9H
  have v11R : σ11.val rRst = m := by rw [hσ11]; simp
  have r12 := UnaryArith.subW_spec cap SB σ11
    (by rw [hσ11, hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hσ11, hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [s0, v11R]; omega) (by rw [s1, v11H]; omega)
  rw [s0, s1, v11H, v11R] at r12
  refine ⟨_, _, WExec.seq r9 (WExec.seq r10 (WExec.seq r11 r12)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hσ11, hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact hA
  · simp only [WState.setv_val, Function.update_apply]; rw [if_neg (by decide)]; exact v11H
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hσ11, hσ10]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_true]
  · simp
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hσ11, hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hσ11, hσ10, hσ9]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide), hσ11]; simp only [WState.setv_val, Function.update_apply]
    rw [if_neg (by decide)]; exact v10T
  · rw [hσ11, hσ10, hσ9]; simp
  · rw [hσ11, hσ10, hσ9]; simp

/-- The numbers program's cost. -/
def numsGCostE (P : StarParams) (cr : ℕ) : ℕ :=
  (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 + StarNums.starCost P.n cr 0 + 1 +
    (P.b * (18 * (P.r / 2) + 8) + 18 * P.b + 10 + 1 + (18 * (P.n - P.r * P.b) + 3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 +
      (P.n - P.r * P.b + 1 + 2) * (90 * (P.n - P.r * P.b + 1) + 90 * 2 + 60))))) + 1 +
    (18 * (P.r / 2 * P.b) + 3 + 1 + (18 * ((P.n - P.r * P.b + 1) / 2) + 3 + 1 + (18 * (P.n - P.r * P.b) + 3 + 1 +
      (30 * ((P.n - P.r * P.b + 1) / 2) + 10)))))

/-- **The numbers program's run**: from the writer's start state, `rA = A`, `rH = h`, `rWd = A + h`,
`rRst = (n−rb) − h`; the streams untouched, the output head at `0`, the output counter and loop registers at `0`. -/
theorem numsG_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (numsG cr) (σG w P.n W) σF c ∧ σF.val rA = aOf P ∧ σF.val rH = hLv P ∧
      σF.val rWd = aOf P + hLv P ∧ σF.val rRst = P.n - P.r * P.b - hLv P ∧ σF.val rOP = 0 ∧ σF.val rK = 0 ∧
      σF.val rT = 0 ∧ σF.st = (σG w P.n W).st ∧ σF.sh gOUT = 0 ∧ c = numsGCostE P cr := by
  have hbn := b_le P
  have hr4 := P.four_r_le_n
  have hrb := P.r_mul_b_le
  have hrs := rb_eq P
  obtain ⟨σ1, c1, e1, f5, f6, f7, fz, fst, fsh, fc1⟩ := part1_spec cr W P hrP sfx w hw hW
  have hrhb : P.r / 2 * P.b ≤ P.n := by unfold aOf at hrs; omega
  obtain ⟨σ2, c2, e2, gA, gH, g7, gz, gst, gsh, gc2⟩ := part2_spec (2 * W + 2) P.b (P.r / 2) (P.n - P.r * P.b) σ1
    f5 f6 f7 fz (by omega)
  obtain ⟨σ3, c3, e3, hA3, hH3, hW3, hR3, hOP, hK, hT, hst3, hsh3, hc3⟩ := part3_spec (2 * W + 2) (P.r / 2 * P.b)
    ((P.n - P.r * P.b + 1) / 2) (P.n - P.r * P.b) σ2 gA gH g7 gz (by omega)
  refine ⟨σ3, _, WExec.seq e1 (WExec.seq e2 e3), hA3, hH3, hW3, hR3, hOP, hK, hT, ?_, ?_, ?_⟩
  · rw [hst3, gst, fst]
  · rw [hsh3, gsh, fsh]
  · rw [fc1, gc2, hc3]
    unfold numsGCostE
    omega

theorem repsLen (k : ℕ) (u : List Bool) : (reps k u).length = k * u.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [reps_succ, List.length_append, ih, Nat.succ_mul]

theorem repsSingle (k : ℕ) (b : Bool) : reps k [b] = List.replicate k b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reps_succ, ih, List.replicate_succ']

/-- The width's emission: `1^(A+h)` on the output. -/
def widthE : WM GS GR := repRegW gOUT rOP rWd rK rT [true]

/-- **The width writer's program.** -/
def widthW (cr : ℕ) : WM GS GR := .seq (numsG cr) widthE

theorem widthW_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (widthW cr) (σG w P.n W) σF c ∧
      σF.st gOUT = List.replicate (aOf P + hLv P) true ∧ σF.st gIN = RepairOrdinary.frame w ∧
      c ≤ numsGCostE P cr + 1 + 100 * (P.n + 3) := by
  have hbn := b_le P
  have hrb := P.r_mul_b_le
  have hrs := rb_eq P
  have hhl : hLv P ≤ P.n - P.r * P.b := by unfold hLv; omega
  obtain ⟨σ3, c3, e3, -, -, hWd, -, hOP, hK, hT, hst, hsh, hc⟩ := numsG_spec cr W P hrP sfx w hw hW
  have hO : σ3.st gOUT = [] := by rw [hst]; simp [σG, gOUT, gIN, gNT, gCT, gAUX]
  have e4 := repRegW_spec (2 * W + 2) gOUT rOP rWd rK rT (by decide) (by decide) (by decide) (by decide) [true] σ3 hK hT
    (by rw [hO, hsh]; rfl) (by rw [hWd]; omega) (by rw [hOP, hWd]; simp; omega)
  refine ⟨_, _, WExec.seq e3 e4, ?_, ?_, ?_⟩
  · simp [hO, hWd, repsSingle]
  · have hIO : gIN ≠ gOUT := by decide
    simp [Function.update_apply, hIO, hst, σG]
  · rw [hc, hWd]
    simp only [List.length_cons, List.length_nil]
    omega

/-- The halves' emission: the marks of `1^A 0^A 1^h 0^rest`, then `0`. -/
def sideE : WM GS GR :=
  .seq (repRegW gOUT rOP rA rK rT [true, true]) (.seq (repRegW gOUT rOP rA rK rT [true, false])
    (.seq (repRegW gOUT rOP rH rK rT [true, true]) (.seq (repRegW gOUT rOP rRst rK rT [true, false])
      (emitW gOUT rOP [false]))))

/-- **The halves writer's program.** -/
def sideW (cr : ℕ) : WM GS GR := .seq (numsG cr) sideE

/-- The halves' word as the writer emits it. -/
def sideWord (A h rest : ℕ) : List Bool :=
  reps A [true, true] ++ reps A [true, false] ++ reps h [true, true] ++ reps rest [true, false] ++ [false]

theorem sideW_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 20 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (sideW cr) (σG w P.n W) σF c ∧
      σF.st gOUT = sideWord (aOf P) (hLv P) (P.n - P.r * P.b - hLv P) ∧ σF.st gIN = RepairOrdinary.frame w ∧
      c ≤ numsGCostE P cr + 1 + 200 * (P.n + 3) := by
  have hbn := b_le P
  have hrb := P.r_mul_b_le
  have hrs := rb_eq P
  have hhl : hLv P ≤ P.n - P.r * P.b := by unfold hLv; omega
  have haP : aOf P ≤ P.n := by omega
  obtain ⟨σ3, c3, e3, hA, hH, -, hR, hOP, hK, hT, hst, hsh, hc⟩ := numsG_spec cr W P hrP sfx w hw hW
  set A := aOf P with hAd
  set h := hLv P with hhd
  set rest := P.n - P.r * P.b - hLv P with hrd
  have hsum : A + A + h + rest = P.n := by omega
  have hO : σ3.st gOUT = [] := by rw [hst]; simp [σG, gOUT, gIN, gNT, gCT, gAUX]
  have nAO : rA ≠ rOP := by decide
  have nHO : rH ≠ rOP := by decide
  have nRO : rRst ≠ rOP := by decide
  have nKO : rK ≠ rOP := by decide
  have nTO : rT ≠ rOP := by decide
  -- 1
  have e4 := repRegW_spec (2 * W + 2) gOUT rOP rA rK rT (by decide) (by decide) (by decide) (by decide) [true, true] σ3
    hK hT (by rw [hO, hsh]; rfl) (by rw [hA]; omega) (by rw [hOP, hA]; simp; omega)
  rw [hA] at e4
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = appendO σ3 gOUT rOP (reps A [true, true]) := ⟨_, rfl⟩
  rw [← hτ1] at e4
  have t1A : τ1.val rA = A := by rw [hτ1]; simp [Function.update_apply, nAO, hA]
  have t1H : τ1.val rH = h := by rw [hτ1]; simp [Function.update_apply, nHO, hH]
  have t1R : τ1.val rRst = rest := by rw [hτ1]; simp [Function.update_apply, nRO, hR]
  have t1K : τ1.val rK = 0 := by rw [hτ1]; simp [Function.update_apply, nKO, hK]
  have t1T : τ1.val rT = 0 := by rw [hτ1]; simp [Function.update_apply, nTO, hT]
  have t1P : τ1.val rOP = 2 * A := by rw [hτ1]; simp [hOP, repsLen]; omega
  have t1O : τ1.sh gOUT = (τ1.st gOUT).length := by rw [hτ1]; simp [hO, hsh]
  -- 2
  have e5 := repRegW_spec (2 * W + 2) gOUT rOP rA rK rT (by decide) (by decide) (by decide) (by decide) [true, false] τ1
    t1K t1T t1O (by rw [t1A]; omega) (by rw [t1P, t1A]; simp; omega)
  rw [t1A] at e5
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = appendO τ1 gOUT rOP (reps A [true, false]) := ⟨_, rfl⟩
  rw [← hτ2] at e5
  have t2H : τ2.val rH = h := by rw [hτ2]; simp [Function.update_apply, nHO, t1H]
  have t2R : τ2.val rRst = rest := by rw [hτ2]; simp [Function.update_apply, nRO, t1R]
  have t2K : τ2.val rK = 0 := by rw [hτ2]; simp [Function.update_apply, nKO, t1K]
  have t2T : τ2.val rT = 0 := by rw [hτ2]; simp [Function.update_apply, nTO, t1T]
  have t2P : τ2.val rOP = 4 * A := by rw [hτ2]; simp [t1P, repsLen]; omega
  have t2O : τ2.sh gOUT = (τ2.st gOUT).length := by rw [hτ2]; simp [t1O]
  -- 3
  have e6 := repRegW_spec (2 * W + 2) gOUT rOP rH rK rT (by decide) (by decide) (by decide) (by decide) [true, true] τ2
    t2K t2T t2O (by rw [t2H]; omega) (by rw [t2P, t2H]; simp; omega)
  rw [t2H] at e6
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = appendO τ2 gOUT rOP (reps h [true, true]) := ⟨_, rfl⟩
  rw [← hτ3] at e6
  have t3R : τ3.val rRst = rest := by rw [hτ3]; simp [Function.update_apply, nRO, t2R]
  have t3K : τ3.val rK = 0 := by rw [hτ3]; simp [Function.update_apply, nKO, t2K]
  have t3T : τ3.val rT = 0 := by rw [hτ3]; simp [Function.update_apply, nTO, t2T]
  have t3P : τ3.val rOP = 4 * A + 2 * h := by rw [hτ3]; simp [t2P, repsLen]; omega
  have t3O : τ3.sh gOUT = (τ3.st gOUT).length := by rw [hτ3]; simp [t2O]
  -- 4
  have e7 := repRegW_spec (2 * W + 2) gOUT rOP rRst rK rT (by decide) (by decide) (by decide) (by decide) [true, false]
    τ3 t3K t3T t3O (by rw [t3R]; omega) (by rw [t3P, t3R]; simp; omega)
  rw [t3R] at e7
  obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = appendO τ3 gOUT rOP (reps rest [true, false]) := ⟨_, rfl⟩
  rw [← hτ4] at e7
  have t4P : τ4.val rOP = 4 * A + 2 * h + 2 * rest := by rw [hτ4]; simp [t3P, repsLen]; omega
  have t4O : τ4.sh gOUT = (τ4.st gOUT).length := by rw [hτ4]; simp [t3O]
  -- 5
  have e8 := emitW_spec (2 * W + 2) gOUT rOP [false] τ4 t4O (by rw [t4P]; simp; omega)
  refine ⟨_, _, WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 e8)))), ?_, ?_, ?_⟩
  · rw [hτ4, hτ3, hτ2, hτ1]
    simp only [appendO_st, Function.update_self, hO]
    simp [sideWord, List.append_assoc]
  · have hIO : gIN ≠ gOUT := by decide
    rw [hτ4, hτ3, hτ2, hτ1]
    simp [Function.update_apply, hIO, hst, σG]
  · rw [hc]
    simp only [List.length_cons, List.length_nil]
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
