import Proof.Wire_3_5.Primitive.SeedFix.CtrUnb

/-! # X3, part 13: the center writer on its layout (P3:1206-1216)

The center at table position `(row, col)` (C4Geo's `centerAt P σ row col`, the pulled-back point of the offset at
`(φ row, φ col)`, P3:1206-1216) is written by **`ctrM`**: the left half's `r/2` blocks (the row's data bits), the
right half's (the column's), the unblocked coordinates (the row's and the column's remaining bits), the frame's end,
every stream back at `0`. **`ctrM_spec`**: from the offset `frameP (ofFn (offset P σ)) ++ [false]`, the row
`frame (binary dRow row)`, the column `frame (binary dR col)`, and any old center frame (`≤ 2n + 1` cells), the center
stream holds `frameP (List.ofFn (centerAt P σ row col)) ++ [false]`, every register is back at its entry value.

Paper quantity of the main type: the center `C4Geo.centerAt P σ row col` (a cell center of the partition). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- The frame's end and the four streams back at `0`. -/
def endM : CM :=
  .seq (wrC false) (.seq (Flips.rew1 zCtr rgOC) (.seq (Flips.rew1 zRow rgROWC) (.seq (Flips.rew1 zCol rgCOLC)
    (Flips.rew1 zOff rgOFFC))))

/-- **The center writer** on its layout. -/
def ctrM : CM :=
  .seq (halfM zRow rgROWC) (.seq (halfM zCol rgCOLC) (.seq (unbM zRow rgROWC rgHL) (.seq (unbM zCol rgCOLC rgHR)
    endM)))

/-- The center writer's steps. -/
def ctrCost (P : StarParams) : ℕ :=
  halfCost P + 1 + (halfCost P + 1 + (100 * P.n + 10 + 1 + (100 * P.n + 10 + 1 + 50 * (P.n + 1))))

section Whole
variable (cap : ℕ)

theorem ctrM_spec (P : StarParams) (σT : P.Translation) (row col : ℕ) (Y0 : List Bool) (x : CS)
    (hoff : x.st zOff = frameP (List.ofFn (offset P σT)) ++ [false])
    (hrow : x.st zRow = frameP (binary (dRow P) row) ++ [false])
    (hcol : x.st zCol = frameP (binary (dR P) col) ++ [false])
    (hctr : x.st zCtr = Y0) (hY : Y0.length ≤ 2 * P.n + 1) (hsh : ∀ i, x.sh i = 0)
    (hB : x.val rgB = P.b) (hS : x.val rgS = P.s) (hH : x.val rgH = P.r / 2) (hHL : x.val rgHL = hL P)
    (hHR : x.val rgHR = P.n - P.r * P.b - hL P) (hz : ∀ r : Fin 26, 5 ≤ r.val → x.val r = 0)
    (hcap : 8 * (P.n + 2) ≤ cap) :
    ∃ τ, WExec cap ctrM x τ (ctrCost P) ∧
      τ.st zCtr = frameP (List.ofFn (centerAt P σT row col)) ++ [false] ∧
      (∀ i, i ≠ zCtr → τ.st i = x.st i) ∧ (∀ i, τ.sh i = 0) ∧ τ.val = x.val ∧ τ.cell = x.cell := by
  -- the arithmetic
  have hrb := rb_eq P
  have hLle := hL_le P
  have hdb : dB P ≤ P.b := by unfold dB; omega
  have hhd : P.r / 2 * dB P ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ hdb
  have hr2 := P.two_le_r
  have hbr : P.b ≤ P.r / 2 * P.b := Nat.le_mul_of_pos_left _ (by omega)
  have hdrow : dRow P = P.r / 2 * dB P + hL P := dRow_eq P
  have hdr : dR P = P.r / 2 * dB P + (P.n - P.r * P.b) / 2 := dR_eq P
  have hhl : hL P = (P.n - P.r * P.b + 1) / 2 := rfl
  have hrbn := P.r_mul_b_le
  have hhbn : P.r / 2 * P.b ≤ P.n := by omega
  have hbn : P.b ≤ P.n := by omega
  have hhdn : P.r / 2 * dB P ≤ P.n := by omega
  have hhn : P.r / 2 ≤ P.n := by have := P.four_r_le_n; omega
  set Tl := List.ofFn (centerAt P σT row col) with hTl
  set offL := List.ofFn (offset P σT) with hoffL
  have lT : Tl.length = P.n := by rw [hTl, List.length_ofFn]
  have lO : offL.length = P.n := by rw [hoffL, List.length_ofFn]
  have zer : ∀ r : Fin 26, 5 ≤ r.val → x.val r = 0 := hz
  -- the left half
  have hHH1 : HH P zRow rgROWC x 0 Tl offL (dRow P) row := by
    refine ⟨Or.inl ⟨rfl, rfl⟩, hrow, by omega, hoff, fun jj hj q hq => ?_, by omega, by omega, hB, hS, hH⟩
    have hx : jj * P.b + q < P.n := by have := blk_lt P jj q hj hq; omega
    rw [Nat.zero_add, cw_getD P σT row col _ hx, cw_left P row col jj q hj hq]
  have hout0 : OutAt Tl Y0 0 x :=
    ⟨by simp [hctr], hsh zCtr, zer rgOC (by decide), hsh zOff, zer rgOFFC (by decide)⟩
  have hzb0 : ZB x :=
    ⟨⟨zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide),
      zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide)⟩,
      zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide), zer _ (by decide)⟩
  obtain ⟨τ1, e1, h1⟩ := half_spec cap P zRow rgROWC 0 0 Tl offL Y0 (dRow P) row x hHH1 hzb0 (zer rgKB (by decide))
    (hsh zRow) (zer rgROWC (by decide)) hout0 (by omega) (by omega) (by omega) (by omega)
  have o1 : ∀ r, r ∉ rgKB :: blkRegs rgROWC → τ1.val r = x.val r := h1.oth
  -- the right half
  have hHH2 : HH P zCol rgCOLC τ1 (P.r / 2 * P.b) Tl offL (dR P) col := by
    refine ⟨Or.inr ⟨rfl, rfl⟩, by rw [h1.st zCol (by decide)]; exact hcol, by omega,
      by rw [h1.st zOff (by decide)]; exact hoff, fun jj hj q hq => ?_, by omega, by omega,
      by rw [o1 rgB (by decide)]; exact hB, by rw [o1 rgS (by decide)]; exact hS, by rw [o1 rgH (by decide)]; exact hH⟩
    have hx : P.r / 2 * P.b + (jj * P.b + q) < P.n := by have := blk_lt P jj q hj hq; omega
    rw [cw_getD P σT row col _ hx, cw_right P row col jj q hj hq]
  obtain ⟨τ2, e2, h2⟩ := half_spec cap P zCol rgCOLC 0 (P.r / 2 * P.b) Tl offL Y0 (dR P) col τ1 hHH2 h1.zero
    (by rw [h1.kb]; omega) (by rw [h1.sh zCol (by decide) (by decide) (by decide)]; exact hsh zCol)
    (by rw [o1 rgCOLC (by decide)]; exact zer rgCOLC (by decide)) (by simpa using h1.out)
    (by omega) (by omega) (by omega) (by omega)
  have o2 : ∀ r, r ∉ rgKB :: blkRegs rgCOLC → τ2.val r = τ1.val r := h2.oth
  -- the unblocked row coordinates
  have hUH1 : UH zRow rgROWC τ2 (P.r / 2 * dB P) (P.r / 2 * P.b + P.r / 2 * P.b) (hL P) Tl offL (dRow P) row := by
    refine ⟨Or.inl ⟨rfl, rfl⟩, by rw [h2.st zRow (by decide), h1.st zRow (by decide)]; exact hrow, by omega,
      by rw [h2.st zOff (by decide), h1.st zOff (by decide)]; exact hoff, fun i hi => ?_, by omega, by omega⟩
    have hx : P.r / 2 * P.b + P.r / 2 * P.b + i < P.n := by omega
    rw [cw_getD P σT row col _ hx, show P.r / 2 * P.b + P.r / 2 * P.b + i = P.r * P.b + i by omega,
      cw_unbL P row col i hi]
  obtain ⟨τ3, e3, h3⟩ := unb_spec cap zRow rgROWC rgHL (by decide) (P.r / 2 * dB P) (2 * (P.r / 2 * dB P))
    (P.r / 2 * P.b + P.r / 2 * P.b) (hL P) Tl offL Y0 (dRow P) row τ2 hUH1
    (by rw [o2 rgHL (by decide), o1 rgHL (by decide)]; exact hHL)
    (by rw [o2 rgKU (by decide), o1 rgKU (by decide)]; exact zer rgKU (by decide))
    h2.zero.1.2.2.2.2.2.1 h2.zero.1.2.2.2.2.2.2.1
    (by rw [h2.sh zRow (by decide) (by decide) (by decide)]; exact h1.shR)
    (by rw [o2 rgROWC (by decide)]; simpa using h1.cn) (by simpa using h2.out) (by omega) (by omega)
  -- the unblocked column coordinates
  have hUH2 : UH zCol rgCOLC τ3 (P.r / 2 * dB P) (P.r / 2 * P.b + P.r / 2 * P.b + hL P)
      (P.n - P.r * P.b - hL P) Tl offL (dR P) col := by
    have hc3 : τ3.st zCol = frameP (binary (dR P) col) ++ [false] := by
      rw [h3.st zCol (by decide), h2.st zCol (by decide), h1.st zCol (by decide)]; exact hcol
    refine ⟨Or.inr ⟨rfl, rfl⟩, hc3, by omega,
      by rw [h3.st zOff (by decide), h2.st zOff (by decide), h1.st zOff (by decide)]; exact hoff,
      fun i hi => ?_, by omega, by omega⟩
    have hx : P.r / 2 * P.b + P.r / 2 * P.b + hL P + i < P.n := by omega
    rw [cw_getD P σT row col _ hx, show P.r / 2 * P.b + P.r / 2 * P.b + hL P + i = P.r * P.b + hL P + i by omega,
      cw_unbR P row col i]
  obtain ⟨τ4, e4, h4⟩ := unb_spec cap zCol rgCOLC rgHR (by decide) (P.r / 2 * dB P) (2 * (P.r / 2 * dB P))
    (P.r / 2 * P.b + P.r / 2 * P.b + hL P) (P.n - P.r * P.b - hL P) Tl offL Y0 (dR P) col τ3 hUH2
    (by rw [h3.oth rgHR (by decide), o2 rgHR (by decide), o1 rgHR (by decide)]; exact hHR)
    (by rw [h3.ku]; omega) h3.z
    (by rw [h3.oth rgT (by decide)]; exact h2.zero.1.2.2.2.2.2.2.1)
    (by rw [h3.sh zCol (by decide) (by decide) (by decide)]; exact h2.shR)
    (by rw [h3.oth rgCOLC (by decide)]; simpa using h2.cn) (by simpa using h3.out) (by omega) (by omega)
  -- the end
  have hk4 : P.r / 2 * P.b + P.r / 2 * P.b + hL P + (P.n - P.r * P.b - hL P) = P.n := by omega
  have out4 := h4.out
  rw [hk4] at out4
  have hTt : Tl.take P.n = Tl := List.take_of_length_le (by omega)
  obtain ⟨τ5, e5, a5, b5, c5, d5, f5, g5⟩ := wrC_spec cap false τ4 (frameP Tl) (Y0.drop (2 * P.n))
    (by rw [out4.st, hTt]) (by rw [out4.sh, frameP_length, lT]) (by rw [out4.oc]; omega)
  have hc5 : τ5.val rgOC = 2 * P.n + 1 := by rw [c5, out4.oc]
  have hs5 : τ5.sh zCtr = 2 * P.n + 1 := by rw [b5, frameP_length, lT]
  obtain ⟨τ6, e6, a6, b6, c6, d6, f6, g6⟩ := Flips.rew1_spec cap zCtr rgOC (2 * P.n + 1) τ5 hc5 hs5 (by omega)
  have hrw : τ6.val rgROWC = 2 * dRow P := by
    rw [f6 rgROWC (by decide), f5 rgROWC (by decide), h4.oth rgROWC (by decide), h3.cn]; rw [hdrow]; ring
  have hrs : τ6.sh zRow = 2 * dRow P := by
    rw [d6 zRow (by decide), (d5 zRow (by decide)).2, h4.sh zRow (by decide) (by decide) (by decide), h3.shR, hdrow]
  obtain ⟨τ7, e7, a7, b7, c7, d7, f7, g7⟩ := Flips.rew1_spec cap zRow rgROWC (2 * dRow P) τ6 hrw hrs (by omega)
  have hcw : τ7.val rgCOLC = 2 * dR P := by
    rw [f7 rgCOLC (by decide), f6 rgCOLC (by decide), f5 rgCOLC (by decide), h4.cn, hdr]; omega
  have hcs : τ7.sh zCol = 2 * dR P := by
    rw [d7 zCol (by decide), d6 zCol (by decide), (d5 zCol (by decide)).2, h4.shR, hdr]; omega
  obtain ⟨τ8, e8, a8, b8, c8, d8, f8, g8⟩ := Flips.rew1_spec cap zCol rgCOLC (2 * dR P) τ7 hcw hcs (by omega)
  have how : τ8.val rgOFFC = 2 * P.n := by
    rw [f8 rgOFFC (by decide), f7 rgOFFC (by decide), f6 rgOFFC (by decide), f5 rgOFFC (by decide), out4.ofc]
  have hos : τ8.sh zOff = 2 * P.n := by
    rw [d8 zOff (by decide), d7 zOff (by decide), d6 zOff (by decide), (d5 zOff (by decide)).2, out4.osh]
  obtain ⟨τ9, e9, a9, b9, c9, d9, f9, g9⟩ := Flips.rew1_spec cap zOff rgOFFC (2 * P.n) τ8 how hos (by omega)
  -- the steps
  have hcost : halfCost P + 1 + (halfCost P + 1 + (100 * hL P + 10 + 1 + (100 * (P.n - P.r * P.b - hL P) + 10 + 1 +
      (7 + 1 + ((2 * P.n + 1) * 5 + 1 + 1 + (2 * dRow P * 5 + 1 + 1 + (2 * dR P * 5 + 1 + 1 + (2 * P.n * 5 + 1)))))))) ≤
      ctrCost P := by
    unfold ctrCost; omega
  refine ⟨τ9, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) hcost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c9, c8, c7, c6, a5]
    have : (Y0.drop (2 * P.n)).drop 1 = [] := by
      rw [List.drop_drop]; exact List.drop_of_length_le (by omega)
    rw [this]
  · intro i hi
    rw [c9, c8, c7, c6, (d5 i hi).1, h4.st i hi, h3.st i hi, h2.st i hi, h1.st i hi]
  · have s0 : τ9.sh zOff = 0 := a9
    have s1 : τ9.sh zRow = 0 := by rw [d9 zRow (by decide), d8 zRow (by decide)]; exact a7
    have s2 : τ9.sh zCol = 0 := by rw [d9 zCol (by decide)]; exact a8
    have s3 : τ9.sh zCtr = 0 := by rw [d9 zCtr (by decide), d8 zCtr (by decide), d7 zCtr (by decide)]; exact a6
    intro i
    fin_cases i <;> simp [s0, s1, s2, s3]
  · have hin : ∀ r, r ∉ [rgKB, rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ, rgBIT,
        rgHQ, rgOC, rgOFFC, rgROWC, rgCOLC, rgKU] → τ9.val r = x.val r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f9 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, f8 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        f7 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, f6 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        f5 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      rw [h4.oth r (by simp [hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])]
      rw [h3.oth r (by simp [hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])]
      rw [o2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])]
      rw [o1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])]
    have hzs : ∀ r, r ∈ [rgKB, rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ, rgBIT,
        rgHQ, rgOC, rgOFFC, rgROWC, rgCOLC, rgKU] → τ9.val r = 0 := by
      obtain ⟨⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩, ypw, ykt, ypar, ybit, yhq⟩ := h2.zero
      have k1 : ∀ r, r ≠ rgOC → r ≠ rgROWC → r ≠ rgCOLC → r ≠ rgOFFC → τ9.val r = τ4.val r := by
        intro r r1 r2 r3 r4
        rw [f9 r r4, f8 r r3, f7 r r2, f6 r r1, f5 r r1]
      have k2 : ∀ r, r ∉ [rgKU, rgZ, rgCOLC, rgOC, rgOFFC, rgROWC] → τ4.val r = τ2.val r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [h4.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
          h3.oth r (by simp [hr.1, hr.2.1, hr.2.2.2.2.2, hr.2.2.2.1, hr.2.2.2.2.1])]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide), h2.kb]; simp
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact ypar
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact ypw
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact ykt
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y1
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y2
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y3
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y4
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y5
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide)]; exact h4.z
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y7
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y8
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y9
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact y10
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact ybit
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide)]; exact yhq
      · rw [f9 _ (by decide), f8 _ (by decide), f7 _ (by decide)]; exact b6
      · exact b9
      · rw [f9 _ (by decide), f8 _ (by decide)]; exact b7
      · rw [f9 _ (by decide)]; exact b8
      · rw [k1 _ (by decide) (by decide) (by decide) (by decide), h4.ku]; simp
    funext r
    by_cases hm : r ∈ [rgKB, rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ, rgBIT,
        rgHQ, rgOC, rgOFFC, rgROWC, rgCOLC, rgKU]
    · rw [hzs r hm, zer r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> decide)]
    · exact hin r hm
  · rw [g9, g8, g7, g6, g5, h4.cell, h3.cell, h2.cell, h1.cell]

end Whole

end NearCubicWires.WireExponent3_5.PrimT.Ctr
