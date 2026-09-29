import Proof.Wire_3_5.Primitive.Writers.SymDecStar

/-! # thrStage4U, part 1: the THR cap `B_T(n)` from `n` in the cell's registers

P3:1188-1189 (star:partition: `r = rowBr c_r n = 2(⌊log₂ L⌋ + c_r)`, `L = ⌈log₂(n+2)⌉`), P3:3819, 3400 (the sparse count
`s(q)`) and P3:3425-3430 (the cap `B_m(q)` of `tr:B`, here in mode `thr`: the THR filter's cap `cap_T = B_T(n)`, the
second entry of the call's hash numbers): from `n` alone (no star parameters: the data stage sees only `n`), PA's
`StarNums.phaseA` (`L`, `r`), `SparseNum.sparseM` (`s(n)`) and `CapNum.capM` with the mode flag `Hb 4` raised
(`Codec.modeBit .thr = true`):

* `capTW`, `capTCost`, **`capT_spec`**: `Hb 13 = Ledger.rowBCap C .thr (rowBr c_r n) s(n) n`, every register outside
  PA's three blocks unchanged, the streams and the cell unchanged.

Paper quantity of the main type: the THR cap `B_T(q)` (`Ledger.rowBCap C .thr …`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SymDec

variable (cap : ℕ) (x : ℕ)

/-- **The THR cap from `n`**: `L`, `r`, `s(n)`, the cap's inputs, the THR flag, the cap. -/
def capTW (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR dN (SGb 0) xT) (.seq (StarNums.phaseA cr SGb)
  (.seq (FinalPass.Hash4.wcopyR (SGb 1) (Gb 0) xT) (.seq (SparseNum.sparseM ζ Cδ Gb)
  (.seq (FinalPass.Hash4.wcopyR dN (Hb 0) xT) (.seq (FinalPass.Hash4.wcopyR (SGb 3) (Hb 1) xT)
  (.seq (FinalPass.Hash4.wcopyR (Gb 12) (Hb 2) xT) (.seq (FinalPass.Hash4.wcopyR (SGb 1) (Hb 3) xT)
  (.seq (.inc (Hb 4)) (CapNum.capM C Hb)))))))))

/-- Its cost bound. -/
def capTCost (n cr t sp L : ℕ) : ℕ :=
  (18 * n + 3) + 1 + ((200 * n + 30 * cr + 800) + 1 + ((18 * L + 3) + 1 + ((t + 5) * (40 * UnaryPow.sq cap) + 1 +
    ((18 * n + 3) + 1 + ((18 * cap + 3) + 1 + ((18 * sp + 3) + 1 + ((18 * L + 3) + 1 +
      (3 + 1 + ((cap + 2) * 200 + 1500) * UnaryPow.sq cap))))))))

theorem capT_spec (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (n : ℕ)
    (σ : WState (LNS x) LNR) (hn : σ.val dN = n)
    (hSG : ∀ i, σ.val (SGb i) = 0) (hG : ∀ i, σ.val (Gb i) = 0) (hH : ∀ i, σ.val (Hb i) = 0) (hx : σ.val xT = 0)
    (hcS : 4 * n + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C .thr n (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) cap) :
    ∃ τ c, WExec cap (capTW x cr ζ Cδ C) σ τ c ∧
      τ.val (Hb 13) = Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n ∧
      (∀ r, SymDec.Outside r → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      c ≤ capTCost cap n cr (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n) (Ledger.Lq n) := by
  obtain ⟨sp, hsp⟩ : ∃ v, v = Ledger.rowBSparse h0 h1 2 Cδ n := ⟨_, rfl⟩
  rw [← hsp] at hcC ⊢
  have hSGne : ∀ (i : Fin 20) (j : Fin 24), SGb i ≠ Gb j := fun i j e => by
    have := congrArg Fin.val e; rw [SGb_val, Gb_val] at this; have := i.isLt; omega
  have hSHne : ∀ (i : Fin 20) (j : Fin 32), SGb i ≠ Hb j := fun i j e => by
    have := congrArg Fin.val e; rw [SGb_val, Hb_val] at this; have := i.isLt; omega
  have hGHne : ∀ (i : Fin 24) (j : Fin 32), Gb i ≠ Hb j := fun i j e => by
    have := congrArg Fin.val e; rw [Gb_val, Hb_val] at this; have := i.isLt; omega
  have hxS : ∀ i, SGb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [xT] at this; omega
  have hxG : ∀ i, Gb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [xT] at this; omega
  have hxH : ∀ i, Hb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [xT] at this; omega
  have hdS : ∀ i, SGb i ≠ dN := fun i e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dN] at this; omega
  have hdH : ∀ i, Hb i ≠ dN := fun i e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dN] at this; omega
  have hdx : dN ≠ xT := by decide
  have hn2 : n ≤ cap := hcC.hq
  -- 1: SGb 0 := n
  have e1 := FinalPass.Hash4.wcopyR_spec cap dN (SGb 0) xT (hdS 0).symm hdx (hxS 0) σ (hSG 0) hx (by rw [hn]; omega)
  rw [hn] at e1
  obtain ⟨σ1, g1⟩ : ∃ y, y = σ.setv (SGb 0) n := ⟨_, rfl⟩
  rw [← g1] at e1
  -- 2: L, r
  have e2 := StarNums.phaseA_spec cap cr SGb σ1 (fun i hi => by
    rw [g1]; simp [Function.update_apply, SGb.injective.ne hi, hSG]) (by rw [g1]; simp; omega)
  have hv0 : σ1.val (SGb 0) = n := by rw [g1]; simp
  rw [hv0] at e2
  obtain ⟨σ2, g2⟩ : ∃ y, y = (σ1.setv (SGb 1) (Nat.clog 2 (n + 2))).setv (SGb 3) (Ledger.rowBr cr n) := ⟨_, rfl⟩
  rw [← g2] at e2
  have v1 : σ2.val (SGb 1) = Ledger.Lq n := by rw [g2]; simp [Function.update_apply, SGb.injective.ne (show (1 : Fin 20) ≠ 3 by decide)]; rfl
  have v3 : σ2.val (SGb 3) = Ledger.rowBr cr n := by rw [g2]; simp
  have o2 : ∀ r, SGb 1 ≠ r → SGb 3 ≠ r → σ2.val r = σ1.val r := fun r a b => by
    rw [g2]; simp [Function.update_of_ne a.symm, Function.update_of_ne b.symm]
  have o1 : ∀ r, SGb 0 ≠ r → σ1.val r = σ.val r := fun r h => by rw [g1]; simp [Function.update_of_ne h.symm]
  have o21 : ∀ r, (∀ i : Fin 20, SGb i ≠ r) → σ2.val r = σ.val r := fun r h => by rw [o2 r (h 1) (h 3), o1 r (h 0)]
  -- 3: Gb 0 := L
  have gL : σ2.val (SGb 1) = Ledger.Lq n := v1
  have e3 := FinalPass.Hash4.wcopyR_spec cap (SGb 1) (Gb 0) xT (hSGne 1 0) (hxS 1) (hxG 0) σ2
    (by rw [o21 _ (fun i => hSGne i 0), hG]) (by rw [o21 _ hxS, hx]) (by rw [gL]; exact hcC.hL1)
  rw [gL] at e3
  obtain ⟨σ3, g3⟩ : ∃ y, y = σ2.setv (Gb 0) (Ledger.Lq n) := ⟨_, rfl⟩
  rw [← g3] at e3
  have o3 : ∀ r, Gb 0 ≠ r → σ3.val r = σ2.val r := fun r h => by rw [g3]; simp [Function.update_of_ne h.symm]
  -- 4: the sparse count
  have e4 := SparseNum.sparse_spec cap h0 h1 Cδ Gb σ3 n (by rw [g3]; simp) (fun i hi => by
      rw [o3 _ (Gb.injective.ne hi).symm, o21 _ (fun k => hSGne k i), hG]) hcP
  rw [← hsp] at e4
  obtain ⟨σ4, g4⟩ : ∃ y, y = (σ3.setv (Gb 11) (Ledger.rowBLambda h0 h1 2 n)).setv (Gb 12) sp := ⟨_, rfl⟩
  rw [← g4] at e4
  have o4 : ∀ r, Gb 11 ≠ r → Gb 12 ≠ r → σ4.val r = σ3.val r := fun r a b => by
    rw [g4]; simp [Function.update_of_ne a.symm, Function.update_of_ne b.symm]
  have vsp : σ4.val (Gb 12) = sp := by rw [g4]; simp
  have oS4 : ∀ i, σ4.val (SGb i) = σ2.val (SGb i) := fun i => by
    rw [o4 _ (hSGne i 11).symm (hSGne i 12).symm, o3 _ (hSGne i 0).symm]
  have oH4 : ∀ j, σ4.val (Hb j) = σ.val (Hb j) := fun j => by
    rw [o4 _ (hGHne 11 j) (hGHne 12 j), o3 _ (hGHne 0 j), o21 _ (fun i => hSHne i j)]
  have ox4 : σ4.val xT = 0 := by rw [o4 _ (hxG 11) (hxG 12), o3 _ (hxG 0), o21 _ hxS, hx]
  have odN4 : σ4.val dN = n := by
    rw [o4 _ (by decide) (by decide), o3 _ (by decide), o21 _ (fun i => hdS i), hn]
  -- 5-8: the cap's inputs
  have e5 := FinalPass.Hash4.wcopyR_spec cap dN (Hb 0) xT (hdH 0).symm hdx (hxH 0) σ4 (by rw [oH4, hH])
    ox4 (by rw [odN4]; omega)
  rw [odN4] at e5
  obtain ⟨σ5, g5⟩ : ∃ y, y = σ4.setv (Hb 0) n := ⟨_, rfl⟩
  rw [← g5] at e5
  have o5 : ∀ r, Hb 0 ≠ r → σ5.val r = σ4.val r := fun r h => by rw [g5]; simp [Function.update_of_ne h.symm]
  have e6 := FinalPass.Hash4.wcopyR_spec cap (SGb 3) (Hb 1) xT (hSHne 3 1) (hxS 3) (hxH 1) σ5
    (by rw [o5 _ (Hb.injective.ne (by decide)), oH4, hH]) (by rw [o5 _ (hxH 0), ox4])
    (by rw [o5 _ (hSHne 3 0).symm, oS4, v3]; exact hcC.hr)
  rw [o5 _ (hSHne 3 0).symm, oS4, v3] at e6
  obtain ⟨σ6, g6⟩ : ∃ y, y = σ5.setv (Hb 1) (Ledger.rowBr cr n) := ⟨_, rfl⟩
  rw [← g6] at e6
  have o6 : ∀ r, Hb 1 ≠ r → σ6.val r = σ5.val r := fun r h => by rw [g6]; simp [Function.update_of_ne h.symm]
  have e7 := FinalPass.Hash4.wcopyR_spec cap (Gb 12) (Hb 2) xT (hGHne 12 2) (hxG 12) (hxH 2) σ6
    (by rw [o6 _ (Hb.injective.ne (by decide)), o5 _ (Hb.injective.ne (by decide)), oH4, hH])
    (by rw [o6 _ (hxH 1), o5 _ (hxH 0), ox4])
    (by rw [o6 _ (hGHne 12 1).symm, o5 _ (hGHne 12 0).symm, vsp]; exact hcC.hs)
  rw [o6 _ (hGHne 12 1).symm, o5 _ (hGHne 12 0).symm, vsp] at e7
  obtain ⟨σ7, g7⟩ : ∃ y, y = σ6.setv (Hb 2) sp := ⟨_, rfl⟩
  rw [← g7] at e7
  have o7 : ∀ r, Hb 2 ≠ r → σ7.val r = σ6.val r := fun r h => by rw [g7]; simp [Function.update_of_ne h.symm]
  have e8 := FinalPass.Hash4.wcopyR_spec cap (SGb 1) (Hb 3) xT (hSHne 1 3) (hxS 1) (hxH 3) σ7
    (by rw [o7 _ (Hb.injective.ne (by decide)), o6 _ (Hb.injective.ne (by decide)),
      o5 _ (Hb.injective.ne (by decide)), oH4, hH])
    (by rw [o7 _ (hxH 2), o6 _ (hxH 1), o5 _ (hxH 0), ox4])
    (by rw [o7 _ (hSHne 1 2).symm, o6 _ (hSHne 1 1).symm, o5 _ (hSHne 1 0).symm, oS4, gL]; exact hcC.hL1)
  rw [o7 _ (hSHne 1 2).symm, o6 _ (hSHne 1 1).symm, o5 _ (hSHne 1 0).symm, oS4, gL] at e8
  obtain ⟨σ8, g8⟩ : ∃ y, y = σ7.setv (Hb 3) (Ledger.Lq n) := ⟨_, rfl⟩
  rw [← g8] at e8
  have o8 : ∀ r, Hb 3 ≠ r → σ8.val r = σ7.val r := fun r h => by rw [g8]; simp [Function.update_of_ne h.symm]
  have o85 : ∀ r, Hb 0 ≠ r → Hb 1 ≠ r → Hb 2 ≠ r → Hb 3 ≠ r → σ8.val r = σ4.val r := fun r a b c d => by
    rw [o8 r d, o7 r c, o6 r b, o5 r a]
  -- 9: the THR flag, then the cap
  have f4 : σ8.val (Hb 4) = 0 := by
    rw [o85 _ (Hb.injective.ne (by decide)) (Hb.injective.ne (by decide)) (Hb.injective.ne (by decide))
      (Hb.injective.ne (by decide)), oH4, hH]
  have e9a : WExec cap (.inc (Hb 4)) σ8 (σ8.setv (Hb 4) (σ8.val (Hb 4) + 1)) 3 :=
    WExec.inc (Hb 4) σ8 (by rw [f4]; exact hcC.hc1)
  rw [f4] at e9a
  obtain ⟨σ8b, g8b⟩ : ∃ y, y = σ8.setv (Hb 4) (0 + 1) := ⟨_, rfl⟩
  rw [← g8b] at e9a
  have o8b : ∀ r, Hb 4 ≠ r → σ8b.val r = σ8.val r := fun r h => by rw [g8b]; simp [Function.update_of_ne h.symm]
  have e9 := CapNum.capM_spec cap C .thr Hb σ8b n (Ledger.rowBr cr n) sp
    (by rw [o8b _ (Hb.injective.ne (by decide)), o8 _ (Hb.injective.ne (by decide)),
      o7 _ (Hb.injective.ne (by decide)), o6 _ (Hb.injective.ne (by decide)), g5]; simp)
    (by rw [o8b _ (Hb.injective.ne (by decide)), o8 _ (Hb.injective.ne (by decide)),
      o7 _ (Hb.injective.ne (by decide)), g6]; simp)
    (by rw [o8b _ (Hb.injective.ne (by decide)), o8 _ (Hb.injective.ne (by decide)), g7]; simp)
    (by rw [o8b _ (Hb.injective.ne (by decide)), g8]; simp)
    (by rw [g8b]; simp [Codec.modeBit])
    (fun i hi => by
      have n0 : Hb 0 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n1 : Hb 1 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n2 : Hb 2 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n3 : Hb 3 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n4 : Hb 4 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      rw [o8b _ n4, o85 _ n0 n1 n2 n3, oH4, hH])
    hcC.hc1 hcC.hr hcC.hs hcC.hq hcC.hL1 hcC.h48 hcC.h32 hcC.h64 hcC.h4832 hcC.hrsq hcC.hC hcC.hnum hcC.hLK
    hcC.hsum hcC.hroot1 hcC.h3 hcC.h3q hcC.hCe hcC.hE hcC.hroot2
  obtain ⟨σ9, g9⟩ : ∃ y, y = σ8b.setv (Hb 13) (Ledger.rowBCap C .thr (Ledger.rowBr cr n) sp n) := ⟨_, rfl⟩
  rw [← g9] at e9
  have o9 : ∀ r, Hb 13 ≠ r → σ9.val r = σ8b.val r := fun r h => by rw [g9]; simp [Function.update_of_ne h.symm]
  have oAll : ∀ r, (∀ i : Fin 20, SGb i ≠ r) → (∀ j : Fin 24, Gb j ≠ r) → (∀ k : Fin 32, Hb k ≠ r) →
      σ9.val r = σ.val r := fun r a b c => by
    rw [o9 r (c 13), o8b r (c 4), o85 r (c 0) (c 1) (c 2) (c 3), o4 r (b 11) (b 12), o3 r (b 0), o21 r a]
  refine ⟨σ9, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9a e9)))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g9]; simp
  · intro r hr
    exact oAll r (SymDec.out_SGb hr) (SymDec.out_Gb hr) (SymDec.out_Hb hr)
  · simp only [g9, g8b, g8, g7, g6, g5, g4, g3, g2, g1, WState.setv_st]
  · simp only [g9, g8b, g8, g7, g6, g5, g4, g3, g2, g1, WState.setv_sh]
  · simp only [g9, g8b, g8, g7, g6, g5, g4, g3, g2, g1, WState.setv_cell]
  · have := hcC.hr
    unfold capTCost
    omega

end NearCubicWires.WireExponent3_5.PrimT.TS4
