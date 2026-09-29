import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR2

/-! # THR decode front, RADIX part 3: the pre-dock program and the docks' entry

`pbPreW = tVW ; wrU (bT) V ; wrU (bT+1) |carriers| ; wrU (bT+2) cap_T ; rRadK := 1`: from the unit's decoded state
at a RADIX unit (the streams as at the entry but the data tape's head), **`pbPre_run`** reaches the docks' entry
`DockInT` (`ThrDecR1`) at the count `tV`, the RADIX marker raised.

Paper quantities of the main type: the front end's and the numbers machine's inputs (P3:2543-2558, 3071-3091). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

section R3
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- The unit's scratch tape `bT + i` (`i < 17`). -/
def sVx (x : ℕ) (hx : dX T N ≤ x) (i : ℕ) (hi : i < 17) : Fin (LNS x + 1) :=
  ⟨161 + bT T N + i, by unfold LNS; unfold dX at hx; omega⟩

theorem sVx_val (x : ℕ) (hx : dX T N ≤ x) (i : ℕ) (hi : i < 17) : (sVx T N x hx i hi).val = 161 + bT T N + i := rfl

/-- **The pre-dock program.** -/
def pbPreW (x : ℕ) (hx : dX T N ≤ x) : WM (LNS x) LNR :=
  .seq (tVW x N.Cn N.Dn) (.seq (HashCell.wrU (sVx T N x hx 0 (by decide)) (H 30) (H 20) (H 31) (H 32))
    (.seq (HashCell.wrU (sVx T N x hx 1 (by decide)) (H 30) (Hb 0) (H 31) (H 32))
    (.seq (HashCell.wrU (sVx T N x hx 2 (by decide)) (H 30) (Hb 1) (H 31) (H 32)) (.inc rRadK))))

theorem blank_st_sT (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (i : Fin (LNS x + 1)) (hi : 161 ≤ i.val) :
    (CellLoopD.blankCellD x w out j u).st i = [] := by
  have n0 : i ≠ sk x 0 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n1 : i ≠ sk x 1 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n2 : i ≠ sk x 2 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n3 : i ≠ sk x 113 := fun e => by rw [e, sk_val] at hi; simp at hi
  simp [CellLoopD.blankCellD, blankCell, n0, n1, n2, n3]

theorem blank_st_mid (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (i : Fin (LNS x + 1))
    (hi : 130 ≤ i.val ∧ i.val ≤ 136) : (CellLoopD.blankCellD x w out j u).st i = [] := by
  have n0 : i ≠ sk x 0 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n1 : i ≠ sk x 1 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n2 : i ≠ sk x 2 := fun e => by rw [e, sk_val] at hi; simp at hi
  have n3 : i ≠ sk x 113 := fun e => by rw [e, sk_val] at hi; simp at hi
  simp [CellLoopD.blankCellD, blankCell, n0, n1, n2, n3]

theorem blank_sh_ne1 (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (i : Fin (LNS x + 1)) (hi : i ≠ sk x 1) :
    (CellLoopD.blankCellD x w out j u).sh i = 0 := by
  simp [CellLoopD.blankCellD, blankCell, hi]

variable (cap : ℕ)

/-- **The pre-dock program, run**: the docks' entry at the count `tV`, the RADIX marker `1`, `H 20 = tV`, every other
register kept, the streams but the three scratch tapes kept, the heads and the cell kept. -/
theorem pbPre_run (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (len n capT ncar : ℕ) (hst : σ.st = (CellLoopD.blankCellD x w out j u).st)
    (hsh : ∀ s, s ≠ sk x 113 → σ.sh s = (CellLoopD.blankCellD x w out j u).sh s)
    (hL : σ.val LEN = len) (hN : σ.val dN = n) (h0 : σ.val (Hb 0) = ncar) (h1 : σ.val (Hb 1) = capT)
    (zH : ∀ k : Fin 40, 20 ≤ k.val → σ.val (H k) = 0) (zT : σ.val TM = 0) (zR : σ.val rRadK = 0)
    (hcA : len + (n + 1) ^ 26 * 2 + n + capT + 42 ≤ cap) (hCn : N.Cn ≤ cap) (hPD : (n + capT + 1) ^ N.Dn ≤ cap)
    (hcB : tV len n capT N.Cn N.Dn + n + capT + ncar + 42 ≤ cap) :
    ∃ τ c, WExec cap (pbPreW T N x hx) σ τ c ∧
      c ≤ 150 * UnaryPow.sq cap + (N.Dn + 1) * (4 * UnaryPow.sq cap) + 40 * (tV len n capT N.Cn N.Dn + ncar + capT) + 40 ∧
      DockInT T N x τ w (tV len n capT N.Cn N.Dn) ncar capT ∧ τ.val rRadK = 1 ∧
      τ.val (H 20) = tV len n capT N.Cn N.Dn ∧ (∀ r, r ≠ rRadK → r ≠ H 20 → τ.val r = σ.val r) ∧
      (∀ i : Fin (LNS x + 1), (i.val < 161 + bT T N ∨ 161 + bT T N + 3 ≤ i.val) → τ.st i = σ.st i) ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, e1, v20, k1, st1, sh1, cl1⟩ := tV_run cap x σ len n capT N.Cn N.Dn hL hN h1 zH zT hcA hCn hPD
    (by omega)
  have nR : ∀ k : Fin 40, H k ≠ rRadK := fun k => H_ne k rRadK (by decide) |>.symm
  have hB := fun (r : Fin LNR) => r
  have s0 : ∀ i : ℕ, (hi : i < 17) → τ1.st (sVx T N x hx i hi) = [] := fun i hi => by
    rw [st1, hst]; exact blank_st_sT x w out j u _ (by rw [sVx_val]; omega)
  have s0h : ∀ i : ℕ, (hi : i < 17) → τ1.sh (sVx T N x hx i hi) = 0 := by
    intro i hi
    have h113 : ((113 : Fin 161) : ℕ) = 113 := rfl
    have h1v : ((1 : Fin 161) : ℕ) = 1 := rfl
    have a1 : sVx T N x hx i hi ≠ sk x 113 := fun e => by
      have := congrArg Fin.val e; rw [sVx_val, sk_val, h113] at this; omega
    have a2 : sVx T N x hx i hi ≠ sk x 1 := fun e => by
      have := congrArg Fin.val e; rw [sVx_val, sk_val, h1v] at this; omega
    rw [sh1, hsh _ a1]
    exact blank_sh_ne1 x w out j u _ a2
  have k30 : τ1.val (H 30) = 0 := by rw [k1 _ (by decide)]; exact zH 30 (by decide)
  have k31 : τ1.val (H 31) = 0 := by rw [k1 _ (by decide)]; exact zH 31 (by decide)
  have k32 : τ1.val (H 32) = 0 := by rw [k1 _ (by decide)]; exact zH 32 (by decide)
  have e2 := HashCell.wrU_spec cap (sVx T N x hx 0 (by decide)) (H 30) (H 20) (H 31) (H 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) τ1 (s0 0 (by decide)) (s0h 0 (by decide)) k30 k31 k32 (by rw [v20]; omega)
  set τ2 := τ1.sets (sVx T N x hx 0 (by decide)) (List.replicate (τ1.val (H 20)) true) with hτ2
  have e3 := HashCell.wrU_spec cap (sVx T N x hx 1 (by decide)) (H 30) (Hb 0) (H 31) (H 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) τ2
    (by rw [hτ2, WState.sets_st, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [sVx_val] at this)]
        exact s0 1 (by decide))
    (by rw [hτ2]; exact s0h 1 (by decide)) k30 k31 k32
    (by rw [hτ2]; simp only [WState.sets_val]; rw [k1 _ (by decide), h0]; omega)
  set τ3 := τ2.sets (sVx T N x hx 1 (by decide)) (List.replicate (τ2.val (Hb 0)) true) with hτ3
  have e4 := HashCell.wrU_spec cap (sVx T N x hx 2 (by decide)) (H 30) (Hb 1) (H 31) (H 32) (by decide) (by decide)
    (by decide) (by decide) (by decide) τ3
    (by rw [hτ3, WState.sets_st, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [sVx_val] at this),
          hτ2, WState.sets_st, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [sVx_val] at this)]
        exact s0 2 (by decide))
    (by rw [hτ3, hτ2]; exact s0h 2 (by decide)) k30 k31 k32
    (by rw [hτ3, hτ2]; simp only [WState.sets_val]; rw [k1 _ (by decide), h1]; omega)
  set τ4 := τ3.sets (sVx T N x hx 2 (by decide)) (List.replicate (τ3.val (Hb 1)) true) with hτ4
  have v4 : τ4.val = τ1.val := by rw [hτ4, hτ3, hτ2]; rfl
  have e5 := WExec.inc (cap := cap) rRadK τ4 (by rw [v4, k1 _ (by decide), zR]; omega)
  set τ := τ4.setv rRadK (τ4.val rRadK + 1) with hτ
  have vHb0 : τ1.val (Hb 0) = ncar := by rw [k1 _ (by decide), h0]
  have vHb1 : τ1.val (Hb 1) = capT := by rw [k1 _ (by decide), h1]
  have stτ : ∀ i : Fin (LNS x + 1), τ.st i = if i.val = 161 + bT T N + 2 then List.replicate capT true
      else if i.val = 161 + bT T N + 1 then List.replicate ncar true
      else if i.val = 161 + bT T N then List.replicate (tV len n capT N.Cn N.Dn) true else τ1.st i := by
    intro i
    rw [hτ, WState.setv_st, hτ4, WState.sets_st, hτ3, WState.sets_st, hτ2, WState.sets_st]
    simp only [Function.update_apply]
    by_cases a2 : i.val = 161 + bT T N + 2
    · rw [if_pos (Fin.ext (by rw [sVx_val]; omega)), if_pos a2]
      simp only [WState.sets_val]; rw [vHb1]
    · rw [if_neg (fun e => a2 (by rw [e, sVx_val])), if_neg a2]
      by_cases a1 : i.val = 161 + bT T N + 1
      · rw [if_pos (Fin.ext (by rw [sVx_val]; omega)), if_pos a1]
        simp only [WState.sets_val]; rw [vHb0]
      · rw [if_neg (fun e => a1 (by rw [e, sVx_val])), if_neg a1]
        by_cases a0 : i.val = 161 + bT T N
        · rw [if_pos (Fin.ext (by rw [sVx_val]; omega)), if_pos a0, v20]
        · rw [if_neg (fun e => a0 (by rw [e, sVx_val]; omega)), if_neg a0]
  have shτ : τ.sh = σ.sh := by rw [hτ, WState.setv_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh, hτ2, WState.sets_sh, sh1]
  have n0 : ∀ i : Fin (LNS x + 1), i.val < 161 → i ≠ sk x 113 → i ≠ sk x 1 → i ≠ sk x 0 → i ≠ sk x 2 →
      σ.st i = [] := fun i _ a b c d => by rw [hst]; simp [CellLoopD.blankCellD, blankCell, a, b, c, d]
  refine ⟨τ, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    ?_, ?_, shτ, ?_⟩
  · rw [v20]
    rw [show τ2.val (Hb 0) = ncar by rw [hτ2]; exact vHb0, show τ3.val (Hb 1) = capT by rw [hτ3, hτ2]; exact vHb1]
    nlinarith [UnaryPow.sq_ge cap]
  · rw [stτ, if_neg (by simp [sk_val]), if_neg (by simp [sk_val]), if_neg (by simp [sk_val]; omega), st1, hst]
    have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
    simp [CellLoopD.blankCellD, blankCell, n0B]
  · rw [shτ, hsh _ (fun e => absurd (sk_inj x e) (by decide))]
    exact blank_sh_ne1 x w out j u _ (fun e => absurd (sk_inj x e) (by decide))
  · intro i hi; rw [stτ, if_neg (by omega), if_neg (by omega), if_pos hi]
  · intro i hi; rw [stτ, if_neg (by omega), if_pos hi]
  · intro i hi; rw [stτ, if_pos hi]
  · intro i hi
    rw [stτ, if_neg (by omega), if_neg (by omega), if_neg (by omega), st1, hst]
    rcases hi with h | h | h
    · exact blank_st_mid x w out j u i h
    · exact blank_st_sT x w out j u i (by omega)
    · exact blank_st_sT x w out j u i (by omega)
  · intro i hi
    rw [shτ]
    by_cases h113 : i = sk x 113
    · rw [h113, sk_val] at hi; simp at hi
    · rw [hsh i h113]
      exact blank_sh_ne1 x w out j u i (fun e => by rw [e, sk_val] at hi; simp at hi)
  · rw [hτ]; simp [v4, k1 rRadK (by decide), zR]
  · rw [hτ]; simp only [WState.setv_val]; rw [Function.update_of_ne (show H 20 ≠ rRadK by decide), v4, v20]
  · intro r a b
    rw [hτ]; simp only [WState.setv_val]; rw [Function.update_of_ne a, v4, k1 r b]
  · intro i hi
    rw [stτ, if_neg (by omega), if_neg (by omega), if_neg (by omega), st1]
  · rw [hτ, WState.setv_cell, hτ4, WState.sets_cell, hτ3, WState.sets_cell, hτ2, WState.sets_cell, cl1]

end R3

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
