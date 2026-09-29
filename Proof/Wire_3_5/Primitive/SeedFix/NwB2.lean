import Proof.Wire_3_5.Primitive.SeedFix.NwB1
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR3

/-! # NW phase (b), part 2: the docks' entry from a clean bank

The pre-dock program `ThrDecF.pbPreW` (the count `tV` into `H 20`, `1^{tV}`, `1^{|carriers|}`, `1^{cap_T}` on the
scratch tapes `bT … bT + 2`, the RADIX marker) run from ANY bank whose request stream `0` holds `frame w` and whose
streams `130 … 136`, `161 …` are blank with heads `0` (at phase (b)'s entry every stream but `sIn` is blank):
**`pbPre_run'`**, the docks' entry `ThrDecF.DockInT` (the unit cell's `pbPre_run` without `blankCellD`).

Paper quantity of the main type: the THR numbers machine's input (the request, the count, `|carriers|`, `cap_T`;
P3:2543-2558). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.UnionMachine.ThrDec NearCubicWires.WireExponent3_5.PrimT.ThrDecF

section R3
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (cap : ℕ)

/-- **The pre-dock program from a clean bank**: the docks' entry at the count `tV`. -/
theorem pbPre_run' (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (w : List Bool)
    (len n capT ncar : ℕ) (hreq : σ.st (sk x 0) = frame w) (hreqh : σ.sh (sk x 0) = 0)
    (hbl : ∀ i : Fin (LNS x + 1), (130 ≤ i.val ∧ i.val ≤ 136) ∨ 161 ≤ i.val → σ.st i = [])
    (hhd : ∀ i : Fin (LNS x + 1), (130 ≤ i.val ∧ i.val ≤ 136) ∨ 161 ≤ i.val → σ.sh i = 0)
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
  have s0 : ∀ i : ℕ, (hi : i < 17) → τ1.st (sVx T N x hx i hi) = [] := fun i hi => by
    rw [st1]; exact hbl _ (Or.inr (by rw [sVx_val]; omega))
  have s0h : ∀ i : ℕ, (hi : i < 17) → τ1.sh (sVx T N x hx i hi) = 0 := fun i hi => by
    rw [sh1]; exact hhd _ (Or.inr (by rw [sVx_val]; omega))
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
  refine ⟨τ, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    ?_, ?_, shτ, ?_⟩
  · rw [v20]
    rw [show τ2.val (Hb 0) = ncar by rw [hτ2]; exact vHb0, show τ3.val (Hb 1) = capT by rw [hτ3, hτ2]; exact vHb1]
    nlinarith [UnaryPow.sq_ge cap]
  · rw [stτ, if_neg (by simp [sk_val]), if_neg (by simp [sk_val]), if_neg (by simp [sk_val]; omega), st1, hreq]
  · rw [shτ]; exact hreqh
  · intro i hi; rw [stτ, if_neg (by omega), if_neg (by omega), if_pos hi]
  · intro i hi; rw [stτ, if_neg (by omega), if_pos hi]
  · intro i hi; rw [stτ, if_pos hi]
  · intro i hi
    rw [stτ, if_neg (by omega), if_neg (by omega), if_neg (by omega), st1]
    rcases hi with h | h | h
    · exact hbl i (Or.inl h)
    · exact hbl i (Or.inr (by omega))
    · exact hbl i (Or.inr (by omega))
  · intro i hi
    rw [shτ]
    rcases hi with h | h | h
    · have e : i = sk x 0 := Fin.ext (by rw [sk_val]; simpa using h)
      rw [e]; exact hreqh
    · exact hhd i (Or.inl h)
    · exact hhd i (Or.inr (by omega))
  · rw [hτ]; simp [v4, k1 rRadK (by decide), zR]
  · rw [hτ]; simp only [WState.setv_val]; rw [Function.update_of_ne (show H 20 ≠ rRadK by decide), v4, v20]
  · intro r a b
    rw [hτ]; simp only [WState.setv_val]; rw [Function.update_of_ne a, v4, k1 r b]
  · intro i hi
    rw [stτ, if_neg (by omega), if_neg (by omega), if_neg (by omega), st1]
  · rw [hτ, WState.setv_cell, hτ4, WState.sets_cell, hτ3, WState.sets_cell, hτ2, WState.sets_cell, cl1]

end R3

end NearCubicWires.WireExponent3_5.PrimT.NwB
