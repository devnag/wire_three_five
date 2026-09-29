import Proof.Wire_3_5.Primitive.SeedFix.ThrDecC

/-! # THR decode front, part D: the capped `[j < TOT]` test and the unit's index split

`ThrDecFront` bounds the front's cost by `bound n`, independent of the unit `j` (only the capacity grows with `j`,
`need n + j ≤ cap`): the counter `1^j` on stream `2` is never read whole. **`cmpW`** walks it at most `TOT` cells
(a countdown from `TOT` in `H 20`, the steps in `H 21`), sets the flag `H 22 = [j < TOT]` and rewinds; only when
`j < TOT` does the decode read the counter (SymDec's `idxW`, at most `TOT` cells).

* `cmpBody`, `cmpW`; **`cmp_loop`**, **`cmp_run`** (cost `≤ 16·TOT + 16` plus one copy, the flag, everything
  else kept);
* **`tIdx_run`**: at `j < TOT` from the numbers' registers (`TNums`: `G 56 = TOT`, `G 55 = EU`, `G 53 = N²`,
  `G 52 = Σp`, `G 41 = |𝒢|`, `dNC = |carriers|`, the block `H` zero), SymDec's `HVals` at `M = 0`.

Paper quantity of the main types: the THR tape's unit `j` (its entry `j / EU`, its row, its state `t` and the state's
seed, selection and prime row, `Enum.thrIndexEquiv`), P3:3011-3016. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

section D
variable (cap : ℕ) (x : ℕ)

/-- One step of the countdown: on a counter cell, count it; past the counter, stop and raise the flag. -/
def cmpBody : WM (LNS x) LNR :=
  .ifs (sk x 2) (.seq (.dec (H 20)) (.seq (.fwd (sk x 2)) (.inc (H 21)))) (.seq (WM.clear (H 20)) (.inc (H 22)))

/-- **The capped test** `H 22 := [j < TOT]`: at most `TOT` cells of the counter walked, then rewound. -/
def cmpW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (G 56) (H 20) TM) (.seq (.whr (H 20) (cmpBody x)) (WM.rewind (sk x 2) (H 21)))

theorem H20_ne_21 : H 20 ≠ H 21 := by decide
theorem H20_ne_22 : H 20 ≠ H 22 := by decide
theorem H21_ne_22 : H 21 ≠ H 22 := by decide

/-- **The countdown loop.** -/
theorem cmp_loop (j : ℕ) : ∀ (m h : ℕ) (σ : WState (LNS x) LNR), σ.val (H 20) = m → σ.val (H 21) = h →
    σ.val (H 22) = 0 → σ.sh (sk x 2) = h → σ.st (sk x 2) = List.replicate j true → h ≤ j → h + m + 1 ≤ cap →
    ∃ τ c, WExec cap (.whr (H 20) (cmpBody x)) σ τ c ∧ c ≤ 10 * m + 10 ∧ τ.val (H 20) = 0 ∧
      τ.val (H 21) = min j (h + m) ∧ τ.val (H 22) = (if j < h + m then 1 else 0) ∧
      τ.sh (sk x 2) = min j (h + m) ∧ (∀ r, r ≠ H 20 → r ≠ H 21 → r ≠ H 22 → τ.val r = σ.val r) ∧
      τ.st = σ.st ∧ (∀ s, s ≠ sk x 2 → τ.sh s = σ.sh s) ∧ τ.cell = σ.cell := by
  intro m
  induction m with
  | zero =>
    intro h σ hK hP hF hs hst hj hc
    refine ⟨σ, 1, WExec.whrF hK, by omega, hK, by rw [hP]; omega, by rw [hF, if_neg (by omega)], by rw [hs]; omega,
      fun _ _ _ _ => rfl, rfl, fun _ _ => rfl, rfl⟩
  | succ m ih =>
    intro h σ hK hP hF hs hst hj hc
    have hK0 : σ.val (H 20) ≠ 0 := by rw [hK]; omega
    by_cases hlt : h < j
    · have hb : wbit σ (sk x 2) = true := by
        unfold wbit; rw [hst, hs, Data.rep_read]; simp [hlt]
      have e1 := WExec.dec (cap := cap) (H 20) σ (by rw [hK]; omega)
      set σ1 := σ.setv (H 20) (σ.val (H 20) - 1) with hσ1
      have e2 := WExec.fwd (cap := cap) (sk x 2) σ1
      set σ2 := σ1.seth (sk x 2) (σ1.sh (sk x 2) + 1) with hσ2
      have e3 := WExec.inc (cap := cap) (H 21) σ2 (by rw [hσ2, hσ1]; simp [Function.update_apply, H20_ne_21.symm, hP]; omega)
      set σ3 := σ2.setv (H 21) (σ2.val (H 21) + 1) with hσ3
      obtain ⟨τ, c, e, cle, t20, t21, t22, tsh, tk, tst, tsho, tcl⟩ := ih (h + 1) σ3
        (by rw [hσ3, hσ2, hσ1]; simp [Function.update_apply, H20_ne_21, hK])
        (by rw [hσ3, hσ2, hσ1]; simp [Function.update_apply, H20_ne_21.symm, hP])
        (by rw [hσ3, hσ2, hσ1]; simp [Function.update_apply, H21_ne_22.symm, H20_ne_22.symm, hF])
        (by rw [hσ3, hσ2, hσ1]; simp [hs])
        (by rw [hσ3, hσ2, hσ1]; simp [hst]) (by omega) (by omega)
      refine ⟨τ, _, WExec.whrT hK0 (WExec.ifsT hb (WExec.seq e1 (WExec.seq e2 e3))) e, by omega, t20, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · rw [t21]; congr 1; omega
      · rw [t22]; congr 1; simp only [eq_iff_iff]; omega
      · rw [tsh]; congr 1; omega
      · intro r a b c'
        rw [tk r a b c', hσ3, hσ2, hσ1]; simp [Function.update_apply, a, b]
      · rw [tst, hσ3, hσ2, hσ1]; rfl
      · intro s hs'
        rw [tsho s hs', hσ3, hσ2, hσ1]; simp [Function.update_apply, hs']
      · rw [tcl, hσ3, hσ2, hσ1]; rfl
    · have hhj : h = j := by omega
      have hb : wbit σ (sk x 2) = false := by
        unfold wbit; rw [hst, hs, Data.rep_read]; simp; omega
      have e1 := wclear_spec cap (H 20) (m + 1) σ hK (by rw [hK]; omega)
      set σ1 := σ.setv (H 20) 0 with hσ1
      have e2 := WExec.inc (cap := cap) (H 22) σ1 (by rw [hσ1]; simp [Function.update_apply, H20_ne_22.symm, hF]; omega)
      set σ2 := σ1.setv (H 22) (σ1.val (H 22) + 1) with hσ2
      have e3 : WExec cap (.whr (H 20) (cmpBody x)) σ2 σ2 1 :=
        WExec.whrF (by rw [hσ2, hσ1]; simp [Function.update_apply, H20_ne_22])
      refine ⟨σ2, _, WExec.whrT hK0 (WExec.ifsF hb (WExec.seq e1 e2)) e3, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ2, hσ1]; simp [Function.update_apply, H20_ne_22]
      · rw [hσ2, hσ1]; simp [Function.update_apply, H21_ne_22, H20_ne_21.symm, hP]; omega
      · rw [hσ2, hσ1]; simp [Function.update_apply, H20_ne_22.symm, hF]; omega
      · rw [hσ2, hσ1]; simp [hs]; omega
      · intro r a b c'
        rw [hσ2, hσ1]; simp [Function.update_apply, a, c']
      · rw [hσ2, hσ1]; rfl
      · intro s _; rw [hσ2, hσ1]; rfl
      · rw [hσ2, hσ1]; rfl

/-- **The capped test, run**: the flag `H 22 = [j < TOT]`, `H 20`, `H 21` back at `0`, the counter's head back at
`0`, everything else kept. -/
theorem cmp_run (σ : WState (LNS x) LNR) (j TOT : ℕ) (g56 : σ.val (G 56) = TOT) (z20 : σ.val (H 20) = 0)
    (z21 : σ.val (H 21) = 0) (z22 : σ.val (H 22) = 0) (zT : σ.val TM = 0)
    (hst : σ.st (sk x 2) = List.replicate j true) (hsh : σ.sh (sk x 2) = 0) (hc : TOT + 2 ≤ cap) :
    ∃ τ c, WExec cap (cmpW x) σ τ c ∧ c ≤ UnaryPow.sq cap + 16 * TOT + 16 ∧
      τ.val (H 22) = (if j < TOT then 1 else 0) ∧ (∀ r, r ≠ H 22 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have e1 := copy1 cap (G 56) (H 20) TM (by decide) (by decide) (by decide) TOT σ g56 z20 zT (by omega)
  set σ1 := σ.setv (H 20) TOT with hσ1
  have hn20 : ∀ r, r ≠ H 20 → σ1.val r = σ.val r := fun r h => by rw [hσ1]; simp [Function.update_of_ne h]
  obtain ⟨τ2, c2, e2, c2le, t20, t21, t22, tsh, tk, tst, tsho, tcl⟩ := cmp_loop cap x j TOT 0 σ1
    (by rw [hσ1]; simp) (by rw [hn20 _ H20_ne_21.symm]; exact z21) (by rw [hn20 _ H20_ne_22.symm]; exact z22)
    (by rw [hσ1]; simpa using hsh) (by rw [hσ1]; simpa using hst) (by omega) (by omega)
  have e3 := wrewind_spec cap (sk x 2) (H 21) (min j (0 + TOT)) τ2 t21 (by rw [t21]; omega)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Nat.min_le_right j (0 + TOT); omega
  · simp [Function.update_apply, H21_ne_22.symm, t22]
  · intro r hr
    simp only [WState.seth_val, WState.setv_val]
    by_cases h21 : r = H 21
    · subst h21; simp [z21]
    · rw [Function.update_of_ne h21]
      by_cases h20 : r = H 20
      · subst h20; rw [t20, z20]
      · rw [tk r h20 h21 hr, hn20 r h20]
  · simp [tst, hσ1]
  · funext s
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases h2 : s = sk x 2
    · subst h2; simp [tsh, hsh]
    · rw [Function.update_of_ne h2, tsho s h2]; rfl
  · simp [tcl, hσ1]

/-- **The unit's index split** at `j < TOT` (SymDec's `idxW` at `M = 0`, `nSt = Σp`, `nFlat = |𝒢|`). -/
theorem tIdx_run (σ : WState (LNS x) LNR) (j TOT EU N2 pS nG nc : ℕ)
    (hst : σ.st (sk x 2) = List.replicate j true) (hsh : σ.sh (sk x 2) = 0) (g56 : σ.val (G 56) = TOT)
    (g55 : σ.val (G 55) = EU) (g32 : σ.val (G 32) = 0) (g53 : σ.val (G 53) = N2) (g52 : σ.val (G 52) = pS)
    (g41 : σ.val (G 41) = nG) (vNC : σ.val dNC = nc) (zH : ∀ k, σ.val (H k) = 0) (hEU : 2 ≤ EU)
    (hN2 : 1 ≤ N2) (hpS : 1 ≤ pS) (hnG : 1 ≤ nG) (hj : j < TOT)
    (hc : 2 * TOT + EU + N2 + pS + nG + nc + 20 ≤ cap) :
    ∃ τ, WExec cap (idxW x) σ τ (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap) ∧
      HVals x τ j TOT EU 0 N2 pS nG nc ∧ (∀ r, (∀ k, H k ≠ r) → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  obtain ⟨τ3, e3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, az, k3, st3, sh3a, sh3, cl3⟩ :=
    idxA_spec x cap σ j TOT EU 0 hst hsh g56 g55 g32 zH hEU (by omega)
  simp only [Nat.zero_add] at a0 a2 a3 a4 a6 a7 a9
  have hw : j % EU < EU := Nat.mod_lt _ (by omega)
  have hv3 : (j % EU - 1) % (0 + 3) < 3 := Nat.mod_lt _ (by omega)
  have hr3 : (j % EU - 1) / (0 + 3) ≤ j % EU - 1 := Nat.div_le_self _ _
  have he : j / EU ≤ j := Nat.div_le_self _ _
  obtain ⟨τ4, e4, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, kLow, bz, k4, st4, sh4, cl4⟩ :=
    idxB_spec x cap τ3 (j / EU) ((j % EU - 1) % (0 + 3)) ((j % EU - 1) / (0 + 3)) 0 N2 pS nG nc a4 a7 a8 a9
      (by rw [k3 _ (fun k => HG 53 k)]; exact g53) (by rw [k3 _ (fun k => HG 52 k)]; exact g52)
      (by rw [k3 _ (fun k => HG 41 k)]; exact g41) (by rw [k3 _ (fun k => (ndNC_H k).symm)]; exact vNC) az
      hN2 hpS hnG (by omega)
  have kτ : ∀ r : Fin LNR, (∀ k, H k ≠ r) → τ4.val r = σ.val r := fun r h => by rw [k4 r h, k3 r h]
  refine ⟨τ4, WExec.seq e3 e4,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, bz⟩, kτ, ?_, ?_, ?_⟩
  · rw [kLow 0 (by decide)]; exact a0
  · rw [kLow 1 (by decide)]; exact a1
  · rw [kLow 2 (by decide)]; exact a2
  · rw [kLow 3 (by decide)]; exact a3
  · rw [kLow 4 (by decide)]; exact a4
  · rw [kLow 5 (by decide)]; exact a5
  · rw [kLow 6 (by decide)]; exact a6
  · rw [kLow 7 (by decide)]; exact a7
  · rw [kLow 8 (by decide)]; exact a8
  · rw [kLow 9 (by decide)]; exact a9
  · rw [st4, st3]
  · funext s
    rw [sh4]
    by_cases h2 : s = sk x 2
    · subst h2; rw [sh3a, hsh]
    · rw [sh3 s h2]
  · rw [cl4, cl3]

end D

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
