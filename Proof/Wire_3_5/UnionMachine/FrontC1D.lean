import Proof.Wire_3_5.UnionMachine.C1Stage
import Proof.Wire_3_5.UnionMachine.FrontCh5

/-! # C6 front, the chain: C1's call with its setup, docked (P3:1324-1362, 3673)

C1's stage (`C1Stage.stageM`: the carrier loop, the request's assembly, C1's call, the framing) needs its entry bank
`c1In`: the loop's bank (the table tapes at most `Hd` long, the register layout at capacity `cap` with the loop's
streams at variable `0`, the ruler `1^Hd`, the eraser's log `0^{Hd+1}`), C1's tapes blank, the framing's cell and
registers. **`c1LocM`** writes it locally from the shared PCPP output, `1^q`, the carriers' codes, `1^V`, a ruler `1^W`
and the count `1^W` (base's eraser for the log, FrontFill's fill for the `73` registers at `2W+2`, two cells), then runs
the stage. **`c1Loc_step`**; docked in the chain: **`c1_step`**.

Paper quantity of the main type: `star:selection`'s selected coset (P3:1357-1360), framed for the table writer. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontC1D
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Local
variable {d : ℕ} (c : Plan.C1At d)

/-- The local bank: the stage's bank, then the fill's count and marker. -/
abbrev NC : ℕ := C1Stage.NB (C1Stage.TC c) + 2

/-- The eraser's slots: the table's tapes, the ruler `1434`, the log `1435`. -/
def eSlL (x : Fin (1357 + 1 + 1)) : Fin (NC c) :=
  ⟨if x.val < 1357 then x.val else if x.val = 1357 then 1434 else 1435, by
    have := x.isLt; unfold NC C1Stage.NB; split_ifs <;> omega⟩

theorem eSlL_inj : Function.Injective (eSlL c) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [eSlL] at hv
  apply Fin.ext
  have := a.isLt; have := b.isLt
  split_ifs at hv <;> omega

def cntL : Fin (NC c) := ⟨C1Stage.NB (C1Stage.TC c), by unfold NC; omega⟩
def auxL : Fin (NC c) := ⟨C1Stage.NB (C1Stage.TC c) + 1, by unfold NC; omega⟩
/-- The fill's targets: the register layout's `64` registers and the framing's `9`. -/
def tgtL (y : Fin (NC c)) : Bool :=
  decide (1369 ≤ y.val ∧ y.val ≤ 1432) || decide (1436 + C1Stage.TC c + 2 ≤ y.val ∧ y.val ≤ 1436 + C1Stage.TC c + 10)
def cel1 : Fin (NC c) := ⟨1358, by unfold NC C1Stage.NB; omega⟩
def cel2 : Fin (NC c) := ⟨1436 + C1Stage.TC c, by unfold NC C1Stage.NB; omega⟩
/-- The stage's slots: the first `NB` tapes. -/
def stL (y : Fin (C1Stage.NB (C1Stage.TC c))) : Fin (NC c) := ⟨y.val, by unfold NC; omega⟩

theorem stL_inj : Function.Injective (stL c) := fun a b h => Fin.ext (by simpa [stL] using congrArg Fin.val h)

/-- **C1's call with its setup**: the eraser (the log), the fill (the registers), the two cells, the stage. -/
noncomputable def c1LocM (cr : ℕ) :=
  Composition.machine (RecoveryFocus.machine (eSlL c) (RecoveryScratchErase.resetMachine 1357))
  (Composition.machine (FrontFill.fillP (cntL c) (auxL c) (tgtL c)).compile
  (Composition.machine (FrontKit.cellP (cel1 c)).compile
  (Composition.machine (FrontKit.cellP (cel2 c)).compile
    (RecoveryFocus.machine (stL c) (C1Stage.stageM c cr)))))

/-- The local entry: the PCPP output, `1^q`, the carriers' codes, `1^V`, the ruler `1^W` and the count `1^W`. -/
def c1Tin (po src : List Bool) (q V W : ℕ) : Fin (NC c) → List Bool := fun y =>
  if y.val = 1360 then po else if y.val = 1365 then List.replicate q true else if y.val = 1366 then src
  else if y.val = 1368 then List.replicate V true else if y.val = 1434 then List.replicate W true
  else if y.val = C1Stage.NB (C1Stage.TC c) then List.replicate W true else []

theorem c1Tin_nil (po src : List Bool) (q V W : ℕ) (y : Fin (NC c)) (h1 : y.val ≠ 1360) (h2 : y.val ≠ 1365)
    (h3 : y.val ≠ 1366) (h4 : y.val ≠ 1368) (h5 : y.val ≠ 1434) (h6 : y.val ≠ C1Stage.NB (C1Stage.TC c)) :
    c1Tin c po src q V W y = [] := by
  unfold c1Tin; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

/-- The eraser's output. -/
def eOut (W : ℕ) : Fin (1357 + 1 + 1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin 1357 => List.replicate W false) (fun _ : Fin 1 => List.replicate W true))
    (fun _ : Fin 1 => List.replicate (max 0 (W + 1)) false)

theorem eOut_val (W : ℕ) (x : Fin (1357 + 1 + 1)) :
    eOut W x = if x.val < 1357 then List.replicate W false else if x.val = 1357 then List.replicate W true
      else List.replicate (W + 1) false := by
  refine Fin.addCases (fun y => ?_) (fun o => ?_) x
  · refine Fin.addCases (fun i => ?_) (fun o => ?_) y
    · rw [eOut, Fin.addCases_left, Fin.addCases_left]; simp [i.isLt]
    · rw [eOut, Fin.addCases_left, Fin.addCases_right]; simp [Subsingleton.elim o 0]
  · rw [eOut, Fin.addCases_right]; simp [Subsingleton.elim o 0]

/-- The entry's eraser tapes: blank table tapes, the ruler, a blank log. -/
theorem erase_in (po src : List Bool) (q V W : ℕ) (x : Fin (1357 + 1 + 1)) :
    c1Tin c po src q V W (eSlL c x) =
      Fin.addCases (Fin.addCases (fun _ : Fin 1357 => ([] : List Bool)) (fun _ : Fin 1 => List.replicate W true))
        (fun _ : Fin 1 => List.replicate 0 false) x := by
  have hx : ∀ z : Fin (1357 + 1 + 1),
      Fin.addCases (Fin.addCases (fun _ : Fin 1357 => ([] : List Bool)) (fun _ : Fin 1 => List.replicate W true))
        (fun _ : Fin 1 => List.replicate 0 false) z = if z.val = 1357 then List.replicate W true else [] := by
    intro z
    refine Fin.addCases (fun y => ?_) (fun o => ?_) z
    · refine Fin.addCases (fun i => ?_) (fun o => ?_) y
      · rw [Fin.addCases_left, Fin.addCases_left]; simp; omega
      · rw [Fin.addCases_left, Fin.addCases_right]; simp [Subsingleton.elim o 0]
    · rw [Fin.addCases_right]; simp [Subsingleton.elim o 0]
  rw [hx]
  have := x.isLt
  have hN : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
  by_cases h0 : x.val < 1357
  · rw [if_neg (by omega)]
    apply c1Tin_nil <;> simp only [eSlL, h0, if_true] <;> omega
  · by_cases h1 : x.val = 1357
    · rw [if_pos h1]
      unfold c1Tin; simp [eSlL, h1]
    · rw [if_neg h1]
      apply c1Tin_nil <;> simp only [eSlL, h0, h1, if_false] <;> omega

/-- The bank after the eraser. -/
theorem a1_val (po src : List Bool) (q V W : ℕ) (y : Fin (NC c)) :
    install (eSlL c) (c1Tin c po src q V W) (eOut W) y =
      if y.val < 1357 then List.replicate W false else if y.val = 1435 then List.replicate (W + 1) false
        else c1Tin c po src q V W y := by
  by_cases hy : y.val < 1357 ∨ y.val = 1434 ∨ y.val = 1435
  · have e : y = eSlL c ⟨if y.val < 1357 then y.val else if y.val = 1434 then 1357 else 1358, by split_ifs <;> omega⟩ := by
      apply Fin.ext; simp only [eSlL]; split_ifs <;> omega
    rw [e, install_slot _ (eSlL_inj c), eOut_val]
    rcases hy with h | h | h
    · simp [eSlL, h]
    · have h' : ¬ y.val < 1357 := by omega
      simp only [eSlL, h', h, if_false, if_true]
      unfold c1Tin; simp
    · have h' : ¬ y.val < 1357 := by omega
      have h'' : y.val ≠ 1434 := by omega
      simp only [eSlL, h', h'', h, if_false, if_true]
      simp
  · rw [install_other _ _ _ _ (fun x e => hy (by
      rw [← e]; simp only [eSlL]; split_ifs <;> omega)), if_neg (by omega), if_neg (by omega)]

/-! ## The stage's entry, flat -/

theorem addCases_lo {α : Type} {m : ℕ} (f : Fin m → α) (g : Fin 1 → α) (i : ℕ) (h : i < m + 1) (hi : i < m) :
    Fin.addCases (m := m) (n := 1) (motive := fun _ => α) f g ⟨i, h⟩ = f ⟨i, hi⟩ := by
  rw [show (⟨i, h⟩ : Fin (m + 1)) = Fin.castAdd 1 ⟨i, hi⟩ from rfl, Fin.addCases_left]

theorem addCases_hi {α : Type} {m : ℕ} (f : Fin m → α) (g : Fin 1 → α) (i : ℕ) (h : i < m + 1) (hi : i = m) :
    Fin.addCases (m := m) (n := 1) (motive := fun _ => α) f g ⟨i, h⟩ = g 0 := by
  rw [show (⟨i, h⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) from Fin.ext (by simp [hi]), Fin.addCases_right]

section Entry
variable (T capC W : ℕ) (S : Fin 11 → List Bool)

/-- The stage's entry below the ruler: the loop bank's table and register layout. -/
theorem c1In_L (j : Fin (C1Stage.NB T)) (h : j.val < 1434) :
    C1Stage.c1In T capC (bank (fun _ => List.replicate W false) (rlR capC S 0) W) j =
      if h1 : j.val < 1357 then List.replicate W false else rlR capC S 0 ⟨j.val - 1357, by omega⟩ := by
  obtain ⟨v, hv⟩ := j
  simp only [C1Stage.c1In, Fin.val_mk] at h ⊢
  rw [dif_pos (show v < 1436 by omega)]
  simp only [bank, Fin.val_mk]
  by_cases hA : v < 1357
  · rw [dif_pos hA, dif_pos hA]
  · rw [dif_neg hA, dif_neg hA, dif_pos h]

theorem rlR_blank (jj : ℕ) (hj : jj < 77) (h : jj = 0 ∨ jj = 10 ∨ jj = 76) : rlR capC S 0 ⟨jj, hj⟩ = [] := by
  simp only [rlR, Fin.val_mk]
  rcases h with h | h | h
  · rw [if_pos (Or.inl h)]
  · rw [if_pos (Or.inr h)]
  · rw [if_neg (by omega), addCases_hi _ _ _ _ h]; rfl

theorem rlR_cell (jj : ℕ) (hj : jj < 77) (h : jj = 1) : rlR capC S 0 ⟨jj, hj⟩ = [false] := by
  subst h
  simp only [rlR, Fin.val_mk]
  rw [if_neg (by omega), addCases_lo _ _ _ _ (by omega), C1Stage.wenc_A_val]
  simp only [Fin.val_mk]; rfl

theorem rlR_st (jj : ℕ) (h1 : 2 ≤ jj) (h2 : jj ≤ 11) (h3 : jj ≠ 10) :
    rlR capC S 0 ⟨jj, by omega⟩ = S ⟨jj - 1, by omega⟩ := by
  simp only [rlR, Fin.val_mk]
  rw [if_neg (by omega), addCases_lo _ _ _ _ (by omega), C1Stage.wenc_A_val]
  simp only [Fin.val_mk]
  rw [if_neg (show ¬ (jj = 0) by omega), if_neg (show ¬ (jj = 1) by omega), dif_pos (show jj ≤ 10 + 1 by omega)]
  rfl

theorem rlR_reg (jj : ℕ) (h1 : 12 ≤ jj) (h2 : jj < 76) : rlR capC S 0 ⟨jj, by omega⟩ = regTape capC 0 := by
  simp only [rlR, Fin.val_mk]
  rw [if_neg (by omega), addCases_lo _ _ _ _ (by omega), C1Stage.wenc_A_val]
  simp only [Fin.val_mk]
  rw [if_neg (show ¬ (jj = 0) by omega), if_neg (show ¬ (jj = 1) by omega), dif_neg (show ¬ (jj ≤ 10 + 1) by omega)]
  rfl

/-- The stage's entry at and past the ruler. -/
theorem c1In_H (j : Fin (C1Stage.NB T)) (h : 1434 ≤ j.val) :
    C1Stage.c1In T capC (bank (fun _ => List.replicate W false) (rlR capC S 0) W) j =
      if j.val = 1434 then List.replicate W true else if j.val = 1435 then List.replicate (W + 1) false
      else if j.val < 1436 + T then [] else if j.val = 1436 + T then [false]
      else if j.val = 1436 + T + 1 ∨ j.val = 1436 + T + 11 then [] else regTape capC 0 := by
  obtain ⟨v, hv⟩ := j
  simp only [C1Stage.c1In, Fin.val_mk] at h ⊢
  by_cases hB : v < 1436
  · rw [dif_pos hB]
    simp only [bank, Fin.val_mk]
    rw [dif_neg (show ¬ v < 1357 by omega), dif_neg (show ¬ v < 1434 by omega)]
    by_cases hD : v = 1434
    · rw [if_pos hD, if_pos hD]
    · rw [if_neg hD, if_neg hD, if_pos (show v = 1435 by omega)]
  · rw [dif_neg hB, if_neg (show ¬ v = 1434 by omega), if_neg (show ¬ v = 1435 by omega)]
    by_cases hE : v < 1436 + T
    · rw [if_pos (show v ≤ 1436 + T by omega), if_neg (show ¬ v = 1436 + T by omega), if_pos hE]
    · rw [if_neg hE]
      by_cases hF : v = 1436 + T
      · rw [if_pos (show v ≤ 1436 + T by omega), if_pos hF, if_pos hF]
      · rw [if_neg (show ¬ v ≤ 1436 + T by omega), if_neg hF]

end Entry

/-! ## The setup's bank is the stage's entry -/

theorem side_iff (v : ℕ) (hv : v < C1Stage.NB (C1Stage.TC c)) :
    FrontFill.side (auxL c) (tgtL c) (stL c ⟨v, hv⟩) ↔
      ((1369 ≤ v ∧ v ≤ 1432) ∨ (1436 + C1Stage.TC c + 2 ≤ v ∧ v ≤ 1436 + C1Stage.TC c + 10)) := by
  have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
  simp only [FrontFill.side, tgtL, stL, auxL, Fin.ext_iff, Fin.val_mk, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- **The setup's bank** (eraser, fill, cells) on the stage's tapes is exactly the stage's entry `c1In` at the loop's
start (variable `0`), capacity `2W+2`, ruler `W`. -/
theorem setup_bank {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool) (W : ℕ)
    (j : Fin (C1Stage.NB (C1Stage.TC c))) :
    Function.update (Function.update (fun i => if FrontFill.side (auxL c) (tgtL c) i then
        List.replicate (2 * W + 3) false else install (eSlL c) (c1Tin c po src q V W) (eOut W) i) (cel1 c) [false])
        (cel2 c) [false] (stL c j) =
      C1Stage.c1In (C1Stage.TC c) (2 * W + 2)
        (bank (fun _ => List.replicate W false) (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src 0) 0) W) j := by
  obtain ⟨v, hv⟩ := j
  have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
  have hne : ∀ k, k < 1436 → k ≠ C1Stage.NB (C1Stage.TC c) := fun k hk => by rw [hNB]; omega
  have e1 : (stL c ⟨v, hv⟩ = cel2 c) ↔ v = 1436 + C1Stage.TC c := by simp [stL, cel2, Fin.ext_iff]
  have e2 : (stL c ⟨v, hv⟩ = cel1 c) ↔ v = 1358 := by simp [stL, cel1, Fin.ext_iff]
  have sv : (stL c ⟨v, hv⟩).val = v := rfl
  rw [Function.update_apply, Function.update_apply]
  by_cases hc2 : v = 1436 + C1Stage.TC c
  · rw [if_pos (e1.mpr hc2), c1In_H _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hc2]
  rw [if_neg (fun h => hc2 (e1.mp h))]
  by_cases hc1 : v = 1358
  · rw [if_pos (e2.mpr hc1), c1In_L _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    rw [dif_neg (by omega), rlR_cell _ _ _ _ (by omega)]
  rw [if_neg (fun h => hc1 (e2.mp h))]
  by_cases hsd : (1369 ≤ v ∧ v ≤ 1432) ∨ (1436 + C1Stage.TC c + 2 ≤ v ∧ v ≤ 1436 + C1Stage.TC c + 10)
  · rw [if_pos ((side_iff c v hv).mpr hsd)]
    rcases hsd with h | h
    · rw [c1In_L _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
      simp only [Fin.val_mk]
      rw [dif_neg (by omega), rlR_reg _ _ (v - 1357) (by omega) (by omega), regTape_zero]
    · rw [c1In_H _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        regTape_zero]
  rw [if_neg (fun h => hsd ((side_iff c v hv).mp h)), a1_val, sv]
  by_cases hA : v < 1357
  · rw [if_pos hA, c1In_L _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]; rw [dif_pos hA]
  rw [if_neg hA]
  by_cases hB : v < 1434
  · rw [if_neg (by omega), c1In_L _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    rw [dif_neg hA]
    by_cases hb : v = 1357 ∨ v = 1367 ∨ v = 1433
    · rw [rlR_blank _ _ _ _ (by omega)]
      apply c1Tin_nil <;> rw [sv] <;> omega
    · rw [rlR_st _ _ (v - 1357) (by omega) (by omega) (by omega)]
      have hr : 1359 ≤ v ∧ v ≤ 1368 := by omega
      obtain ⟨hr1, hr2⟩ := hr
      interval_cases v <;> first | omega | simp [c1Tin, stL, C1Gates.Sj, C1Gates.GF, C1Gates.PF, C1Gates.gtF,
        C1Gates.npF, RepairOrdinary.Streaming.marks, hne]
  · rw [c1In_H _ _ _ _ _ (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    by_cases h34 : v = 1434
    · rw [if_neg (by omega), if_pos h34]
      unfold c1Tin; rw [sv]; simp [h34]
    by_cases h35 : v = 1435
    · rw [if_pos h35, if_neg h34, if_pos h35]
    rw [if_neg h35, if_neg h34, if_neg h35]
    by_cases hE : v < 1436 + C1Stage.TC c
    · rw [if_pos hE]; apply c1Tin_nil <;> rw [sv] <;> omega
    · rw [if_neg hE, if_neg hc2, if_pos (by omega)]; apply c1Tin_nil <;> rw [sv] <;> omega

/-! ## The local run -/

/-- The setup's and the stage's fuel. -/
noncomputable def c1LocCost (W nS : ℕ) : ℕ :=
  (2 * W + 4) + 1 + ((11 * W + 20) + 1 + (1 + 1 + (1 + 1 + nS)))

/-- **C1's call with its setup, locally**: from the shared PCPP output, `1^q`, the carriers' codes, `1^V`, the ruler
`1^W` and the count `1^W`, the loop's run (`hloop`, e.g. `C1Gates.gates_loop` at capacity `2W+2` and ruler `W`), the
assembly, C1's call and the framing leave `frame (natListWord (selArgmin R))` on the framing's output; the PCPP output,
`1^q`, the carriers' codes and the count are kept. -/
theorem c1Loc_step {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool) (W cr nL : ℕ)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0)
        (bank (fun _ => List.replicate W false) (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src 0) 0) W) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src V) k) W)
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (C1Gates.GF Cs lits V)
      (C1Gates.PF Cs lits cb V) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ 2 * W + 2)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits V + C1Gates.npF lits V + 6 * (natBitLength q +
      natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits V) + natBitLength (C1Gates.npF lits V)) +
        (frame (Plan.selWord R)).length + 50 ≤ 2 * W + 2)
    (hcapC : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      2 * W + 2) :
    ∃ A' : Fin (NC c) → List Bool,
      Step (c1LocM c cr) (c1LocCost W (nL + 1 + ((2 * C1Asm.asmCost cr q (C1Gates.gtF Cs lits V) (C1Gates.npF lits V)
        (C1Gates.GF Cs lits V) (C1Gates.PF Cs lits cb V) + 2) + 1 + ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
          (2 * C1Stage.convCost (SelectionMachine.selArgmin R) + 2)))))
        (fun _ => 0) (c1Tin c po src q V W) (fun _ => 0) A' ∧
      A' (stL c (C1Stage.outT c)) = frame (natListWord (SelectionMachine.selArgmin R)) ∧
      A' (stL c (C1Stage.lb (C1Stage.TC c) ⟨1360, by omega⟩)) = po ∧
      A' (stL c (C1Stage.lb (C1Stage.TC c) ⟨1365, by omega⟩)) = List.replicate q true ∧
      A' (stL c (C1Stage.lb (C1Stage.TC c) ⟨1366, by omega⟩)) = src ∧
      A' (cntL c) = List.replicate W true := by
  have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
  -- 1. the eraser (the log `0^{W+1}`)
  have he := step_of_rready (RecoveryScratchErase.erase_ready (t := 1357) W 0 (fun _ => []) (by simp))
  have d1 := Step.dockAt he (eSlL c) (eSlL_inj c) (fun _ => 0) (c1Tin c po src q V W) (fun _ => rfl)
    (erase_in c po src q V W)
  rw [FrontFoldDock.zeroH] at d1
  have d1' : Step (RecoveryFocus.machine (eSlL c) (RecoveryScratchErase.resetMachine 1357)) (2 * W + 4) (fun _ => 0)
      (c1Tin c po src q V W) (fun _ => 0) (install (eSlL c) (c1Tin c po src q V W) (eOut W)) := d1
  set A1 := install (eSlL c) (c1Tin c po src q V W) (eOut W) with hA1
  have a1c : A1 (cntL c) = List.replicate W true := by
    rw [hA1, a1_val, if_neg (by simp [cntL]; omega), if_neg (by simp [cntL]; omega)]
    unfold c1Tin
    simp only [cntL, Fin.val_mk]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  -- 2. the fill (the registers at `2W+2`)
  have hf := step_of_ready (FrontKit.fill_ready (cntL c) (auxL c) (tgtL c) A1 W
    (fun e => by have := congrArg Fin.val e; simp [cntL, auxL] at this)
    (by simp [tgtL, cntL]; omega) (by simp [tgtL, auxL]; omega) a1c
    (fun i hi => by
      rw [hA1, a1_val]
      simp only [FrontFill.side, tgtL, auxL, Fin.ext_iff, Fin.val_mk, Bool.or_eq_true, decide_eq_true_eq] at hi
      rw [if_neg (by omega), if_neg (by omega)]
      apply c1Tin_nil <;> omega))
  set A2 := (fun i => if FrontFill.side (auxL c) (tgtL c) i then List.replicate (2 * W + 3) false else A1 i) with hA2
  -- 3, 4. the cells
  have hc1 := step_of_ready (FrontKit.cell_ready (cel1 c) A2 (by
    rw [hA2]
    simp only
    rw [if_neg (by
      simp only [FrontFill.side, tgtL, auxL, cel1, Fin.ext_iff, Fin.val_mk, Bool.or_eq_true, decide_eq_true_eq]
      omega), hA1, a1_val, if_neg (by simp [cel1]), if_neg (by simp [cel1])]
    apply c1Tin_nil <;> simp [cel1] <;> omega))
  set A3 := Function.update A2 (cel1 c) [false] with hA3
  have hc2 := step_of_ready (FrontKit.cell_ready (cel2 c) A3 (by
    rw [hA3, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [cel1, cel2] at this; omega), hA2]
    simp only
    rw [if_neg (by
      simp only [FrontFill.side, tgtL, auxL, cel2, Fin.ext_iff, Fin.val_mk, Bool.or_eq_true, decide_eq_true_eq]
      omega), hA1, a1_val, if_neg (by simp only [cel2, Fin.val_mk]; omega), if_neg (by simp only [cel2, Fin.val_mk]; omega)]
    apply c1Tin_nil <;> simp [cel2] <;> omega))
  set A4 := Function.update A3 (cel2 c) [false] with hA4
  -- 5. the stage
  obtain ⟨A', hS, o1, o2, o3, o4⟩ := C1Stage.c1Stage_step c Cs lits cb V po src (2 * W + 2) W cr (2 * W + 2) nL
    (bank (fun _ => List.replicate W false) (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src 0) 0) W) hloop R hpre hreq
    hcap1 hcap2 hcapC
  have d5 := Step.dockAt hS (stL c) (stL_inj c) (fun _ => 0) A4 (fun _ => rfl)
    (fun j => by rw [hA4, hA3, hA2, hA1]; exact setup_bank c Cs lits cb V po src W j)
  rw [FrontFoldDock.zeroH] at d5
  refine ⟨install (stL c) A4 A', Step.seq d1' (Step.seq hf (Step.seq hc1 (Step.seq hc2 d5))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot _ (stL_inj c)]; exact o1
  · rw [install_slot _ (stL_inj c)]; exact o2
  · rw [install_slot _ (stL_inj c)]; exact o4
  · rw [install_slot _ (stL_inj c)]; exact o3
  · rw [install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; have := j.isLt; simp [stL, cntL] at *; omega), hA4,
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [cntL, cel2] at this),
      hA3, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [cntL, cel1] at this; omega), hA2]
    simp only
    rw [if_neg (by
      simp only [FrontFill.side, tgtL, auxL, cntL, Fin.ext_iff, Fin.val_mk, Bool.or_eq_true, decide_eq_true_eq]
      omega)]
    exact a1c

end Local

/-! ## C1's call in the chain -/

section Phase
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3 NearCubicWires.WireExponent3_5.UnionMachine.FrontCh5
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  {d : ℕ} (c : Plan.C1At d)

/-- The phase's size: the ruler's copy, the variable count's copy, C1's call with its setup. -/
abbrev C1P : ℕ := 8 + NC c

variable (k0 : ℕ) (h : k0 + C1P c ≤ tf)

include h in
theorem hd1 : k0 + 4 ≤ tf := by unfold C1P at h; omega
include h in
theorem hd2 : (k0 + 4) + 4 ≤ tf := by unfold C1P at h; omega
include h in
theorem hd3 : (k0 + 8) + NC c ≤ tf := by unfold C1P at h; omega

variable (poT qT srcT cT nvT : Fin (NW P tf))

/-- The ruler `1^W` and the loop's count `1^V`, copied. -/
noncomputable def ruT : Fin (NW P tf) := sl P tf (sh1 P tf cT) k0 (hd1 tf c k0 h) (2 : Fin 4)
noncomputable def jsT : Fin (NW P tf) := sl P tf (sh1 P tf nvT) (k0 + 4) (hd2 tf c k0 h) (2 : Fin 4)

/-- C1's shared inputs. -/
noncomputable def c1L : List (ℕ × Fin (NW P tf)) :=
  [(1360, poT), (1365, qT), (1366, srcT), (1368, jsT P tf c k0 h nvT), (1434, ruT P tf c k0 h cT),
    (C1Stage.NB (C1Stage.TC c), cT)]

/-- **The phase's machine.** -/
noncomputable def c1M (cr : ℕ) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf cT) k0 (hd1 tf c k0 h)) ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf nvT) (k0 + 4) (hd2 tf c k0 h)) ClockUnarySum.machine)
    (RecoveryFocus.machine (sl P tf (insL P tf (c1L P tf c k0 h poT qT srcT cT nvT)) (k0 + 8) (hd3 tf c k0 h))
      (c1LocM c cr)))

/-- The framed coset's tape. -/
noncomputable def c1O : Fin (NW P tf) :=
  sl P tf (insL P tf (c1L P tf c k0 h poT qT srcT cT nvT)) (k0 + 8) (hd3 tf c k0 h) (stL c (C1Stage.outT c))

theorem ruT_val : (ruT P tf c k0 h cT).val = 2 + NL P + (k0 + 2) := by
  unfold ruT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf cT _ (by decide)), rg_val]; rfl
theorem jsT_val : (jsT P tf c k0 h nvT).val = 2 + NL P + (k0 + 4 + 2) := by
  unfold jsT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf nvT _ (by decide)), rg_val]; rfl

/-- The phase's fuel. -/
noncomputable def c1Cost (W V nS : ℕ) : ℕ := (2 * (W + 0) + 6) + 1 + ((2 * (V + 0) + 6) + 1 + c1LocCost W nS)

/-- **C1's call in the chain**: the framed coset `frame (natListWord (selArgmin R))` on `c1O`; the tapes below the phase
kept, the tapes past it blank. -/
theorem c1_step {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool) (W cr nL : ℕ)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0)
        (bank (fun _ => List.replicate W false) (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src 0) 0) W) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src V) k) W)
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (C1Gates.GF Cs lits V)
      (C1Gates.PF Cs lits cb V) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ 2 * W + 2)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits V + C1Gates.npF lits V + 6 * (natBitLength q +
      natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits V) + natBitLength (C1Gates.npF lits V)) +
        (frame (Plan.selWord R)).length + 50 ≤ 2 * W + 2)
    (hcapC : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      2 * W + 2)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hLo : ∀ y ∈ [poT, qT, srcT, cT, nvT], 2 + NL P ≤ y.val ∧ y.val < 2 + NL P + k0)
    (hpq : poT ≠ qT) (hps : poT ≠ srcT) (hpc : poT ≠ cT) (hqs : qT ≠ srcT) (hqc : qT ≠ cT) (hsc : srcT ≠ cT)
    (hpo : A poT = po ∧ H poT = 0) (hq : A qT = List.replicate q true ∧ H qT = 0) (hsr : A srcT = src ∧ H srcT = 0)
    (hW : A cT = List.replicate W true ∧ H cT = 0) (hV : A nvT = List.replicate V true ∧ H nvT = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (c1M P tf c k0 h poT qT srcT cT nvT cr) (c1Cost W V (nL + 1 + ((2 * C1Asm.asmCost cr q
        (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (C1Gates.GF Cs lits V) (C1Gates.PF Cs lits cb V) + 2) + 1 +
          ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
            (2 * C1Stage.convCost (SelectionMachine.selArgmin R) + 2))))) H A H A' ∧
      A' (c1O P tf c k0 h poT qT srcT cT nvT) = frame (natListWord (SelectionMachine.selArgmin R)) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧
      PristineH P tf H A' (k0 + C1P c) := by
  have lp := hLo poT (by simp)
  have lq := hLo qT (by simp)
  have ls := hLo srcT (by simp)
  have lc := hLo cT (by simp)
  have lv := hLo nvT (by simp)
  have vR := ruT_val P tf c k0 h cT
  have vJ := jsT_val P tf c k0 h nvT
  have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
  -- 1, 2. the copies
  obtain ⟨A1, s1, w1, l1, p1⟩ := cpStage P tf W k0 (hd1 tf c k0 h) cT lc H A hPr hW
  obtain ⟨A2, s2, w2, l2, p2⟩ := cpStage P tf V (k0 + 4) (hd2 tf c k0 h) nvT ⟨lv.1, by omega⟩ H A1 p1
    ⟨by rw [l1 nvT (by omega)]; exact hV.1, hV.2⟩
  have e2 : k0 + 4 + 4 = k0 + 8 := rfl
  rw [e2] at p2
  -- 3. C1's call with its setup
  obtain ⟨Al, hS, o1, o2, o3, o4, o5⟩ := c1Loc_step c Cs lits cb V po src W cr nL hloop R hpre hreq hcap1 hcap2 hcapC
  have mem : ∀ (i : Fin (NC c)) (a : Fin (NW P tf)), (i.val, a) ∈ c1L P tf c k0 h poT qT srcT cT nvT →
      (i.val = 1360 ∧ a = poT) ∨ (i.val = 1365 ∧ a = qT) ∨ (i.val = 1366 ∧ a = srcT) ∨
        (i.val = 1368 ∧ a = jsT P tf c k0 h nvT) ∨ (i.val = 1434 ∧ a = ruT P tf c k0 h cT) ∨
          (i.val = C1Stage.NB (C1Stage.TC c) ∧ a = cT) := by
    intro i a hm
    simpa only [c1L, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] using hm
  have nJ : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ jsT P tf c k0 h nvT := fun y hy e => by
    rw [e, vJ] at hy; omega
  have nR : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ ruT P tf c k0 h cT := fun y hy e => by
    rw [e, vR] at hy; omega
  have nJR : jsT P tf c k0 h nvT ≠ ruT P tf c k0 h cT := fun e => by
    have := congrArg Fin.val e; rw [vJ, vR] at this; omega
  obtain ⟨st, hsl, hlow, hpr⟩ := stepK P tf (c1LocM c cr) _ (c1Tin c po src q V W) Al hS
    (insL P tf (c1L P tf c k0 h poT qT srcT cT nvT)) (k0 + 8) (hd3 tf c k0 h)
    (insL_inj P tf _ (hd_of_nodup P tf _ (by
      simp only [c1L, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_or, not_false_eq_true]
      exact ⟨⟨hpq, hps, (nJ poT lp.2).symm.symm, nR poT lp.2, hpc⟩, ⟨hqs, nJ qT lq.2, nR qT lq.2, hqc⟩,
        ⟨nJ srcT ls.2, nR srcT ls.2, hsc⟩, ⟨nJR, (nJ cT lc.2).symm⟩, (nR cT lc.2).symm⟩)))
    (insL_low P tf _ _ (fun p hp => by
      simp only [c1L, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨lp.1, by dsimp only; omega⟩
      · exact ⟨lq.1, by dsimp only; omega⟩
      · exact ⟨ls.1, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨lc.1, by dsimp only; omega⟩))
    H A2 p2
    (fun i a hi => by
      rcases mem i a (insL_some P tf _ i a hi) with ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ <;>
        rw [ha]
      · refine ⟨?_, hpo.2⟩
        rw [l2 poT (by omega), l1 poT (by omega), hpo.1]; unfold c1Tin; rw [if_pos e]
      · refine ⟨?_, hq.2⟩
        rw [l2 qT (by omega), l1 qT (by omega), hq.1]; unfold c1Tin; rw [if_neg (by omega), if_pos e]
      · refine ⟨?_, hsr.2⟩
        rw [l2 srcT (by omega), l1 srcT (by omega), hsr.1]; unfold c1Tin
        rw [if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, (hPr.1 _ (by omega)).2⟩
        rw [show jsT P tf c k0 h nvT = sl P tf (sh1 P tf nvT) (k0 + 4) (hd2 tf c k0 h) 2 from rfl, w2]
        unfold c1Tin; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, (hPr.1 _ (by omega)).2⟩
        rw [l2 _ (by omega), show ruT P tf c k0 h cT = sl P tf (sh1 P tf cT) k0 (hd1 tf c k0 h) 2 from rfl, w1]
        unfold c1Tin
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, hW.2⟩
        rw [l2 cT (by omega), l1 cT (by omega), hW.1]; unfold c1Tin
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e])
    (fun i hi => by
      have hn := insL_none P tf _ i hi
      have h1 := hn (1360, poT) (by simp [c1L])
      have h2 := hn (1365, qT) (by simp [c1L])
      have h3 := hn (1366, srcT) (by simp [c1L])
      have h4 := hn (1368, jsT P tf c k0 h nvT) (by simp [c1L])
      have h5 := hn (1434, ruT P tf c k0 h cT) (by simp [c1L])
      have h6 := hn (C1Stage.NB (C1Stage.TC c), cT) (by simp [c1L])
      simp only at h1 h2 h3 h4 h5 h6
      exact c1Tin_nil c po src q V W i (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4) (Ne.symm h5) (Ne.symm h6))
  have e7 : k0 + 8 + NC c = k0 + C1P c := by unfold C1P; omega
  rw [e7] at hpr
  refine ⟨_, ?_, (hsl _).trans o1, fun y hy => ?_, hpr⟩
  · unfold c1M c1Cost
    exact Step.seq s1 (Step.seq s2 st)
  · rw [hlow y (by omega) (fun j hj => ?_), l2 y (by omega), l1 y (by omega)]
    rcases mem j y (insL_some P tf _ j y hj) with ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩
    · rw [show j = stL c (C1Stage.lb (C1Stage.TC c) ⟨1360, by omega⟩) from Fin.ext (by simp [stL, C1Stage.lb, e]), o2]
      unfold c1Tin; simp [stL, C1Stage.lb]
    · rw [show j = stL c (C1Stage.lb (C1Stage.TC c) ⟨1365, by omega⟩) from Fin.ext (by simp [stL, C1Stage.lb, e]), o3]
      unfold c1Tin; simp [stL, C1Stage.lb]
    · rw [show j = stL c (C1Stage.lb (C1Stage.TC c) ⟨1366, by omega⟩) from Fin.ext (by simp [stL, C1Stage.lb, e]), o4]
      unfold c1Tin; simp [stL, C1Stage.lb]
    · exact absurd ha (nJ _ hy)
    · exact absurd ha (nR _ hy)
    · rw [show j = cntL c from Fin.ext (by simp [cntL, e]), o5]
      unfold c1Tin; simp only [cntL, Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp

end Phase

end NearCubicWires.WireExponent3_5.UnionMachine.FrontC1D
