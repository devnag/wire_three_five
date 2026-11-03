import Proof.Wire_3_5.FinalPass.S5TChCBase

/-! # S5-THR, part 26: the prelude with the top power erased (P3:3170-3181)

The scrub charges its stage at most `R - 1 = W - 1` steps, so the stage cannot erase the top power `sent W` (about
`W` steps). The prelude erases it instead, before the scrub, without a register: to its end, then backwards,
overwriting ones by zeros until the leading zero (`eraseB`, the head back at `0`).

* `eraseBLoop_spec`, `eraseB` / **`eraseB_spec`**;
* `preW3 = preW2 ; eraseB (xs D)` / **`preW3_spec`**, `preSt3`; `preSub3`, `τOut3`, `preSub3_spec`;
* `preM3`, `σ03`, **`pre_step3`** (`pre_step2` with the top power blank: `W + 1` zeros).

Paper quantity of the main type: the front's register capacity `2W + 2`, `W = (|fpIn| + 1 + c0)^{D+1}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj sTape_ne_c sTape_ne_r cTape_ne_r wslot
  wslot_s wslot_c wenc_A_c wenc_H_c)

section Words
variable {ns nr : ℕ} (cap : ℕ)

/-- The backward erase loop. -/
def eraseBLoop (X : Fin (ns + 1)) : WM ns nr := .whs X (.seq (.wr X false) (.bwd X))

theorem eraseBLoop_spec (X : Fin (ns + 1)) : ∀ (p q : ℕ) (σ : WState ns nr),
    σ.st X = (false :: List.replicate p true) ++ List.replicate q false → σ.sh X = p →
      WExec cap (eraseBLoop X) σ ((σ.sets X (List.replicate (p + 1 + q) false)).seth X 0) (5 * p + 1)
  | 0, q, σ, hs, hh => by
    have hb : wbit σ X = false := by unfold wbit; rw [hs, hh]; rfl
    have e : (σ.sets X (List.replicate (0 + 1 + q) false)).seth X 0 = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp [hh]
        · simp [Function.update_apply, hi]
      · funext i; by_cases hi : i = X
        · subst hi
          simp only [WState.seth_st, WState.sets_st, Function.update_self]
          rw [hs, List.replicate_zero, List.cons_append, List.nil_append, show 0 + 1 + q = q + 1 by omega,
            List.replicate_succ]
        · simp [Function.update_apply, hi]
      · rfl
      · rfl
    rw [e]; exact WExec.whsF hb
  | p + 1, q, σ, hs, hh => by
    have hb : wbit σ X = true := by
      unfold wbit; rw [hs, hh]
      simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_replicate]
    have e1 := WExec.wr (cap := cap) X false σ
    have hw : writeTapeBit (σ.st X) (σ.sh X) false = (false :: List.replicate p true) ++ List.replicate (q + 1) false := by
      have hm := writeTapeBit_mid (false :: List.replicate p true) (List.replicate q false) true false
      simp only [List.length_cons, List.length_replicate] at hm
      rw [hs, hh, show (false :: List.replicate (p + 1) true) ++ List.replicate q false =
        (false :: List.replicate p true) ++ true :: List.replicate q false by
          rw [List.replicate_succ']; simp only [List.cons_append, List.append_assoc, List.singleton_append,
            List.nil_append]]
      rw [hm, List.replicate_succ]
    rw [hw] at e1
    have e2 := WExec.bwd (cap := cap) X (σ.sets X ((false :: List.replicate p true) ++ List.replicate (q + 1) false))
    have ih := eraseBLoop_spec X p (q + 1) ((σ.sets X ((false :: List.replicate p true) ++
      List.replicate (q + 1) false)).seth X ((σ.sets X ((false :: List.replicate p true) ++
      List.replicate (q + 1) false)).sh X - 1)) (by simp) (by simp [hh])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ (by omega)
    rw [show p + 1 + (q + 1) = p + 1 + 1 + q by omega]
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · rfl
    · rfl

/-- **Erase a sentinel word backwards**, register-free: to its end, then zeros back to the leading zero. -/
def eraseB (X : Fin (ns + 1)) : WM ns nr := .seq (fwdEnd X) (.seq (.bwd X) (eraseBLoop X))

theorem eraseB_spec (X : Fin (ns + 1)) (W : ℕ) (σ : WState ns nr) (hs : σ.st X = sent W) (hh : σ.sh X = 0) :
    WExec cap (eraseB X) σ (σ.sets X (List.replicate (W + 1) false)) (3 * W + 3 + 1 + (1 + 1 + (5 * W + 1))) := by
  have e1 := fwdEnd_spec cap X W σ hs hh
  have e2 := WExec.bwd (cap := cap) X (σ.seth X (W + 1))
  have e3 := eraseBLoop_spec cap X W 0 ((σ.seth X (W + 1)).seth X ((σ.seth X (W + 1)).sh X - 1))
    (by simp [hs, sent]) (by simp)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  apply WState.eq
  · funext i; by_cases hi : i = X
    · subst hi; simp [hh]
    · simp [Function.update_apply, hi]
  · funext i; by_cases hi : i = X
    · subst hi; simp
    · simp [Function.update_apply, hi]
  · rfl
  · rfl

/-- The padded count program, then the top power erased. -/
def preW3 (I T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (D c0 : ℕ) : WM ns nr :=
  .seq (preW2 I T P C xs D c0) (eraseB (xs D))

/-- Its exit state. -/
def preSt3 (σ : WState ns nr) (T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (b c0 D : ℕ) : WState ns nr :=
  (preSt2 σ T P C xs b c0 D).sets (xs D) (List.replicate ((b + c0) ^ (D + 1) + 1) false)

/-- Its cost. -/
def preCost3 (b c0 D : ℕ) : ℕ :=
  preCost2 b c0 D + 1 + (3 * (b + c0) ^ (D + 1) + 3 + 1 + (1 + 1 + (5 * (b + c0) ^ (D + 1) + 1)))

theorem preSt2_xsD (σ : WState ns nr) (T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (b c0 D : ℕ)
    (hxs : ∀ i j, i ≤ D → j ≤ D → xs i = xs j → i = j) (hCx : ∀ j, j ≤ D → xs j ≠ C) :
    (preSt2 σ T P C xs b c0 D).st (xs D) = sent ((b + c0) ^ (D + 1)) := by
  unfold preSt2
  simp only [WState.sets_st]
  rw [Function.update_of_ne (hCx D le_rfl)]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp [chainSt]
  · exact chainSt_st_self xs D hxs _ (b + c0) D D le_rfl hD le_rfl

theorem preW3_spec (I T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (D c0 : ℕ)
    (hxs : ∀ i j, i ≤ D → j ≤ D → xs i = xs j → i = j)
    (hIT : I ≠ T) (hTP : T ≠ P) (hPC : P ≠ C) (hTC : T ≠ C) (hPx : ∀ j, j ≤ D → xs j ≠ P)
    (hTx : ∀ j, j ≤ D → xs j ≠ T) (hCx : ∀ j, j ≤ D → xs j ≠ C)
    (u : List Bool) (σ : WState ns nr) (hI : σ.st I = frame u) (hIh : σ.sh I = 0) (hT : σ.st T = [])
    (hTh : σ.sh T = 0) (hP : σ.st P = []) (hPh : σ.sh P = 0) (hC : σ.st C = []) (hCh : σ.sh C = 0)
    (hx : ∀ j, j ≤ D → σ.st (xs j) = []) (hxh : ∀ j, j ≤ D → σ.sh (xs j) = 0) :
    WExec cap (preW3 I T P C xs D c0) σ (preSt3 σ T P C xs (u.length + 1) c0 D) (preCost3 (u.length + 1) c0 D) := by
  have e1 := preW2_spec cap I T P C xs D c0 hxs hIT hTP hPC hTC hPx hTx hCx u σ hI hIh hT hTh hP hPh hC hCh hx hxh
  have e2 := eraseB_spec cap (xs D) ((u.length + 1 + c0) ^ (D + 1)) (preSt2 σ T P C xs (u.length + 1) c0 D)
    (preSt2_xsD σ T P C xs (u.length + 1) c0 D hxs hCx)
    (by unfold preSt2; simp [chainSt_sh]; exact hxh D le_rfl)
  exact WExec.cast cap (WExec.seq e1 e2) rfl le_rfl

end Words

/-- The padded count program with the top power erased, on its own layout. -/
def preSub3 (D c0 : ℕ) : WM (D + 4) 0 := preW3 (sI2 D) (sT2 D) (sP2 D) (sC2 D) (sxs2 D) D c0

/-- Its exit state. -/
def τOut3 (D c0 : ℕ) (u : List Bool) : WState (D + 4) 0 :=
  preSt3 (σIn2 D u) (sT2 D) (sP2 D) (sC2 D) (sxs2 D) (u.length + 1) c0 D

theorem preSub3_spec (D c0 : ℕ) (u : List Bool) :
    WExec 0 (preSub3 D c0) (σIn2 D u) (τOut3 D c0 u) (preCost3 (u.length + 1) c0 D) := by
  have hv : ∀ j, j ≤ D → (sxs2 D j).val = 4 + j := fun j hj => sxs2_val D j hj
  have ne : ∀ {a b : Fin (D + 5)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  refine preW3_spec 0 (sI2 D) (sT2 D) (sP2 D) (sC2 D) (sxs2 D) D c0
    (fun i j hi hj e => by have := congrArg Fin.val e; rw [hv i hi, hv j hj] at this; omega)
    (ne (by simp [sI2, sT2])) (ne (by simp [sT2, sP2])) (ne (by simp [sP2, sC2])) (ne (by simp [sT2, sC2]))
    (fun j hj => ne (by rw [hv j hj]; simp [sP2]; omega)) (fun j hj => ne (by rw [hv j hj]; simp [sT2]; omega))
    (fun j hj => ne (by rw [hv j hj]; simp [sC2]; omega)) u (σIn2 D u)
    (by show (if sI2 D = sI2 D then frame u else []) = frame u; rw [if_pos rfl]) rfl
    (by show (if sT2 D = sI2 D then frame u else []) = []; rw [if_neg (ne (by simp [sI2, sT2]))]) rfl
    (by show (if sP2 D = sI2 D then frame u else []) = []; rw [if_neg (ne (by simp [sI2, sP2]))]) rfl
    (by show (if sC2 D = sI2 D then frame u else []) = []; rw [if_neg (ne (by simp [sI2, sC2]))]) rfl
    (fun j hj => by
      show (if sxs2 D j = sI2 D then frame u else []) = []
      rw [if_neg (ne (by rw [hv j hj]; simp [sI2]))]) (fun _ _ => rfl)

theorem τOut3_sh (D c0 : ℕ) (u : List Bool) : (τOut3 D c0 u).sh = fun _ => 0 := by
  unfold τOut3 preSt3 preSt2; simp [chainSt_sh]; rfl

theorem τOut3_cell (D c0 : ℕ) (u : List Bool) : (τOut3 D c0 u).cell = false := by
  unfold τOut3 preSt3 preSt2; simp [chainSt_cell]; rfl

theorem τOut3_C (D c0 : ℕ) (u : List Bool) :
    (τOut3 D c0 u).st (sC2 D) = List.replicate ((u.length + 1 + c0) ^ (D + 1)) true := by
  have hne : sxs2 D D ≠ sC2 D := fun e => by
    have h := congrArg Fin.val e; rw [sxs2_val D D le_rfl] at h; simp only [sC2] at h; omega
  unfold τOut3 preSt3 preSt2; simp [Function.update_apply, hne.symm]

variable {ns nr : ℕ}

/-- **The prelude's machine**, the top power erased. -/
noncomputable def preM3 (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (c0 : ℕ) :=
  Composition.machine (Composition.machine (cellP2 (ns := ns) (nr := nr)).compile
    (RecoveryFocus.machine (preSlots2 (nr := nr) D fs) (preSub3 D c0).toProg.compile))
    (UnionMachine.FrontFill.fillP Scrub.driverTape Scrub.logTape regSel2).compile

/-- The prelude's exit state. -/
noncomputable def σ03 (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (c0 : ℕ) (u : List Bool) : WState ns nr :=
  ⟨fun _ => 0, install fs (fun _ => []) (fun k => if k = sC2 D then [] else (τOut3 D c0 u).st k), fun _ => 0, false⟩

/-- The prelude's cost. -/
def preTotal3 (b c0 D : ℕ) : ℕ := 1 + 1 + preCost3 b c0 D + 1 + (11 * (b + c0) ^ (D + 1) + 20)

/-- **The prelude**: from the entry bank to the scrub's source bank at `R = W`, `L = 2W + 3`. -/
theorem pre_step3 (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (hfs : Function.Injective fs) (h0 : fs (sI2 D) = 0)
    (c0 : ℕ) (u : List Bool) :
    Step (preM3 (nr := nr) D fs c0) (preTotal3 (u.length + 1) c0 D) (fun _ => 0) (A02 u) (fun _ => 0)
      (Scrub.bank (wenc (2 * (u.length + 1 + c0) ^ (D + 1) + 2) (σ03 D fs c0 u)).A ((u.length + 1 + c0) ^ (D + 1))
        (2 * (u.length + 1 + c0) ^ (D + 1) + 3)) := by
  have hsl := preSlots2_inj (nr := nr) D fs hfs
  have hne : ∀ {a b : Fin (D + 5)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  have hIC : sI2 D ≠ sC2 D := hne (by simp [sI2, sC2])
  have hfs0 : ∀ k, (sTape (nr := nr) (fs k)).val = 0 ↔ k = sI2 D := by
    intro k
    rw [PrimAsm.DockW.sTape_val]
    constructor
    · intro h
      split at h
      · exact hfs (by rw [h0]; exact Fin.ext (by assumption))
      · omega
    · intro h; subst h; rw [h0]; rfl
  have hC0 : (Scrub.inner (sTape (nr := nr) (fs (sC2 D)))).val ≠ 0 := by
    rw [Scrub.inner_val]; exact fun h => hIC ((hfs0 _).1 h).symm
  -- 1: the cell
  have s1 := Exec.step (Exec.act (⟨fun _ => 0, A02 u⟩ : Bank (ns + 2 + nr + 1 + 1)) (writeAt (Scrub.inner cTape) false)
    (fun _ => .stay))
  obtain ⟨A1, hA1⟩ : ∃ A : Fin (ns + 2 + nr + 1 + 1) → List Bool,
      A = Function.update (A02 u) (Scrub.inner cTape) [false] := ⟨_, rfl⟩
  have hA0c : A02 (ns := ns) (nr := nr) u (Scrub.inner cTape) = [] := by
    simp only [A02]; rw [if_neg (by rw [Scrub.inner_val, PrimAsm.DockW.cTape_val]; omega)]
  have e1 : (⟨fun _ => 0, A02 u⟩ : Bank (ns + 2 + nr + 1 + 1)).act (writeAt (Scrub.inner cTape) false)
      (fun _ => .stay) = ⟨fun _ => 0, A1⟩ := by
    apply Bank.ext'
    · intro j; simp [Bank.act, HeadMove.apply]
    · intro j
      rw [hA1]
      simp only [Bank.act, writeAt]
      by_cases h : j = Scrub.inner cTape
      · subst h; rw [if_pos rfl, Function.update_self, hA0c]; rfl
      · rw [if_neg h, Function.update_of_ne h]
  rw [e1] at s1
  -- 2: the padded count program, docked
  have s2 := (Exec.step (WExec.exec 0 (preSub3_spec D c0 u))).dock (preSlots2 (nr := nr) D fs) hsl (fun _ => 0) A1
    (fun j => by rw [wenc0_H2 D _ (fun _ => rfl)])
    (fun j => by
      rcases tape_cases j with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        by_cases hk : k = sC2 D
        · subst hk
          rw [preSlots2_C, hA1, Function.update_of_ne (Ne.symm (Scrub.inner_ne_driver _))]
          simp only [A02, σIn2]
          rw [if_neg (by rw [Scrub.driver_val]; omega), if_neg (Ne.symm hIC)]
        · rw [preSlots2_s D fs k hk, hA1, Function.update_of_ne (fun h => sTape_ne_c _ (inner_inj h))]
          simp only [A02, σIn2]
          rw [Scrub.inner_val]
          by_cases hi : k = sI2 D
          · rw [if_pos ((hfs0 k).2 hi), if_pos hi]
          · rw [if_neg (fun h => hi ((hfs0 k).1 h)), if_neg hi]
      · rw [preSlots2_c, wenc_A_c, hA1, Function.update_self]; rfl
      · exact r.elim0)
  rw [wenc0_H2 D _ (fun i => by rw [τOut3_sh])] at s2
  have hdz : dockH (preSlots2 (nr := nr) D fs) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, preSlots2 (nr := nr) D fs j = i
    · obtain ⟨j, rfl⟩ := hi; rw [dockH_slot _ hsl]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  rw [hdz] at s2
  obtain ⟨A2, hA2⟩ : ∃ A, A = install (preSlots2 (nr := nr) D fs) A1 (wenc 0 (τOut3 D c0 u)).A := ⟨_, rfl⟩
  rw [← hA2] at s2
  have hA2s : ∀ k, k ≠ sC2 D → A2 (Scrub.inner (sTape (fs k))) = (τOut3 D c0 u).st k := fun k hk => by
    rw [hA2, ← preSlots2_s D fs k hk, install_slot _ hsl, wenc_A_s]
  have hA2d : A2 Scrub.driverTape = List.replicate ((u.length + 1 + c0) ^ (D + 1)) true := by
    rw [hA2, ← preSlots2_C (nr := nr) D fs, install_slot _ hsl, wenc_A_s, τOut3_C]
  have hA2c : A2 (Scrub.inner cTape) = [false] := by
    rw [hA2, ← preSlots2_c (nr := nr) D fs, install_slot _ hsl, wenc_A_c, τOut3_cell]
  have notin : ∀ i, (∀ j, preSlots2 (nr := nr) D fs j ≠ i) → A2 i = A1 i := fun i hi => by
    rw [hA2, install_other _ _ _ _ hi]
  have hA2o : ∀ i : Fin (ns + 1), (∀ k, k ≠ sC2 D → fs k ≠ i) → A2 (Scrub.inner (sTape i)) = [] := by
    intro i hi
    have hi0 : (Scrub.inner (sTape (nr := nr) i)).val ≠ 0 := by
      rw [Scrub.inner_val, PrimAsm.DockW.sTape_val]
      split
      · exact absurd (by rw [h0]; exact (Fin.ext (by assumption)).symm) (hi (sI2 D) hIC)
      · omega
    rw [notin _ (fun j h => by
      rcases tape_cases j with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
      · by_cases hk : k = sC2 D
        · subst hk; rw [preSlots2_C] at h; exact Scrub.inner_ne_driver _ h.symm
        · rw [preSlots2_s D fs k hk] at h; exact hi k hk (sTape_inj (inner_inj h))
      · rw [preSlots2_c] at h; exact sTape_ne_c i (inner_inj h).symm
      · exact r.elim0), hA1, Function.update_of_ne (fun h => sTape_ne_c i (inner_inj h)), A02, if_neg hi0]
  have hA2r : ∀ r, A2 (Scrub.inner (rTape r)) = [] := fun r => by
    rw [notin _ (fun j h => by
      rcases tape_cases j with ⟨k, rfl⟩ | rfl | ⟨q, rfl⟩
      · by_cases hk : k = sC2 D
        · subst hk; rw [preSlots2_C] at h; exact Scrub.inner_ne_driver _ h.symm
        · rw [preSlots2_s D fs k hk] at h; exact sTape_ne_r _ r (inner_inj h)
      · rw [preSlots2_c] at h; exact cTape_ne_r r (inner_inj h)
      · exact q.elim0), hA1, Function.update_of_ne (fun h => cTape_ne_r r (inner_inj h).symm), A02,
      if_neg (by rw [Scrub.inner_val]; simp [rTape])]
  have hA2l : A2 Scrub.logTape = [] := by
    rw [notin _ (fun j h => by
      rcases tape_cases j with ⟨k, rfl⟩ | rfl | ⟨q, rfl⟩
      · by_cases hk : k = sC2 D
        · subst hk; rw [preSlots2_C] at h; exact Scrub.driver_ne_log h
        · rw [preSlots2_s D fs k hk] at h; exact Scrub.inner_ne_log _ h
      · rw [preSlots2_c] at h; exact Scrub.inner_ne_log _ h
      · exact q.elim0), hA1, Function.update_of_ne (Ne.symm (Scrub.inner_ne_log _)), A02,
      if_neg (by rw [Scrub.log_val]; omega)]
  -- 3: the fill from the driver
  have s3 := Exec.step (UnionMachine.FrontFill.fillP_exec Scrub.driverTape Scrub.logTape regSel2 (fun _ => 0) A2
    Scrub.driver_ne_log regSel2_drv regSel2_log ((u.length + 1 + c0) ^ (D + 1)) hA2d (fun _ _ => rfl)
    (fun i hi => by
      rcases hi with hi | hi
      · revert hi
        refine Scrub.cover (motive := fun i => regSel2 i = true → A2 i = []) (fun i => ?_) (fun h => ?_)
          (fun h => ?_) i
        · rcases tape_cases i with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
          · intro h; rw [regSel2_s] at h; exact absurd h (by decide)
          · intro h; rw [regSel2_c] at h; exact absurd h (by decide)
          · intro _; exact hA2r r
        · rw [regSel2_log] at h; exact absurd h (by decide)
        · rw [regSel2_drv] at h; exact absurd h (by decide)
      · subst hi; exact hA2l))
  refine (Step.seq (Step.seq s1 s2) s3).congr ?_ ?_
  · funext j
    simp only [UnionMachine.FrontFill.stB]
    split_ifs <;> omega
  · funext j
    simp only [UnionMachine.FrontFill.stB]
    refine Scrub.cover (motive := fun j => (if regSel2 j = true then _ else if j = Scrub.logTape then _ else A2 j) =
      Scrub.bank _ _ _ j) (fun i => ?_) ?_ ?_ j
    · rw [Scrub.bank_inner]
      rcases tape_cases i with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSel2_s, if_neg (by decide), if_neg (Scrub.inner_ne_log _), wenc_A_s]
        by_cases hk : ∃ m, fs m = k
        · obtain ⟨m, rfl⟩ := hk
          simp only [σ03]
          rw [install_slot _ hfs]
          by_cases hm : m = sC2 D
          · subst hm
            rw [if_pos rfl, hA2o _ (fun k hk e => hk (hfs e))]
          · rw [if_neg hm, hA2s m hm]
        · simp only [σ03]
          rw [install_other _ _ _ _ (fun m h => hk ⟨m, h⟩), hA2o _ (fun m _ h => hk ⟨m, h⟩)]
      · rw [regSel2_c, if_neg (by decide), if_neg (Scrub.inner_ne_log _), wenc_A_c, hA2c]; rfl
      · rw [regSel2_r, if_pos rfl, wenc_A_r, show (σ03 (nr := nr) D fs c0 u).val r = 0 from rfl, regTape_zero]
    · rw [regSel2_log, if_neg (by decide), if_pos rfl, Scrub.bank_log]; simp
    · rw [regSel2_drv, if_neg (by decide), if_neg Scrub.driver_ne_log, Scrub.bank_driver, hA2d]

end NearCubicWires.WireExponent3_5.FinalPass.S5T
