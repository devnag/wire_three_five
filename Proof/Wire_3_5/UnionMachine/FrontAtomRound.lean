import Proof.Wire_3_5.UnionMachine.FrontAtomLayout

/-! # C6 front, U1b: one round of the atom loop (P3:3670)

One round decodes one guessed atom: erase the decoder's private tapes to `replicate H false` (base
`RecoveryScratchErase`, ruler `1^H`), erase its raw tape to `replicate P false` (ruler: the decoder's driver `1^P`),
copy the entry's code onto the raw tape (`FrontAtomCopy.copyAtom_spec`), run the Theorem 2.5 repository's decoder padded
(`FrontAtomDecoder.dec_step`), and record the verdict (`FrontAtomTail.tail_spec`). The round's banks are explicit up to
the decoder's private scratch (`bankA`, `bankH`).

Main statements: the five stage steps `eraseH_step`, `eraseP_step`, `copy_step`, `dec_stepAt`, `tail_step`, and
**`round_pass`** / **`round_fail`**. Paper quantity: the decoding of one guessed atom. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLayout NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

/-! ## The banks -/

section Banks
variable (r : List Bool) (P H q W L cap : ℕ)

/-- The decoder bank: raw `one`, template, output `out`, driver, policies, private `pv`. -/
def decA (one out : List Bool) (pv : Fin 1703 → List Bool) (i : Fin 1703) : List Bool :=
  if i.val = 1 then one else if i.val = 1674 then UnaryTemplate.tape q else if i.val = 1688 then out
  else if i.val = 1694 then List.replicate P true else if i.val = 1698 then List.replicate W true
  else if i.val = 1699 then List.replicate L true else pv i

/-- The loop's own tapes. -/
def smA (pg J bad : ℕ) (cond : Bool) : Fin 11 → List Bool :=
  ![frame r, [false], regTape cap pg, regTape cap 0, regTape cap 0, [cond], regTape cap J, regTape cap bad,
    List.replicate H true, List.replicate (H + 2) false, List.replicate (P + 2) false]

/-- Their heads. -/
def smH (pg J bad : ℕ) : Fin 11 → ℕ := ![pg, 0, pg, 0, 0, 0, J, bad, 0, 0, 0]

def bankA (one out : List Bool) (pv : Fin 1703 → List Bool) (pg J bad : ℕ) (cond : Bool) : Fin AT → List Bool :=
  Fin.addCases (decA P q W L one out pv) (smA r P H cap pg J bad cond)

def bankH (dh : Fin 1703 → ℕ) (pg J bad : ℕ) : Fin AT → ℕ := Fin.addCases dh (smH pg J bad)

@[simp] theorem bankA_dm (one out : List Bool) (pv : Fin 1703 → List Bool) (pg J bad : ℕ) (cond : Bool)
    (i : Fin 1703) : bankA r P H q W L cap one out pv pg J bad cond (dm i) = decA P q W L one out pv i := by
  simp [bankA, dm]

@[simp] theorem bankA_sm (one out : List Bool) (pv : Fin 1703 → List Bool) (pg J bad : ℕ) (cond : Bool)
    (k : Fin 11) : bankA r P H q W L cap one out pv pg J bad cond (sm k) = smA r P H cap pg J bad cond k := by
  simp [bankA, sm]

@[simp] theorem bankH_dm (dh : Fin 1703 → ℕ) (pg J bad : ℕ) (i : Fin 1703) : bankH dh pg J bad (dm i) = dh i := by
  simp [bankH, dm]

@[simp] theorem bankH_sm (dh : Fin 1703 → ℕ) (pg J bad : ℕ) (k : Fin 11) : bankH dh pg J bad (sm k) = smH pg J bad k := by
  simp [bankH, sm]

/-- A bank from a decoder half and the loop's own tapes. -/
def bankG (dT : Fin 1703 → List Bool) (sA : Fin 11 → List Bool) : Fin AT → List Bool := Fin.addCases dT sA
def bankGH (dH : Fin 1703 → ℕ) (sH : Fin 11 → ℕ) : Fin AT → ℕ := Fin.addCases dH sH

@[simp] theorem bankG_dm (dT : Fin 1703 → List Bool) (sA : Fin 11 → List Bool) (i : Fin 1703) :
    bankG dT sA (dm i) = dT i := by simp [bankG, dm]
@[simp] theorem bankG_sm (dT : Fin 1703 → List Bool) (sA : Fin 11 → List Bool) (k : Fin 11) :
    bankG dT sA (sm k) = sA k := by simp [bankG, sm]
@[simp] theorem bankGH_dm (dH : Fin 1703 → ℕ) (sH : Fin 11 → ℕ) (i : Fin 1703) :
    bankGH dH sH (dm i) = dH i := by simp [bankGH, dm]
@[simp] theorem bankGH_sm (dH : Fin 1703 → ℕ) (sH : Fin 11 → ℕ) (k : Fin 11) :
    bankGH dH sH (sm k) = sH k := by simp [bankGH, sm]

theorem decA_priv (one out : List Bool) (pv : Fin 1703 → List Bool) (i : Fin 1703) (hi : isPub i = false) :
    decA P q W L one out pv i = pv i := by
  simp only [isPub, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
  simp [decA, hi]

theorem decA_pub (one out : List Bool) (pv pv' : Fin 1703 → List Bool) (i : Fin 1703) (hi : isPub i = true) :
    decA P q W L one out pv i = decA P q W L one out pv' i := by
  simp only [isPub, Bool.or_eq_true, beq_iff_eq] at hi
  unfold decA; rcases hi with ((((h | h) | h) | h) | h) | h <;> simp [h]

end Banks

/-- Every tape is a decoder tape or one of the loop's own. -/
theorem at_cases (y : Fin AT) : (∃ i, y = dm i) ∨ (∃ k, y = sm k) := by
  refine Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun k => Or.inr ⟨k, rfl⟩) y

/-- An install that matches a target bank at the slots and nowhere changes the ambient elsewhere. -/
theorem install_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A B : Fin u → List Bool)
    (out : Fin t → List Bool) (hin : ∀ j, B (slots j) = out j) (hout : ∀ y, (∀ j, slots j ≠ y) → B y = A y) :
    install slots A out = B := by
  funext y
  by_cases hy : ∃ j, slots j = y
  · obtain ⟨j, rfl⟩ := hy; rw [install_slot _ hi, hin]
  · rw [install_other _ _ _ _ (fun j hj => hy ⟨j, hj⟩), hout y (fun j hj => hy ⟨j, hj⟩)]

theorem dockH_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A B : Fin u → ℕ)
    (out : Fin t → ℕ) (hin : ∀ j, B (slots j) = out j) (hout : ∀ y, (∀ j, slots j ≠ y) → B y = A y) :
    dockH slots A out = B := by
  funext y
  by_cases hy : ∃ j, slots j = y
  · obtain ⟨j, rfl⟩ := hy; rw [dockH_slot slots hi, hin]
  · rw [dockH_other slots A out y (fun j hj => hy ⟨j, hj⟩), hout y (fun j hj => hy ⟨j, hj⟩)]

theorem Step.congr_out {t s : ℕ} {p : Machine t s} {n : ℕ} {H0 H1 H2 : Fin t → ℕ} {A0 A1 A2 : Fin t → List Bool}
    (h : Step p n H0 A0 H1 A1) (e1 : H1 = H2) (e2 : A1 = A2) : Step p n H0 A0 H2 A2 := by
  subst e1; subst e2; exact h

/-! ## Stage 1: the private eraser -/

section Stages
variable (r : List Bool) (P H q W L cap : ℕ)

/-- The private eraser, on its tapes. -/
noncomputable def eraseH := RecoveryFocus.machine em (RecoveryScratchErase.resetMachine 1697)

theorem em_cases (x : Fin (1697 + 1 + 1)) :
    (∃ k, x = Fin.castAdd 1 (Fin.castAdd 1 k)) ∨ x = Fin.castAdd 1 (Fin.natAdd 1697 (0 : Fin 1)) ∨
      x = Fin.natAdd (1697 + 1) (0 : Fin 1) := by
  refine Fin.addCases (fun y => ?_) (fun o => ?_) x
  · refine Fin.addCases (fun k => Or.inl ⟨k, rfl⟩) (fun o => ?_) y
    right; left; rw [Subsingleton.elim o 0]
  · right; right; rw [Subsingleton.elim o 0]

theorem eraseH_step (one out : List Bool) (pv : Fin 1703 → List Bool) (dh : Fin 1703 → ℕ) (pg J bad : ℕ) (cond : Bool)
    (hpv : ∀ i, isPub i = false → (pv i).length ≤ H) (hdh : ∀ i, isPub i = false → dh i = 0) :
    Step (eraseH) (2 * H + 4) (bankH dh pg J bad) (bankA r P H q W L cap one out pv pg J bad cond)
      (bankH dh pg J bad) (bankA r P H q W L cap one out (fun _ => List.replicate H false) pg J bad cond) := by
  have he := step_of_rready (RecoveryScratchErase.erase_ready (t := 1697) H (H + 2) (fun k => pv (priv k))
    (fun k => hpv _ (priv_pub k)))
  have hd := Step.dockAt he em em_inj (bankH dh pg J bad) (bankA r P H q W L cap one out pv pg J bad cond)
    (by
      intro x
      rcases em_cases x with ⟨k, rfl⟩ | rfl | rfl
      · rw [em_priv, bankH_dm]; exact hdh _ (priv_pub k)
      · rw [em_ruler, bankH_sm]; rfl
      · rw [em_cap, bankH_sm]; rfl)
    (by
      intro x
      rcases em_cases x with ⟨k, rfl⟩ | rfl | rfl
      · rw [em_priv, bankA_dm, decA_priv _ _ _ _ _ _ _ _ (priv_pub k), Fin.addCases_left, Fin.addCases_left]
      · rw [em_ruler, bankA_sm, Fin.addCases_left, Fin.addCases_right]; rfl
      · rw [em_cap, bankA_sm, Fin.addCases_right]; rfl)
  have eA : install em (bankA r P H q W L cap one out pv pg J bad cond)
      (Fin.addCases (Fin.addCases (fun _ : Fin 1697 => List.replicate H false) (fun _ : Fin 1 => List.replicate H true))
        (fun _ : Fin 1 => List.replicate (max (H + 2) (H + 1)) false)) =
      bankA r P H q W L cap one out (fun _ => List.replicate H false) pg J bad cond := by
    refine install_eq_of em em_inj _ _ _ ?_ ?_
    · intro x
      rcases em_cases x with ⟨k, rfl⟩ | rfl | rfl
      · rw [em_priv, bankA_dm, decA_priv _ _ _ _ _ _ _ _ (priv_pub k), Fin.addCases_left, Fin.addCases_left]
      · rw [em_ruler, bankA_sm, Fin.addCases_left, Fin.addCases_right]; rfl
      · rw [em_cap, bankA_sm, Fin.addCases_right, Nat.max_eq_left (by omega)]; rfl
    · intro y hy
      rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [bankA_dm, bankA_dm]
        cases hp : isPub i with
        | true => exact decA_pub _ _ _ _ _ _ _ _ _ hp
        | false =>
          obtain ⟨k, rfl⟩ := priv_surj i hp
          exact absurd (em_priv k) (hy _)
      · rw [bankA_sm, bankA_sm]
  have eH : dockH em (bankH dh pg J bad) (fun _ => 0) = bankH dh pg J bad := by
    refine dockH_eq_of em em_inj _ _ _ ?_ (fun _ _ => rfl)
    intro x
    rcases em_cases x with ⟨k, rfl⟩ | rfl | rfl
    · rw [em_priv, bankH_dm]; exact hdh _ (priv_pub k)
    · rw [em_ruler, bankH_sm]; rfl
    · rw [em_cap, bankH_sm]; rfl
  rw [eA, eH] at hd
  exact hd

/-! ## Stage 2: the raw tape's eraser -/

/-- The raw tape's eraser, on its tapes. -/
noncomputable def eraseP := RecoveryFocus.machine pm (RecoveryScratchErase.resetMachine 1)

theorem fin3_cases (f g h : List Bool) (x : Fin (1 + 1 + 1)) :
    Fin.addCases (Fin.addCases (fun _ : Fin 1 => f) (fun _ : Fin 1 => g)) (fun _ : Fin 1 => h) x = ![f, g, h] x := by
  fin_cases x <;> rfl

theorem eraseP_step (one out : List Bool) (pv : Fin 1703 → List Bool) (dh : Fin 1703 → ℕ) (pg J bad : ℕ) (cond : Bool)
    (hone : one.length ≤ P) (hd1 : dh 1 = 0) (hd2 : dh 1694 = 0) :
    Step (eraseP) (2 * P + 4) (bankH dh pg J bad) (bankA r P H q W L cap one out pv pg J bad cond)
      (bankH dh pg J bad) (bankA r P H q W L cap (List.replicate P false) out pv pg J bad cond) := by
  have he := step_of_rready (RecoveryScratchErase.erase_ready (t := 1) P (P + 2) (fun _ => one) (fun _ => hone))
  have hH : ∀ x, bankH dh pg J bad (pm x) = (fun _ => 0) x := by
    intro x; fin_cases x
    · show bankH dh pg J bad (dm 1) = 0; rw [bankH_dm]; exact hd1
    · show bankH dh pg J bad (dm 1694) = 0; rw [bankH_dm]; exact hd2
    · show bankH dh pg J bad (sm 10) = 0; rw [bankH_sm]; rfl
  have hd := Step.dockAt he pm pm_inj (bankH dh pg J bad) (bankA r P H q W L cap one out pv pg J bad cond) hH
    (by
      intro x; rw [fin3_cases]; fin_cases x
      · show bankA r P H q W L cap one out pv pg J bad cond (dm 1) = one; rw [bankA_dm]; simp [decA]
      · show bankA r P H q W L cap one out pv pg J bad cond (dm 1694) = _; rw [bankA_dm]; simp [decA]
      · show bankA r P H q W L cap one out pv pg J bad cond (sm 10) = _; rw [bankA_sm]; rfl)
  refine Step.congr_out hd (dockH_eq_of pm pm_inj _ _ _ hH (fun _ _ => rfl)) ?_
  refine install_eq_of pm pm_inj _ _ _ ?_ ?_
  · intro x; rw [fin3_cases, Nat.max_eq_left (show P + 1 ≤ P + 2 by omega)]; fin_cases x
    · show bankA r P H q W L cap _ out pv pg J bad cond (dm 1) = _; rw [bankA_dm]; simp [decA]
    · show bankA r P H q W L cap _ out pv pg J bad cond (dm 1694) = _; rw [bankA_dm]; simp [decA]
    · show bankA r P H q W L cap _ out pv pg J bad cond (sm 10) = _; rw [bankA_sm]; rfl
  · intro y hy
    rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [bankA_dm, bankA_dm]
      have h1' : i.val ≠ 1 := fun h => hy 0 (by
        have e : i = 1 := Fin.ext (by simpa using h)
        rw [e]; rfl)
      simp [decA, h1']
    · rw [bankA_sm, bankA_sm]

/-! ## Stage 3: the entry's code onto the raw tape -/

/-- The copy, on its tapes. -/
noncomputable def copyM := RecoveryFocus.machine cm FrontAtomCopy.copyAtom.toProg.compile

theorem copy_step (out : List Bool) (pv : Fin 1703 → List Bool) (dh : Fin 1703 → ℕ) (J bad : ℕ) (cond : Bool)
    (P0 : ℕ) (b x : Bool) (p rest : List Bool)
    (hr : r.drop P0 = FrontEntriesRef.gridWord b x ++ (List.replicate p.length true ++ false :: p) ++ rest)
    (hk : 1 ≤ p.length) (hP : 2 * p.length + 1 ≤ P) (hcap : 2 * (P0 + 2 * p.length + 5) + 2 ≤ cap)
    (hd1 : dh 1 = 0) :
    ∃ n, n ≤ 70 * (p.length + 2) ∧
      Step copyM n (bankH dh (2 * P0) J bad) (bankA r P H q W L cap (List.replicate P false) out pv (2 * P0) J bad cond)
        (bankH dh (2 * (P0 + 2 * p.length + 5)) J bad)
        (bankA r P H q W L cap (ZeroPadding.pad P (frame p)) out pv (2 * (P0 + 2 * p.length + 5)) J bad cond) := by
  obtain ⟨n, hn, hw⟩ := FrontAtomCopy.copyAtom_spec cap r P0 b x p rest P hr hk hP hcap (by omega) false
  have hs := (WExec.exec cap hw).step
  refine ⟨n, hn, ?_⟩
  have hd := Step.dockAt hs cm cm_inj (bankH dh (2 * P0) J bad)
    (bankA r P H q W L cap (List.replicate P false) out pv (2 * P0) J bad cond)
    (by
      intro j; fin_cases j
      · show bankH dh _ J bad (sm 0) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 1) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (dm 1) = _; rw [bankH_dm, hd1]; rfl
      · show bankH dh _ J bad (sm 2) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 3) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 4) = _; rw [bankH_sm]; rfl)
    (by
      intro j; fin_cases j
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 0) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 1) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (dm 1) = _; rw [bankA_dm]; simp [decA]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 2) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 3) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 4) = _; rw [bankA_sm]; rfl)
  have eA : install cm (bankA r P H q W L cap (List.replicate P false) out pv (2 * P0) J bad cond)
      (wenc cap (FrontAtomCopy.st r ⟨2 * (P0 + 2 * p.length + 5), 0, 0, ZeroPadding.pad P (frame p), false⟩)).A =
      bankA r P H q W L cap (ZeroPadding.pad P (frame p)) out pv (2 * (P0 + 2 * p.length + 5)) J bad cond := by
    refine install_eq_of cm cm_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 0) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 1) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (dm 1) = _; rw [bankA_dm]; simp [decA]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 2) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 3) = _; rw [bankA_sm]; rfl
      · show bankA r P H q W L cap _ out pv _ J bad cond (sm 4) = _; rw [bankA_sm]; rfl
    · intro y hy
      rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [bankA_dm, bankA_dm]
        have h1 : i.val ≠ 1 := fun h => hy 2 (by
          have e : i = 1 := Fin.ext (by simpa using h)
          show dm 1 = dm i; rw [e])
        simp [decA, h1]
      · rw [bankA_sm, bankA_sm]
        have h0 : k ≠ 0 := fun h => hy 0 (by rw [h]; rfl)
        have h2 : k ≠ 2 := fun h => hy 3 (by rw [h]; rfl)
        clear hy
        fin_cases k <;> simp [smA] at h0 h2 ⊢
  have eH : dockH cm (bankH dh (2 * P0) J bad)
      (wenc cap (FrontAtomCopy.st r ⟨2 * (P0 + 2 * p.length + 5), 0, 0, ZeroPadding.pad P (frame p), false⟩)).H =
      bankH dh (2 * (P0 + 2 * p.length + 5)) J bad := by
    refine dockH_eq_of cm cm_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · show bankH dh _ J bad (sm 0) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 1) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (dm 1) = _; rw [bankH_dm, hd1]; rfl
      · show bankH dh _ J bad (sm 2) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 3) = _; rw [bankH_sm]; rfl
      · show bankH dh _ J bad (sm 4) = _; rw [bankH_sm]; rfl
    · intro y hy
      rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [bankH_dm, bankH_dm]
      · rw [bankH_sm, bankH_sm]
        have h0 : k ≠ 0 := fun h => hy 0 (by rw [h]; rfl)
        have h2 : k ≠ 2 := fun h => hy 3 (by rw [h]; rfl)
        clear hy
        fin_cases k <;> simp [smH] at h0 h2 ⊢
  rw [eA, eH] at hd
  exact hd

/-! ## Stage 4: the decoder -/

/-- The decoder of mode `m`, on its tapes. -/
noncomputable def decM (m : Mode) := RecoveryFocus.machine dm (FrontAtomDecoder.dec m)

theorem padIn_eq (bits out : List Bool) (i : Fin 1703) :
    decA P q W L (ZeroPadding.pad P (frame bits)) out (fun _ => List.replicate H false) i =
      CloseoutRowsCircuitPadding.input P H q W L bits out i := by
  simp only [decA, CloseoutRowsCircuitPadding.input, Fin.ext_iff]
  norm_num

theorem dec_stepAt (m : Mode) (bits out : List Bool) (pg J bad : ℕ) (cond : Bool)
    (hC : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P) (hH : P + 1 ≤ H) :
    ∃ r0 : ExecutionReceipt 1703 (FrontAtomDecoder.decS m),
      Step (decM m) (CloseoutRowsCircuitWholeBudget.budget P bits.length)
        (bankH (CloseoutRowsCircuitColdEntry.heads out) pg J bad)
        (bankA r P H q W L cap (ZeroPadding.pad P (frame bits)) out (fun _ => List.replicate H false) pg J bad cond)
        (bankGH r0.final.heads (smH pg J bad)) (bankG r0.final.tapes (smA r P H cap pg J bad cond)) ∧
      r0.final.heads 1700 = 0 ∧ (readTapeBit (r0.final.tapes 1700) 0 = true ↔ FrontAtomDecoder.passedM m q W L bits) ∧
      (FrontAtomDecoder.passedM m q W L bits →
        r0.final.heads = CloseoutRowsCircuitColdEntry.heads (out ++ FrontAtomDecoder.nativeM m q bits) ∧
        r0.final.tapes 1688 = out ++ FrontAtomDecoder.nativeM m q bits ∧ r0.final.tapes 1674 = UnaryTemplate.tape q ∧
        r0.final.tapes 1694 = List.replicate P true ∧ r0.final.tapes 1698 = List.replicate W true ∧
        r0.final.tapes 1699 = List.replicate L true ∧ r0.final.tapes 1 = ZeroPadding.pad P (frame bits) ∧
        ∀ i, i ≠ 1 → i ≠ 1674 → i ≠ 1694 → i ≠ 1698 → i ≠ 1699 → i ≠ 1688 → (r0.final.tapes i).length ≤ H) := by
  obtain ⟨r0, hr, hs, hfh, hflag, -, -, -, -, hgood⟩ := FrontAtomDecoder.dec_step m P H q W L bits out hC hH
  have hstep : Step (FrontAtomDecoder.dec m) (CloseoutRowsCircuitWholeBudget.budget P bits.length)
      (CloseoutRowsCircuitColdEntry.heads out) (CloseoutRowsCircuitPadding.input P H q W L bits out)
      r0.final.heads r0.final.tapes := Step.of_run hr rfl rfl
  have hd := Step.dockAt hstep dm dm_inj (bankH (CloseoutRowsCircuitColdEntry.heads out) pg J bad)
    (bankA r P H q W L cap (ZeroPadding.pad P (frame bits)) out (fun _ => List.replicate H false) pg J bad cond)
    (fun i => by rw [bankH_dm]) (fun i => by rw [bankA_dm, padIn_eq])
  refine ⟨r0, Step.congr_out hd ?_ ?_, hfh, hflag, hgood⟩
  · refine dockH_eq_of dm dm_inj _ _ _ (fun i => by rw [bankGH_dm]) ?_
    intro y hy
    rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · exact absurd rfl (hy i)
    · rw [bankGH_sm, bankH_sm]
  · refine install_eq_of dm dm_inj _ _ _ (fun i => by rw [bankG_dm]) ?_
    intro y hy
    rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · exact absurd rfl (hy i)
    · rw [bankG_sm, bankA_sm]

/-! ## Stage 5: the verdict -/

/-- The verdict step, on its tapes. -/
noncomputable def tailM := RecoveryFocus.machine tm FrontAtomTail.tailP.toProg.compile

theorem tail_stepAt (dT : Fin 1703 → List Bool) (dH : Fin 1703 → ℕ) (pg J bad : ℕ) (cond : Bool)
    (hfh : dH 1700 = 0) (hbad : bad ≤ 1) (hJ : J ≤ cap) (hcap : 1 ≤ cap) :
    Step tailM 12 (bankGH dH (smH pg J bad)) (bankG dT (smA r P H cap pg J bad cond))
      (bankGH dH (smH pg (J - 1) (FrontAtomTail.badNext (dT 1700) bad)))
      (bankG dT (smA r P H cap pg (J - 1) (FrontAtomTail.badNext (dT 1700) bad)
        (FrontAtomTail.condOf (J - 1) (FrontAtomTail.badNext (dT 1700) bad)))) := by
  have hw := FrontAtomTail.tail_spec cap (dT 1700) J bad cond hbad hJ hcap
  have hs := (WExec.exec cap hw).step
  have hd := Step.dockAt hs tm tm_inj (bankGH dH (smH pg J bad)) (bankG dT (smA r P H cap pg J bad cond))
    (by
      intro j; fin_cases j
      · show bankGH dH (smH pg J bad) (dm 1700) = _; rw [bankGH_dm, hfh]; rfl
      · show bankGH dH (smH pg J bad) (sm 5) = _; rw [bankGH_sm]; rfl
      · show bankGH dH (smH pg J bad) (sm 6) = _; rw [bankGH_sm]; rfl
      · show bankGH dH (smH pg J bad) (sm 7) = _; rw [bankGH_sm]; rfl)
    (by
      intro j; fin_cases j
      · show bankG dT (smA r P H cap pg J bad cond) (dm 1700) = _; rw [bankG_dm]; rfl
      · show bankG dT (smA r P H cap pg J bad cond) (sm 5) = _; rw [bankG_sm]; rfl
      · show bankG dT (smA r P H cap pg J bad cond) (sm 6) = _; rw [bankG_sm]; rfl
      · show bankG dT (smA r P H cap pg J bad cond) (sm 7) = _; rw [bankG_sm]; rfl)
  refine Step.congr_out hd ?_ ?_
  · refine dockH_eq_of tm tm_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · show bankGH dH _ (dm 1700) = _; rw [bankGH_dm, hfh]; rfl
      · show bankGH dH _ (sm 5) = _; rw [bankGH_sm]; rfl
      · show bankGH dH _ (sm 6) = _; rw [bankGH_sm]; rfl
      · show bankGH dH _ (sm 7) = _; rw [bankGH_sm]; rfl
    · intro y hy
      rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [bankGH_dm, bankGH_dm]
      · have h5 : k ≠ 5 := fun h => hy 1 (by rw [h]; rfl)
        have h6 : k ≠ 6 := fun h => hy 2 (by rw [h]; rfl)
        have h7 : k ≠ 7 := fun h => hy 3 (by rw [h]; rfl)
        clear hy
        rw [bankGH_sm, bankGH_sm]
        fin_cases k <;> simp [smH] at h5 h6 h7 ⊢
  · refine install_eq_of tm tm_inj _ _ _ ?_ ?_
    · intro j; fin_cases j
      · show bankG dT _ (dm 1700) = _; rw [bankG_dm]; rfl
      · show bankG dT _ (sm 5) = _; rw [bankG_sm]; rfl
      · show bankG dT _ (sm 6) = _; rw [bankG_sm]; rfl
      · show bankG dT _ (sm 7) = _; rw [bankG_sm]; rfl
    · intro y hy
      rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · rw [bankG_dm, bankG_dm]
      · have h5 : k ≠ 5 := fun h => hy 1 (by rw [h]; rfl)
        have h6 : k ≠ 6 := fun h => hy 2 (by rw [h]; rfl)
        have h7 : k ≠ 7 := fun h => hy 3 (by rw [h]; rfl)
        clear hy
        rw [bankG_sm, bankG_sm]
        fin_cases k <;> simp [smA] at h5 h6 h7 ⊢

end Stages

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound
