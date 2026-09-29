import Proof.Wire_3_5.UnionMachine.C1CarPre
import Proof.Wire_3_5.UnionMachine.C1RL
import Proof.Wire_3_5.UnionMachine.FrontAtomRound
import Proof.Wire_3_5.UnionMachine.FrontDescDecoder
import Proof.Wire_3_5.UnionMachine.WalkKit

/-! # C6 front, the C1 dock: the carrier loop's bank and stages (P3:1326-1330, 3409-3410, 3673)

One round per PCPP variable: base's eraser clears the carrier-table bank, the item copy writes the variable's
carrier code onto the table's input (`C1RL.itemRL`), the table's stages 1–7 decode it (`C1CarPre.carPreM`), and the
variable's round (`C1RL.roundRL`) appends its gates and population to C1's request pieces.
Bank (`1436` tapes): `1357`, the register layout's `76` tapes and its log (its streams `0` and `9` are the
table's tapes `304` and `0`; the two own copies stay blank), the eraser's ruler `1^Hd` and capacity tape.
* `bank`, the views `bank_cp`, `bank_w`, `bank_e`;
* **`eraseStage`**, **`wmStage`** (any register program ending with every register at `0`), **`carStage`**.

Paper quantity: none (the loop's plumbing; the gates and populations are `C1RL.roundRL_spec`'s). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Loop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (frItems)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natListWord)

/-! ## Slots -/

def cpSl (i : Fin 1357) : Fin 1436 := ⟨i.val, by have := i.isLt; omega⟩
def wSl (j : Fin 77) : Fin 1436 :=
  ⟨if j.val = 0 then 304 else if j.val = 10 then 0 else 1357 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def eSl (x : Fin (1357 + 1 + 1)) : Fin 1436 :=
  ⟨if x.val < 1357 then x.val else if x.val = 1357 then 1434 else 1435, by have := x.isLt; split_ifs <;> omega⟩

theorem cpSl_inj : Function.Injective cpSl := fun a b h => Fin.ext (by simpa [cpSl] using congrArg Fin.val h)
theorem wSl_inj : Function.Injective wSl := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [wSl] at hv
  apply Fin.ext
  have := a.isLt; have := b.isLt
  split_ifs at hv <;> omega
theorem eSl_inj : Function.Injective eSl := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [eSl] at hv
  apply Fin.ext
  have := a.isLt; have := b.isLt
  split_ifs at hv <;> omega

/-! ## The bank -/

/-- The bank from the table's tapes `D`, the register layout's region `R` (its tapes `0` and `10` unused), `Hd`. -/
def bank (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ) : Fin 1436 → List Bool := fun t =>
  if h : t.val < 1357 then D ⟨t.val, h⟩
  else if h2 : t.val < 1434 then R ⟨t.val - 1357, by omega⟩
  else if t.val = 1434 then List.replicate Hd true else List.replicate (Hd + 1) false

theorem bank_cp (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ) (i : Fin 1357) :
    bank D R Hd (cpSl i) = D i := by
  simp only [bank, cpSl, i.isLt, dif_pos]

/-- The register layout's view: its streams `0`, `9` are the table's tapes `304`, `0`. -/
def wview (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (j : Fin 77) : List Bool :=
  if j.val = 0 then D 304 else if j.val = 10 then D 0 else R j

theorem bank_w (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ) (j : Fin 77) :
    bank D R Hd (wSl j) = wview D R j := by
  unfold bank wSl wview
  have := j.isLt
  by_cases h0 : j.val = 0
  · simp [h0]
  · by_cases h10 : j.val = 10
    · simp [h10]
    · simp only [h0, h10, if_false]
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 1; apply Fin.ext; simp

theorem bank_e (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ) (x : Fin (1357 + 1 + 1)) :
    bank D R Hd (eSl x) = Fin.addCases (Fin.addCases D (fun _ : Fin 1 => List.replicate Hd true))
      (fun _ : Fin 1 => List.replicate (Hd + 1) false) x := by
  refine Fin.addCases (fun y => ?_) (fun o => ?_) x
  · refine Fin.addCases (fun i => ?_) (fun o => ?_) y
    · rw [Fin.addCases_left, Fin.addCases_left]
      simp only [bank, eSl, Fin.val_castAdd, i.isLt, if_true, dif_pos]
    · rw [Fin.addCases_left, Fin.addCases_right]
      simp [bank, eSl]
  · rw [Fin.addCases_right]
    simp [bank, eSl]

/-! ## The eraser -/

noncomputable def eraseC := RecoveryFocus.machine eSl (RecoveryScratchErase.resetMachine 1357)

/-- **The eraser**: every table tape to `false^Hd`. -/
theorem eraseStage (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ) (hD : ∀ i, (D i).length ≤ Hd) :
    Step eraseC (2 * Hd + 4) (fun _ => 0) (bank D R Hd) (fun _ => 0) (bank (fun _ => List.replicate Hd false) R Hd) := by
  have he := step_of_rready (RecoveryScratchErase.erase_ready (t := 1357) Hd (Hd + 1) D hD)
  have hd := Step.dockAt he eSl eSl_inj (fun _ => 0) (bank D R Hd) (fun _ => rfl) (fun x => bank_e D R Hd x)
  refine FrontDescDecoder.Step.congrOut hd ?_ ?_
  · exact FrontLoopKit.dockH_self eSl eSl_inj _ _ (fun _ => rfl)
  · refine FrontAtomRound.install_eq_of eSl eSl_inj _ _ _ (fun x => ?_) (fun y hy => ?_)
    · rw [bank_e]
      refine Fin.addCases (fun z => ?_) (fun o => ?_) x
      · refine Fin.addCases (fun i => ?_) (fun o => ?_) z <;> simp
      · simp
    · unfold bank
      have hy' : ¬ y.val < 1357 := fun h => hy ⟨y.val, by omega⟩ (Fin.ext (by simp [eSl, h]))
      have hy2 : y.val ≠ 1434 := fun h => hy ⟨1357, by omega⟩ (Fin.ext (by simp [eSl, h]))
      have hy3 : y.val ≠ 1435 := fun h => hy ⟨1358, by omega⟩ (Fin.ext (by simp [eSl, h]))
      simp only [hy', dif_neg, not_false_eq_true]

/-! ## A register program's stage -/

/-- The register layout's state with streams `S` (heads, registers `0`, cell `false`). -/
def ρS (S : Fin 11 → List Bool) : C1RL.RLS := ⟨fun _ => 0, S, fun _ => 0, false⟩

/-- The layout's own region: the encoded state and the log `0^k` (tapes `0`, `10` unused, blank). -/
def rlR (cap : ℕ) (S : Fin 11 → List Bool) (k : ℕ) : Fin 77 → List Bool := fun j =>
  if j.val = 0 ∨ j.val = 10 then [] else Fin.addCases (wenc cap (ρS S)).A (fun _ : Fin 1 => List.replicate k false) j

/-- The streams the register layout sees: `0` and `9` are the table's tapes `304` and `0`. -/
def upd (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) : Fin 11 → List Bool :=
  Function.update (Function.update S 0 (D 304)) 9 (D 0)

/-- The table's tapes after a register program: `304`, `0` from its streams `0`, `9`. -/
def upd2 (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) : Fin 1357 → List Bool :=
  Function.update (Function.update D 304 (S 0)) 0 (S 9)

theorem wenc_A_eq (cap : ℕ) (σ τ : C1RL.RLS) (hst : σ.st = τ.st) (hv : σ.val = τ.val) (hc : σ.cell = τ.cell) :
    (wenc cap σ).A = (wenc cap τ).A := by
  funext j; simp only [wenc]; rw [hst, hv, hc]

theorem role_stream_ne (j : Fin (10 + 2 + 64)) (i : Fin 11) (hr : role j = Role.stream i) (h0 : j.val ≠ 0)
    (h10 : j.val ≠ 10) : i ≠ 0 ∧ i ≠ 9 := by
  unfold role at hr
  split_ifs at hr with a b c
  · exact absurd a h0
  · cases hr
    constructor
    · intro e; have := congrArg Fin.val e; simp at this; omega
    · intro e; have := congrArg Fin.val e; simp at this; omega

theorem wenc_other (cap : ℕ) (S S' : Fin 11 → List Bool) (h : ∀ i : Fin 11, i ≠ 0 → i ≠ 9 → S i = S' i)
    (j : Fin (10 + 2 + 64)) (h0 : j.val ≠ 0) (h10 : j.val ≠ 10) :
    (wenc cap (ρS S)).A j = (wenc cap (ρS S')).A j := by
  simp only [wenc]
  cases hr : role j with
  | stream i =>
    obtain ⟨a, b⟩ := role_stream_ne j i hr h0 h10
    exact h i a b
  | cell => rfl
  | reg r => rfl

theorem wview_rl (cap : ℕ) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (k : ℕ) (j : Fin 77) :
    wview D (rlR cap S k) j = Fin.addCases (wenc cap (ρS (upd D S))).A (fun _ : Fin 1 => List.replicate k false) j := by
  unfold wview rlR
  refine Fin.addCases (m := 76) (n := 1) (fun i => ?_) (fun o => ?_) j
  · have hi := i.isLt
    simp only [Fin.addCases_left, Fin.val_castAdd]
    by_cases h0 : i.val = 0
    · have e : i = sTape (nr := 64) (0 : Fin 11) := Fin.ext (by simp [sTape, h0])
      rw [if_pos h0, e, wenc_A_s]; simp [ρS, upd]
    · by_cases h10 : i.val = 10
      · have e : i = sTape (nr := 64) (9 : Fin 11) := Fin.ext (by simp [sTape, h10])
        rw [if_neg h0, if_pos h10, e, wenc_A_s]; simp [ρS, upd]
      · rw [if_neg h0, if_neg h10, if_neg (by omega)]
        exact wenc_other cap S (upd D S) (fun i' a b => by simp [upd, a, b]) i h0 h10
  · simp only [Fin.addCases_right]
    simp [Subsingleton.elim o 0]

theorem pad_rep (k k0 : ℕ) : ZeroPadding.pad k (List.replicate k0 false) = List.replicate (max k k0) false := by
  unfold ZeroPadding.pad
  rw [List.length_replicate, ← List.replicate_add]
  congr 1; omega

theorem wenc_H_zero' (cap : ℕ) (S : Fin 11 → List Bool) : (wenc cap (ρS S)).H = fun _ => 0 := by
  funext j; simp only [wenc, ρS]; split <;> rfl

/-- **A register program's stage**: any program ending with every register at `0` and the cell `false`, compiled and
rewound, docked at the layout's slots; the table's tapes `304`, `0` take its streams `0`, `9`. -/
theorem wmStage (cap : ℕ) (P : WM 10 64) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (k Hd n : ℕ)
    (ρ' : C1RL.RLS) (hw : WExec cap P (ρS (upd D S)) ρ' n) (hv : ∀ r, ρ'.val r = 0) (hc : ρ'.cell = false) :
    ∃ k', Step (RecoveryFocus.machine wSl (Rewind.machine P.toProg.compile)) (2 * n + 2) (fun _ => 0)
      (bank D (rlR cap S k) Hd) (fun _ => 0) (bank (upd2 D ρ'.st) (rlR cap ρ'.st k') Hd) := by
  obtain ⟨out, k0, hs, hout, hlog, -⟩ := WalkKit.wm_stepJ cap P (ρS (upd D S)) ρ' n hw (wenc_H_zero' cap _)
  let capv : Fin (10 + 2 + 64 + 1) → ℕ := fun j => if j.val = 76 then k else 0
  have hp := FrontDescDecoder.Step.pad hs capv
  have hin : ∀ j : Fin 77, ZeroPadding.pad (capv j)
      (Fin.addCases (wenc cap (ρS (upd D S))).A (fun _ : Fin 1 => ([] : List Bool)) j) = wview D (rlR cap S k) j := by
    intro j
    rw [wview_rl]
    refine Fin.addCases (m := 76) (n := 1) (fun i => ?_) (fun o => ?_) j
    · have hi := i.isLt
      simp only [Fin.addCases_left, capv, Fin.val_castAdd, show i.val ≠ 76 by omega, if_false, ZeroPadding.pad_zero]
    · simp only [Fin.addCases_right]
      simp [capv, Subsingleton.elim o 0, ZeroPadding.pad]
  have hd := Step.dockAt hp wSl wSl_inj (fun _ => 0) (bank D (rlR cap S k) Hd) (fun _ => rfl)
    (fun j => by rw [bank_w, ← hin j])
  refine ⟨max k k0, FrontDescDecoder.Step.congrOut hd (FrontLoopKit.dockH_self wSl wSl_inj _ _ (fun _ => rfl)) ?_⟩
  have hw' : ∀ i : Fin 76, i.val ≠ 0 → i.val ≠ 10 → (wenc cap ρ').A i = (wenc cap (ρS ρ'.st)).A i := by
    intro i _ _
    rw [wenc_A_eq cap ρ' (ρS ρ'.st) rfl (funext hv) hc]
  refine FrontAtomRound.install_eq_of wSl wSl_inj _ _ _ (fun j => ?_) (fun y hy => ?_)
  · rw [bank_w]
    unfold wview
    refine Fin.addCases (m := 76) (n := 1) (fun i => ?_) (fun o => ?_) j
    · have hi := i.isLt
      have ho : ZeroPadding.pad (capv (Fin.castAdd 1 i)) (out (Fin.castAdd 1 i)) = (wenc cap ρ').A i := by
        simp only [capv, Fin.val_castAdd, show i.val ≠ 76 by omega, if_false, ZeroPadding.pad_zero]
        exact hout i
      rw [ho]
      simp only [Fin.val_castAdd]
      by_cases h0 : i.val = 0
      · rw [if_pos h0]
        have e : i = sTape (nr := 64) (0 : Fin 11) := Fin.ext (by simp [sTape, h0])
        rw [e, wenc_A_s]; simp [upd2]
      · rw [if_neg h0]
        by_cases h10 : i.val = 10
        · rw [if_pos h10]
          have e : i = sTape (nr := 64) (9 : Fin 11) := Fin.ext (by simp [sTape, h10])
          rw [e, wenc_A_s]; simp [upd2]
        · rw [if_neg h10]
          unfold rlR
          simp only [Fin.val_castAdd, h0, h10, or_self, if_false, Fin.addCases_left]
          exact (hw' i h0 h10).symm
    · have hv76 : (Fin.natAdd 76 o : Fin 77).val = 76 := by simp [Subsingleton.elim o 0]
      rw [if_neg (by omega), if_neg (by omega)]
      unfold rlR
      rw [if_neg (by omega), Fin.addCases_right]
      have hc76 : capv (Fin.natAdd 76 o) = k := by simp [capv, Subsingleton.elim o 0]
      rw [hc76, show Fin.natAdd 76 o = Fin.natAdd (10 + 2 + 64) (0 : Fin 1) from by rw [Subsingleton.elim o 0],
        hlog, pad_rep]
  · -- tapes outside the layout's slots
    have hy304 : y.val ≠ 304 := fun h => hy ⟨0, by omega⟩ (Fin.ext (by simp [wSl, h]))
    have hy0 : y.val ≠ 0 := fun h => hy ⟨10, by omega⟩ (Fin.ext (by simp [wSl, h]))
    have hyR : ∀ m : ℕ, m < 77 → m ≠ 0 → m ≠ 10 → y.val ≠ 1357 + m := fun m hm a b h =>
      hy ⟨m, hm⟩ (Fin.ext (by simp [wSl, a, b, h]))
    unfold bank
    by_cases h1 : y.val < 1357
    · rw [dif_pos h1, dif_pos h1]
      have n0 : (⟨y.val, h1⟩ : Fin 1357) ≠ 0 := fun e => hy0 (by simpa using congrArg Fin.val e)
      have n304 : (⟨y.val, h1⟩ : Fin 1357) ≠ 304 := fun e => hy304 (by simpa using congrArg Fin.val e)
      simp only [upd2, Function.update_apply, n0, n304, if_false]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : y.val < 1434
      · rw [dif_pos h2, dif_pos h2]
        have hd' : y.val - 1357 = 0 ∨ y.val - 1357 = 10 := by
          by_contra hc'
          push Not at hc'
          exact hyR (y.val - 1357) (by omega) hc'.1 hc'.2 (by omega)
        unfold rlR
        simp only [hd', or_true, true_or, if_true]
      · rw [dif_neg h2, dif_neg h2]

/-! ## The carrier table's stages 1–7 -/

noncomputable def carC := RecoveryFocus.machine cpSl C1CarPre.carPreM

/-- **The table's stages 1–7** on the bank, over `false^Hd` padding. -/
theorem carStage {n : ℕ} (X : Stars.Carrier n) (D : Fin 1357 → List Bool) (R : Fin 77 → List Bool) (Hd : ℕ)
    (hD : ∀ i, D i = ZeroPadding.pad Hd (PrimT.CarTable.carIn X.code 0 0 i)) :
    ∃ D' : Fin 1357 → List Bool, Step carC (C1CarPre.carPreCost X 0 0) (fun _ => 0) (bank D R Hd) (fun _ => 0)
      (bank D' R Hd) ∧
      D' 0 = ZeroPadding.pad Hd (frame (RepairRepresentation.natWord X.code)) ∧
      D' 304 = ZeroPadding.pad Hd (PrimT.CarWM.accHdr ++ PrimT.tabSeg X) ∧
      ∀ i, (D' i).length ≤ max Hd (max (2 * (RepairRepresentation.natWord X.code).length + 1)
        (C1CarPre.carPreCost X 0 0 + 1)) := by
  obtain ⟨tout, hs, h0, h304⟩ := C1CarPre.carPre_step X 0 0
  have hp := FrontDescDecoder.Step.pad hs (fun _ => Hd)
  have hd := Step.dockAt hp cpSl cpSl_inj (fun _ => 0) (bank D R Hd) (fun _ => rfl)
    (fun i => by rw [bank_cp, hD])
  refine ⟨fun i => ZeroPadding.pad Hd (tout i), ?_, ?_, ?_, ?_⟩
  · refine FrontDescDecoder.Step.congrOut hd (FrontLoopKit.dockH_self cpSl cpSl_inj _ _ (fun _ => rfl)) ?_
    refine FrontAtomRound.install_eq_of cpSl cpSl_inj _ _ _ (fun i => by rw [bank_cp]) (fun y hy => ?_)
    unfold bank
    have h1 : ¬ y.val < 1357 := fun h => hy ⟨y.val, h⟩ (Fin.ext (by simp [cpSl]))
    rw [dif_neg h1, dif_neg h1]
  · simp only; rw [h0]
  · simp only; rw [h304]
  · intro i
    have hl := C1CarPre.Step.len_le hs i
    simp only [ZeroPadding.pad_length]
    have hin : (PrimT.CarTable.carIn X.code 0 0 i).length ≤ 2 * (RepairRepresentation.natWord X.code).length + 1 := by
      unfold PrimT.CarTable.carIn
      split_ifs <;> simp [frame_length]
    omega

/-! ## One round -/

noncomputable def itemM := RecoveryFocus.machine wSl (Rewind.machine C1RL.itemRL.toProg.compile)
noncomputable def roundM := RecoveryFocus.machine wSl (Rewind.machine C1RL.roundRL.toProg.compile)

/-- **One round**: erase, the item copy, the table's stages 1–7, the variable's round. -/
noncomputable def rndM := Composition.machine eraseC (Composition.machine itemM (Composition.machine carC roundM))

theorem upd_other (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (i : Fin 11) (h0 : i ≠ 0) (h9 : i ≠ 9) :
    upd D S i = S i := by
  simp [upd, Function.update_apply, h0, h9]

theorem readTapeBit_rep (m : ℕ) : readTapeBit (List.replicate m false) 0 = false := by
  cases m <;> rfl

/-- **One round of the carrier loop.** -/
theorem roundStep (cap Hd : ℕ) {q : ℕ} (X : Stars.Carrier q) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool)
    (k : ℕ) (ws : List (List Bool)) (rest8 : List Bool) (x : ℕ) (hx : x < ws.length)
    (hwsx : ws.getD x [] = RepairRepresentation.natWord X.code)
    (Gacc Pacc bits rest2 : List Bool) (lits : List ℕ) (sys aux cb gt np V j kk : ℕ)
    (hD : ∀ i, (D i).length ≤ Hd)
    (hS1 : S 1 = marks Gacc) (hS2 : S 2 = C1Cnt.poWord sys aux cb bits lits ++ rest2)
    (hbits : bits.length = sys * q) (hS3 : S 3 = List.replicate x true) (hS4 : S 4 = marks Pacc)
    (hS5 : S 5 = List.replicate gt true) (hS6 : S 6 = List.replicate np true) (hS7 : S 7 = List.replicate q true)
    (hS8 : S 8 = frItems ws ++ rest8) (hS10 : S 10 = List.replicate j true ++ List.replicate kk false) (hj : 1 ≤ j)
    (hsV : sys ≤ V) (haV : aux ≤ V) (hcV : cb ≤ V) (hlV : lits.length ≤ V) (hV : ∀ l ∈ lits, l ≤ V) (hxV : x ≤ V)
    (h3V : 3 ≤ V)
    (hHd : max (2 * (RepairRepresentation.natWord X.code).length + 1) (C1CarPre.carPreCost X 0 0 + 1) ≤ Hd)
    (hxc : x ≤ cap)
    (hcap : sys * q + q + lits.length + 6 * V + 8 + x + q + GateConv.capNeed X +
      2 * (X.flatMap GateConv.selGate).length + gt + X.length + C1Cnt.cntOf x lits + cb + np + 2 ^ (cb + 2) +
      (marks (natListWord (List.range' gt X.length))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length +
      6 * natBitLength (gt + X.length) + 6 * natBitLength (C1Cnt.cntOf x lits + 2 ^ (cb + 1)) + 40 ≤ cap) :
    ∃ (D' : Fin 1357 → List Bool) (S' : Fin 11 → List Bool) (k' : ℕ),
      Step rndM ((2 * Hd + 4) + 1 + ((2 * C1Item.itemC x (frItems ws).length + 2) + 1 +
        (C1CarPre.carPreCost X 0 0 + 1 + (2 * (C1RoundW.roundC x q V lits.length cb (C1RoundW.gateC X Gacc.length + 1 +
          C1RoundW.popC gt X.length (C1Cnt.cntOf x lits) cb Pacc.length np
            (marks (natListWord (List.range' gt X.length))).length
            (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length) + 1 +
          (3 * j + 5)) + 2))))
        (fun _ => 0) (bank D (rlR cap S k) Hd) (fun _ => 0) (bank D' (rlR cap S' k') Hd) ∧
      (∀ i, (D' i).length ≤ Hd) ∧ S' 2 = S 2 ∧ S' 7 = S 7 ∧ S' 8 = S 8 ∧ S' 3 = List.replicate (x + 1) true ∧
      S' 1 = (if 0 < C1Cnt.cntOf x lits then marks Gacc ++ marks (X.flatMap GateConv.selGate) else marks Gacc) ∧
      S' 4 = (if 0 < C1Cnt.cntOf x lits then marks Pacc ++ marks (natListWord (List.range' gt X.length)) ++
        marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1))) else marks Pacc) ∧
      S' 5 = List.replicate (gt + if 0 < C1Cnt.cntOf x lits then X.length else 0) true ∧
      S' 6 = List.replicate (np + if 0 < C1Cnt.cntOf x lits then 1 else 0) true ∧
      S' 10 = List.replicate (j - 1) true ++ List.replicate (kk + 1) false := by
  set w := RepairRepresentation.natWord X.code with hw
  -- 1. erase
  have e1 := eraseStage D (rlR cap S k) Hd hD
  set E : Fin 1357 → List Bool := fun _ => List.replicate Hd false with hE
  -- 2. the item
  obtain ⟨ρ1, i1, it9, itO, itv, itc⟩ := C1RL.itemRL_spec cap (ρS (upd E S)) ws rest8 x Hd
    (by show upd E S 8 = _; rw [upd_other E S 8 (by decide) (by decide), hS8])
    (by show upd E S 9 = _; simp [upd, hE])
    (by show upd E S 3 = _; rw [upd_other E S 3 (by decide) (by decide), hS3])
    (fun _ => rfl) (fun _ => rfl) hx (by rw [hwsx]; exact le_trans (le_max_left _ _) hHd) hxc
  obtain ⟨k1, e2⟩ := wmStage cap C1RL.itemRL E S k Hd _ ρ1 i1 itv (by rw [itc]; rfl)
  -- the table's input
  set D1 := upd2 E ρ1.st with hD1
  have hD1v : ∀ i, D1 i = ZeroPadding.pad Hd (PrimT.CarTable.carIn X.code 0 0 i) := by
    intro i
    have hfl : (frame w).length = 2 * w.length + 1 := frame_length w
    by_cases h0 : i = 0
    · subst h0
      simp only [hD1, upd2, Function.update_self]
      rw [it9, hwsx]
      have hc0 : PrimT.CarTable.carIn X.code 0 0 0 = frame w := by simp [PrimT.CarTable.carIn, hw]
      rw [hc0]
      unfold ZeroPadding.pad
      rw [hfl]
    · by_cases h304 : i = 304
      · subst h304
        simp only [hD1, upd2, Function.update_apply, show (304 : Fin 1357) ≠ 0 by decide, if_false, if_true]
        rw [itO 0 (by decide)]
        simp [ρS, upd, PrimT.CarTable.carIn, ZeroPadding.pad, hE]
      · simp only [hD1, upd2, Function.update_apply, h0, h304, if_false, hE]
        have hc : PrimT.CarTable.carIn X.code 0 0 i = [] := by
          unfold PrimT.CarTable.carIn
          split_ifs with a b c
          · exact absurd (Fin.ext a) h0
          · simp
          · simp
          · rfl
        rw [hc]; simp [ZeroPadding.pad]
  -- 3. the table's stages 1–7
  obtain ⟨D2, e3, hD20, hD2304, hlen2⟩ := carStage X D1 (rlR cap ρ1.st k1) Hd hD1v
  -- 4. the variable's round
  have st1 : ∀ i : Fin 11, i ≠ 0 → i ≠ 9 → ρ1.st i = S i := fun i a b => by
    rw [itO i b]; exact upd_other E S i a b
  obtain ⟨ρ2, r2, rt0, rt2, rt7, rt8, rt9, rt3, rt1, rt4, rt5, rt6, rt10, rtv, rtc⟩ :=
    C1RL.roundRL_spec cap X (ρS (upd D2 ρ1.st)) (List.replicate (Hd - (PrimT.CarWM.accHdr ++ PrimT.tabSeg X).length) false)
      Gacc Pacc bits rest2 lits sys aux cb x gt np V j kk
      (by show upd D2 ρ1.st 0 = _; simp only [upd, Function.update_apply, show (0 : Fin 11) ≠ 9 by decide, if_false,
            if_true]; rw [hD2304]; simp [ZeroPadding.pad]; rfl)
      (readTapeBit_rep _)
      (by show upd D2 ρ1.st 1 = _; rw [upd_other _ _ 1 (by decide) (by decide), st1 1 (by decide) (by decide), hS1])
      (by show upd D2 ρ1.st 2 = _; rw [upd_other _ _ 2 (by decide) (by decide), st1 2 (by decide) (by decide), hS2])
      hbits
      (by show upd D2 ρ1.st 3 = _; rw [upd_other _ _ 3 (by decide) (by decide), st1 3 (by decide) (by decide), hS3])
      (by show upd D2 ρ1.st 4 = _; rw [upd_other _ _ 4 (by decide) (by decide), st1 4 (by decide) (by decide), hS4])
      (by show upd D2 ρ1.st 5 = _; rw [upd_other _ _ 5 (by decide) (by decide), st1 5 (by decide) (by decide), hS5])
      (by show upd D2 ρ1.st 6 = _; rw [upd_other _ _ 6 (by decide) (by decide), st1 6 (by decide) (by decide), hS6])
      (by show upd D2 ρ1.st 7 = _; rw [upd_other _ _ 7 (by decide) (by decide), st1 7 (by decide) (by decide), hS7])
      (by show upd D2 ρ1.st 10 = _; rw [upd_other _ _ 10 (by decide) (by decide), st1 10 (by decide) (by decide), hS10])
      hj (fun _ => rfl) (fun _ => rfl) hsV haV hcV hlV hV hxV h3V hcap
  obtain ⟨k2, e4⟩ := wmStage cap C1RL.roundRL D2 ρ1.st k1 Hd _ ρ2 r2 rtv (by rw [rtc]; rfl)
  have hD' : upd2 D2 ρ2.st = D2 := by
    funext i
    simp only [upd2, Function.update_apply]
    split_ifs with a b
    · subst a; rw [rt9]; simp [ρS, upd]
    · subst b; rw [rt0]; simp [ρS, upd]
    · rfl
  refine ⟨D2, ρ2.st, k2, ?_, fun i => (hlen2 i).trans (max_le le_rfl hHd), ?_, ?_, ?_, rt3, rt1, rt4, rt5, rt6, rt10⟩
  · rw [← hD']
    exact e1.seq (e2.seq (e3.seq e4))
  · rw [rt2]; show upd D2 ρ1.st 2 = S 2
    rw [upd_other _ _ 2 (by decide) (by decide), st1 2 (by decide) (by decide)]
  · rw [rt7]; show upd D2 ρ1.st 7 = S 7
    rw [upd_other _ _ 7 (by decide) (by decide), st1 7 (by decide) (by decide)]
  · rw [rt8]; show upd D2 ρ1.st 8 = S 8
    rw [upd_other _ _ 8 (by decide) (by decide), st1 8 (by decide) (by decide)]

end NearCubicWires.WireExponent3_5.UnionMachine.C1Loop
