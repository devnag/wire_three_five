import Proof.Wire_3_5.UnionMachine.C1RefBase
import Proof.CaseAnalysis.FinalWordFunctionDock

/-! # C6 front, the C1 dock: the stage (P3:1324-1362, 3673)

The carrier loop (`C1Gates.gates_loop`), the request's assembly (`C1Asm.asmW`, rewound), C1's call (base's
`C10WordFunctionDock.rewound_dock` of `c1.impl`) and the framing of its output (PA's `copyNatListM`, rewound), on one
bank: the loop's `1436` tapes (the assembly's output on the register layout's blank tape `1357`, its log on `1367`),
C1's tapes (its input slot is `1357`), and the framing's `12` tapes.
* **`wmDock`**: a register program, compiled and rewound, docked at any injective slots;
* `asl` (the assembly's slots in the loop bank), **`asmStage`**;
* **`c1Stage_step`**: from the loop's entry bank to `frame (natListWord (selArgmin R))` on the framing's output.

Paper quantity of the main type: `star:selection`'s selected coset (P3:1357-1360), framed for the table writer. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Stage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-! ## A register program, rewound, at any slots -/

theorem wmDock {ns nr u : ℕ} (cap : ℕ) (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0)
    (sl : Fin (ns + 2 + nr + 1) → Fin u) (hsl : Function.Injective sl) (A : Fin u → List Bool)
    (hA : ∀ i, A (sl (Fin.castAdd 1 i)) = (wenc cap σ).A i) (hL : A (sl (Fin.natAdd (ns + 2 + nr) 0)) = []) :
    ∃ k, k ≤ n ∧ Step (RecoveryFocus.machine sl (Rewind.machine P.toProg.compile)) (2 * n + 2) (fun _ => 0) A
      (fun _ => 0) (install sl A (Fin.addCases (wenc cap τ).A (fun _ => List.replicate k false))) := by
  obtain ⟨out, k, hs, hout, hlog, hk⟩ := WalkKit.wm_stepJ cap P σ τ n hw (FrontKit.wenc_H_zero cap σ hs0 hv0)
  have hd := Step.dockAt hs sl hsl (fun _ => 0) A (fun _ => rfl) (fun j => by
    refine Fin.addCases (m := ns + 2 + nr) (n := 1) (fun i => ?_) (fun o => ?_) j
    · rw [Fin.addCases_left]; exact hA i
    · rw [Fin.addCases_right, Subsingleton.elim o 0]; exact hL)
  refine ⟨k, hk, FrontDescDecoder.Step.congrOut hd (dockH_self sl hsl _ _ (fun _ => rfl)) ?_⟩
  congr 1
  funext j
  refine Fin.addCases (m := ns + 2 + nr) (n := 1) (fun i => ?_) (fun o => ?_) j
  · rw [Fin.addCases_left]; exact hout i
  · rw [Fin.addCases_right, Subsingleton.elim o 0]; exact hlog

/-- The encoded bank's tape, by position. -/
theorem wenc_A_val {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (j : Fin (ns + 2 + nr)) :
    (wenc cap σ).A j = if j.val = 0 then σ.st 0 else if j.val = 1 then [σ.cell]
      else if h : j.val ≤ ns + 1 then σ.st ⟨j.val - 1, by omega⟩
      else regTape cap (σ.val ⟨j.val - (ns + 2), by omega⟩) := by
  simp only [wenc, role]
  split_ifs <;> rfl

/-! ## The assembly in the loop bank -/

/-- The assembly layout's slots: its streams `0 … 4` are the register layout's `1, 4, 5, 6, 7` (the gates, the
populations, `1^gt`, `1^np`, `1^q`), its output `5` the blank tape `1357`, its stream `6` the layout's `3`, its cell and
registers the layout's, its log the blank tape `1367`. -/
def aslV (j : ℕ) : ℕ :=
  if j = 0 then 1359 else if j = 1 then 1358 else if j = 2 then 1362 else if j = 3 then 1363 else if j = 4 then 1364
  else if j = 5 then 1365 else if j = 6 then 1357 else if j = 7 then 1361 else if j < 32 then 1361 + j else 1367

def asl (j : Fin (6 + 2 + 24 + 1)) : Fin 1436 :=
  ⟨aslV j.val, by have := j.isLt; unfold aslV; split_ifs <;> omega⟩

/-- The slots' inverse. -/
def aslI (m : ℕ) : ℕ :=
  if m = 1359 then 0 else if m = 1358 then 1 else if m = 1362 then 2 else if m = 1363 then 3 else if m = 1364 then 4
  else if m = 1365 then 5 else if m = 1357 then 6 else if m = 1361 then 7 else if m = 1367 then 32 else m - 1361

theorem aslI_aslV (j : ℕ) (hj : j < 33) : aslI (aslV j) = j := by
  interval_cases j <;> rfl

theorem asl_inj : Function.Injective asl := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [asl] at h'
  apply Fin.ext
  rw [← aslI_aslV a.val a.isLt, ← aslI_aslV b.val b.isLt, h']

/-- The assembly's entry state on the register layout's streams `S`. -/
def σA (S : Fin 11 → List Bool) : C1Asm.AS :=
  ⟨fun _ => 0, fun i => if i.val = 0 then S 1 else if i.val = 1 then S 4 else if i.val = 2 then S 5
    else if i.val = 3 then S 6 else if i.val = 4 then S 7 else if i.val = 5 then [] else S 3, fun _ => 0, false⟩

theorem rl_at (cap Hd k : ℕ) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (m : ℕ) (hm : m < 76) :
    bank D (rlR cap S k) Hd ⟨1357 + m, by omega⟩ =
      if m = 0 ∨ m = 10 then [] else (wenc cap (ρS S)).A ⟨m, hm⟩ := by
  unfold bank
  rw [dif_neg (by simp), dif_pos (by simp; omega)]
  unfold rlR
  simp only [Nat.add_sub_cancel_left]
  split_ifs with h
  · rfl
  · exact Fin.addCases_left (m := 76) (n := 1) (motive := fun _ => List Bool) ⟨m, hm⟩

theorem asm_entry (cap Hd k : ℕ) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (i : Fin (6 + 2 + 24)) :
    bank D (rlR cap S k) Hd (asl (Fin.castAdd 1 i)) = (wenc cap (σA S)).A i := by
  obtain ⟨i, hi⟩ := i
  by_cases h8 : i < 8
  · have e : asl (Fin.castAdd 1 ⟨i, hi⟩) = ⟨1357 + (aslV i - 1357), by unfold aslV; split_ifs <;> omega⟩ := by
      apply Fin.ext; simp only [asl, Fin.val_castAdd]; unfold aslV; split_ifs <;> omega
    rw [e, rl_at cap Hd k D S _ (by unfold aslV; split_ifs <;> omega), wenc_A_val, wenc_A_val]
    interval_cases i <;> simp [aslV, σA, ρS]
  · have e2 : asl (Fin.castAdd 1 ⟨i, hi⟩) = ⟨1357 + (i + 4), by omega⟩ := by
      apply Fin.ext; simp only [asl, Fin.val_castAdd]; unfold aslV; split_ifs <;> omega
    rw [e2, rl_at cap Hd k D S (i + 4) (by omega), if_neg (by omega)]
    have r1 : (⟨i + 4, by omega⟩ : Fin (10 + 2 + 64)) = rTape (ns := 10) (nr := 64) ⟨i - 8, by omega⟩ :=
      Fin.ext (by simp [rTape]; omega)
    have r2 : (⟨i, hi⟩ : Fin (6 + 2 + 24)) = rTape (ns := 6) (nr := 24) ⟨i - 8, by omega⟩ :=
      Fin.ext (by simp [rTape]; omega)
    rw [r1, r2, wenc_A_r, wenc_A_r]; rfl

theorem asm_log (cap Hd k : ℕ) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) :
    bank D (rlR cap S k) Hd (asl (Fin.natAdd (6 + 2 + 24) 0)) = [] := by
  have e : asl (Fin.natAdd (6 + 2 + 24) 0) = ⟨1357 + 10, by omega⟩ := by
    apply Fin.ext; simp [asl, aslV]
  rw [e, rl_at cap Hd k D S 10 (by omega)]; simp

/-- The assembly, compiled and rewound, at its slots. -/
noncomputable def asmM (cr : ℕ) := RecoveryFocus.machine asl (Rewind.machine (C1Asm.asmW cr).toProg.compile)

/-- **The assembly on the loop bank**: its output `frame (reqWord …)` on tape `1357`; `1^q` kept; every tape outside
its slots unchanged. -/
theorem asmStage (cap cr Hd k : ℕ) (D : Fin 1357 → List Bool) (S : Fin 11 → List Bool) (Gs Ps : List Bool)
    (q gt np : ℕ) (s1 : S 1 = marks Gs) (s4 : S 4 = marks Ps) (s5 : S 5 = List.replicate gt true)
    (s6 : S 6 = List.replicate np true) (s7 : S 7 = List.replicate q true)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ cap)
    (hcap2 : q + Ledger.rowBr cr q + gt + np + 6 * (natBitLength q + natBitLength (Ledger.rowBr cr q) +
      natBitLength gt + natBitLength np) + (frame (C1Asm.reqWord q (Ledger.rowBr cr q) gt np Gs Ps)).length + 50 ≤
        cap) :
    ∃ A' : Fin 1436 → List Bool,
      Step (asmM cr) (2 * C1Asm.asmCost cr q gt np Gs Ps + 2) (fun _ => 0) (bank D (rlR cap S k) Hd) (fun _ => 0) A' ∧
      A' ⟨1357, by omega⟩ = frame (C1Asm.reqWord q (Ledger.rowBr cr q) gt np Gs Ps) ∧
      A' ⟨1365, by omega⟩ = S 7 ∧ ∀ y, (∀ j, asl j ≠ y) → A' y = bank D (rlR cap S k) Hd y := by
  obtain ⟨τ, hw, t5, tt⟩ := C1Asm.asmW_spec cap cr q gt np Gs Ps (σA S) (by simp [σA, s1]) (by simp [σA, s4])
    (by simp [σA, s5]) (by simp [σA, s6]) (by simp [σA, s7]) (by simp [σA]) (fun _ => rfl) (fun _ => rfl) hcap1 hcap2
  obtain ⟨k', -, hs⟩ := wmDock cap _ (σA S) τ _ hw (fun _ => rfl) (fun _ => rfl) asl asl_inj _
    (asm_entry cap Hd k D S) (asm_log cap Hd k D S)
  refine ⟨_, hs, ?_, ?_, fun y hy => install_other _ _ _ _ hy⟩
  · have e : (⟨1357, by omega⟩ : Fin 1436) = asl (Fin.castAdd 1 (sTape (ns := 6) (nr := 24) 5)) :=
      Fin.ext (by simp [asl, aslV, sTape])
    rw [e, install_slot _ asl_inj, Fin.addCases_left, wenc_A_s, t5]
  · have e : (⟨1365, by omega⟩ : Fin 1436) = asl (Fin.castAdd 1 (sTape (ns := 6) (nr := 24) 4)) :=
      Fin.ext (by simp [asl, aslV, sTape])
    rw [e, install_slot _ asl_inj, Fin.addCases_left, wenc_A_s, tt 4 (by decide)]
    simp [σA]

/-! ## The framing of C1's output -/

def Q9 : Fin 9 ↪ Fin 9 := Function.Embedding.refl _

/-- Copy the raw `natListWord` of stream `0` onto stream `1` as a frame. -/
def convW : WM 1 9 := .seq (PrimAsm.CopyNat.copyNatListM false 0 1 Q9) (emitC 1 7 false)

def convCost (xs : List ℕ) : ℕ :=
  ((xs.length + 12) * (300 * xs.length + 300) + 64 * (natListWord xs).length + 64) + 1 + 7

/-- The framing's entry state. -/
def σC (xs : List ℕ) : WState 1 9 := ⟨fun _ => 0, fun i => if i.val = 0 then natListWord xs else [], fun _ => 0, false⟩

theorem conv_spec (capC : ℕ) (xs : List ℕ)
    (hcap : 8 * xs.length + 2 * (natListWord xs).length + 17 ≤ capC) :
    ∃ τ : WState 1 9, WExec capC convW (σC xs) τ (convCost xs) ∧ τ.st 1 = frame (natListWord xs) := by
  have h1 := PrimAsm.CopyNat.copyNatListM_spec capC false 0 1 (by decide) Q9 xs [] [] (σC xs)
    (by simp [σC, PrimAsm.ParseNat.enc]) rfl (by simp [σC]) (fun _ _ => rfl) (by simp [σC]; omega)
  obtain ⟨τ1, hτ1⟩ : ∃ τ : WState 1 9, τ = (PrimAsm.WriteNat.appendO (σC xs) 1 (Q9 7) (marks (natListWord xs))).seth 0
      (([] : List Bool).length + PrimAsm.ParseNat.stp false * (natListWord xs).length) := ⟨_, rfl⟩
  rw [← hτ1] at h1
  have hsh : τ1.sh 1 = (τ1.st 1).length := by rw [hτ1]; simp [σC]
  have hv : τ1.val 7 < capC := by
    rw [hτ1]; simp [σC, Q9, C1Rng.marks_length]; omega
  have h2 := emitC_spec capC 1 7 false τ1 hsh hv
  refine ⟨_, WExec.seq h1 h2, ?_⟩
  simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
  rw [C1Asm.frameM, hτ1]; simp [σC]

/-! ## The stage's bank -/

abbrev NB (T : ℕ) : ℕ := 1436 + T + 12

def lb (T : ℕ) (i : Fin 1436) : Fin (NB T) := ⟨i.val, by unfold NB; omega⟩

theorem lb_inj (T : ℕ) : Function.Injective (lb T) := fun a b h => Fin.ext (by simpa [lb] using congrArg Fin.val h)

/-- C1's slots: its input slot is the assembly's output `1357`, its other tapes `1436 + j`. -/
def csl (T : ℕ) (j : Fin T) : Fin (NB T) := if j.val = 0 then ⟨1357, by unfold NB; omega⟩ else ⟨1436 + j.val, by unfold NB; omega⟩

theorem csl_inj (T : ℕ) : Function.Injective (csl T) := by
  intro a b h
  have h' := congrArg Fin.val h
  unfold csl at h'
  apply Fin.ext
  split_ifs at h' <;> simp at h' <;> omega

/-- The framing's slots: its source is C1's output tape, the rest `1436 + T + j − 1`. -/
def cvl (T : ℕ) (o : Fin T) (j : Fin (1 + 2 + 9 + 1)) : Fin (NB T) :=
  if j.val = 0 then csl T o else ⟨1436 + T + j.val - 1, by unfold NB; omega⟩

theorem cvl_inj (T : ℕ) (o : Fin T) : Function.Injective (cvl T o) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := o.isLt
  unfold cvl csl at h'
  apply Fin.ext
  split_ifs at h' <;> simp at h' <;> omega

/-- The stage's entry bank: the loop's `L`, C1's tapes blank, the framing's cell `[false]`, output and log blank,
registers `regTape capC 0`. -/
def c1In (T capC : ℕ) (L : Fin 1436 → List Bool) : Fin (NB T) → List Bool := fun y =>
  if h : y.val < 1436 then L ⟨y.val, h⟩
  else if y.val ≤ 1436 + T then (if y.val = 1436 + T then [false] else [])
  else if y.val = 1436 + T + 1 ∨ y.val = 1436 + T + 11 then [] else regTape capC 0

theorem conv_entry (T capC : ℕ) (L : Fin 1436 → List Bool) (o : Fin T) (xs : List ℕ) (A : Fin (NB T) → List Bool)
    (h0 : A (csl T o) = natListWord xs) (hr : ∀ y : Fin (NB T), 1436 + T ≤ y.val → A y = c1In T capC L y)
    (i : Fin (1 + 2 + 9)) : A (cvl T o (Fin.castAdd 1 i)) = (wenc capC (σC xs)).A i := by
  obtain ⟨i, hi⟩ := i
  rw [wenc_A_val]
  by_cases hi0 : i = 0
  · subst hi0
    have e : cvl T o (Fin.castAdd 1 ⟨0, hi⟩) = csl T o := by simp [cvl]
    rw [e, h0]; simp [σC]
  · have e : cvl T o (Fin.castAdd 1 ⟨i, hi⟩) = ⟨1436 + T + i - 1, by unfold NB; omega⟩ := by simp [cvl, hi0]
    rw [e, hr _ (by show 1436 + T ≤ 1436 + T + i - 1; omega)]
    unfold c1In
    simp only [Fin.val_mk]
    rw [dif_neg (by omega)]
    by_cases hi1 : i = 1
    · subst hi1; simp [σC]
    · by_cases hi2 : i = 2
      · subst hi2; simp [σC]
      · rw [if_neg (by omega), if_neg (by omega), if_neg hi0, if_neg hi1, dif_neg (by omega)]
        simp [σC]

theorem conv_log (T capC : ℕ) (L : Fin 1436 → List Bool) (o : Fin T) (A : Fin (NB T) → List Bool)
    (hr : ∀ y : Fin (NB T), 1436 + T ≤ y.val → A y = c1In T capC L y) :
    A (cvl T o (Fin.natAdd (1 + 2 + 9) 0)) = [] := by
  have e : cvl T o (Fin.natAdd (1 + 2 + 9) 0) = ⟨1436 + T + 11, by unfold NB; omega⟩ := by
    apply Fin.ext; simp [cvl]
  rw [e, hr _ (by show 1436 + T ≤ 1436 + T + 11; omega)]
  unfold c1In
  rw [dif_neg (by show ¬ 1436 + T + 11 < 1436; omega)]
  simp

/-! ## The stage -/

section Stage
variable {d : ℕ} (c : Plan.C1At d)

/-- C1's tape count. -/
abbrev TC : ℕ := c.impl.program.tapeCount

/-- **The stage's machine**: the carrier loop, the assembly, C1's call, the framing. -/
noncomputable def stageM (cr : ℕ) :=
  Composition.machine (RecoveryFocus.machine (lb (TC c)) (StreamController.machine rndM (wSl 11)))
    (Composition.machine (RecoveryFocus.machine (lb (TC c)) (asmM cr))
      (Composition.machine (RecoveryFocus.machine (csl (TC c)) c.impl.program.machine)
        (RecoveryFocus.machine (cvl (TC c) c.impl.program.outputTape) (Rewind.machine convW.toProg.compile))))

/-- The framing's output tape. -/
def outT : Fin (NB (TC c)) := ⟨1436 + TC c + 1, by unfold NB; omega⟩

/-- **The C1 stage**: from the loop's entry bank (and C1's and the framing's entry tapes), the loop's result
(`hloop`, e.g. `C1Gates.gates_loop`), the assembly, C1's call on `frame (selWord R)` and the framing leave
`frame (natListWord (selArgmin R))` on `outT`; the PCPP output (`1360`), the carriers' codes (`1366`) and `1^q`
(`1365`) are kept. -/
theorem c1Stage_step {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool)
    (cap Hd cr capC nL : ℕ) (L : Fin 1436 → List Bool)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0) L Hn An ∧ Hn = (fun _ => 0) ∧
        ∃ (D : Fin 1357 → List Bool) (k : ℕ), An = bank D (rlR cap (C1Gates.Sj Cs lits cb V po src V) k) Hd)
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (C1Gates.GF Cs lits V)
      (C1Gates.PF Cs lits cb V) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ cap)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits V + C1Gates.npF lits V + 6 * (natBitLength q +
      natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits V) + natBitLength (C1Gates.npF lits V)) +
        (frame (Plan.selWord R)).length + 50 ≤ cap)
    (hcapC : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      capC) :
    ∃ A' : Fin (NB (TC c)) → List Bool,
      Step (stageM c cr) (nL + 1 + ((2 * C1Asm.asmCost cr q (C1Gates.gtF Cs lits V) (C1Gates.npF lits V)
        (C1Gates.GF Cs lits V) (C1Gates.PF Cs lits cb V) + 2) + 1 + ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
          (2 * convCost (SelectionMachine.selArgmin R) + 2)))) (fun _ => 0) (c1In (TC c) capC L) (fun _ => 0) A' ∧
      A' (outT c) = frame (natListWord (SelectionMachine.selArgmin R)) ∧
      A' (lb (TC c) ⟨1360, by omega⟩) = po ∧ A' (lb (TC c) ⟨1366, by omega⟩) = src ∧
      A' (lb (TC c) ⟨1365, by omega⟩) = List.replicate q true := by
  set T := TC c with hT
  obtain ⟨Hn, An, hl, hHn, D, k, hAn⟩ := hloop
  subst hHn
  -- the loop, lifted
  have h1 := Step.dockAt hl (lb T) (lb_inj T) (fun _ => 0) (c1In T capC L) (fun _ => rfl)
    (fun j => by unfold c1In lb; simp)
  rw [dockH_self (lb T) (lb_inj T) _ _ (fun _ => rfl)] at h1
  set A1 := install (lb T) (c1In T capC L) An with hA1
  -- the assembly
  set S := C1Gates.Sj Cs lits cb V po src V with hS
  obtain ⟨A2', h2, a1357, a1365, aout⟩ := asmStage cap cr Hd k D S (C1Gates.GF Cs lits V) (C1Gates.PF Cs lits cb V) q
    (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (by simp [hS, C1Gates.Sj]) (by simp [hS, C1Gates.Sj])
    (by simp [hS, C1Gates.Sj]) (by simp [hS, C1Gates.Sj]) (by simp [hS, C1Gates.Sj]) hcap1 (by rw [hreq]; exact hcap2)
  have h2' := Step.dockAt h2 (lb T) (lb_inj T) (fun _ => 0) A1 (fun _ => rfl)
    (fun j => by rw [hA1, install_slot _ (lb_inj T), hAn])
  rw [dockH_self (lb T) (lb_inj T) _ _ (fun _ => rfl)] at h2'
  set A2 := install (lb T) A1 A2' with hA2
  -- C1's call
  have hin : A2 (csl T (C10WordFunctionDock.inSlot c.impl.program)) =
      frame ((fun r : {r // (Plan.c1sized d c.E₁ c.c₁).pre r} => (Plan.c1sized d c.E₁ c.c₁).input r.1) ⟨R, hpre⟩) := by
    have e : csl T (C10WordFunctionDock.inSlot c.impl.program) = lb T ⟨1357, by omega⟩ := by
      apply Fin.ext; simp [csl, lb, C10WordFunctionDock.inSlot]
    rw [e, hA2, install_slot _ (lb_inj T), a1357, hreq]
    rfl
  have hblank : ∀ j, j ≠ C10WordFunctionDock.inSlot c.impl.program → A2 (csl T j) = [] := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have hTC : TC c = c.impl.program.tapeCount := rfl
    have e : csl T j = ⟨1436 + j.val, by unfold NB; omega⟩ := by simp [csl, hj0]
    have hno : ∀ i, lb T i ≠ csl T j := fun i h => by
      rw [e] at h; have := congrArg Fin.val h; simp [lb] at this; omega
    rw [hA2, install_other _ _ _ _ hno, hA1, install_other _ _ _ _ hno, e]
    unfold c1In
    simp only [Fin.val_mk]
    rw [dif_neg (by omega), if_pos (by omega), if_neg (by omega)]
  obtain ⟨tout, hout, h3⟩ := C10WordFunctionDock.rewound_dock c.impl (csl T) (csl_inj T) (fun _ => 0) A2 ⟨R, hpre⟩
    (fun _ => rfl) hin hblank
  rw [dockH_self (csl T) (csl_inj T) _ _ (fun _ => rfl)] at h3
  set A3 := install (csl T) A2 tout with hA3
  -- the framing
  set xs := SelectionMachine.selArgmin R with hxs
  obtain ⟨τ, hw, hτ⟩ := conv_spec capC xs hcapC
  have hr3 : ∀ y : Fin (NB T), 1436 + T ≤ y.val → A3 y = c1In T capC L y := by
    intro y hy
    have n1 : ∀ i, lb T i ≠ y := fun i h => by subst h; simp [lb] at hy; omega
    have n3 : ∀ j, csl T j ≠ y := fun j h => by
      subst h; have := j.isLt; unfold csl at hy; split_ifs at hy <;> simp at hy <;> omega
    rw [hA3, install_other _ _ _ _ n3, hA2, install_other _ _ _ _ n1, hA1, install_other _ _ _ _ n1]
  have h0 : A3 (csl T c.impl.program.outputTape) = natListWord xs := by
    rw [hA3, install_slot _ (csl_inj T), hout]; rfl
  obtain ⟨k4, -, h4⟩ := wmDock capC convW (σC xs) τ _ hw (fun _ => rfl) (fun _ => rfl) (cvl T c.impl.program.outputTape)
    (cvl_inj T _) A3 (conv_entry T capC L _ xs A3 h0 hr3) (conv_log T capC L _ A3 hr3)
  refine ⟨_, Step.seq h1 (Step.seq h2' (Step.seq h3 h4)), ?_, ?_, ?_, ?_⟩
  · have e : outT c = cvl T c.impl.program.outputTape (Fin.castAdd 1 (sTape (ns := 1) (nr := 9) 1)) := by
      apply Fin.ext; simp [outT, cvl, sTape, hT]
    rw [e, install_slot _ (cvl_inj T _), Fin.addCases_left, wenc_A_s, hτ]
  all_goals
    have nc : ∀ y : Fin 1436, y.val ≠ 1357 → (∀ j, cvl T c.impl.program.outputTape j ≠ lb T y) ∧
        (∀ j, csl T j ≠ lb T y) := by
      intro y hy
      have hy2 := y.isLt
      refine ⟨fun j h => ?_, fun j h => ?_⟩
      · have h' := congrArg Fin.val h
        have := c.impl.program.outputTape.isLt
        unfold cvl csl at h'
        split_ifs at h' <;> simp [lb] at h' <;> omega
      · have h' := congrArg Fin.val h
        have := j.isLt
        unfold csl at h'
        split_ifs at h' <;> simp [lb] at h' <;> omega
    have keep : ∀ y : Fin 1436, y.val ≠ 1357 →
        install (cvl T c.impl.program.outputTape) A3 (Fin.addCases (wenc capC τ).A (fun _ => List.replicate k4 false))
          (lb T y) = A2' y := by
      intro y hy
      rw [install_other _ _ _ _ (nc y hy).1, hA3, install_other _ _ _ _ (nc y hy).2, hA2, install_slot _ (lb_inj T)]
    have noA : ∀ m : ℕ, (hm : m < 1436) → aslV (aslI m) ≠ m → ∀ j, asl j ≠ ⟨m, hm⟩ := by
      intro m hm hne j h
      have h' := congrArg Fin.val h
      simp only [asl] at h'
      have e2 := aslI_aslV j.val j.isLt
      rw [h'] at e2
      rw [e2] at hne
      exact hne h'
  · rw [keep _ (by simp), aout _ (noA 1360 (by omega) (by decide))]
    have e : (⟨1360, by omega⟩ : Fin 1436) = ⟨1357 + 3, by omega⟩ := rfl
    rw [e, rl_at cap Hd k D S 3 (by omega), if_neg (by omega), wenc_A_val]
    simp [ρS, hS, C1Gates.Sj]
  · rw [keep _ (by simp), aout _ (noA 1366 (by omega) (by decide))]
    have e : (⟨1366, by omega⟩ : Fin 1436) = ⟨1357 + 9, by omega⟩ := rfl
    rw [e, rl_at cap Hd k D S 9 (by omega), if_neg (by omega), wenc_A_val]
    simp [ρS, hS, C1Gates.Sj]
  · rw [keep _ (by simp), a1365]
    simp [hS, C1Gates.Sj]

end Stage

end NearCubicWires.WireExponent3_5.UnionMachine.C1Stage
