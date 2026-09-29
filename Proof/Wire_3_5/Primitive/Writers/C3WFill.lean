import Proof.Wire_3_5.Primitive.Writers.C3WWriters

/-! # C3 request writer, part 9: the fill and the register program's masked phases

Paper quantity: none (the machine plumbing of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

/-! ## The fill -/

/-- The register tapes (the fill's targets). -/
def regSelC (j : Fin WT) : Bool := decide (CN + 2 ≤ j.val)

/-- The program's tapes before the fill: the streams `st`, the cell and the registers blank. -/
def rawC (st : Fin (CN + 1) → List Bool) : Fin WT → List Bool := fun j => match role j with
  | .stream i => st i
  | .cell => []
  | .reg _ => []

theorem rawC_s (st : Fin (CN + 1) → List Bool) (s : Fin (CN + 1)) : rawC st (sTape s) = st s := by
  simp [rawC, role_sTape]
theorem rawC_c (st : Fin (CN + 1) → List Bool) : rawC st cTape = [] := by simp [rawC, role_cTape]
theorem rawC_r (st : Fin (CN + 1) → List Bool) (r : Fin CR) : rawC st (rTape r) = [] := by simp [rawC, role_rTape]

theorem sTape_eq_iffC (a b : Fin (CN + 1)) : sTape (nr := CR) a = sTape b ↔ a = b :=
  ⟨fun h => sTape_inj h, fun h => h ▸ rfl⟩

theorem regSelC_s (s : Fin (CN + 1)) : regSelC (sTape (nr := CR) s) = false := by
  have : s.val < CN + 1 := s.isLt
  simp only [regSelC, decide_eq_false_iff_not, not_le]
  show (if s.val = 0 then 0 else s.val + 1) < CN + 2
  split <;> omega

theorem regSelC_c : regSelC (cTape (ns := CN) (nr := CR)) = false := by
  unfold regSelC; rw [show (cTape (ns := CN) (nr := CR)).val = 1 from rfl]; decide

theorem regSelC_r (r : Fin CR) : regSelC (rTape (ns := CN) r) = true := by simp [regSelC, rTape]

/-- The fill: the registers at capacity `2W + 2` from the count `1^W` on `cCT`, the marker on `cAUX`. -/
def fillC : Prog WT :=
  .seq (UnionMachine.FrontFill.fillP (sTape cCT) (sTape cAUX) regSelC) (.act (writeAt cTape false) (fun _ => .stay))

/-- The program's start state after the fill. -/
def σF (st : Fin (CN + 1) → List Bool) (W : ℕ) : WState CN CR :=
  ⟨fun _ => 0, Function.update st cAUX (List.replicate (2 * W + 3) false), fun _ => 0, false⟩

theorem fillC_exec (st : Fin (CN + 1) → List Bool) (W : ℕ) (hct : st cCT = List.replicate W true)
    (haux : st cAUX = []) :
    Exec fillC ⟨fun _ => 0, rawC st⟩ (wenc (2 * W + 2) (σF st W)) (11 * W + 20 + 1 + 1) := by
  have hca : sTape (nr := CR) cCT ≠ sTape cAUX := fun h => absurd (sTape_inj h) (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (sTape (nr := CR) cAUX) regSelC i → rawC st i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSelC_s] at hi; exact absurd hi (by decide)
      · rw [regSelC_c] at hi; exact absurd hi (by decide)
      · exact rawC_r st r
    · subst hi
      rw [rawC_s]; exact haux
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape cCT) (sTape cAUX) regSelC (fun _ => 0) (rawC st) hca
    (regSelC_s _) (regSelC_s _) W (by rw [rawC_s]; exact hct) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape cCT) (sTape cAUX) regSelC (fun _ => 0) (rawC st) W 0)
    (writeAt (cTape (ns := CN) (nr := CR)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape cCT) (sTape cAUX) regSelC (fun _ => 0) (rawC st) W 0).act
      (writeAt (cTape (ns := CN) (nr := CR)) false) (fun _ => .stay) = wenc (2 * W + 2) (σF st W) := by
    apply Bank.ext'
    · intro j
      simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_H_s]
        split_ifs <;> simp [σF] <;> omega
      · rw [wenc_H_c]
        split_ifs <;> omega
      · rw [wenc_H_r]
        split_ifs <;> simp [σF] <;> omega
    · intro j
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSelC_s, Bool.false_eq_true,
          sTape_eq_iffC, rawC_s, σF]
        by_cases hx : s = cAUX
        · subst hx; simp
        · simp [hx]
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSelC_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := CR) (ns := CN) s).symm, rawC_c]
        simp [σF, UnionMachine.FrontFill.side, regSelC_c, fun s => (sTape_ne_c (nr := CR) (ns := CN) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSelC_r, if_true, σF]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

/-! ## The masked phases -/

/-- The streams and the cell (the masked phases' reset). -/
def selS (j : Fin WT) : Bool := decide (j.val < CN + 2)

/-- Every stream head at `0`. -/
def rs (σ : WState CN CR) : WState CN CR := ⟨fun _ => 0, σ.st, σ.val, σ.cell⟩

/-- A masked phase: the program, then every stream head back at `0`. -/
noncomputable def phM (P : Prog WT) := MaskedReset.machine P.compile selS

theorem selS_H (cap : ℕ) (τ : WState CN CR) :
    (fun i => if selS i = true then 0 else (wenc cap τ).H i) = (wenc 0 (rs τ)).H := by
  funext i
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · have h : selS (sTape (nr := CR) s) = true := by
      simp only [selS, decide_eq_true_eq]
      show (if s.val = 0 then 0 else s.val + 1) < CN + 2
      have := s.isLt
      split <;> omega
    rw [if_pos h, wenc_H_s]; rfl
  · rw [if_pos (by decide), wenc_H_c]
  · have h : selS (rTape (ns := CN) r) = false := by simp [selS, rTape]
    rw [if_neg (by simp [h]), wenc_H_r, wenc_H_r]; rfl

theorem selS_zero (cap : ℕ) (σ : WState CN CR) (hsh : ∀ s, σ.sh s = 0) :
    ∀ i, selS i = true → (wenc cap σ).H i = 0 := by
  intro i hi
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s, hsh]
  · rw [wenc_H_c]
  · simp [selS, rTape] at hi

namespace Lay
variable (L : Lay)

/-- The layout's heads at a program state: the program's heads, every other head at `0`. -/
def gHead (σ : WState CN CR) : Fin L.U → ℕ :=
  Fin.addCases (Fin.addCases (wenc 0 σ).H (fun _ : Fin 1 => 0)) (fun _ : Fin L.X => 0)

/-- The layout's bank at a program state: the program's tapes, the record `0^m`, the rest `R`. -/
def gBank (cap : ℕ) (σ : WState CN CR) (m : ℕ) (R : Fin L.X → List Bool) : Fin L.U → List Bool :=
  Fin.addCases (Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate m false)) R

theorem cast_wm (j : Fin WT) : Fin.castAdd L.X (Fin.castAdd 1 j) = L.wm j := Fin.ext rfl

theorem cast_rec (u : Fin 1) : Fin.castAdd L.X (Fin.natAdd WT u) = L.wrec := by
  apply Fin.ext
  rw [Subsingleton.elim u 0]
  rfl

/-- **A masked phase, embedded**: the rest of the layout kept. -/
theorem ph_run (P : Prog WT) (cap c : ℕ) (b : Bank WT) (τ : WState CN CR) (hb : ∀ i, selS i = true → b.H i = 0)
    (h : Exec P b (wenc cap τ) c) (k : ℕ) (R : Fin L.X → List Bool) :
    ∃ m, Step (TapeEmbedding.machine L.X (phM P)) (2 * c + 2)
      (Fin.addCases (Fin.addCases b.H (fun _ : Fin 1 => 0)) (fun _ : Fin L.X => 0))
      (Fin.addCases (Fin.addCases b.A (fun _ : Fin 1 => List.replicate k false)) R)
      (L.gHead (rs τ)) (L.gBank cap (rs τ) m R) := by
  obtain ⟨m, hm⟩ := maskBlank h.step selS hb k
  refine ⟨m, ?_⟩
  have e := (Step.congr (hout' := Fin.addCases (wenc 0 (rs τ)).H (fun _ : Fin 1 => 0)) hm
    (by rw [selS_H]) rfl).embed (fun _ : Fin L.X => 0) R
  exact e

/-- The bank as program tapes, record and rest. -/
theorem bank_split (B : Fin L.U → List Bool) (cap : ℕ) (σ : WState CN CR) (m : ℕ)
    (hw : ∀ j : Fin WT, B (L.wm j) = (wenc cap σ).A j) (hr : B L.wrec = List.replicate m false) :
    B = L.gBank cap σ m (fun x => B (Fin.natAdd (WT + 1) x)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun x => ?_) i
  · unfold gBank
    rw [Fin.addCases_left]
    refine Fin.addCases (fun j' => ?_) (fun u => ?_) j
    · rw [Fin.addCases_left, L.cast_wm]; exact hw j'
    · rw [Fin.addCases_right, L.cast_rec]; exact hr
  · unfold gBank
    rw [Fin.addCases_right]

theorem gBank_wm (cap : ℕ) (σ : WState CN CR) (m : ℕ) (R : Fin L.X → List Bool) (j : Fin WT) :
    L.gBank cap σ m R (L.wm j) = (wenc cap σ).A j := by
  rw [← L.cast_wm]; unfold gBank; rw [Fin.addCases_left, Fin.addCases_left]

theorem gBank_rec (cap : ℕ) (σ : WState CN CR) (m : ℕ) (R : Fin L.X → List Bool) :
    L.gBank cap σ m R L.wrec = List.replicate m false := by
  rw [← L.cast_rec 0]; unfold gBank; rw [Fin.addCases_left, Fin.addCases_right]

theorem gBank_x (cap : ℕ) (σ : WState CN CR) (m : ℕ) (R : Fin L.X → List Bool) (i : Fin L.U) (hi : WT + 1 ≤ i.val) :
    L.gBank cap σ m R i = R ⟨i.val - (WT + 1), by have hl : i.val < WT + 1 + L.X := i.isLt; omega⟩ := by
  have e : i = Fin.natAdd (WT + 1) (⟨i.val - (WT + 1), by have hl : i.val < WT + 1 + L.X := i.isLt; omega⟩ : Fin L.X) :=
    Fin.ext (by simp; omega)
  conv_lhs => rw [e]
  unfold gBank; rw [Fin.addCases_right]

theorem gHead_ws (σ : WState CN CR) (s : Fin (CN + 1)) : L.gHead σ (L.ws s) = σ.sh s := by
  unfold ws gHead
  rw [← L.cast_wm, Fin.addCases_left, Fin.addCases_left, wenc_H_s]

theorem gHead_x (σ : WState CN CR) (i : Fin L.U) (hi : WT + 1 ≤ i.val) : L.gHead σ i = 0 := by
  have e : i = Fin.natAdd (WT + 1) (⟨i.val - (WT + 1), by have hl : i.val < WT + 1 + L.X := i.isLt; omega⟩ : Fin L.X) :=
    Fin.ext (by simp; omega)
  rw [e]; unfold gHead; rw [Fin.addCases_right]

/-- **The first phase**: the fill, then the first program, from the bank before the fill. -/
theorem ph1_run (B : Fin L.U → List Bool) (st : Fin (CN + 1) → List Bool) (hI : L.Inv B st L.oA) (W : ℕ)
    (hct : st cCT = List.replicate W true) (haux : st cAUX = []) (τ : WState CN CR) (c : ℕ)
    (h : WExec (2 * W + 2) wm1 (σF st W) τ c) :
    ∃ m, Step (TapeEmbedding.machine L.X (phM (Prog.seq fillC wm1.toProg))) (2 * (11 * W + 20 + 1 + 1 + 1 + c) + 2)
      (fun _ => 0) B (L.gHead (rs τ)) (L.gBank (2 * W + 2) (rs τ) m (fun x => B (Fin.natAdd (WT + 1) x))) := by
  obtain ⟨hs, hc, hr, hrc, _⟩ := hI
  have e := Exec.seq (fillC_exec st W hct haux) (WExec.exec (2 * W + 2) h)
  obtain ⟨m, hm⟩ := L.ph_run _ (2 * W + 2) _ ⟨fun _ => 0, rawC st⟩ τ (fun _ _ => rfl) e 0
    (fun x => B (Fin.natAdd (WT + 1) x))
  refine ⟨m, Step.congr_in hm ?_ ?_⟩
  · funext i
    refine Fin.addCases (fun j => ?_) (fun x => ?_) i
    · rw [Fin.addCases_left]
      refine Fin.addCases (fun j' => ?_) (fun u => ?_) j <;> simp
    · rw [Fin.addCases_right]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun x => ?_) i
    · rw [Fin.addCases_left]
      refine Fin.addCases (fun j' => ?_) (fun u => ?_) j
      · rw [Fin.addCases_left, L.cast_wm]
        rcases tape_cases j' with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
        · show rawC st _ = _; rw [rawC_s]; exact (hs s).symm
        · show rawC st (cTape (ns := CN) (nr := CR)) = _; rw [rawC_c]; exact hc.symm
        · show rawC st _ = _; rw [rawC_r]; exact (hr r).symm
      · rw [Fin.addCases_right, L.cast_rec]; exact hrc.symm
    · rw [Fin.addCases_right]

end Lay

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
