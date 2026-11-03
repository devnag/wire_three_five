import Proof.Wire_3_5.Primitive.SeedFix.W6A
import Proof.Wire_3_5.Primitive.Writers.DataRun

/-! # W6, part 2: the numbers machine's fill on its layout

P3:2543-2558 and P3:2596-2604 (the THR call's numbers, NumsPort ports `3 … 19`): the numbers are unary values in the
layout's registers, filled once from the caller's count `1^V` (port `20`, stream `sCnt`). The fill (`W6Lay`) on
this module's layout (192 streams, 80 registers; the two programs' blocks are streams):
* `sAUX` (the fill's marker stream), `regSel6`, `rawB f` (the raw bank), `σF f V` (the filled state), `fill6`;
* **`fill6_exec`**: `fill6` runs from `rawB f` (heads `0`) to `wenc (2V+2) (σF f V)` when `f sCnt = 1^V`, `f sAUX = []`.

Paper quantity of the main type: none directly (the register capacity of the numbers machine). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- The fill's marker tape. -/
def sAUX : Fin 192 := 4

/-- The register tapes (the fill's targets). -/
def regSel6 (j : Fin (191 + 2 + 80)) : Bool := decide (191 + 2 ≤ j.val)

/-- **The raw bank**: stream `s` holds `f s`; the cell and every register tape blank. -/
def rawB (f : Fin 192 → List Bool) : Fin (191 + 2 + 80) → List Bool := fun j =>
  match role (ns := 191) (nr := 80) j with
  | .stream i => f i
  | .cell => []
  | .reg _ => []

theorem rawB_s (f : Fin 192 → List Bool) (s : Fin 192) : rawB f (sTape s) = f s := by
  simp [rawB, role_sTape]

theorem rawB_c (f : Fin 192 → List Bool) : rawB f cTape = [] := by
  simp [rawB, role_cTape]

theorem rawB_r (f : Fin 192 → List Bool) (r : Fin 80) : rawB f (rTape r) = [] := by
  simp [rawB, role_rTape]

theorem regSel6_s (s : Fin 192) : regSel6 (sTape (nr := 80) s) = false := by
  have := s.isLt
  simp only [regSel6, DockW.sTape_val, decide_eq_false_iff_not, not_le]
  split <;> omega

theorem regSel6_c : regSel6 (cTape (ns := 191) (nr := 80)) = false := by
  unfold regSel6
  rw [show (cTape (ns := 191) (nr := 80)).val = 1 from rfl]
  decide

theorem regSel6_r (r : Fin 80) : regSel6 (rTape (ns := 191) r) = true := by simp [regSel6, rTape]

/-- **The filled state**: every register `0`, the marker tape `0^{2V+3}`, the other streams `f`, heads `0`. -/
def σF (f : Fin 192 → List Bool) (V : ℕ) : WState 191 80 :=
  ⟨fun _ => 0, fun s => if s = sAUX then List.replicate (2 * V + 3) false else f s, fun _ => 0, false⟩

/-- **The fill and the cell.** -/
def fill6 : Prog (191 + 2 + 80) :=
  .seq (UnionMachine.FrontFill.fillP (sTape sCnt) (sTape sAUX) regSel6) (.act (writeAt cTape false) (fun _ => .stay))

/-- **The fill's run**: from the raw bank to the register-language state at capacity `2V + 2`. -/
theorem fill6_exec (f : Fin 192 → List Bool) (V : ℕ) (hV : f sCnt = List.replicate V true) (hA : f sAUX = []) :
    Exec fill6 ⟨fun _ => 0, rawB f⟩ (wenc (2 * V + 2) (σF f V)) (11 * V + 20 + 1 + 1) := by
  have hca : sTape (nr := 80) sCnt ≠ sTape sAUX := fun h => absurd (sTape_inj h) (by decide)
  have hside : ∀ i, UnionMachine.FrontFill.side (sTape (nr := 80) sAUX) regSel6 i → rawB f i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSel6_s] at hi; exact absurd hi (by decide)
      · rw [regSel6_c] at hi; exact absurd hi (by decide)
      · exact rawB_r f r
    · subst hi
      rw [rawB_s]
      exact hA
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape sCnt) (sTape sAUX) regSel6 (fun _ => 0) (rawB f) hca
    (regSel6_s _) (regSel6_s _) V (by rw [rawB_s]; exact hV) (fun _ _ => rfl) hside
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape sCnt) (sTape sAUX) regSel6 (fun _ => 0) (rawB f) V 0)
    (writeAt (cTape (ns := 191) (nr := 80)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape sCnt) (sTape sAUX) regSel6 (fun _ => 0) (rawB f) V 0).act
      (writeAt (cTape (ns := 191) (nr := 80)) false) (fun _ => .stay) = wenc (2 * V + 2) (σF f V) := by
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
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSel6_s,
          Bool.false_eq_true, rawB_s, σF]
        by_cases hx : s = sAUX
        · subst hx
          simp [hA]
        · have hx' : sTape (nr := 80) s ≠ sTape sAUX := fun e => hx (sTape_inj e)
          simp [hx, hx']
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSel6_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := 80) (ns := 191) s).symm, rawB_c]
        simp [σF, UnionMachine.FrontFill.side, regSel6_c, fun s => (sTape_ne_c (nr := 80) (ns := 191) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSel6_r, if_true, σF]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

end NearCubicWires.WireExponent3_5.PrimT.W6
