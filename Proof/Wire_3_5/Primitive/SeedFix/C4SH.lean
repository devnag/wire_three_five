import Proof.Wire_3_5.Primitive.SeedFix.C4SG

/-! # C4 per-call setup (item 3), part 8: the SYM numbers machine (fill, program, every head back at `0`)

P3:2987-2988, 3011-3016, 2929-2941 (as parts 2–7): the program `bigW F` as a machine in NumsX's pattern (`nums_step`):
C6's fill (`FrontFill.fillP`, the registers at capacity `2W + 2` from the count `1^W` on an extra tape), the cell and
the decode's output stream `[false]`, the program (the fill's two tapes kept beside it), PA's masked reset:

* `BT`, `BX`, `bIn`, `bCnt`, `bAux`, `bTgt`, `fillB`, `rawB`, **`fillB_exec`**; `bigM`, **`big_step`**.

Paper quantities of the main type: the words of `bigS_spec` (the enumeration's rulers and constants, the generator's
inputs, the compiler request's numbers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- The program's tapes. -/
abbrev BT : ℕ := LNS 0 + 2 + LNR
/-- Plus the fill count and its marker. -/
abbrev BX : ℕ := BT + 2

def bIn (i : Fin BT) : Fin BX := Fin.castAdd 2 i
def bCnt : Fin BX := Fin.natAdd BT 0
def bAux : Fin BX := Fin.natAdd BT 1
/-- The fill's targets: the register tapes. -/
def bTgt (i : Fin BX) : Bool := decide (LNS 0 + 2 ≤ i.val ∧ i.val < BT)

theorem bIn_val (i : Fin BT) : (bIn i).val = i.val := rfl
theorem bCnt_val : bCnt.val = BT := rfl
theorem bAux_val : bAux.val = BT + 1 := rfl

/-- The writes after the fill: the cell and the decode's output stream `[false]`. -/
def bW : Fin BX → Option Bool := fun i =>
  if i = bIn cTape then some false else if i = bIn (sTape (sk 0 1)) then some false else none

/-- **The fill, the cell and the decode's output stream**. -/
def fillB : Prog BX :=
  .seq (UnionMachine.FrontFill.fillP bCnt bAux bTgt) (.act bW (fun _ => .stay))

/-- The machine's entry bank: the framed request on stream `0`, the counts on stream `113`, `1^W` on the count. -/
def rawB (w u : List Bool) (W : ℕ) : Fin BX → List Bool := fun i =>
  if i = bIn (sTape (sk 0 0)) then RepairOrdinary.frame w else if i = bIn (sTape (sk 0 113)) then u
  else if i = bCnt then List.replicate W true else []

/-- The fill's two tapes after the fill. -/
def xB (W : ℕ) : Fin 2 → List Bool := ![List.replicate W true, List.replicate (2 * W + 3) false]

theorem bIn_ne_cnt (i : Fin BT) : bIn i ≠ bCnt := fun e => by
  have := congrArg Fin.val e; rw [bIn_val, bCnt_val] at this; have := i.isLt; omega
theorem bIn_ne_aux (i : Fin BT) : bIn i ≠ bAux := fun e => by
  have := congrArg Fin.val e; rw [bIn_val, bAux_val] at this; have := i.isLt; omega
theorem bIn_inj {i j : Fin BT} (h : bIn i = bIn j) : i = j :=
  Fin.ext (by have := congrArg Fin.val h; rwa [bIn_val, bIn_val] at this)

theorem sk_ne (a b : Fin 161) (h : a ≠ b) : sk 0 a ≠ sk 0 b := fun e => h (by
  have := congrArg Fin.val e; simp [sk] at this; exact Fin.ext this)

@[simp] theorem cA_cnt (i : Fin BT) : (Fin.castAdd 2 i = bCnt) ↔ False := ⟨fun e => bIn_ne_cnt i e, False.elim⟩
@[simp] theorem cA_aux (i : Fin BT) : (Fin.castAdd 2 i = bAux) ↔ False := ⟨fun e => bIn_ne_aux i e, False.elim⟩
@[simp] theorem cnt_cA (i : Fin BT) : (bCnt = Fin.castAdd 2 i) ↔ False := ⟨fun e => bIn_ne_cnt i e.symm, False.elim⟩
@[simp] theorem aux_cA (i : Fin BT) : (bAux = Fin.castAdd 2 i) ↔ False := ⟨fun e => bIn_ne_aux i e.symm, False.elim⟩
theorem nA0 (h : 0 < 2) : (Fin.natAdd BT (⟨0, h⟩ : Fin 2) : Fin BX) = bCnt := rfl
theorem nA1 (h : 1 < 2) : (Fin.natAdd BT (⟨1, h⟩ : Fin 2) : Fin BX) = bAux := rfl
@[simp] theorem cA_inj (i j : Fin BT) : (Fin.castAdd 2 i = Fin.castAdd 2 j) ↔ i = j := ⟨fun e => bIn_inj e, fun e => e ▸ rfl⟩
@[simp] theorem Wsub (W : ℕ) : W - (2 * W + 3) = 0 := by omega

theorem sT_ne (a b : Fin 161) (h : a ≠ b) : sTape (nr := LNR) (sk 0 a) ≠ sTape (sk 0 b) :=
  fun e => sk_ne a b h (sTape_inj e)

theorem bc_st (w u : List Bool) (s : Fin (LNS 0 + 1)) (h0 : s ≠ sk 0 0) (h1 : s ≠ sk 0 1) (h2 : s ≠ sk 0 2)
    (h3 : s ≠ sk 0 113) : (CellLoopD.blankCellD 0 w [] 0 u).st s = [] := by
  simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, h0, h1, h2, h3]

/-- **The fill, run**: from the entry bank to the register-language state `blankCellD 0 w [] 0 u` at capacity `2W + 2`
(the fill's two tapes beside it). -/
theorem fillB_exec (w u : List Bool) (W : ℕ) :
    Exec fillB ⟨fun _ => 0, rawB w u W⟩
      ⟨Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD 0 w [] 0 u)).H (fun _ : Fin 2 => 0),
        Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD 0 w [] 0 u)).A (xB W)⟩ (11 * W + 20 + 1 + 1) := by
  have hca : bCnt ≠ bAux := fun e => by have := congrArg Fin.val e; rw [bCnt_val, bAux_val] at this; omega
  have hct : bTgt bCnt = false := by simp [bTgt, bCnt_val]
  have hat : bTgt bAux = false := by simp [bTgt, bAux_val]
  have hA : ∀ i, UnionMachine.FrontFill.side bAux bTgt i → rawB w u W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · simp only [bTgt, decide_eq_true_eq] at hi
      have n0 : i ≠ bIn (sTape (sk 0 0)) := fun e => by rw [e, bIn_val] at hi; simp [sTape_val, sk] at hi
      have n1 : i ≠ bIn (sTape (sk 0 113)) := fun e => by rw [e, bIn_val] at hi; simp [sTape_val, sk] at hi
      have n2 : i ≠ bCnt := fun e => by rw [e, bCnt_val] at hi; omega
      simp [rawB, n0, n1, n2]
    · subst hi; simp [rawB, (bIn_ne_aux _).symm, hca.symm]
  have e1 := UnionMachine.FrontFill.fillP_exec bCnt bAux bTgt (fun _ => 0) (rawB w u W) hca hct hat W
    (by simp [rawB, (bIn_ne_cnt _).symm]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB bCnt bAux bTgt (fun _ => 0) (rawB w u W) W 0) bW (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB bCnt bAux bTgt (fun _ => 0) (rawB w u W) W 0).act bW (fun _ => .stay) =
      ⟨Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD 0 w [] 0 u)).H (fun _ : Fin 2 => 0),
        Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD 0 w [] 0 u)).A (xB W)⟩ := by
   apply Bank.ext'
   · intro j
     simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
     refine Fin.addCases (fun a => ?_) (fun b => ?_) j
     · rw [Fin.addCases_left]
       have ha : Fin.castAdd 2 a ≠ bCnt := bIn_ne_cnt a
       rcases tape_cases a with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
       · rw [wenc_H_s]
         simp only [if_neg ha]
         split_ifs <;> simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply] <;>
           split_ifs <;> simp
       · rw [wenc_H_c]; simp only [if_neg ha]; split_ifs <;> rfl
       · rw [wenc_H_r]; simp only [if_neg ha]; split_ifs <;> simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
     · rw [Fin.addCases_right]
       fin_cases b
       · show (if bCnt = bCnt then _ else _) = 0; simp
       · show (if bAux = bCnt then _ else _) = 0
         rw [if_neg hca.symm]
         simp [UnionMachine.FrontFill.side]
   · intro j
     simp only [Bank.act, UnionMachine.FrontFill.stB]
     refine Fin.addCases (fun a => ?_) (fun b => ?_) j
     · rw [Fin.addCases_left]
       rcases tape_cases a with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
       · rw [wenc_A_s]
         have htg : bTgt (Fin.castAdd 2 (sTape s)) = false := by
           simp only [bTgt, decide_eq_false_iff_not, not_and, not_lt]
           intro h; have := (sTape (nr := LNR) s).isLt; simp [sTape_val] at h ⊢; split_ifs at h <;> omega
         have nc : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 cTape := fun e => sTape_ne_c s (bIn_inj e)
         simp only [bW, bIn, htg, Bool.false_eq_true, if_false, cA_aux, cA_cnt, nc, cA_inj, Wsub]
         by_cases h1 : s = sk 0 1
         · subst h1
           simp [rawB, bIn, sT_ne 1 0 (by decide), sT_ne 1 113 (by decide), writeTapeBit,
             CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, sk_ne 1 113 (by decide),
             sk_ne 1 0 (by decide), sk_ne 1 2 (by decide)]
         · have n1 : sTape (nr := LNR) s ≠ sTape (sk 0 1) := fun e => h1 (sTape_inj e)
           simp only [n1, if_false, rawB, bIn, cA_inj, cA_cnt, if_false]
           by_cases h0 : s = sk 0 0
           · subst h0; simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply,
               sk_ne 0 113 (by decide)]
           · have m0 : sTape (nr := LNR) s ≠ sTape (sk 0 0) := fun e => h0 (sTape_inj e)
             by_cases h113 : s = sk 0 113
             · subst h113
               simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, sT_ne 113 0 (by decide)]
             · have m1 : sTape (nr := LNR) s ≠ sTape (sk 0 113) := fun e => h113 (sTape_inj e)
               simp only [m0, m1, if_false]
               by_cases h2 : s = sk 0 2
               · subst h2
                 simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply,
                   sk_ne 2 113 (by decide), sk_ne 2 0 (by decide), sk_ne 2 1 (by decide)]
               · rw [bc_st w u s h0 h1 h2 h113]
       · rw [wenc_A_c]
         have htg : bTgt (Fin.castAdd 2 (cTape (ns := LNS 0) (nr := LNR))) = false := by
           simp [bTgt, cTape_val]
         simp only [bW, htg, Bool.false_eq_true, if_false, bIn_ne_aux, if_true]
         have n0 : bIn (cTape (ns := LNS 0) (nr := LNR)) ≠ bIn (sTape (sk 0 0)) := fun e => sTape_ne_c _ (bIn_inj e).symm
         have n1 : bIn (cTape (ns := LNS 0) (nr := LNR)) ≠ bIn (sTape (sk 0 113)) := fun e => sTape_ne_c _ (bIn_inj e).symm
         have c0 : cTape (ns := LNS 0) (nr := LNR) ≠ sTape (sk 0 0) := (sTape_ne_c _).symm
         have c1 : cTape (ns := LNS 0) (nr := LNR) ≠ sTape (sk 0 113) := (sTape_ne_c _).symm
         simp [rawB, bIn, c0, c1, writeTapeBit, CellLoopD.blankCellD, CellState.blankCell, WState.sets]
       · rw [wenc_A_r]
         have htg : bTgt (Fin.castAdd 2 (rTape (ns := LNS 0) r)) = true := by
           simp [bTgt, rTape_val]
         simp only [htg, if_true]
         have n0 : Fin.castAdd 2 (rTape (ns := LNS 0) r) ≠ bIn cTape := fun e => cTape_ne_r r (bIn_inj e).symm
         have n1 : Fin.castAdd 2 (rTape (ns := LNS 0) r) ≠ bIn (sTape (sk 0 1)) := fun e => by
           have := congrArg Fin.val (bIn_inj e); simp [rTape_val, sTape_val, sk] at this; omega
         simp only [bW, n0, n1, if_false]
         simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, regTape_zero]
     · rw [Fin.addCases_right]
       fin_cases b
       · simp only [nA0]
         simp [bW, xB, rawB, bIn, hct, UnionMachine.FrontFill.side, hca]
       · simp only [nA1]
         simp [bW, xB, bIn, hat, hca.symm]

  rw [← eB]
  exact Exec.seq e1 e2

/-- The stage before its teardown: the fill, then the program (the fill's two tapes kept beside it). -/
noncomputable def bigP (P : WM (LNS 0) LNR) :=
  Composition.machine fillB.compile (TapeEmbedding.machine 2 P.toProg.compile)

/-- **The numbers machine** of a program on PA's SYM layout (every head back at `0`). -/
noncomputable def bigM (P : WM (LNS 0) LNR) := MaskedReset.machine (bigP P) (fun _ => true)

/-- The numbers machine's step bound from the program's. -/
def bigCost (W c : ℕ) : ℕ := 2 * (11 * W + 20 + 1 + 1 + 1 + c) + 2

/-- **The numbers machine's run**: from the framed request on stream `0`, the counts `u` on stream `113` and `1^W` on
the fill count, every head back at `0`, the program's exit state at capacity `2W + 2` on the program's tapes, the
fill's two tapes beside it, the teardown's log. -/
theorem big_step (P : WM (LNS 0) LNR) (w u : List Bool) (W : ℕ) (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * W + 2) P (CellLoopD.blankCellD 0 w [] 0 u) τ c) :
    ∃ m, Step (bigM P) (bigCost W c) (fun _ => 0) (Fin.addCases (rawB w u W) (fun _ : Fin 1 => []))
      (fun _ => 0) (Fin.addCases (Fin.addCases (wenc (2 * W + 2) τ).A (xB W)) (fun _ : Fin 1 => List.replicate m false)) := by
  have s0 := Exec.step (fillB_exec w u W)
  have s1 := (Exec.step (WExec.exec (2 * W + 2) hx)).embed (fun _ : Fin 2 => 0) (xB W)
  have core : Step (bigP P) (11 * W + 20 + 1 + 1 + 1 + c) (fun _ => 0) (rawB w u W)
      (Fin.addCases (wenc (2 * W + 2) τ).H (fun _ : Fin 2 => 0)) (Fin.addCases (wenc (2 * W + 2) τ).A (xB W)) :=
    s0.seq s1
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (BX + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i : Fin BX => if (fun _ => true) i = true then 0 else
      (Fin.addCases (wenc (2 * W + 2) τ).H (fun _ : Fin 2 => 0) : Fin BX → ℕ) i) (fun _ : Fin 1 => 0) : Fin (BX + 1) → ℕ) =
      fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  exact ⟨m, (hm.congr_in eh rfl).congr eh' rfl⟩

end NearCubicWires.WireExponent3_5.PrimT.C4Set
