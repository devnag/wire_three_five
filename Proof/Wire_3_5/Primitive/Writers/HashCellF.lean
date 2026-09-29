import Proof.Wire_3_5.Primitive.Writers.HashCellA
import Proof.Wire_3_5.Primitive.SeedFix.C4SH

/-! # HASH setup (C), P2b part 5: the HASH cell's fill (the registers at capacity `2W + 2`)

P3:3011-3016 (the setup before the loop): the HASH cell is a register program on one fresh cell; its registers are
filled at capacity `2W + 2` from the count `1^W` (`W = 2^{capExp2 C n}`, the numbers cell's capacity, P1's front copy)
by C6's `FrontFill.fillP` on two extra tapes (the C4SH `fillB` pattern, here on the layout `LNS x` with the count
`1^V` of the docks raw on stream `2`): from the request on stream `0`, the data word `u` on `113`, `1^V` on `2` and
`1^W` on the count, the state `blankCellD x w [] V u` at capacity `2W + 2`, the fill's two tapes beside it.

* `BT`, `BX`, `bIn`, `bCnt`, `bAux`, `bTgt`, `bW`, `fillX`, `rawX`, `xB`; **`fillX_exec`**.

Paper quantity of the main type: none (the cell's register capacity `2W + 2`; the cell's words are the consumers'). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

section Fill
variable (x : ℕ)

/-- The program's tapes. -/
abbrev BT : ℕ := LNS x + 2 + LNR
/-- Plus the fill count and its marker. -/
abbrev BX : ℕ := BT x + 2

def bIn (i : Fin (BT x)) : Fin (BX x) := Fin.castAdd 2 i
def bCnt : Fin (BX x) := Fin.natAdd (BT x) 0
def bAux : Fin (BX x) := Fin.natAdd (BT x) 1
/-- The fill's targets: the register tapes. -/
def bTgt (i : Fin (BX x)) : Bool := decide (LNS x + 2 ≤ i.val ∧ i.val < BT x)

theorem bIn_val (i : Fin (BT x)) : (bIn x i).val = i.val := rfl
theorem bCnt_val : (bCnt x).val = BT x := rfl
theorem bAux_val : (bAux x).val = BT x + 1 := rfl

/-- The writes after the fill: the cell and the output stream `[false]`. -/
def bW : Fin (BX x) → Option Bool := fun i =>
  if i = bIn x cTape then some false else if i = bIn x (sTape (sk x 1)) then some false else none

/-- **The fill, the cell and the output stream.** -/
def fillX : Prog (BX x) :=
  .seq (UnionMachine.FrontFill.fillP (bCnt x) (bAux x) (bTgt x)) (.act (bW x) (fun _ => .stay))

/-- The cell's entry bank: the framed request on stream `0`, the data word on `113`, `1^V` on `2`, `1^W` on the
count. -/
def rawX (w u : List Bool) (V W : ℕ) : Fin (BX x) → List Bool := fun i =>
  if i = bIn x (sTape (sk x 0)) then RepairOrdinary.frame w else if i = bIn x (sTape (sk x 113)) then u
  else if i = bIn x (sTape (sk x 2)) then List.replicate V true
  else if i = bCnt x then List.replicate W true else []

/-- The fill's two tapes after the fill. -/
def xB (W : ℕ) : Fin 2 → List Bool := ![List.replicate W true, List.replicate (2 * W + 3) false]

theorem bIn_ne_cnt (i : Fin (BT x)) : bIn x i ≠ bCnt x := fun e => by
  have := congrArg Fin.val e; rw [bIn_val, bCnt_val] at this; have := i.isLt; omega
theorem bIn_ne_aux (i : Fin (BT x)) : bIn x i ≠ bAux x := fun e => by
  have := congrArg Fin.val e; rw [bIn_val, bAux_val] at this; have := i.isLt; omega
theorem bIn_inj {i j : Fin (BT x)} (h : bIn x i = bIn x j) : i = j :=
  Fin.ext (by have := congrArg Fin.val h; rwa [bIn_val, bIn_val] at this)

theorem sTne (a b : Fin 161) (h : a.val ≠ b.val) : sTape (nr := LNR) (sk x a) ≠ sTape (sk x b) :=
  fun e => skne x a b h (sTape_inj e)

theorem nA0 (h : 0 < 2) : (Fin.natAdd (BT x) (⟨0, h⟩ : Fin 2) : Fin (BX x)) = bCnt x := rfl
theorem nA1 (h : 1 < 2) : (Fin.natAdd (BT x) (⟨1, h⟩ : Fin 2) : Fin (BX x)) = bAux x := rfl

theorem sTsk_le (k : Fin 161) : (sTape (nr := LNR) (sk x k)).val ≤ LNS x + 1 := by
  rw [sTape_val, sk_val]; have := k.isLt; unfold LNS; split_ifs <;> omega

/-- The fill's exit bank. -/
def fillOut (w u : List Bool) (V W : ℕ) : Bank (BX x) :=
  ⟨Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD x w [] V u)).H (fun _ : Fin 2 => 0),
    Fin.addCases (wenc (2 * W + 2) (CellLoopD.blankCellD x w [] V u)).A (xB W)⟩

theorem bcX_st (w u : List Bool) (V : ℕ) (s : Fin (LNS x + 1)) (h0 : s ≠ sk x 0) (h1 : s ≠ sk x 1)
    (h2 : s ≠ sk x 2) (h3 : s ≠ sk x 113) : (CellLoopD.blankCellD x w [] V u).st s = [] := by
  simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, h0, h1, h2, h3]

/-- **The fill, run**: from the entry bank to `blankCellD x w [] V u` at capacity `2W + 2`, the fill's two tapes beside
it. -/
theorem fillX_exec (w u : List Bool) (V W : ℕ) :
    Exec (fillX x) ⟨fun _ => 0, rawX x w u V W⟩ (fillOut x w u V W) (11 * W + 20 + 1 + 1) := by
  have hca : bCnt x ≠ bAux x := fun e => by have := congrArg Fin.val e; rw [bCnt_val, bAux_val] at this; omega
  have hct : bTgt x (bCnt x) = false := by simp [bTgt, bCnt_val]
  have hat : bTgt x (bAux x) = false := by simp [bTgt, bAux_val]
  have n01 : sk x 0 ≠ sk x 1 := skne x 0 1 (by decide)
  have n02 : sk x 0 ≠ sk x 2 := skne x 0 2 (by decide)
  have n0B : sk x 0 ≠ sk x 113 := skne x 0 113 (by decide)
  have n12 : sk x 1 ≠ sk x 2 := skne x 1 2 (by decide)
  have n1B : sk x 1 ≠ sk x 113 := skne x 1 113 (by decide)
  have n2B : sk x 2 ≠ sk x 113 := skne x 2 113 (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (bAux x) (bTgt x) i → rawX x w u V W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · simp only [bTgt, decide_eq_true_eq] at hi
      have m0 : i ≠ bIn x (sTape (sk x 0)) := fun e => by rw [e, bIn_val] at hi; have := sTsk_le x 0; omega
      have m1 : i ≠ bIn x (sTape (sk x 113)) := fun e => by rw [e, bIn_val] at hi; have := sTsk_le x 113; omega
      have m2 : i ≠ bIn x (sTape (sk x 2)) := fun e => by rw [e, bIn_val] at hi; have := sTsk_le x 2; omega
      have m3 : i ≠ bCnt x := fun e => by rw [e, bCnt_val] at hi; omega
      simp [rawX, m0, m1, m2, m3]
    · subst hi
      simp [rawX, (bIn_ne_aux x _).symm, hca.symm]
  have e1 := UnionMachine.FrontFill.fillP_exec (bCnt x) (bAux x) (bTgt x) (fun _ => 0) (rawX x w u V W) hca hct hat W
    (by simp [rawX, (bIn_ne_cnt x _).symm]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (bCnt x) (bAux x) (bTgt x) (fun _ => 0) (rawX x w u V W) W 0)
    (bW x) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (bCnt x) (bAux x) (bTgt x) (fun _ => 0) (rawX x w u V W) W 0).act (bW x)
      (fun _ => .stay) = fillOut x w u V W := by
   apply Bank.ext'
   · intro j
     simp only [fillOut, Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
     refine Fin.addCases (fun a => ?_) (fun b => ?_) j
     · rw [Fin.addCases_left]
       have ha : Fin.castAdd 2 a ≠ bCnt x := bIn_ne_cnt x a
       rcases tape_cases a with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
       · rw [wenc_H_s]
         simp only [if_neg ha]
         split_ifs <;> simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply] <;>
           split_ifs <;> simp
       · rw [wenc_H_c]; simp only [if_neg ha]; split_ifs <;> rfl
       · rw [wenc_H_r]; simp only [if_neg ha]; split_ifs <;> simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
     · rw [Fin.addCases_right]
       fin_cases b
       · show (if bCnt x = bCnt x then _ else _) = 0; simp
       · show (if bAux x = bCnt x then _ else _) = 0
         rw [if_neg hca.symm]
         simp [UnionMachine.FrontFill.side]
   · intro j
     simp only [fillOut, Bank.act, UnionMachine.FrontFill.stB]
     refine Fin.addCases (fun a => ?_) (fun b => ?_) j
     · rw [Fin.addCases_left]
       rcases tape_cases a with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
       · rw [wenc_A_s]
         have htg : bTgt x (Fin.castAdd 2 (sTape (nr := LNR) s)) = false := by
           simp only [bTgt, decide_eq_false_iff_not, not_and, not_lt]
           intro h; have := (sTape (nr := LNR) s).isLt; simp [sTape_val] at h ⊢; split_ifs at h <;> omega
         have nc : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 cTape := fun e => sTape_ne_c s (bIn_inj x e)
         have nca : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ bAux x := bIn_ne_aux x _
         have ncc : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ bCnt x := bIn_ne_cnt x _
         simp only [bW, bIn, htg, Bool.false_eq_true, if_false, nca, ncc, nc]
         by_cases h1 : s = sk x 1
         · subst h1
           have q0 : Fin.castAdd 2 (sTape (nr := LNR) (sk x 1)) ≠ Fin.castAdd 2 (sTape (sk x 0)) :=
             fun e => n01.symm (sTape_inj (bIn_inj x e))
           have q1 : Fin.castAdd 2 (sTape (nr := LNR) (sk x 1)) ≠ Fin.castAdd 2 (sTape (sk x 113)) :=
             fun e => n1B (sTape_inj (bIn_inj x e))
           have q2 : Fin.castAdd 2 (sTape (nr := LNR) (sk x 1)) ≠ Fin.castAdd 2 (sTape (sk x 2)) :=
             fun e => n12 (sTape_inj (bIn_inj x e))
           simp [rawX, bIn, q0, q1, q2, ncc, writeTapeBit, CellLoopD.blankCellD, CellState.blankCell, WState.sets,
             Function.update_apply, n1B, n01.symm, n12]
         · have n1 : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 (sTape (sk x 1)) :=
             fun e => h1 (sTape_inj (bIn_inj x e))
           simp only [n1, if_false, rawX, bIn]
           by_cases h0 : s = sk x 0
           · subst h0
             simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0B]
           · have m0 : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 (sTape (sk x 0)) :=
               fun e => h0 (sTape_inj (bIn_inj x e))
             by_cases h113 : s = sk x 113
             · subst h113
               have q : sTape (nr := LNR) (sk x 113) ≠ sTape (sk x 0) := sTne x 113 0 (by decide)
               simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0B.symm, q]
             · have m1 : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 (sTape (sk x 113)) :=
                 fun e => h113 (sTape_inj (bIn_inj x e))
               simp only [m0, m1, if_false]
               by_cases h2 : s = sk x 2
               · subst h2
                 simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n2B, n02.symm,
                   n12.symm]
               · have m2 : Fin.castAdd 2 (sTape (nr := LNR) s) ≠ Fin.castAdd 2 (sTape (sk x 2)) :=
                   fun e => h2 (sTape_inj (bIn_inj x e))
                 simp only [m2, if_false, ncc]
                 rw [bcX_st x w u V s h0 h1 h2 h113]
       · rw [wenc_A_c]
         have htg : bTgt x (Fin.castAdd 2 (cTape (ns := LNS x) (nr := LNR))) = false := by
           simp [bTgt, cTape_val]
         simp only [bW, htg, Bool.false_eq_true, if_false, bIn_ne_aux, if_true]
         have n0 : bIn x (cTape (ns := LNS x) (nr := LNR)) ≠ bIn x (sTape (sk x 0)) :=
           fun e => sTape_ne_c _ (bIn_inj x e).symm
         have n1 : bIn x (cTape (ns := LNS x) (nr := LNR)) ≠ bIn x (sTape (sk x 113)) :=
           fun e => sTape_ne_c _ (bIn_inj x e).symm
         have n2 : bIn x (cTape (ns := LNS x) (nr := LNR)) ≠ bIn x (sTape (sk x 2)) :=
           fun e => sTape_ne_c _ (bIn_inj x e).symm
         have c0 : cTape (ns := LNS x) (nr := LNR) ≠ sTape (sk x 0) := (sTape_ne_c _).symm
         have c1 : cTape (ns := LNS x) (nr := LNR) ≠ sTape (sk x 113) := (sTape_ne_c _).symm
         have c2 : cTape (ns := LNS x) (nr := LNR) ≠ sTape (sk x 2) := (sTape_ne_c _).symm
         have d1 : Fin.castAdd 2 (cTape (ns := LNS x) (nr := LNR)) ≠ bAux x := bIn_ne_aux x _
         have d2 : Fin.castAdd 2 (cTape (ns := LNS x) (nr := LNR)) ≠ bCnt x := bIn_ne_cnt x _
         simp [rawX, bIn, c0, c1, c2, d1, d2, writeTapeBit, CellLoopD.blankCellD, CellState.blankCell, WState.sets]
       · rw [wenc_A_r]
         have htg : bTgt x (Fin.castAdd 2 (rTape (ns := LNS x) r)) = true := by
           simp [bTgt, rTape_val]
         simp only [htg, if_true]
         have n0 : Fin.castAdd 2 (rTape (ns := LNS x) r) ≠ bIn x cTape := fun e => cTape_ne_r r (bIn_inj x e).symm
         have n1 : Fin.castAdd 2 (rTape (ns := LNS x) r) ≠ bIn x (sTape (sk x 1)) := fun e => by
           have := congrArg Fin.val (bIn_inj x e); simp [rTape_val, sTape_val, sk_val] at this; omega
         simp only [bW, n0, n1, if_false]
         simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, regTape_zero]
     · rw [Fin.addCases_right]
       fin_cases b
       · simp only [nA0]
         have d0 : bCnt x ≠ Fin.castAdd 2 (cTape (ns := LNS x) (nr := LNR)) := (bIn_ne_cnt x _).symm
         have d1 : bCnt x ≠ Fin.castAdd 2 (sTape (nr := LNR) (sk x 1)) := (bIn_ne_cnt x _).symm
         have d2 : bCnt x ≠ Fin.castAdd 2 (sTape (nr := LNR) (sk x 0)) := (bIn_ne_cnt x _).symm
         have d3 : bCnt x ≠ Fin.castAdd 2 (sTape (nr := LNR) (sk x 113)) := (bIn_ne_cnt x _).symm
         have d4 : bCnt x ≠ Fin.castAdd 2 (sTape (nr := LNR) (sk x 2)) := (bIn_ne_cnt x _).symm
         simp [bW, xB, rawX, bIn, hct, UnionMachine.FrontFill.side, hca, d0, d1, d2, d3, d4]
       · simp only [nA1]
         have d0 : bAux x ≠ Fin.castAdd 2 (cTape (ns := LNS x) (nr := LNR)) := (bIn_ne_aux x _).symm
         have d1 : bAux x ≠ Fin.castAdd 2 (sTape (nr := LNR) (sk x 1)) := (bIn_ne_aux x _).symm
         simp [bW, xB, bIn, hat, hca.symm, d0, d1]
  rw [← eB]
  exact Exec.seq e1 e2

end Fill

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
