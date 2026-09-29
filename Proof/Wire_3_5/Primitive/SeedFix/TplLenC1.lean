import Proof.Wire_3_5.Primitive.Writers.TplLenB

/-! # TplLenC, part 1: the third part of the template length's program

`tplLenP3 O W RT` (E's `tplW` onto `O`, the output counter `W 24` into `RT`, the rewind, the clears), one step
per declaration: **`p3a_spec`** (`tplW_spec`: the raw template word appended to `O`, its length in `W 24`),
**`p3b_spec`** (the counter copied into `RT`), **`p3c_spec`** (`O` rewound by the counter), **`p3d_spec`** (the four
parameters cleared), **`p3_spec`** (the part: `RT = |word|`, every `W i` at `0`, `O` holds the word, heads and cell
kept).

Paper quantity of the main type: the stage-5 template word's length (`list:base`/`list:flatten`, P3:1449-1477; the call word `4·3 + j`, P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.TplLenC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.TplLen

section P3
variable {ns nr : ℕ} (c : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RT : Fin nr)

/-- **Step a**: the raw template word appended to `O`, its length in `W 24`. -/
theorem p3a_spec (s : WState ns nr) (M Sv J L : ℕ) (h0 : s.val (W 0) = Sv) (h1 : s.val (W 1) = J)
    (h25 : s.val (W 25) = M) (h26 : s.val (W 26) = L)
    (hz : ∀ i : Fin 30, i ≠ 0 → i ≠ 1 → i ≠ 25 → i ≠ 26 → s.val (W i) = 0) (ho : s.sh O = (s.st O).length)
    (hcap : LevelW.lvCap Sv J J ≤ c) (hw : (FinalPass.SymParts.Tmpl.tplWord M Sv J L).length ≤ c) (hJc : J + 1 ≤ c)
    (hLc : L ≤ c) (hMc : M ≤ c) :
    ∃ n, WExec c (FinalPass.SymParts.Tmpl.tplW O W) s
      (appendO s O (W 24) (FinalPass.SymParts.Tmpl.tplWord M Sv J L)) n ∧
      n ≤ FinalPass.SymParts.Tmpl.tplWBound c J M :=
  FinalPass.SymParts.Tmpl.tplW_spec c O W s M Sv J L h0 h1 h25 h26
    (fun i a b => hz i (by intro e; subst e; simp at a) (by intro e; subst e; simp at a)
      (by intro e; subst e; simp at b) (by intro e; subst e; simp at b))
    (hz 27 (by decide) (by decide) (by decide) (by decide)) (hz 28 (by decide) (by decide) (by decide) (by decide))
    (hz 29 (by decide) (by decide) (by decide) (by decide)) ho hcap
    (by rw [hz 24 (by decide) (by decide) (by decide) (by decide)]; omega) hJc hLc hMc

/-- **Step b**: the counter copied into `RT`. -/
theorem p3b_spec (hRT : ∀ i, W i ≠ RT) (a : WState ns nr) (m : ℕ) (h24 : a.val (W 24) = m) (hT : a.val RT = 0)
    (h29 : a.val (W 29) = 0) (hm : m ≤ c) :
    WExec c (FinalPass.Hash4.wcopyR (W 24) RT (W 29)) a (a.setv RT m) (UnaryPow.sq c) :=
  SparseNum.copy1 c (W 24) RT (W 29) (hRT 24) (W.injective.ne (by decide)) (fun e => hRT 29 e.symm) m a h24 hT h29 hm

/-- **Step c**: `O` rewound by the counter. -/
theorem p3c_spec (b : WState ns nr) (m : ℕ) (h24 : b.val (W 24) = m) (hm : m ≤ c) :
    WExec c (WM.rewind O (W 24)) b ((b.setv (W 24) 0).seth O (b.sh O - m)) (5 * m + 1) :=
  wrewind_spec c O (W 24) m b h24 (by omega)

/-- **Step d**: the four parameters cleared. -/
theorem p3d_spec (d : WState ns nr) (Sv J M L : ℕ) (h0 : d.val (W 0) = Sv) (h1 : d.val (W 1) = J)
    (h25 : d.val (W 25) = M) (h26 : d.val (W 26) = L) (hS : Sv ≤ c) (hJ : J ≤ c) (hM : M ≤ c) (hL : L ≤ c) :
    WExec c (.seq (WM.clear (W 0)) (.seq (WM.clear (W 1)) (.seq (WM.clear (W 25)) (WM.clear (W 26))))) d
      ((((d.setv (W 0) 0).setv (W 1) 0).setv (W 25) 0).setv (W 26) 0) (4 * UnaryPow.sq c + 3) := by
  have hne : ∀ {i j : Fin 30}, i ≠ j → W i ≠ W j := fun h => W.injective.ne h
  have e1 := SparseNum.clear1 c (W 0) Sv d h0 hS
  have e2 := SparseNum.clear1 c (W 1) J (d.setv (W 0) 0)
    (by simp [Function.update_of_ne (hne (show (1 : Fin 30) ≠ 0 by decide)), h1]) hJ
  have e3 := SparseNum.clear1 c (W 25) M ((d.setv (W 0) 0).setv (W 1) 0)
    (by simp [Function.update_of_ne (hne (show (25 : Fin 30) ≠ 1 by decide)),
      Function.update_of_ne (hne (show (25 : Fin 30) ≠ 0 by decide)), h25]) hM
  have e4 := SparseNum.clear1 c (W 26) L (((d.setv (W 0) 0).setv (W 1) 0).setv (W 25) 0)
    (by simp [Function.update_of_ne (hne (show (26 : Fin 30) ≠ 25 by decide)),
      Function.update_of_ne (hne (show (26 : Fin 30) ≠ 1 by decide)),
      Function.update_of_ne (hne (show (26 : Fin 30) ≠ 0 by decide)), h26]) hL
  exact WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega)

end P3

end NearCubicWires.WireExponent3_5.PrimT.TplLenC
