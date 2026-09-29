import Proof.Wire_3_5.FinalPass.RadBW2

/-! # RADIX stage 5b, part 3: the label fields and the stage-3∘5 data (row:radix, P3:2585-2623)

* `phB`/**`phB_spec`**: the label fields `pieceB labs (labSum labs)` of the digit's occurrences (the loop `gisLoop`,
  the label log's field `0^{labSum}`, the empty field), the indices' stream rewound, the scratch registers restored;
* `phP`/**`phP_spec`**: the stage-3∘5 data `pieceP (lw.flatMap m2) t sgn c false`: the table word `lw` copied from
  the table stream (its length `capC/4 − L − 1` by `kComp`), `unary t`, the scratch `0^{c+1}`, the sign, 15 registers,
  the flag `false`; the table stream rewound.

Paper quantity of the main types: the RADIX row's factor block's fields (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

variable {ns nr : ℕ} (cap : ℕ)

theorem aO_ho {O : Fin (ns + 1)} {P : Fin nr} (τ : WState ns nr) (hO : τ.sh O = (τ.st O).length) (u : List Bool) :
    (appendO τ O P u).sh O = ((appendO τ O P u).st O).length := by
  simp [hO]

theorem aO_val_ne (τ : WState ns nr) (O : Fin (ns + 1)) {P r : Fin nr} (h : r ≠ P) (u : List Bool) :
    (appendO τ O P u).val r = τ.val r := by
  simp [Function.update_of_ne h]

theorem aO_val_self (τ : WState ns nr) (O : Fin (ns + 1)) (P : Fin nr) (u : List Bool) :
    (appendO τ O P u).val P = τ.val P + u.length := by
  simp

theorem flatMap_m2_length (w : List Bool) : (w.flatMap m2).length = 4 * w.length := by
  induction w with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, List.length_append, ih]; simp [m2]; ring

theorem gS_ho {O GS : Fin (ns + 1)} {Rg : Fin 64 ↪ Fin nr} (hOG : O ≠ GS) (σ : WState ns nr)
    (ho : σ.sh O = (σ.st O).length) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).sh O = ((gS O GS Rg σ u c h p).st O).length := by
  rw [gS_sh, gS_st]; simp [Function.update_apply, hOG, ho]

theorem gS_val7 {O GS : Fin (ns + 1)} {Rg : Fin 64 ↪ Fin nr} (σ : WState ns nr) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).val (Rg 7) = σ.val (Rg 7) + u.length := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  rw [gS_val]; simp [hR]

theorem gS_val20 {O GS : Fin (ns + 1)} {Rg : Fin 64 ↪ Fin nr} (σ : WState ns nr) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).val (Rg 20) = c := by
  have hR : ∀ i j : Fin 64, Rg i = Rg j ↔ i = j := fun i j => Rg.injective.eq_iff
  rw [gS_val]; simp [hR]

theorem gS_val37 {O GS : Fin (ns + 1)} {Rg : Fin 64 ↪ Fin nr} (σ : WState ns nr) (u : List Bool) (c h p : ℕ) :
    (gS O GS Rg σ u c h p).val (Rg 37) = p := by
  rw [gS_val]; simp

/-! ## The label fields -/

/-- The label fields: `11 := 4·row`, `20 := 5`, the occurrences' labels, the log's field, the empty field; `GS`
rewound, `11 := 0`. -/
def phB (O GS : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (add4 (Rg 2) (Rg 11) (Rg 9))
  (.seq (incN (Rg 20) 5)
  (.seq (gisLoop O GS Rg)
  (.seq (emitW O (Rg 7) (m2 false ++ [true, false]))
  (.seq (repW O (Rg 7) (Rg 20) (m2 false))
  (.seq (emitW O (Rg 7) ([true, false] ++ [true, false]))
  (.seq (WM.rewind GS (Rg 37))
  (WM.clear (Rg 11))))))))

/-! ## The stage-3∘5 data -/

/-- The zero fields' registers (`PopBlockW.zf`): the block writer's with `0 ↔ 7` swapped (output counter `7`,
`c+1` in `51`, scratch `61`, `62`). -/
def xR (Rg : Fin 64 ↪ Fin nr) : Fin 64 ↪ Fin nr := (Equiv.swap (0 : Fin 64) 7).toEmbedding.trans Rg

/-- The stage-3∘5 data: `40 := |lw|`, the table word copied (`41` its position), `T` rewound, `unary t` (`3`),
`51 := c + 1`, the zero fields and the sign (`4`), the flag `false`; `51 := 0`. -/
def phP (O T : Fin (ns + 1)) (Rg : Fin 64 ↪ Fin nr) : WM ns nr :=
  .seq (kComp Rg)
  (.seq (copyLoop O T (Rg 7) (Rg 41) (Rg 40))
  (.seq (WM.rewind T (Rg 41))
  (.seq (emitW O (Rg 7) [true, false])
  (.seq (repRegW O (Rg 7) (Rg 3) (Rg 38) (Rg 39) (m2 true))
  (.seq (emitW O (Rg 7) (m2 false ++ [true, false]))
  (.seq (Hash4.wcopyR (Rg 6) (Rg 51) (Rg 42))
  (.seq (.inc (Rg 51))
  (.seq (PrimAsm.PopBlockW.zf O (xR Rg))
  (.seq (.ifr (Rg 4) (emitW O (Rg 7) (m2 true ++ [true, false])) (emitW O (Rg 7) (m2 false ++ [true, false])))
  (.seq (PrimAsm.PopBlockW.repP (PrimAsm.PopBlockW.zf O (xR Rg)) 15)
  (.seq (emitW O (Rg 7) (m2 false ++ [true, false]))
  (WM.clear (Rg 51)))))))))))))

end NearCubicWires.WireExponent3_5.FinalPass.RadB
