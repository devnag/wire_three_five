import Proof.Wire_3_5.Primitive.SeedFix.CtrParAll

/-! # X3, part 7: the second pass, one block's center coordinates (P3:1206-1216)

"A fixed linear basis of each code gives polynomial-time encoding" (P3:1216): the second pass of a block writes its
`b` codeword bits XOR the offset, in order: at a parity position `2^u − 1` the parity bit `u` (the low bit of
`rgPAR`, `halfW`), at a data position the next data bit (`readB`). Here:

* `OutAt` (the center stream holds the first `k` center bits, framed), `frameP_take_succ`, **`emit_step`** (one center
  coordinate `Tl[k]` emitted);
* `P2S` (the second pass's state at position `q`), `p2Data_spec`, `p2Par_spec`, **`p2Mid_spec`** (one position of
  the block: `encB P zb q ⊕ offset`, `enc_data` / `enc_par`).

Paper quantity of the main types: the center's coordinates `Tl[k]` (`Tl = List.ofFn (centerAt P σ row col)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo

/-- The center stream after `k` coordinates: their frame, then what was there before. -/
structure OutAt (Tl Y0 : List Bool) (k : ℕ) (τ : CS) : Prop where
  st : τ.st zCtr = frameP (Tl.take k) ++ Y0.drop (2 * k)
  sh : τ.sh zCtr = 2 * k
  oc : τ.val rgOC = 2 * k
  osh : τ.sh zOff = 2 * k
  ofc : τ.val rgOFFC = 2 * k

theorem frameP_snoc (l : List Bool) (b : Bool) : frameP (l ++ [b]) = frameP l ++ [true, b] := by
  simp [frameP, List.flatMap_append]

theorem frameP_take_succ (Tl : List Bool) (k : ℕ) (hk : k < Tl.length) :
    frameP (Tl.take (k + 1)) = frameP (Tl.take k) ++ [true, Tl.getD k false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, frameP_snoc,
    List.getD_eq_getElem _ _ hk]

section Emit
variable (cap : ℕ)

/-- **One center coordinate emitted**: `Tl[k] = X ⊕ offset[k]`. -/
theorem emit_step (Tl offL Y0 : List Bool) (k : ℕ) (X : Fin 26) (hXO : X ≠ rgOC) (hXF : X ≠ rgOFFC) (τ : CS)
    (hout : OutAt Tl Y0 k τ) (hoff : τ.st zOff = frameP offL ++ [false]) (hko : k < offL.length)
    (hkt : k < Tl.length) (cb : Bool) (hX : τ.val X = cb.toNat)
    (hT : Tl.getD k false = xor cb (offL.getD k false)) (hcap : 2 * k + 2 ≤ cap) :
    ∃ τ', WExec cap (emitX X) τ τ' 40 ∧ OutAt Tl Y0 (k + 1) τ' ∧ τ'.st zOff = τ.st zOff ∧
      (∀ i, i ≠ zCtr → i ≠ zOff → τ'.st i = τ.st i ∧ τ'.sh i = τ.sh i) ∧
      (∀ r, r ≠ rgOC → r ≠ rgOFFC → τ'.val r = τ.val r) ∧ τ'.cell = τ.cell := by
  obtain ⟨τ', e, a, b, c, d, f, g, h, i, j⟩ := emitX_spec cap X hXO hXF τ (by rw [hX]; exact Bool.toNat_le cb)
    (frameP (Tl.take k)) (Y0.drop (2 * k)) hout.st (by rw [hout.sh, frameP_length, List.length_take]; omega)
    (by rw [hout.oc]; omega) (by rw [hout.ofc]; omega)
  have hbit : xor (decide (τ.val X = 1)) (readTapeBit (τ.st zOff) (τ.sh zOff + 1)) = Tl.getD k false := by
    rw [hoff, hout.osh, readTapeBit_frameP offL [false] k hko, hT, hX]
    cases cb <;> rfl
  refine ⟨τ', e, ⟨?_, ?_, ?_, ?_, ?_⟩, g, h, i, j⟩
  · rw [a, hbit, frameP_take_succ Tl k hkt, List.drop_drop, show 2 * (k + 1) = 2 * k + 2 by ring]
    simp [Nat.add_comm]
  · rw [b, frameP_length, List.length_take]; omega
  · rw [c, hout.oc]; ring
  · rw [d, hout.osh]; ring
  · rw [f, hout.ofc]; ring

end Emit

end NearCubicWires.WireExponent3_5.PrimT.Ctr
