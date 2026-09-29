import Proof.Wire_3_5.UnionMachine.FrontFmtCA
import Proof.Wire_3_5.UnionMachine.FrontFoldSem

/-! # C6 front, U5, the source formats (d): the formats hold the fold's data

For a parsed guess `D` whose PCPP output's support rows are the systematic supports' bitmaps and whose entries' codes
are the grid atoms' codes (`TWRel.esc`), the formats' outputs are exactly the fold's inputs (P3:3672, 3409-3410):
* **`bm_eq`**: the bitmaps' output is `(foldOf D).ys.flatMap frame`;
* **`ca_eq`**: the atoms' codes' output is `(foldOf D).as.flatMap frame`.

Paper quantity of the main types: the parity atoms' supports and each variable's grid atoms' codes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtSem
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf nvOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord)
open NearCubicWires.RepairRepresentation (natWord)

variable {D : UnionCheckData}

theorem bitmap_empty (q : ℕ) : bitmap (∅ : Finset (Fin q)) = List.replicate q false := by
  simp [bitmap, List.ofFn_const]

/-- **The bitmaps are the fold's bitmaps.** -/
theorem bm_eq (sb : List Bool)
    (hrow : ∀ i (hi : i < D.pcpp.systematicBits), FrontFmtBM.chunk D.q sb i = bitmap (D.pcpp.systematicSupport ⟨i, hi⟩)) :
    (FrontFmtBM.rows D.q sb D.pcpp.systematicBits ++
      List.replicate D.pcpp.auxiliaryBits (List.replicate D.q false)).flatMap frame =
      (foldOf D).ys.flatMap frame := by
  congr 1
  have hl : (FrontFmtBM.rows D.q sb D.pcpp.systematicBits).length = D.pcpp.systematicBits := by
    simp [FrontFmtBM.rows]
  apply List.ext_getElem
  · simp [FoldIn.ys, foldOf, nvOf, hl]
  · intro n h1 h2
    have hn : n < nvOf D := by simpa [FoldIn.ys, foldOf] using h2
    rw [show ((foldOf D).ys)[n] = bitmap ((foldOf D).supp n) by simp [FoldIn.ys]]
    show _ = bitmap (if h : n < nvOf D then D.support ⟨n, h⟩ else ∅)
    rw [dif_pos hn]
    unfold UnionCheckData.support
    by_cases hs : n < D.pcpp.systematicBits
    · rw [List.getElem_append_left (by rw [hl]; exact hs), dif_pos hs]
      simp only [FrontFmtBM.rows, List.getElem_map, List.getElem_range]
      exact hrow n hs
    · rw [List.getElem_append_right (by rw [hl]; omega), dif_neg hs, bitmap_empty]
      simp

theorem codesOf_ofFn (m : Mode) {q : ℕ} : ∀ (s : ℕ) (g : ℕ → ℕ) (f : Fin s → m.Circuit q),
    (∀ a : Fin s, g a.val = m.code (f a)) → FrontFold.codesOf g s = codesWord m (List.ofFn f)
  | 0, g, f, _ => by simp [FrontFold.codesOf, codesWord]
  | s + 1, g, f, h => by
    rw [FrontFold.codesOf_succ, List.ofFn_succ', List.concat_eq_append, codesWord_append, codesWord_single,
      codesOf_ofFn m s g (fun i => f i.castSucc) (fun (a : Fin s) => h a.castSucc), ← h (Fin.last s)]
    rfl

/-- **The atoms' codes are the fold's carrier inputs.** -/
theorem ca_eq (es : List (Bool × Bool × ℕ))
    (hcode : ∀ (X : PcppVar D.pcpp) (a : Fin D.s), FrontFmtCA.codeE es (X.val * D.s + a.val) = D.mode.code (D.atom X a)) :
    FrontFmtCA.itemsOf es D.s (nvOf D) = (foldOf D).as.flatMap frame := by
  unfold FrontFmtCA.itemsOf FoldIn.as
  congr 1
  simp only [foldOf]
  apply List.map_congr_left
  intro X hX
  have hX' := List.mem_range.mp hX
  rw [dif_pos hX']
  exact codesOf_ofFn D.mode D.s _ _ (fun a => hcode ⟨X, hX'⟩ a)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtSem
