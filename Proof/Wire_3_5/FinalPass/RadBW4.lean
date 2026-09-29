import Proof.Wire_3_5.FinalPass.RadBW3

/-! # RADIX stage 5b, part 4: the block writer (row:radix, P3:2585-2623)

**`radBlockW2 : RadSpec2.RadBlockW2`**: one factor block of the RADIX row's store,
`marks (true :: blockC D L t sgn false (labsOf G row gis))`, appended to the output stream with its position register
`OP` (`RadSpec2.RadBlockW2`, the exit `appendO σ O OP B`). The program writes the block with the scratch counter
`7` (`PopRec.blockE_eq`: the marker, `pieceA` by `phA`, `pieceB` by `phB`, `pieceP` by `phP`), then moves `7` into
`OP`; the table and indices' streams are rewound and every scratch register is `0` again. Capacity
`need N = 300·(N+1)` (linear in the block writer's size), cost `bound c = 10^5·(c+1)^2`.

Paper quantity of the main type: the RADIX row's factor blocks (row:radix, P3:2585-2623). -/

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
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists

/-! ## Sizes -/

theorem mem_le_gisWord (gi : ℕ) : ∀ gis : List ℕ, gi ∈ gis → gi + 2 ≤ (gisWord gis).length
  | [], h => by simp at h
  | g :: gs, h => by
    rw [gisWord_cons, List.length_append, gw_length]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := mem_le_gisWord gi gs h; omega

theorem len_le_gisWord : ∀ gis : List ℕ, 2 * gis.length + 1 ≤ (gisWord gis).length
  | [] => by simp [gisWord_nil]
  | g :: gs => by
    rw [gisWord_cons, List.length_append, gw_length, List.length_cons]
    have := len_le_gisWord gs; omega

theorem gLabs_length (r4 G : ℕ) : ∀ gis : List ℕ, (gLabs r4 G gis).length = 4 * gis.length
  | [] => rfl
  | gi :: gis => by
    rw [gLabs_cons, List.length_append, gLabs_length r4 G gis]; simp [gateLabs]; ring

theorem gisB_le (r4 G Mg N : ℕ) (h1 : (r4 + 4) * G ≤ N) (h2 : Mg ≤ N) (h3 : r4 ≤ N) (h4 : G ≤ N) :
    gisB r4 G Mg ≤ 1000 * (N + 1) := by
  have e1 : (r4 + 3) * G ≤ (r4 + 4) * G := Nat.mul_le_mul_right _ (by omega)
  have e2 : G * (18 * (r4 + 3) + 8) = 18 * ((r4 + 3) * G) + 8 * G := by ring
  unfold gisB gateCost labCost1
  omega

theorem pieceB_len (labs : List ℕ) (cap1 : ℕ) :
    (pieceB labs cap1).length = (labs.flatMap labE).length + 6 + 4 * cap1 + 4 := by
  unfold pieceB
  simp only [List.length_append, PrimAsm.FiltRecW.reps_length, m2, List.length_cons, List.length_nil]
  ring

/-! ## The numbers -/

theorem radNum (cap N ol L d t c lw gw G row lAdd lE lA lB lP : ℕ) (hN : 300 * (N + 1) ≤ cap)
    (hNd : N = ol + (2 + (lA + (lB + lP))) + lw + gw + (G + 1) * (4 * row + 4) + t + d + c)
    (hgw : 2 * L + 1 ≤ gw) (hc : c = 4 * (lw + L + 1)) (hlB : lB = lE + 6 + 4 * (5 + lAdd) + 4) :
    2 ≤ cap ∧ 2 + 4 * (8 * (4 * L) + 6) + 30 + 4 * d + 6 + 4 * L + d + 10 ≤ cap ∧ gw + 1 ≤ cap ∧ gw ≤ cap ∧
    5 * row ≤ cap ∧
    2 + lA + lE + 4 * (4 * (gw + (4 * row + 4) * G) + 4) + (5 + lAdd) + 4 * (2 * (gw + (4 * row + 4) * G) + 10) +
      7 * (gw + (4 * row + 4) * G) + 4 * row + G + 20 ≤ cap ∧
    2 + lA + lB ≤ cap ∧ c + 1 ≤ cap ∧ t ≤ cap ∧ 2 + lA + lB + lP ≤ cap ∧
    (4 * row + 4) * G ≤ N ∧ gw ≤ N ∧ 4 * row ≤ N ∧ G ≤ N ∧ L ≤ N ∧ d ≤ N ∧ t ≤ N ∧ c ≤ N ∧ lw ≤ N ∧
    4 * (5 + lAdd) ≤ N ∧ 2 + (lA + (lB + lP)) ≤ N := by
  have f1 : (G + 1) * (4 * row + 4) = 4 * (row * G) + 4 * G + 4 * row + 4 := by ring
  have f2 : (4 * row + 4) * G = 4 * (row * G) + 4 * G := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem radCost (cap N L d t c lw gw row labS nA nB nP gB B : ℕ) (hN : 300 * (N + 1) ≤ cap)
    (hL : L ≤ N) (hd : d ≤ N) (ht : t ≤ N) (hc : c ≤ N) (hlw : lw ≤ N) (hgw : gw ≤ N) (hrow : 4 * row ≤ N)
    (hlS : 4 * labS ≤ N) (hB : B ≤ N) (bA : nA ≤ 2000 * (L + d + 10))
    (bB : nB ≤ L * gB + 40 * labS + 90 * row + 5 * gw + 200) (bP : nP ≤ 1000 * (lw + L + t + c + 10))
    (hgB : gB ≤ 1000 * (N + 1)) :
    8 * 2 + 1 + (nA + 1 + (nB + 1 + (nP + 1 + (7 * B + 1)))) ≤ 100000 * (cap + 1) ^ 2 := by
  have hNc : N ≤ cap := by omega
  have hLg : L * gB ≤ cap * (1000 * (cap + 1)) :=
    Nat.mul_le_mul (by omega) (le_trans hgB (Nat.mul_le_mul_left _ (by omega)))
  have hsq : cap * (1000 * (cap + 1)) ≤ 1000 * (cap + 1) ^ 2 := by
    calc cap * (1000 * (cap + 1)) = 1000 * (cap * (cap + 1)) := by ring
      _ ≤ 1000 * ((cap + 1) * (cap + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 1000 * (cap + 1) ^ 2 := by ring
  have hsq1 : cap + 1 ≤ (cap + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-! ## The program -/

/-- **The RADIX block writer**: the marker, `pieceA`, `pieceB`, `pieceP` (counter `7`), then `OP += 7`, `7 := 0`. -/
def radProg {ns nr : ℕ} (O T GS : Fin (ns + 1)) (_Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr)
    (OP : Fin nr) : WM ns nr :=
  .seq (emitW O (Rg 7) [true, true]) (.seq (phA O Rg) (.seq (phB O GS Rg) (.seq (phP O T Rg) (WM.move (Rg 7) OP))))

/-- The capacity. -/
def radNeed (N : ℕ) : ℕ := 300 * (N + 1)

/-- The cost. -/
def radBound (c : ℕ) : ℕ := 100000 * (c + 1) ^ 2

end NearCubicWires.WireExponent3_5.FinalPass.RadB
