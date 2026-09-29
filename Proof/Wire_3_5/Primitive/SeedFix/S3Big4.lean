import Proof.Wire_3_5.Primitive.SeedFix.S3Big2
import Proof.Wire_3_5.Primitive.SeedFix.S3Big3

/-! # S3, part 10: a circuit's scratch prepared at one list seed

Before circuit `j`'s factor at the list seed `e'_i` (P3:3170-3178, the reported-list value at one sampled input),
the evaluator writes the scratch the circuit program reads: the stage-5 template (word `templJ`, rewound), the seed's
flat table (the next `λ_j` cells of the all-seeds word `tablesJ`, whose head advances by `λ_j`: after seed `i` it
stands at `(i+1)·λ_j`), the zero counts on the two population accumulators (`h_j` pairs `true, false`), and the
guard bit. **`prepJ_spec`**: from blank scratch, the scratch READS like the circuit program's entry (`RdEq`), the
offset register and the table head advanced by `λ_j`, every other register and head as found, every word and point
stream unchanged.

Registers of the evaluator's layout: `qKo = qS 28` the factor, `qRh` the running product `R̂`, `qIc` the seed counter,
`qAc` the circuit guard, `qCt qBk qTp qSk` the writers' counters, `qOff j` circuit `j`'s table offset.

Paper quantity of the main type: the scratch the reported-list value at seed `e'_i` reads (the seed's flat table). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-! ## Registers -/

/-- The factor register (`qS 28`). -/
def qKo : Fin 67 := ⟨47, by omega⟩
/-- The running product `R̂`. -/
def qRh : Fin 67 := ⟨51, by omega⟩
/-- The seed counter. -/
def qIc : Fin 67 := ⟨52, by omega⟩
/-- The circuit guard. -/
def qAc : Fin 67 := ⟨53, by omega⟩
/-- The writers' counter. -/
def qCt : Fin 67 := ⟨54, by omega⟩
/-- The writers' head counter. -/
def qBk : Fin 67 := ⟨55, by omega⟩
/-- The writers' temporary. -/
def qTp : Fin 67 := ⟨56, by omega⟩
/-- The source head counter. -/
def qSk : Fin 67 := ⟨57, by omega⟩
/-- Circuit `j`'s table offset. -/
def qOff (j : Fin 4) : Fin 67 := ⟨58 + j.val, by omega⟩

theorem qKo_eq : qKo = qS 28 := rfl

theorem qN_lt (i : Fin 18) : (qN i).val < 19 := by
  show 1 + i.val < 19
  omega

theorem qN_ne (i : Fin 18) {r : Fin 67} (hr : 19 ≤ r.val) : qN i ≠ r := fun h => by
  have := congrArg Fin.val h
  have := qN_lt i
  omega

theorem bW_ne (w : Fin 16) {i : Fin 28} (hi : 19 ≤ i.val) : bW w ≠ i := fun h => by
  have := congrArg Fin.val h
  have := bW_lt w
  omega

theorem lo_ne {i s : Fin 28} (hi : i.val < 19) (hs : 19 ≤ s.val) : i ≠ s := fun h => by
  have := congrArg Fin.val h
  omega

theorem ne_qOff (j : Fin 4) {r : Fin 67} (hr : r.val < 58) : r ≠ qOff j := fun h => by
  have := congrArg Fin.val h
  simp only [qOff] at this
  omega

theorem qOff_ne (j : Fin 4) {r : Fin 67} (hr : r.val < 58) : qOff j ≠ r := fun h => ne_qOff j hr h.symm

theorem read_nil (p : ℕ) : readTapeBit [] p = false := by
  unfold readTapeBit
  simp

/-! ## The preparation -/

/-- **Circuit `j`'s scratch at the current seed**: the template, the seed's table, the zero counts, the guard bit. -/
def prepJ (j : Fin 4) : BM :=
  .seq (copyTN (bW (wIdx 3 j)) bT5 (qN (nIdx 3 j)) qCt qTp qBk qSk)
    (.seq (copyN (bW (wIdx 2 j)) bFT (qN (nIdx 2 j)) qCt qTp qBk (qOff j))
      (.seq (markN bPos (qN (nIdx 1 j)) qCt qTp qBk)
        (.seq (markN bNeg (qN (nIdx 1 j)) qCt qTp qBk) (.wr bSp true))))

theorem prepJ_spec (cap : ℕ) (j : Fin 4) (T FT : List Bool) (h : ℕ) (ω : BS)
    (hT : ω.st (bW (wIdx 3 j)) = T) (hμ : ω.val (qN (nIdx 3 j)) = T.length)
    (hlam : ω.val (qN (nIdx 2 j)) = FT.length)
    (htab : ∀ p, p < FT.length →
      readTapeBit (ω.st (bW (wIdx 2 j))) (ω.sh (bW (wIdx 2 j)) + p) = readTapeBit FT p)
    (hh : ω.val (qN (nIdx 1 j)) = h)
    (hsc : ∀ i : Fin 28, 19 ≤ i.val → RdEq (ω.st i) []) (hscs : ∀ i : Fin 28, 19 ≤ i.val → ω.sh i = 0)
    (hs3 : ω.sh (bW (wIdx 3 j)) = 0)
    (hct : ω.val qCt = 0) (htp : ω.val qTp = 0) (hbk : ω.val qBk = 0) (hsk : ω.val qSk = 0)
    (c1 : T.length ≤ cap) (c2 : ω.val (qOff j) + FT.length ≤ cap) (c3 : 2 * h ≤ cap) :
    ∃ τ, WExec cap (prepJ j) ω τ (46 * T.length + 41 * FT.length + 96 * h + 35) ∧
      τ.val = Function.update ω.val (qOff j) (ω.val (qOff j) + FT.length) ∧
      τ.sh = Function.update ω.sh (bW (wIdx 2 j)) (ω.sh (bW (wIdx 2 j)) + FT.length) ∧
      (∀ i : Fin 28, i.val < 19 → τ.st i = ω.st i) ∧
      RdEq (τ.st bPos) (frameP (binary h 0) ++ [false]) ∧ RdEq (τ.st bNeg) (frameP (binary h 0) ++ [false]) ∧
      RdEq (τ.st bX) [] ∧ RdEq (τ.st bZ) [] ∧ RdEq (τ.st bSp) [true] ∧ RdEq (τ.st bSm) [] ∧
      RdEq (τ.st bT5) T ∧ RdEq (τ.st bSS) [] ∧ RdEq (τ.st bFT) FT ∧ τ.cell = ω.cell := by
  -- the template
  obtain ⟨ω1, e1, r1, o1, sh1, v1, cl1⟩ := copyTN_spec cap (bW (wIdx 3 j)) bT5 (bW_ne _ (by decide))
    (qN (nIdx 3 j)) qCt qTp qBk qSk (qN_ne _ (by decide)) (qN_ne _ (by decide)) (by decide) (by decide) (by decide)
    (by decide) (qN_ne _ (by decide)) ω hct htp hbk hsk (hscs bT5 (by decide)) hs3 (by rw [hμ]; exact c1)
  -- the seed's table
  obtain ⟨ω2, e2, r2, o2, sh2, v2, cl2⟩ := copyN_spec cap (bW (wIdx 2 j)) bFT (bW_ne _ (by decide))
    (qN (nIdx 2 j)) qCt qTp qBk (qOff j) (qN_ne _ (by decide)) (qN_ne _ (by decide)) (by decide) (by decide)
    (ne_qOff j (by decide)) (ne_qOff j (by decide)) ω1 (by rw [v1]; exact hct) (by rw [v1]; exact htp)
    (by rw [v1]; exact hbk) (by rw [sh1]; exact hscs bFT (by decide)) (by rw [v1, hlam]; omega)
    (by rw [v1, hlam]; exact c2)
  have u2 : ∀ r, r ≠ qOff j → ω2.val r = ω.val r := fun r hr => by rw [v2, Function.update_of_ne hr, v1]
  have s2 : ∀ i, i ≠ bW (wIdx 2 j) → ω2.sh i = ω.sh i := fun i hi => by rw [sh2, Function.update_of_ne hi, sh1]
  -- the zero counts
  obtain ⟨ω3, e3, r3, o3, sh3, v3, cl3⟩ := markN_spec cap bPos (qN (nIdx 1 j)) qCt qTp qBk (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω2 (by rw [u2 _ (ne_qOff j (by decide))]; exact hct)
    (by rw [u2 _ (ne_qOff j (by decide))]; exact htp) (by rw [u2 _ (ne_qOff j (by decide))]; exact hbk)
    (by rw [s2 _ (bW_ne _ (by decide)).symm]; exact hscs bPos (by decide))
    (by rw [u2 _ (ne_qOff j (by have := qN_lt (nIdx 1 j); omega)), hh]; exact c3)
  obtain ⟨ω4, e4, r4, o4, sh4, v4, cl4⟩ := markN_spec cap bNeg (qN (nIdx 1 j)) qCt qTp qBk (qN_ne _ (by decide))
    (qN_ne _ (by decide)) (by decide) (by decide) ω3 (by rw [v3, u2 _ (ne_qOff j (by decide))]; exact hct)
    (by rw [v3, u2 _ (ne_qOff j (by decide))]; exact htp) (by rw [v3, u2 _ (ne_qOff j (by decide))]; exact hbk)
    (by rw [sh3, s2 _ (bW_ne _ (by decide)).symm]; exact hscs bNeg (by decide))
    (by rw [v3, u2 _ (ne_qOff j (by have := qN_lt (nIdx 1 j); omega)), hh]; exact c3)
  -- the guard bit
  have e5 := WExec.wr (cap := cap) bSp true ω4
  obtain ⟨ω5, hω5⟩ : ∃ y, y = ω4.sets bSp (writeTapeBit (ω4.st bSp) (ω4.sh bSp) true) := ⟨_, rfl⟩
  rw [← hω5] at e5
  have m1 : ω.val (qN (nIdx 3 j)) = T.length := hμ
  have m2 : ω1.val (qN (nIdx 2 j)) = FT.length := by rw [v1, hlam]
  have m3 : ω2.val (qN (nIdx 1 j)) = h := by rw [u2 _ (ne_qOff j (by have := qN_lt (nIdx 1 j); omega)), hh]
  have m4 : ω3.val (qN (nIdx 1 j)) = h := by rw [v3, m3]
  have st5 : ∀ i, i ≠ bSp → ω5.st i = ω4.st i := fun i hi => by
    rw [hω5, WState.sets_st, Function.update_of_ne hi]
  have st41 : ∀ i, i ≠ bNeg → i ≠ bPos → i ≠ bFT → i ≠ bT5 → ω4.st i = ω.st i := fun i a1 a2 a3 a4 => by
    rw [o4 i a1, o3 i a2, o2 i a3, o1 i a4]
  have sh5 : ω5.sh = Function.update ω.sh (bW (wIdx 2 j)) (ω.sh (bW (wIdx 2 j)) + FT.length) := by
    rw [hω5, WState.sets_sh, sh4, sh3, sh2, sh1, v1, hlam]
  refine ⟨ω5, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega), ?_, sh5,
    fun i hi => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_,
    fun p => ?_, fun p => ?_, ?_⟩
  · rw [hω5, WState.sets_val, v4, v3, v2, v1, hlam]
  · rw [st5 i (lo_ne hi (by decide)), st41 i (lo_ne hi (by decide)) (lo_ne hi (by decide)) (lo_ne hi (by decide))
      (lo_ne hi (by decide))]
  · rw [st5 _ (by decide), o4 _ (by decide), r3 p, m3, bin0_rep, read_marks]
    split_ifs with hp
    · rfl
    · rw [o2 _ (by decide), o1 _ (by decide), hsc bPos (by decide) p, read_nil]
  · rw [st5 _ (by decide), r4 p, m4, bin0_rep, read_marks]
    split_ifs with hp
    · rfl
    · rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), hsc bNeg (by decide) p, read_nil]
  · rw [st5 _ (by decide), st41 _ (by decide) (by decide) (by decide) (by decide)]
    exact hsc bX (by decide) p
  · rw [st5 _ (by decide), st41 _ (by decide) (by decide) (by decide) (by decide)]
    exact hsc bZ (by decide) p
  · have hsp : ω4.sh bSp = 0 := by
      rw [sh4, sh3, sh2, Function.update_of_ne (bW_ne _ (by decide)).symm, sh1]
      exact hscs bSp (by decide)
    rw [hω5, WState.sets_st, Function.update_self, hsp, readTapeBit_write]
    cases p with
    | zero => rfl
    | succ m =>
      rw [if_neg (by omega), st41 _ (by decide) (by decide) (by decide) (by decide), hsc bSp (by decide) (m + 1),
        read_nil]
      unfold readTapeBit
      simp
  · rw [st5 _ (by decide), st41 _ (by decide) (by decide) (by decide) (by decide)]
    exact hsc bSm (by decide) p
  · rw [st5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), r1 p, hμ, hT]
    split_ifs with hp
    · rfl
    · rw [hsc bT5 (by decide) p, read_nil, read_ge T p (by omega)]
  · rw [st5 _ (by decide), st41 _ (by decide) (by decide) (by decide) (by decide)]
    exact hsc bSS (by decide) p
  · rw [st5 _ (by decide), o4 _ (by decide), o3 _ (by decide), r2 p, m2]
    split_ifs with hp
    · rw [o1 _ (bW_ne _ (by decide)), sh1]
      exact htab p hp
    · rw [o1 _ (by decide), hsc bFT (by decide) p, read_nil, read_ge FT p (by omega)]
  · rw [hω5, WState.sets_cell, cl4, cl3, cl2, cl1]

end NearCubicWires.WireExponent3_5.PrimT.S3
