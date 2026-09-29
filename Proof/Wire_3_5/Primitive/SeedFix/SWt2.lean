import Proof.Wire_3_5.Primitive.SeedFix.SWt1

/-! # SWt, part 2: one slot of the top tables

**`topW S O R`**: if the scan tape `S` is filled (`natWord x ++ (frame y ++ rest)`, its first bit `1`), skip the
`natWord` (counted), copy the frame to `O` (counted), rewind both exactly; if `S` is blank, write `[false] = frame []`.
Registers `R = (d, e, t, c, D₂, C₂, C₃, C₄)` start and end at `0`: **`top_fill`**, **`top_empty`** (the bank is
`σ.sets O (frame y)`).

Paper quantity of the main types: circuit `j`'s framed top table (`symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

theorem frame_len' (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [frame_eq_frameP]; unfold frameP; simp; ring

section Top
variable {ns nr : ℕ} (cap : ℕ)

/-- **One slot of the top tables.** -/
def topW (S O : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .ifs S
    (.seq (skipCW S (R 0) (R 1) (R 2)) (.seq (copyCW S O (R 3))
    (.seq (FinalPass.Hash4.wcopyR (R 0) (R 4) (R 2)) (.seq (FinalPass.Hash4.wcopyR (R 3) (R 5) (R 2))
    (.seq (FinalPass.Hash4.wcopyR (R 3) (R 6) (R 2)) (.seq (FinalPass.Hash4.wcopyR (R 3) (R 7) (R 2))
    (.seq (WM.rewind S (R 0)) (.seq (WM.rewind S (R 4)) (.seq (WM.rewind S (R 3)) (.seq (WM.rewind S (R 5))
    (.seq (.bwd S) (.seq (WM.rewind O (R 6)) (.seq (WM.rewind O (R 7)) (.bwd O))))))))))))))
    (.wr O false)

theorem top_empty (S O : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (σ : WState ns nr) (hS : σ.st S = [])
    (hSh : σ.sh S = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0) :
    WExec cap (topW S O R) σ (σ.sets O (frame [])) 2 := by
  have hb : wbit σ S = false := by simp [wbit, hS, hSh, readTapeBit]
  have h := WExec.wr (cap := cap) O false σ
  rw [hO, hOh] at h
  have e : writeTapeBit [] 0 false = frame [] := rfl
  rw [e] at h
  exact WExec.ifsF hb h

theorem top_fill (S O : Fin (ns + 1)) (hSO : S ≠ O) (R : Fin 8 ↪ Fin nr) (x : ℕ) (y rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = natWord x ++ (frame y ++ rest)) (hSh : σ.sh S = 0) (hO : σ.st O = [])
    (hOh : σ.sh O = 0) (hz : ∀ i, σ.val (R i) = 0) (hcap : 2 * natBitLength x + 2 * y.length + 2 ≤ cap) :
    ∃ c, WExec cap (topW S O R) σ (σ.sets O (frame y)) c ∧
      c ≤ 20 * UnaryPow.sq cap + 40 * natBitLength x + 40 * y.length + 200 := by
  have hne : ∀ {i j : Fin 8}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hOS : O ≠ S := fun e => hSO e.symm
  have hL1 : 1 ≤ natBitLength x := by unfold natBitLength; omega
  obtain ⟨L, hLd⟩ : ∃ L, L = natBitLength x := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = y.length := ⟨_, rfl⟩
  have hnw : (natWord x).length = 2 * L + 1 := by
    have : natWord x = List.replicate (natBitLength x) true ++
      false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x := rfl
    rw [this, hLd]; simp [WilliamsPublishedForm.fixedWidthNatBits]; omega
  have hb : wbit σ S = true := by
    unfold wbit; rw [hS, hSh]
    have := rd_ones [] (frame y ++ rest) x 0 hL1
    simpa using this
  have hsq := UnaryPow.lin_le_sq cap
  obtain ⟨c1, e1, c1le⟩ := skipC_spec cap S (R 0) (R 1) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide))
    x [] (frame y ++ rest) σ (by simpa using hS) (by simpa using hSh) (hz 0) (hz 1) (hz 2) (by omega)
  rw [← hLd] at e1 c1le
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = (σ.seth S (([] : List Bool).length + (natWord x).length)).setv (R 0) L := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have s1S : σ1.st S = natWord x ++ (frame y ++ rest) := by rw [hσ1]; simpa using hS
  have s1Sh : σ1.sh S = (natWord x).length := by rw [hσ1]; simp
  have s1O : σ1.st O = [] := by rw [hσ1]; simpa using hO
  have s1Oh : σ1.sh O = 0 := by rw [hσ1]; simp [Function.update_of_ne hOS, hOh]
  have s1v : ∀ i : Fin 8, σ1.val (R i) = if i = 0 then L else 0 := by
    intro i
    rw [hσ1]
    by_cases hi : i = 0
    · subst hi; simp
    · simp [Function.update_of_ne (hne hi), hz, hi]
  have s1j : ∀ j, j ≠ S → σ1.st j = σ.st j ∧ σ1.sh j = σ.sh j := fun j hj => by
    rw [hσ1]; simp [Function.update_of_ne hj]
  have s1q : ∀ q, (∀ i, R i ≠ q) → σ1.val q = σ.val q := fun q hq => by
    rw [hσ1]; simp [Function.update_of_ne (Ne.symm (hq 0))]
  obtain ⟨τ2, e2, o2, o2h, n2, n2h, oth2, v2, c2⟩ := copyC_spec cap S O (R 3) hSO (natWord x) y rest σ1 s1S s1Sh
    (by rw [s1Oh, s1O]; rfl) (by rw [s1v]; simp; omega)
  rw [s1O, List.nil_append] at o2
  have v2R : ∀ i : Fin 8, τ2.val (R i) = if i = 0 then L else if i = 3 then Y else 0 := by
    intro i
    rw [v2]
    by_cases h3 : i = 3
    · subst h3; simp [s1v, hYd]
    · rw [Function.update_of_ne (hne h3), s1v]; simp [h3]
  have v2q : ∀ q, (∀ i, R i ≠ q) → τ2.val q = σ.val q := fun q hq => by
    rw [v2, Function.update_of_ne (Ne.symm (hq 3)), s1q q hq]
  -- the counters copied
  have e3 := SparseNum.copy1 cap (R 0) (R 4) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide)) L τ2
    (by rw [v2R]; simp) (by rw [v2R]; simp) (by rw [v2R]; simp) (by omega)
  have e4 := SparseNum.copy1 cap (R 3) (R 5) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide)) Y
    (τ2.setv (R 4) L) (by simp [Function.update_of_ne (hne (show (3 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (5 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (2 : Fin 8) ≠ 4 by decide)), v2R]) (by omega)
  have e5 := SparseNum.copy1 cap (R 3) (R 6) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide)) Y
    ((τ2.setv (R 4) L).setv (R 5) Y)
    (by simp [Function.update_of_ne (hne (show (3 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (3 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (6 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (6 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (2 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (2 : Fin 8) ≠ 4 by decide)), v2R]) (by omega)
  have e6 := SparseNum.copy1 cap (R 3) (R 7) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide)) Y
    (((τ2.setv (R 4) L).setv (R 5) Y).setv (R 6) Y)
    (by simp [Function.update_of_ne (hne (show (3 : Fin 8) ≠ 6 by decide)),
      Function.update_of_ne (hne (show (3 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (3 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (7 : Fin 8) ≠ 6 by decide)),
      Function.update_of_ne (hne (show (7 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (7 : Fin 8) ≠ 4 by decide)), v2R])
    (by simp [Function.update_of_ne (hne (show (2 : Fin 8) ≠ 6 by decide)),
      Function.update_of_ne (hne (show (2 : Fin 8) ≠ 5 by decide)),
      Function.update_of_ne (hne (show (2 : Fin 8) ≠ 4 by decide)), v2R]) (by omega)
  obtain ⟨σ6, hσ6⟩ : ∃ s, s = (((τ2.setv (R 4) L).setv (R 5) Y).setv (R 6) Y).setv (R 7) Y := ⟨_, rfl⟩
  rw [← hσ6] at e6
  have v6 : ∀ i : Fin 8, σ6.val (R i) = if i = 0 then L else if i = 4 then L else if i = 1 ∨ i = 2 then 0 else Y := by
    intro i
    rw [hσ6]
    fin_cases i <;> simp [Function.update_apply, v2R, hne]
  have v6q : ∀ q, (∀ i, R i ≠ q) → σ6.val q = σ.val q := fun q hq => by
    rw [hσ6]
    simp [Function.update_of_ne (Ne.symm (hq 7)), Function.update_of_ne (Ne.symm (hq 6)),
      Function.update_of_ne (Ne.symm (hq 5)), Function.update_of_ne (Ne.symm (hq 4)), v2q q hq]
  have st6 : σ6.st = τ2.st := by rw [hσ6]; rfl
  have sh6 : σ6.sh = τ2.sh := by rw [hσ6]; rfl
  have cl6 : σ6.cell = τ2.cell := by rw [hσ6]; rfl
  -- the rewinds
  have e7 := wrewind_spec cap S (R 0) L σ6 (by rw [v6]; simp) (by rw [v6]; simp; omega)
  obtain ⟨σ7, hσ7⟩ : ∃ s, s = (σ6.setv (R 0) 0).seth S (σ6.sh S - L) := ⟨_, rfl⟩
  rw [← hσ7] at e7
  have e8 := wrewind_spec cap S (R 4) L σ7
    (by rw [hσ7]; simp [Function.update_of_ne (hne (show (4 : Fin 8) ≠ 0 by decide)), v6])
    (by rw [hσ7]; simp [Function.update_of_ne (hne (show (4 : Fin 8) ≠ 0 by decide)), v6]; omega)
  obtain ⟨σ8, hσ8⟩ : ∃ s, s = (σ7.setv (R 4) 0).seth S (σ7.sh S - L) := ⟨_, rfl⟩
  rw [← hσ8] at e8
  have e9 := wrewind_spec cap S (R 3) Y σ8
    (by rw [hσ8, hσ7]; simp [Function.update_of_ne (hne (show (3 : Fin 8) ≠ 0 by decide)),
      Function.update_of_ne (hne (show (3 : Fin 8) ≠ 4 by decide)), v6])
    (by rw [hσ8, hσ7]; simp [Function.update_of_ne (hne (show (3 : Fin 8) ≠ 0 by decide)),
      Function.update_of_ne (hne (show (3 : Fin 8) ≠ 4 by decide)), v6]; omega)
  obtain ⟨σ9, hσ9⟩ : ∃ s, s = (σ8.setv (R 3) 0).seth S (σ8.sh S - Y) := ⟨_, rfl⟩
  rw [← hσ9] at e9
  have v9 : ∀ i : Fin 8, σ9.val (R i) = if i = 5 ∨ i = 6 ∨ i = 7 then Y else 0 := by
    intro i
    rw [hσ9, hσ8, hσ7]
    fin_cases i <;> simp [Function.update_apply, v6, hne]
  have v9q : ∀ q, (∀ i, R i ≠ q) → σ9.val q = σ.val q := fun q hq => by
    rw [hσ9, hσ8, hσ7]
    simp [Function.update_of_ne (Ne.symm (hq 0)), Function.update_of_ne (Ne.symm (hq 4)),
      Function.update_of_ne (Ne.symm (hq 3)), v6q q hq]
  have sh9S : σ9.sh S = σ6.sh S - L - L - Y := by rw [hσ9, hσ8, hσ7]; simp
  have sh9 : ∀ j, j ≠ S → σ9.sh j = σ6.sh j := fun j hj => by
    rw [hσ9, hσ8, hσ7]; simp [Function.update_of_ne hj]
  have st9 : σ9.st = σ6.st := by rw [hσ9, hσ8, hσ7]; rfl
  have cl9 : σ9.cell = σ6.cell := by rw [hσ9, hσ8, hσ7]; rfl
  have e10 := wrewind_spec cap S (R 5) Y σ9 (by rw [v9]; simp) (by rw [v9]; simp; omega)
  obtain ⟨σ10, hσ10⟩ : ∃ s, s = (σ9.setv (R 5) 0).seth S (σ9.sh S - Y) := ⟨_, rfl⟩
  rw [← hσ10] at e10
  have e11 := WExec.bwd (cap := cap) S σ10
  obtain ⟨σ11, hσ11⟩ : ∃ s, s = σ10.seth S (σ10.sh S - 1) := ⟨_, rfl⟩
  rw [← hσ11] at e11
  have e12 := wrewind_spec cap O (R 6) Y σ11
    (by rw [hσ11, hσ10]; simp [Function.update_of_ne (hne (show (6 : Fin 8) ≠ 5 by decide)), v9])
    (by rw [hσ11, hσ10]; simp [Function.update_of_ne (hne (show (6 : Fin 8) ≠ 5 by decide)), v9]; omega)
  obtain ⟨σ12, hσ12⟩ : ∃ s, s = (σ11.setv (R 6) 0).seth O (σ11.sh O - Y) := ⟨_, rfl⟩
  rw [← hσ12] at e12
  have e13 := wrewind_spec cap O (R 7) Y σ12
    (by rw [hσ12, hσ11, hσ10]; simp [Function.update_of_ne (hne (show (7 : Fin 8) ≠ 6 by decide)),
      Function.update_of_ne (hne (show (7 : Fin 8) ≠ 5 by decide)), v9])
    (by rw [hσ12, hσ11, hσ10]; simp [Function.update_of_ne (hne (show (7 : Fin 8) ≠ 6 by decide)),
      Function.update_of_ne (hne (show (7 : Fin 8) ≠ 5 by decide)), v9]; omega)
  obtain ⟨σ13, hσ13⟩ : ∃ s, s = (σ12.setv (R 7) 0).seth O (σ12.sh O - Y) := ⟨_, rfl⟩
  rw [← hσ13] at e13
  have e14 := WExec.bwd (cap := cap) O σ13
  have hS6 : σ6.sh S = 2 * L + 1 + 2 * Y := by rw [sh6, n2h, hnw, hYd]
  have hO6 : σ6.sh O = 2 * Y + 1 := by rw [sh6, o2h, o2, frame_len', hYd]
  refine ⟨_, WExec.cast cap (WExec.ifsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12
    (WExec.seq e13 e14)))))))))))))) ?_ le_rfl, by omega⟩
  apply WState.eq
  · funext j
    rw [hσ13, hσ12, hσ11, hσ10]
    by_cases hjO : j = O
    · subst hjO
      simp [Function.update_of_ne hOS, sh9 _ hOS, hO6, hOh]
      omega
    · by_cases hjS : j = S
      · subst hjS
        simp [Function.update_of_ne hSO, sh9S, hS6, hSh]
        omega
      · simp [Function.update_of_ne hjO, Function.update_of_ne hjS, sh9 _ hjS, sh6, (oth2 j hjS hjO).2,
          (s1j j hjS).2]
  · funext j
    rw [hσ13, hσ12, hσ11, hσ10]
    simp only [WState.seth_st, WState.setv_st, WState.sets_st, st9, st6]
    by_cases hjO : j = O
    · subst hjO; simp [o2]
    · by_cases hjS : j = S
      · subst hjS; simp [Function.update_of_ne hSO, n2, s1S, hS]
      · simp [Function.update_of_ne hjO, (oth2 j hjS hjO).1, (s1j j hjS).1]
  · funext q
    rw [hσ13, hσ12, hσ11, hσ10]
    by_cases hq : ∃ i, R i = q
    · obtain ⟨i, rfl⟩ := hq
      simp only [WState.seth_val, WState.setv_val, WState.sets_val]
      fin_cases i <;> simp [Function.update_apply, v9, hne, hz]
    · have hq' : ∀ i, R i ≠ q := fun i h => hq ⟨i, h⟩
      simp only [WState.seth_val, WState.setv_val, WState.sets_val]
      simp [Function.update_of_ne (Ne.symm (hq' 7)), Function.update_of_ne (Ne.symm (hq' 6)),
        Function.update_of_ne (Ne.symm (hq' 5)), v9q q hq']
  · rw [hσ13, hσ12, hσ11, hσ10]
    simp only [WState.seth_cell, WState.setv_cell, WState.sets_cell]
    rw [cl9, cl6, c2, hσ1]; rfl

end Top

end NearCubicWires.WireExponent3_5.PrimT.SWt
