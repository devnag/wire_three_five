import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Prep

/-! # TopFrontPort3 body, part 3: the word stage after the guard (`mW`, `m_spec`)

P3:3071-3091 (the call's circuits by their codes). After the guard has seen `a' ≥ 1`, the word stage prepares `1^n`
and `1^{(n+1)^26}` (`TF3Prep`), runs PA's verified split (`Data.setupW`: slot `i < a'` holds circuit `i`'s
framed code, `1^n`, `1^L`) and writes each filled slot's result cell `[false]` on its stream `3`, so that every filled
slot's first `1781` streams are exactly the decode-block entry (`ThrTab.blockIn code n L`).

* `cellW`, `cellsW`, `cellsUpto`, **`cell_step`**, **`cells_spec`**;
* `mW`, `mCost`, **`MPost`**, **`m_spec`**: from the guard's exit state (`σ0` of the fill, the request's head past the
  arity field, `a'` in register `9`), `MPost`: the request and the count kept, the filled slots in block form, the
  empty ones blank, every slot stream from `4` on blank at head `0`.

Paper quantities of the main type: the circuits' codes of the THR request, split one per slot, with `n` and the
description bound `(n+1)^26`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Main
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data

/-- Slot `i`'s result cell: `[false]` on its stream `3` when the slot is filled. -/
def cellW (i : Fin 4) : WM DS DR := .ifs (sSym i 0) (.wr (sSym i 3) false) .skip

/-- The four result cells. -/
def cellsW : WM DS DR := .seq (cellW 0) (.seq (cellW 1) (.seq (cellW 2) (cellW 3)))

/-- The state after the cells of the slots `i < min a k`. -/
def cellsUpto (τ : WState DS DR) (a k : ℕ) : WState DS DR :=
  ⟨τ.sh, fun s => if ∃ i : Fin 4, i.val < a ∧ i.val < k ∧ s = sSym i 3 then [false] else τ.st s, τ.val, τ.cell⟩

theorem sSym3_ne_trip (i i' : Fin 4) (j : Fin 3) : sSym i 3 ≠ sSym i' ⟨j.val, by omega⟩ := by
  intro h
  have := (sSym_eq_iff _ _ _ _).mp h
  have hj := congrArg Fin.val this.2
  have := j.isLt
  simp at hj
  omega

theorem cellsUpto_trip (τ : WState DS DR) (a k : ℕ) (i : Fin 4) (j : Fin 3) :
    (cellsUpto τ a k).st (sSym i ⟨j.val, by omega⟩) = τ.st (sSym i ⟨j.val, by omega⟩) := by
  have : ¬ ∃ i' : Fin 4, i'.val < a ∧ i'.val < k ∧ sSym i ⟨j.val, by omega⟩ = sSym i' 3 := by
    rintro ⟨i', -, -, h⟩
    exact sSym3_ne_trip i' i j h.symm
  simp only [cellsUpto, if_neg this]

theorem cellsUpto_zero (τ : WState DS DR) (a : ℕ) : cellsUpto τ a 0 = τ := by
  apply WState.eq
  · rfl
  · funext s
    simp [cellsUpto]
  · rfl
  · rfl

theorem cellsUpto_iff (a k : ℕ) (i : Fin 4) (s : Fin (DS + 1)) (hs : s ≠ sSym i 3) (hk : k = i.val) :
    (∃ i' : Fin 4, i'.val < a ∧ i'.val < k ∧ s = sSym i' 3) ↔
      (∃ i' : Fin 4, i'.val < a ∧ i'.val < k + 1 ∧ s = sSym i' 3) := by
  constructor
  · rintro ⟨i', h1, h2, h4⟩
    exact ⟨i', h1, by omega, h4⟩
  · rintro ⟨i', h1, h2, h4⟩
    refine ⟨i', h1, ?_, h4⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
    · exact h
    · exact absurd (h4.trans (by rw [show i' = i from Fin.ext (h.trans hk)])) hs

theorem cellsUpto_blank_iff (a k : ℕ) (hk : a ≤ k) (s : Fin (DS + 1)) :
    (∃ i' : Fin 4, i'.val < a ∧ i'.val < k ∧ s = sSym i' 3) ↔
      (∃ i' : Fin 4, i'.val < a ∧ i'.val < k + 1 ∧ s = sSym i' 3) := by
  constructor
  · rintro ⟨i', h1, h2, h4⟩
    exact ⟨i', h1, by omega, h4⟩
  · rintro ⟨i', h1, h2, h4⟩
    exact ⟨i', h1, by omega, h4⟩

/-- **One result cell**: slot `i` filled (`i < a`) gets `[false]` on stream `3`; an empty slot is skipped. -/
theorem cell_step (cap : ℕ) (τ : WState DS DR) (a : ℕ) (i : Fin 4) (xs : Fin 4 → ℕ) (n L : ℕ)
    (hdone : i.val < a → Done τ (symTrip i) (xs i) n L) (hblank : a ≤ i.val → Blank τ (symTrip i))
    (h3 : τ.st (sSym i 3) = []) (h3h : τ.sh (sSym i 3) = 0) :
    WExec cap (cellW i) (cellsUpto τ a i.val) (cellsUpto τ a (i.val + 1)) 2 := by
  by_cases hi : i.val < a
  · obtain ⟨d1, d2, -, -, -, -⟩ := hdone hi
    simp only [symTrip] at d1 d2
    have hb : wbit (cellsUpto τ a i.val) (sSym i 0) = true := by
      unfold wbit
      have e := cellsUpto_trip τ a i.val i 0
      rw [show (⟨(0 : Fin 3).val, by omega⟩ : Fin 1789) = 0 from rfl] at e
      rw [e, show (cellsUpto τ a i.val).sh = τ.sh from rfl, d1, d2]
      exact frame_natWord_head _
    have hw := WExec.wr (cap := cap) (sSym i 3) false (cellsUpto τ a i.val)
    refine WExec.cast cap (WExec.ifsT hb hw) ?_ (by omega)
    have hn : ¬ ∃ i' : Fin 4, i'.val < a ∧ i'.val < i.val ∧ sSym i 3 = sSym i' 3 := by
      rintro ⟨i', -, hl, h⟩
      have := ((sSym_eq_iff _ _ _ _).mp h).1
      subst this
      omega
    have hy : ∃ i' : Fin 4, i'.val < a ∧ i'.val < i.val + 1 ∧ sSym i 3 = sSym i' 3 := ⟨i, hi, by omega, rfl⟩
    apply WState.eq
    · rfl
    · funext s
      by_cases hs : s = sSym i 3
      · subst hs
        have e1 : (cellsUpto τ a i.val).st (sSym i 3) = [] := by simp only [cellsUpto, if_neg hn, h3]
        have e2 : (cellsUpto τ a i.val).sh (sSym i 3) = 0 := h3h
        simp only [WState.sets_st, Function.update_self, e1, e2]
        simp only [cellsUpto, if_pos hy]
        rfl
      · simp only [WState.sets_st, Function.update_of_ne hs, cellsUpto]
        rw [if_congr (cellsUpto_iff a i.val i s hs rfl) rfl rfl]
    · rfl
    · rfl
  · obtain ⟨b1, b2, -, -, -, -⟩ := hblank (by omega)
    simp only [symTrip] at b1 b2
    have hb : wbit (cellsUpto τ a i.val) (sSym i 0) = false := by
      unfold wbit
      have e := cellsUpto_trip τ a i.val i 0
      rw [show (⟨(0 : Fin 3).val, by omega⟩ : Fin 1789) = 0 from rfl] at e
      rw [e, b1]
      rfl
    refine WExec.cast cap (WExec.ifsF hb (WExec.skip _)) ?_ (by omega)
    apply WState.eq
    · rfl
    · funext s
      simp only [cellsUpto]
      rw [if_congr (cellsUpto_blank_iff a i.val (by omega) s) rfl rfl]
    · rfl
    · rfl

/-- **The four result cells.** -/
theorem cells_spec (cap : ℕ) (τ : WState DS DR) (a : ℕ) (xs : Fin 4 → ℕ) (n L : ℕ)
    (hdone : ∀ i : Fin 4, i.val < a → Done τ (symTrip i) (xs i) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank τ (symTrip i))
    (h3 : ∀ i : Fin 4, τ.st (sSym i 3) = [] ∧ τ.sh (sSym i 3) = 0) :
    WExec cap cellsW τ (cellsUpto τ a 4) 11 := by
  have s0 : WExec cap (cellW 0) (cellsUpto τ a 0) (cellsUpto τ a 1) 2 :=
    cell_step cap τ a 0 xs n L (hdone 0) (hblank 0) (h3 0).1 (h3 0).2
  have s1 : WExec cap (cellW 1) (cellsUpto τ a 1) (cellsUpto τ a 2) 2 :=
    cell_step cap τ a 1 xs n L (hdone 1) (hblank 1) (h3 1).1 (h3 1).2
  have s2 : WExec cap (cellW 2) (cellsUpto τ a 2) (cellsUpto τ a 3) 2 :=
    cell_step cap τ a 2 xs n L (hdone 2) (hblank 2) (h3 2).1 (h3 2).2
  have s3 : WExec cap (cellW 3) (cellsUpto τ a 3) (cellsUpto τ a 4) 2 :=
    cell_step cap τ a 3 xs n L (hdone 3) (hblank 3) (h3 3).1 (h3 3).2
  rw [cellsUpto_zero] at s0
  exact WExec.seq s0 (WExec.seq s1 (WExec.seq s2 s3))

/-! ## The word stage -/

/-- **The word stage after the guard**: preparation, PA's split, the result cells. -/
def mW : WM DS DR := .seq TF3Prep.pAW (.seq TF3Prep.pBW (.seq setupW cellsW))

/-- The word stage's cost. -/
def mCost (n L V cap : ℕ) (codes cc : List ℕ) : ℕ :=
  TF3Prep.pACost n V + 1 + (TF3Prep.pBCost n L cap + 1 + (setupCost n L codes cc + 1 + 11))

/-- The guard's exit state (the fill's state, the request's head past the arity field, `a` in register `9`). -/
def gSt (w : List Bool) (V n a : ℕ) : WState DS DR := ((σ0 w 0 0 V).seth sIN (TF3Guard.gPos n a)).setv 9 a

/-- **The word stage's exit**: the request and the count kept; filled slot `i < |codes|` holds circuit `i`'s framed
code, `1^n`, `1^L` and the cell `[false]` on its streams `0 … 3`; an empty slot is blank; every slot stream from `4`
on is blank; all these heads at `0`. -/
structure MPost (τ : WState DS DR) (w : List Bool) (codes : List ℕ) (n L V : ℕ) : Prop where
  inp : τ.st sIN = frame w
  cnt : τ.st sCT = List.replicate V true
  done : ∀ i : Fin 4, ∀ h : i.val < codes.length, Done τ (symTrip i) (codes.get ⟨i.val, h⟩) n L
  cell : ∀ i : Fin 4, i.val < codes.length → τ.st (sSym i 3) = [false] ∧ τ.sh (sSym i 3) = 0
  blank : ∀ i : Fin 4, codes.length ≤ i.val → Blank τ (symTrip i) ∧ τ.st (sSym i 3) = [] ∧ τ.sh (sSym i 3) = 0
  free : ∀ i : Fin 4, ∀ j : Fin 1789, 4 ≤ j.val → τ.st (sSym i j) = [] ∧ τ.sh (sSym i j) = 0

theorem sNT_ne_sIN : sNT ≠ sIN := by decide
theorem sNT_ne_sCT : sNT ≠ sCT := by decide
theorem sLT_ne_sIN : sLT ≠ sIN := by decide
theorem sLT_ne_sCT : sLT ≠ sCT := by decide

theorem low_ne (i : Fin 4) (j : Fin 1789) (s : Fin (DS + 1)) (hs : s.val < 14) : sSym i j ≠ s :=
  sSym_ne_low i j s hs

theorem cellsUpto_st_other (τ : WState DS DR) (a k : ℕ) (s : Fin (DS + 1)) (hs : ∀ i : Fin 4, s ≠ sSym i 3) :
    (cellsUpto τ a k).st s = τ.st s := by
  have : ¬ ∃ i : Fin 4, i.val < a ∧ i.val < k ∧ s = sSym i 3 := fun ⟨i, _, _, h⟩ => hs i h
  simp only [cellsUpto, if_neg this]

/-- **The word stage's run** from the guard's exit state. -/
theorem m_spec (cap n : ℕ) (codes cc : List ℕ) (tl : List Bool) (V L : ℕ) (hL : (n + 1) ^ 26 = L)
    (ha : codes.length ≤ 4) (hk : cc.length ≤ 2)
    (hpos : TF3Guard.gPos n codes.length ≤ V) (hV : V ≤ cap) (hn : 2 ^ (natBitLength n + 1) ≤ cap)
    (hnV : 2 * (RepairRepresentation.natWord n).length ≤ V) (hLc : L ≤ cap)
    (hcN : natBitLength n + 1 ≤ cap) (hcA : 2 ^ (natBitLength codes.length + 1) ≤ cap)
    (hcK : 2 ^ (natBitLength cc.length + 1) ≤ cap)
    (hcx : ∀ x ∈ codes, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ cap)
    (hcy : ∀ y ∈ cc, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ cap) (hc4 : 4 ≤ cap) :
    ∃ τ, WExec cap mW (gSt (reqW n true codes cc tl) V n codes.length) τ (mCost n L V cap codes cc) ∧
      MPost τ (reqW n true codes cc tl) codes n L V := by
  set a := codes.length with ha'
  set σG := gSt (reqW n true codes cc tl) V n a with hσG
  have n9 : ∀ r : Fin DR, r ≠ 9 → σG.val r = 0 := fun r hr => by simp [hσG, gSt, σ0, Function.update_apply, hr]
  have q1 := TF3Prep.pA_spec cap n codes cc tl V (TF3Guard.gPos n a) σG (by simp [hσG, gSt, σ0])
    (by simp [hσG, gSt]) hpos (by simp [hσG, gSt, σ0, sIN, sNT, sLT, sCT])
    (by simp [hσG, gSt, σ0, Function.update_of_ne TF3Prep.sCT_ne_sIN])
    (n9 0 (by decide)) (n9 1 (by decide)) (n9 2 (by decide)) (n9 3 (by decide)) (n9 5 (by decide))
    (n9 6 (by decide)) (n9 7 (by decide)) (n9 8 (by decide)) hV hn hnV
  set σA := ((σG.seth sCT V).seth sIN 0).setv 8 n with hσA
  have nA : ∀ r : Fin DR, r ≠ 8 → r ≠ 9 → σA.val r = 0 := fun r h8 h9 => by
    simp [hσA, Function.update_apply, h8]; exact n9 r h9
  have q2 := TF3Prep.pB_spec cap n L hL σA (by simp [hσA, hσG, gSt, σ0, sIN, sNT])
    (by simp [hσA, hσG, gSt, σ0, Function.update_of_ne sNT_ne_sIN, Function.update_of_ne sNT_ne_sCT])
    (by simp [hσA, hσG, gSt, σ0, sIN, sNT, sLT])
    (by simp [hσA, hσG, gSt, σ0, Function.update_of_ne sLT_ne_sIN, Function.update_of_ne sLT_ne_sCT]) (by simp [hσA])
    (nA 10 (by decide) (by decide)) (nA 11 (by decide) (by decide)) (nA 12 (by decide) (by decide))
    (nA 13 (by decide) (by decide)) (nA 14 (by decide) (by decide)) (nA 15 (by decide) (by decide)) hLc
  set σB := (((σA.sets sNT (List.replicate n true)).sets sLT (List.replicate L true)).setv 10 (n + 1)).setv 12 L
    with hσB
  have stB : ∀ i : Fin 4, ∀ j : Fin 1789, σB.st (sSym i j) = [] ∧ σB.sh (sSym i j) = 0 := by
    intro i j
    have h1 := low_ne i j sNT (by decide)
    have h2 := low_ne i j sLT (by decide)
    have h3 := low_ne i j sIN (by decide)
    have h4 := low_ne i j sCT (by decide)
    constructor
    · simp [hσB, hσA, hσG, gSt, Function.update_apply, h1, h2]
      exact σ0_sym (reqW n true codes cc tl) 0 V i j
    · simp [hσB, hσA, hσG, gSt, σ0, Function.update_apply, h3, h4]
  have stC : ∀ k : Fin 2, ∀ j : Fin 1357, σB.st (sCar k j) = [] ∧ σB.sh (sCar k j) = 0 := by
    intro k j
    have h1 := sCar_ne_low k j sNT (by decide)
    have h2 := sCar_ne_low k j sLT (by decide)
    have h3 := sCar_ne_low k j sIN (by decide)
    have h4 := sCar_ne_low k j sCT (by decide)
    constructor
    · simp [hσB, hσA, hσG, gSt, Function.update_apply, h1, h2]
      exact σ0_car (reqW n true codes cc tl) 0 V k j
    · simp [hσB, hσA, hσG, gSt, σ0, Function.update_apply, h3, h4]
  have nB : ∀ r : Fin DR, r.val < 8 → σB.val r = 0 := fun r hr => by
    have h8 : r ≠ 8 := fun e => by subst e; exact absurd hr (by decide)
    have h9 : r ≠ 9 := fun e => by subst e; exact absurd hr (by decide)
    have h10 : r ≠ 10 := fun e => by subst e; exact absurd hr (by decide)
    have h12 : r ≠ 12 := fun e => by subst e; exact absurd hr (by decide)
    simp [hσB, Function.update_apply, h10, h12]
    exact nA r h8 h9
  obtain ⟨τ1, q3, d1, b1, -, -, f1, i1, -, -⟩ := setup_spec cap n L true codes cc tl σB ha hk
    (by simp [hσB, hσA, hσG, gSt, σ0, sIN, sNT, sLT])
    (by simp [hσB, hσA, hσG, gSt])
    (by simp [hσB, hσA, TF3Prep.sNT_ne_sLT])
    (by simp [hσB, hσA, hσG, gSt, σ0, Function.update_of_ne sNT_ne_sIN, Function.update_of_ne sNT_ne_sCT])
    (by simp [hσB, hσA])
    (by simp [hσB, hσA, hσG, gSt, σ0, Function.update_of_ne sLT_ne_sIN, Function.update_of_ne sLT_ne_sCT])
    (fun i => ⟨(stB i 0).1, (stB i 0).2, (stB i 1).1, (stB i 1).2, (stB i 2).1, (stB i 2).2⟩)
    (fun k => ⟨(stC k 0).1, (stC k 0).2, (stC k 1).1, (stC k 1).2, (stC k 2).1, (stC k 2).2⟩)
    (nB 0 (by decide)) (nB 1 (by decide)) (nB 2 (by decide)) (nB 3 (by decide)) (nB 4 (by decide))
    (nB 5 (by decide)) (nB 6 (by decide)) (nB 7 (by decide)) hcN hcA hcK hcx hcy hc4
  have keep : ∀ i : Fin 4, ∀ j : Fin 1789, 3 ≤ j.val → τ1.st (sSym i j) = [] ∧ τ1.sh (sSym i j) = 0 := by
    intro i j hj
    have hnot : ∀ i', ¬ tmem (sSym i j) (symTrip i') := by
      intro i' hm
      simp only [symTrip, tmem, sSym_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sSym i j) hnot (fun k => not_tmem_carTrip_of_sym _ _ _) (sSym_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (stB i j).1, this.2.trans (stB i j).2⟩
  have q4 := cells_spec cap τ1 a (fun i => if h : i.val < a then codes.get ⟨i.val, h⟩ else 0) n L
    (fun i hi => by simpa [dif_pos hi] using d1 i hi) (fun i hi => b1 i hi)
    (fun i => keep i 3 (by decide))
  refine ⟨cellsUpto τ1 a 4, WExec.seq q1 (WExec.seq q2 (WExec.seq q3 q4)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [cellsUpto_st_other _ _ _ _ (fun i => (low_ne i 3 sIN (by decide)).symm), i1]
    simp [hσB, hσA, hσG, gSt, σ0, Function.update_of_ne (Ne.symm sLT_ne_sIN), Function.update_of_ne (Ne.symm sNT_ne_sIN)]
  · rw [cellsUpto_st_other _ _ _ _ (fun i => (low_ne i 3 sCT (by decide)).symm)]
    have hnot : ∀ i', ¬ tmem sCT (symTrip i') := fun i' => low_not_tmem_sym _ (by decide) i'
    have hnot' : ∀ k, ¬ tmem sCT (carTrip k) := fun k => low_not_tmem_car _ (by decide) k
    rw [(f1 sCT hnot hnot' (by decide)).1]
    simp [hσB, hσA, hσG, gSt, σ0, sCT, sIN, sNT, sLT]
  · intro i h
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := d1 i h
    simp only [symTrip] at x1 x2 x3 x4 x5 x6
    refine ⟨?_, x2, ?_, x4, ?_, x6⟩
    · show (cellsUpto τ1 a 4).st (sSym i 0) = _
      rw [show (sSym i 0) = sSym i ⟨(0 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x1
    · show (cellsUpto τ1 a 4).st (sSym i 1) = _
      rw [show (sSym i 1) = sSym i ⟨(1 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x3
    · show (cellsUpto τ1 a 4).st (sSym i 2) = _
      rw [show (sSym i 2) = sSym i ⟨(2 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x5
  · intro i h
    have hy : ∃ i' : Fin 4, i'.val < a ∧ i'.val < 4 ∧ sSym i 3 = sSym i' 3 := ⟨i, h, i.isLt, rfl⟩
    exact ⟨by simp only [cellsUpto, if_pos hy], (keep i 3 (by decide)).2⟩
  · intro i h
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := b1 i h
    simp only [symTrip] at x1 x2 x3 x4 x5 x6
    have hn : ¬ ∃ i' : Fin 4, i'.val < a ∧ i'.val < 4 ∧ sSym i 3 = sSym i' 3 := by
      rintro ⟨i', h1, -, he⟩
      have := ((sSym_eq_iff _ _ _ _).mp he).1
      subst this
      omega
    refine ⟨⟨?_, x2, ?_, x4, ?_, x6⟩, by simp only [cellsUpto, if_neg hn]; exact (keep i 3 (by decide)).1,
      (keep i 3 (by decide)).2⟩
    · show (cellsUpto τ1 a 4).st (sSym i 0) = _
      rw [show (sSym i 0) = sSym i ⟨(0 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x1
    · show (cellsUpto τ1 a 4).st (sSym i 1) = _
      rw [show (sSym i 1) = sSym i ⟨(1 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x3
    · show (cellsUpto τ1 a 4).st (sSym i 2) = _
      rw [show (sSym i 2) = sSym i ⟨(2 : Fin 3).val, by omega⟩ from rfl, cellsUpto_trip]
      exact x5
  · intro i j hj
    have hn : ∀ i' : Fin 4, sSym i j ≠ sSym i' 3 := by
      intro i' he
      have := congrArg Fin.val ((sSym_eq_iff _ _ _ _).mp he).2
      simp at this
      omega
    rw [cellsUpto_st_other _ _ _ _ hn]
    exact keep i j (by omega)

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Main
