import Proof.Wire_3_5.Selection.CosAsm

/-! # C1.5 parse, part 1: the request's numbers (P3:1188-1189, 1326-1330)

Paper: the star partition's parameters "`r` even, `s = ⌊log₂(n/r+1)⌋`, `b = 2^s − 1`, `k = rs`" (P3:1188-1189) of the
request `(n, r, gates, populations)` (P3:1326-1330). From the framed request word on the input stream: `lenP` counts its
length `L` (the key width); `numsP` reads `n` and `r` (PA's `readNatM`) and computes `s`, `b`, `r/2`, `n − rb`,
`s·(r/2)`, `k` (PA's phases B–D, `StarNums`); `shapeP` sets the gate routine's shape registers (C1.4's `hh`, `b`,
`s`, `fL`, `fR`, `V + 1`) and `n + 1`; `widthP` sets the word width `W = 8(L + n + 2)`, `2W + 1` and the rewind bound
`8W²`. Main declarations: `lenP_spec`, `numsP_spec`, `shapeP_spec`, `widthP_spec`. Paper quantity: the star
partition's parameters of the request. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec dbl dbl_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (halveM halveM_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith (mulAddW mulAddW_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.StarNums (phaseB phaseC phaseD phaseB_spec phaseC_spec phaseD_spec)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)
open NearCubicWires.WireExponent3_5 (ratWord)

/-! ## The length -/

/-- The counting loop of `lenP`. -/
def lenLoop : WM 49 112 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.inc 85) (.seq (.inc 89) (.inc 89)))))

theorem lenLoop_spec (cap : ℕ) (w : List Bool) :
    ∀ (j : ℕ) (σ : WState 49 112) (a b : ℕ), σ.st 0 = frameP w ++ [false] → σ.sh 0 = 2 * (w.length - j) →
      j ≤ w.length → σ.val 85 = a → σ.val 89 = b → a + j ≤ cap → b + 2 * j ≤ cap →
      WExec cap lenLoop σ (((σ.seth 0 (2 * w.length)).setv 85 (a + j)).setv 89 (b + 2 * j)) (j * 17 + 1)
  | 0, σ, a, b, hI, hIh, _, h85, h89, _, _ => by
    refine WExec.cast cap (WExec.whsF ?_) ?_ (by omega)
    · simp only [wbit, hI, hIh, Nat.sub_zero]
      exact readTapeBit_frameP_end w []
    · apply WState.eq
      · funext i; by_cases hi : i = 0
        · subst hi; simp [hIh]
        · simp [Function.update_apply, hi]
      · rfl
      · funext r; by_cases h1 : r = 89
        · subst h1; simp [h89]
        · by_cases h2 : r = 85
          · subst h2; simp [h85]
          · simp [Function.update_apply, h1, h2]
      · rfl
  | j + 1, σ, a, b, hI, hIh, hj, h85, h89, ha, hb => by
    have hm : wbit σ 0 = true := by
      simp only [wbit, hI, hIh]
      have := PrimT.rd_marker [] w [false] (w.length - (j + 1)) (by omega)
      simpa [show 2 * (w.length - (j + 1)) = 2 * (w.length - (j + 1)) from rfl] using this
    have s1 := WExec.fwd (cap := cap) 0 σ
    set σ1 := σ.seth 0 (σ.sh 0 + 1) with hσ1
    have s2 := WExec.fwd (cap := cap) 0 σ1
    set σ2 := σ1.seth 0 (σ1.sh 0 + 1) with hσ2
    have s3 := WExec.inc (cap := cap) 85 σ2 (by simp [hσ2, hσ1, h85]; omega)
    set σ3 := σ2.setv 85 (σ2.val 85 + 1) with hσ3
    have s4 := WExec.inc (cap := cap) 89 σ3 (by simp [hσ3, hσ2, hσ1, h89]; omega)
    set σ4 := σ3.setv 89 (σ3.val 89 + 1) with hσ4
    have s5 := WExec.inc (cap := cap) 89 σ4 (by simp [hσ4, hσ3, hσ2, hσ1, h89]; omega)
    set σ5 := σ4.setv 89 (σ4.val 89 + 1) with hσ5
    have ih := lenLoop_spec cap w j σ5 (a + 1) (b + 2) (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hI])
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hIh]; omega) (by omega) (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, h85])
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, h89]) (by omega) (by omega)
    refine WExec.cast cap (WExec.whsT hm (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ih) ?_
      (by ring_nf; omega)
    apply WState.eq
    · funext i; by_cases hi : i = 0
      · subst hi; simp
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hi]
    · rfl
    · funext r; by_cases h1 : r = 89
      · subst h1; simp; omega
      · by_cases h2 : r = 85
        · subst h2; simp [hσ5, hσ4, hσ3, hσ2, hσ1, h85, Function.update_apply]; omega
        · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h1, h2]
    · rfl

/-- The length count's cost. -/
def lenCost (L : ℕ) : ℕ := L * 17 + 1 + 1 + (2 * L * (1 + 8) + 1 + 1 + (7 * (2 * L) + 1) + 1 + (3 * (2 * L) + 1))

/-- **The input's length** into `85`; the input head home, `89` back to `0`. -/
theorem lenP_spec (cap : ℕ) (w : List Bool) (σ : WState 49 112) (hI : σ.st 0 = frame w) (hIh : σ.sh 0 = 0)
    (h85 : σ.val 85 = 0) (h89 : σ.val 89 = 0) (h98 : σ.val 98 = 0) (hcap : 2 * w.length + 1 ≤ cap) :
    WExec cap lenP σ (σ.setv 85 w.length) (lenCost w.length) := by
  have x1 := lenLoop_spec cap w w.length σ 0 0 (by rw [hI, frame_eq_frameP]) (by simp [hIh]) le_rfl h85 h89
    (by omega) (by omega)
  simp only [Nat.zero_add] at x1
  set σ1 := ((σ.seth 0 (2 * w.length)).setv 85 w.length).setv 89 (2 * w.length) with hσ1
  have x2 := rewS_spec cap 0 89 98 (by decide) σ1 (2 * w.length) (by simp [hσ1]) (by simp [hσ1, h98]) (by omega)
    (by simp [hσ1])
  have x3 := wclear_spec (cap := cap) 89 (2 * w.length) (σ1.seth 0 0) (by simp [hσ1]) (by simp [hσ1]; omega)
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ (by unfold lenCost; omega)
  apply WState.eq
  · funext i; by_cases hi : i = 0
    · subst hi; simp [hσ1, hIh]
    · simp [hσ1, Function.update_apply, hi]
  · rfl
  · funext r; by_cases h1 : r = 89
    · subst h1; simp [hσ1, h89]
    · simp [hσ1, Function.update_apply, h1]
  · rfl

/-! ## `n`, `r` and the star numbers -/

/-- The request word after its first two fields. -/
def tailG (R : SelectionReq) : List Bool :=
  natWord R.gates.length ++ ((gInts R).flatMap intWord ++ (natWord R.pops.length ++
    R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2))

theorem selWord_eq (R : SelectionReq) : selWord R = natWord R.n ++ (natWord R.r ++ tailG R) := by
  unfold selWord tailG
  rw [gates_word_eq]
  simp [List.append_assoc]

/-- The numbers' state: `n`, `r`, `s`, `b`, `r/2`, `n − rb`, `s·(r/2)`, `k`; the input head past `n`, `r`. -/
def numsSt (R : SelectionReq) (h : ParamsOk R) (σ : WState 49 112) : WState 49 112 :=
  (((((((((σ.seth 0 (2 * ((natWord R.n).length + (natWord R.r).length))).setv 64 R.n).setv 67 R.r).setv 68 R.s).setv
    69 (starParamsOf R h).b).setv 70 (R.r / 2)).setv 71 (R.n - R.r * (starParamsOf R h).b)).setv 72
    (R.s * (R.r / 2))).setv 73 (R.r * R.s))

/-- The numbers' cost. -/
def numsCost (R : SelectionReq) (h : ParamsOk R) : ℕ :=
  (natBitLength R.n + 2) * (40 * 2 ^ natBitLength R.n + 40) + 1 + ((natBitLength R.r + 2) * (40 * 2 ^ natBitLength R.r +
    40) + 1 + ((R.n + 2) * (180 * R.n + 60) + 91 * R.n + 211 + 1 + (R.s * (18 * 2 ^ R.s + 7) + 18 * R.s +
      (starParamsOf R h).b * (18 * R.r + 8) + 18 * (starParamsOf R h).b + 33 * (R.r * (starParamsOf R h).b) +
      18 * R.n + 30 * R.r + 80 + 1 + ((R.r / 2) * (18 * R.s + 8) + 18 * (R.r / 2) + R.s * (18 * R.r + 8) +
        18 * R.s + 0 * (18 * 0 + 8) + 18 * 0 + 7 * 0 + 40))))

theorem Pm_apply (i : Fin 20) : Pm i = ⟨64 + i.val, by omega⟩ := rfl

theorem Pm_0 : Pm 0 = 64 := by decide
theorem Pm_1 : Pm 1 = 65 := by decide
theorem Pm_2 : Pm 2 = 66 := by decide
theorem Pm_3 : Pm 3 = 67 := by decide
theorem Pm_4 : Pm 4 = 68 := by decide
theorem Pm_5 : Pm 5 = 69 := by decide
theorem Pm_6 : Pm 6 = 70 := by decide
theorem Pm_7 : Pm 7 = 71 := by decide
theorem Pm_8 : Pm 8 = 72 := by decide
theorem Pm_9 : Pm 9 = 73 := by decide
theorem Pm_10 : Pm 10 = 74 := by decide

/-- **`n`, `r` and the star numbers** into PA's block. -/
theorem numsP_spec (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (σ : WState 49 112)
    (hI : σ.st 0 = frame (selWord R)) (hIh : σ.sh 0 = 0)
    (hz : ∀ r : Fin 112, ((64 ≤ r.val ∧ r.val < 84) ∨ r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 94) → σ.val r = 0)
    (hc1 : 2 ^ (natBitLength R.n + 1) ≤ cap) (hc2 : 2 ^ (natBitLength R.r + 1) ≤ cap) (hc3 : R.n + 4 ≤ cap)
    (hc4 : 2 ^ (R.s + 1) ≤ cap) (hc5 : R.n + R.r * (starParamsOf R h).b + R.r + (starParamsOf R h).b + 1 ≤ cap)
    (hc6 : R.s * (R.r / 2) + R.s + R.r / 2 ≤ cap) (hc7 : R.r * R.s + R.r + R.s ≤ cap) :
    WExec cap numsP σ (numsSt R h σ) (numsCost R h) := by
  have h' := h
  obtain ⟨hr2, h2, h4⟩ := h'
  have zv : ∀ r : Fin 112, 64 ≤ r.val → r.val < 84 → σ.val r = 0 := fun r h1 h2 => hz r (Or.inl ⟨h1, h2⟩)
  have zP : ∀ i : Fin 20, σ.val (Pm i) = 0 := fun i => zv _ (by simp [Pm_apply]) (by simp [Pm_apply]; omega)
  have hz89 := hz 89 (by decide)
  have hz90 := hz 90 (by decide)
  have hz91 := hz 91 (by decide)
  have hz94 := hz 94 (by decide)
  -- n
  have x1 := readNatM_spec cap true 0 91 90 64 94 89 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) R.n [] (frameP (natWord R.r ++ tailG R) ++ [false]) σ
    (by rw [hI, selWord_eq, frame_eq_frameP, frameP_append']; simp [PrimAsm.ParseNat.enc, marks_eq])
    (by simp [hIh]) hz91 hz90 hz94 hz89 (by rw [zv 64 (by decide) (by decide)]; simpa using hc1)
  rw [zv 64 (by decide) (by decide), Nat.zero_add] at x1
  simp only [PrimAsm.ParseNat.stp, if_true, List.length_nil, Nat.zero_add] at x1
  set σ1 := (σ.seth 0 (2 * (natWord R.n).length)).setv 64 R.n with hσ1
  -- r
  have h67 : σ1.val 67 = 0 := by simp [hσ1, zv 67 (by decide) (by decide)]
  have x2 := readNatM_spec cap true 0 91 90 67 94 89 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) R.r (frameP (natWord R.n))
    (frameP (tailG R) ++ [false]) σ1
    (by simp [hσ1, hI, selWord_eq, frame_eq_frameP, frameP_append', PrimAsm.ParseNat.enc, marks_eq])
    (by simp [hσ1, frameP_length']) (by simp [hσ1, hz91]) (by simp [hσ1, hz90]) (by simp [hσ1, hz94])
    (by simp [hσ1, hz89]) (by rw [h67]; simpa using hc2)
  rw [h67, Nat.zero_add] at x2
  simp only [PrimAsm.ParseNat.stp, if_true, frameP_length'] at x2
  set σ2 := (σ1.seth 0 (2 * (natWord R.n).length + 2 * (natWord R.r).length)).setv 67 R.r with hσ2
  -- phases B–D
  have hs2 : ∀ i : Fin 20, 11 ≤ i.val → σ2.val (Pm i) = 0 := by
    intro i hi
    have h64 : Pm i ≠ 64 := fun e => by have := congrArg Fin.val e; simp [Pm_apply] at this; omega
    have h67' : Pm i ≠ 67 := fun e => by have := congrArg Fin.val e; simp [Pm_apply] at this; omega
    simp [hσ2, hσ1, h64, h67', zP i]
  have v20 : σ2.val (Pm 0) = R.n := by simp [hσ2, hσ1, Pm_0]
  have v23 : σ2.val (Pm 3) = R.r := by simp [hσ2, Pm_3]
  have xB := phaseB_spec cap Pm σ2 hs2 (by simp [hσ2, hσ1, Pm_2, zv 66 (by decide) (by decide)])
    (by simp [hσ2, hσ1, Pm_4, zv 68 (by decide) (by decide)]) (by rw [v23]; omega) (by rw [v23, v20]; omega)
    (by rw [v20]; omega)
  rw [v20, v23] at xB
  set σ3 := σ2.setv (Pm 4) (Nat.log 2 (R.n / R.r + 1)) with hσ3
  have hs3 : ∀ i : Fin 20, 11 ≤ i.val → σ3.val (Pm i) = 0 := by
    intro i hi
    have h4' : Pm i ≠ Pm 4 := fun e => by have := Pm.injective e; subst this; simp at hi
    simp [hσ3, h4', hs2 i hi]
  have xC := phaseC_spec cap Pm σ3 R.n R.r R.s (starParamsOf R h).b hs3
    (by simp [hσ3, hσ2, hσ1, Pm_0, Pm_4]) (by simp [hσ3, hσ2, Pm_3, Pm_4]) (by simp [hσ3]; rfl) rfl
    (by simp [hσ3, hσ2, hσ1, Pm_5, Pm_4, zv 69 (by decide) (by decide)])
    (by simp [hσ3, hσ2, hσ1, Pm_6, Pm_4, zv 70 (by decide) (by decide)])
    (by simp [hσ3, hσ2, hσ1, Pm_7, Pm_4, zv 71 (by decide) (by decide)]) hc4 hc5
  set σ4 := ((σ3.setv (Pm 5) (starParamsOf R h).b).setv (Pm 6) (R.r / 2)).setv (Pm 7)
    (R.n - R.r * (starParamsOf R h).b) with hσ4
  have hs4 : ∀ i : Fin 20, 11 ≤ i.val → σ4.val (Pm i) = 0 := by
    intro i hi
    have n5 : Pm i ≠ Pm 5 := fun e => by have := Pm.injective e; subst this; simp at hi
    have n6 : Pm i ≠ Pm 6 := fun e => by have := Pm.injective e; subst this; simp at hi
    have n7 : Pm i ≠ Pm 7 := fun e => by have := Pm.injective e; subst this; simp at hi
    simp [hσ4, n5, n6, n7, hs3 i hi]
  have xD := phaseD_spec cap 0 Pm σ4 0 R.r R.s (R.r / 2) hs4
    (by simp [hσ4, hσ3, hσ2, hσ1, Pm_1, Pm_4, Pm_5, Pm_6, Pm_7, zv 65 (by decide) (by decide)])
    (by simp [hσ4, hσ3, hσ2, Pm_3, Pm_4, Pm_5, Pm_6, Pm_7])
    (by simp [hσ4, hσ3, Pm_4, Pm_5, Pm_6, Pm_7]; rfl) (by simp [hσ4, Pm_6, Pm_7])
    (by simp [hσ4, hσ3, hσ2, hσ1, Pm_8, Pm_4, Pm_5, Pm_6, Pm_7, zv 72 (by decide) (by decide)])
    (by simp [hσ4, hσ3, hσ2, hσ1, Pm_9, Pm_4, Pm_5, Pm_6, Pm_7, zv 73 (by decide) (by decide)])
    (by simp [hσ4, hσ3, hσ2, hσ1, Pm_10, Pm_4, Pm_5, Pm_6, Pm_7, zv 74 (by decide) (by decide)]) hc6 hc7 (by simp)
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq xB (WExec.seq xC xD)))) ?_ (by unfold numsCost; omega)
  have e74 : σ.val 74 = 0 := zv 74 (by decide) (by decide)
  simp only [hσ4, hσ3, hσ2, hσ1, Pm_4, Pm_5, Pm_6, Pm_7, Pm_8, Pm_9, Pm_10, Nat.zero_mul]
  apply WState.eq
  · funext i; by_cases hi : i = 0
    · subst hi; simp [numsSt]; ring
    · simp [numsSt, Function.update_apply, hi]
  · rfl
  · funext r
    by_cases h74 : r = 74
    · subst h74; simp [numsSt, e74]
    · simp only [numsSt, WState.setv_val, WState.seth_val, Function.update_apply, h74, if_false]
      rfl
  · rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
