import Proof.Wire_3_5.Selection.CosLoop
import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # C1.5: a raw `natWord` from a unary register (P3:1360, 3673)

Paper: "Select a minimum objective" (P3:1360); the union machine reads the selected coset (P3:3673) as the raw word
`cosetWord c = natListWord c`, whose fields are the self-delimiting naturals `natWord v = 1^L 0 b₀…b_{L−1}`
(`L = natBitLength v`, little-endian). **`rawNatW O R`** appends `natWord v` RAW (one cell per bit) to the stream `O`
from the unary register `R 0 = v`: PA's `bitLenM` computes `L`, then `L` ones and a zero, then `L` halvings of a copy
of `v` (PA's `halveM`), each remainder emitted (`emitW`). Donors checked: PA's `writeNatM` writes
the FRAMED form `marks (natWord v)` (a table's field), not the raw output word; C6's `CWEnvChk` parses raw words. Main
declarations: `appS`, `onesW`, `payW`, `rawNatW`, `rawCost`, **`rawNatW_spec`**. Paper quantity: one syndrome code of
the selected coset, as a field of the output word. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (emitW emitW_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (halveM halveM_spec bitLenM bitLenM_spec)

variable {ns nr : ℕ}

/-- The state with `u` appended to stream `O` and its head at the new end. -/
def appS (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : WState ns nr :=
  (σ.sets O (σ.st O ++ u)).seth O ((σ.st O).length + u.length)

@[simp] theorem appS_st (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) :
    (appS σ O u).st = Function.update σ.st O (σ.st O ++ u) := rfl
@[simp] theorem appS_sh (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) :
    (appS σ O u).sh = Function.update σ.sh O ((σ.st O).length + u.length) := rfl
@[simp] theorem appS_val (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : (appS σ O u).val = σ.val := rfl
@[simp] theorem appS_cell (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : (appS σ O u).cell = σ.cell := rfl

theorem appS_append (σ : WState ns nr) (O : Fin (ns + 1)) (u u' : List Bool) :
    appS (appS σ O u) O u' = appS σ O (u ++ u') := by
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp; ring
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl

theorem appS_nil (σ : WState ns nr) (O : Fin (ns + 1)) (hO : σ.sh O = (σ.st O).length) : appS σ O [] = σ := by
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hO]
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl

theorem appS_setv (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) (r : Fin nr) (x : ℕ) :
    appS (σ.setv r x) O u = (appS σ O u).setv r x := rfl

theorem appS_hO (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) :
    (appS σ O u).sh O = ((appS σ O u).st O).length := by simp

theorem emitW_app (cap : ℕ) (O : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (emitW O b) σ (appS σ O [b]) 3 := by
  have h := emitW_spec cap O b σ hO
  exact h

/-! ## `1^m` -/

/-- `m` ones appended (`K = m` counts down). -/
def onesW (O : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (emitW O true))

theorem onesW_spec (cap : ℕ) (O : Fin (ns + 1)) (K : Fin nr) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val K = m → m ≤ cap → σ.sh O = (σ.st O).length →
      WExec cap (onesW O K) σ ((appS σ O (List.replicate m true)).setv K 0) (7 * m + 1)
  | 0, σ, h0, _, hO => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by omega)
    rw [List.replicate_zero, appS_nil σ O hO, ← h0, wsetv_same]
  | m + 1, σ, hm, hc, hO => by
    have d := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e := emitW_app cap O true σ1 (by simp [hσ1, hO])
    have ih := onesW_spec cap O K m (appS σ1 O [true]) (by simp [hσ1, hm]) (by omega) (appS_hO _ _ _)
    rw [appS_append] at ih
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d e) ih) ?_ (by omega)
    rw [hσ1, appS_setv, wsetv_setv, List.singleton_append, ← List.replicate_succ]

/-! ## The payload bits -/

/-- `m` low bits of `w`, least significant first, appended (`K = m` counts down; `w` is halved each round). -/
def payW (O : Fin (ns + 1)) (w q rb K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (halveM w q rb) (.seq (.ifr rb (emitW O true) (emitW O false)) (WM.clear rb))))

theorem testBit_zero_eq (w : ℕ) : w.testBit 0 = decide (w % 2 = 1) := Nat.testBit_zero w

theorem payW_spec (cap : ℕ) (O : Fin (ns + 1)) (w q rb K : Fin nr) (hwq : w ≠ q) (hwr : w ≠ rb) (hqr : q ≠ rb)
    (hKw : K ≠ w) (hKq : K ≠ q) (hKr : K ≠ rb) (hcap1 : 1 ≤ cap) :
    ∀ (m : ℕ) (σ : WState ns nr) (w0 : ℕ), σ.val K = m → σ.val w = w0 → σ.val q = 0 → σ.val rb = 0 → m ≤ cap →
      w0 ≤ cap → σ.sh O = (σ.st O).length →
      WExec cap (payW O w q rb K) σ
        (((appS σ O ((List.range m).map fun i => w0.testBit i)).setv w (w0 / 2 ^ m)).setv K 0)
        (m * (9 * w0 + 25) + 1)
  | 0, σ, w0, h0, hw, _, _, _, _, hO => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by omega)
    simp only [List.range_zero, List.map_nil, pow_zero, Nat.div_one]
    rw [appS_nil σ O hO, ← hw, wsetv_same, ← h0, wsetv_same]
  | m + 1, σ, w0, hm, hw, hq, hr, hc, hwc, hO => by
    have d := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have h := halveM_spec cap w q rb hwq hwr hqr σ1 (by simp [hσ1, Ne.symm hKq, hq])
      (by simp [hσ1, Ne.symm hKr, hr]) (by simp [hσ1, Ne.symm hKw, hw, hwc]) hcap1
    have hw1 : σ1.val w = w0 := by simp [hσ1, Ne.symm hKw, hw]
    rw [hw1] at h
    set σ2 := (σ1.setv w (w0 / 2)).setv rb (w0 % 2) with hσ2
    have hO2 : σ2.sh O = (σ2.st O).length := by simp [hσ2, hσ1, hO]
    set b := w0.testBit 0 with hb
    have x3 : WExec cap (.ifr rb (emitW O true) (emitW O false)) σ2 (appS σ2 O [b]) (3 + 1) := by
      by_cases h2 : w0 % 2 = 1
      · have hb' : b = true := by rw [hb, testBit_zero_eq]; simp [h2]
        rw [hb']
        exact WExec.ifrT (by simp [hσ2, h2]) (emitW_app cap O true σ2 hO2)
      · have hb' : b = false := by rw [hb, testBit_zero_eq]; simp [h2]
        rw [hb']
        exact WExec.ifrF (by simp [hσ2]; omega) (emitW_app cap O false σ2 hO2)
    have hrb3 : (appS σ2 O [b]).val rb = w0 % 2 := by simp [hσ2]
    have x4 := wclear_spec (cap := cap) rb (w0 % 2) (appS σ2 O [b]) hrb3 (by rw [hrb3]; omega)
    set σ4 := (appS σ2 O [b]).setv rb 0 with hσ4
    have ih := payW_spec cap O w q rb K hwq hwr hqr hKw hKq hKr hcap1 m σ4 (w0 / 2)
      (by simp [hσ4, hσ2, hσ1, hKr, hKw, Ne.symm hKr, Ne.symm hKw, hm]) (by simp [hσ4, hσ2, hwr])
      (by simp [hσ4, hσ2, hσ1, hqr, hwq, hKq, Ne.symm hqr, Ne.symm hwq, Ne.symm hKq, hq]) (by simp [hσ4]) (by omega)
      (by have := Nat.div_le_self w0 2; omega) (appS_hO _ _ _)
    have hcost : 1 + 1 + (9 * w0 + 6 + 1 + (3 + 1 + 1 + (3 * (w0 % 2) + 1))) + 2 + (m * (9 * (w0 / 2) + 25) + 1) ≤
        (m + 1) * (9 * w0 + 25) + 1 := by
      have h1 : w0 / 2 ≤ w0 := Nat.div_le_self w0 2
      have h2 : m * (9 * (w0 / 2) + 25) ≤ m * (9 * w0 + 25) := Nat.mul_le_mul_left _ (by omega)
      have h3 : w0 % 2 ≤ 1 := by omega
      nlinarith
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d (WExec.seq h (WExec.seq x3 x4))) ih) ?_ hcost
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [hσ4, hσ2, hσ1, List.range_succ_eq_map]; ring
      · simp [hσ4, hσ2, hσ1, Function.update_apply, hj]
    · funext j; by_cases hj : j = O
      · subst hj
        simp [hσ4, hσ2, hσ1, List.range_succ_eq_map, Function.comp_def, Nat.testBit_div_two, hb,
          List.append_assoc]
      · simp [hσ4, hσ2, hσ1, Function.update_apply, hj]
    · funext j
      by_cases hjK : j = K
      · subst hjK; simp [Function.update_apply]
      · by_cases hjw : j = w
        · subst hjw
          simp [hσ4, hσ2, hσ1, Function.update_apply, hjK, hwr, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
        · by_cases hjr : j = rb
          · subst hjr; simp [hσ4, hσ2, hσ1, Function.update_apply, hjK, hjw, hr]
          · simp [hσ4, hσ2, hσ1, Function.update_apply, hjK, hjw, hjr]
    · simp [hσ4, hσ2, hσ1]

/-! ## The raw writer -/

/-- The writer's eight registers as PA's block (`R 0 = v`, `w`, `q`, `rb`, `L`, `K`, `t`, unused). -/
def wB (R : Fin 12 ↪ Fin nr) : Fin 8 ↪ Fin nr :=
  ⟨fun i => R (Fin.castLE (by omega) i), fun a b h => Fin.castLE_injective _ (R.injective h)⟩

theorem wB_apply (R : Fin 12 ↪ Fin nr) (i : Fin 8) : wB R i = R (Fin.castLE (by omega) i) := rfl

/-- **Append the raw `natWord v`** (`v = R 0`, kept). -/
def rawNatW (O : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (bitLenM (wB R)) (.seq (FinalPass.Hash4.wcopyR (R 4) (R 5) (R 6)) (.seq (onesW O (R 5))
    (.seq (emitW O false) (.seq (FinalPass.Hash4.wcopyR (R 0) (R 1) (R 6)) (.seq (FinalPass.Hash4.wcopyR (R 4) (R 5) (R 6))
      (.seq (payW O (R 1) (R 2) (R 3) (R 5)) (.seq (WM.clear (R 4)) (WM.clear (R 1)))))))))

/-- The writer's cost at the value `v`. -/
def rawCost (v : ℕ) : ℕ :=
  60 * v + 60 + 1 + (18 * natBitLength v + 3 + 1 + (7 * natBitLength v + 1 + 1 + (3 + 1 + (18 * v + 3 + 1 +
    (18 * natBitLength v + 3 + 1 + (natBitLength v * (9 * v + 25) + 1 + 1 + (3 * natBitLength v + 1 + 1 + (3 * 0 + 1))))))))

theorem fixedWidth_eq (L v : ℕ) :
    WilliamsPublishedForm.fixedWidthNatBits L v = (List.range L).map fun i => v.testBit i := by
  unfold WilliamsPublishedForm.fixedWidthNatBits
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem natBitLength_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 v
  omega

/-- **The raw writer**: `natWord v` appended to `O` (head at the new end); every register comes back. -/
theorem rawNatW_spec (cap : ℕ) (O : Fin (ns + 1)) (R : Fin 12 ↪ Fin nr) (σ : WState ns nr)
    (hz : ∀ i : Fin 12, 1 ≤ i.val → i.val ≤ 6 → σ.val (R i) = 0) (hO : σ.sh O = (σ.st O).length)
    (hcap : 2 * σ.val (R 0) + 4 ≤ cap) :
    WExec cap (rawNatW O R) σ (appS σ O (RepairRepresentation.natWord (σ.val (R 0)))) (rawCost (σ.val (R 0))) := by
  have rne : ∀ i j : Fin 12, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
  set v := σ.val (R 0) with hv
  set L := natBitLength v with hL
  have hLv : L ≤ v + 1 := natBitLength_le v
  have hvL : v < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) v
  have z1 := hz 1 (by decide) (by decide)
  have z2 := hz 2 (by decide) (by decide)
  have z3 := hz 3 (by decide) (by decide)
  have z4 := hz 4 (by decide) (by decide)
  have z5 := hz 5 (by decide) (by decide)
  have z6 := hz 6 (by decide) (by decide)
  have x1 := bitLenM_spec cap (wB R) σ (by rw [wB_apply]; exact z1) (by rw [wB_apply]; exact z2)
    (by rw [wB_apply]; exact z3) (by rw [wB_apply]; exact z4) (by rw [wB_apply]; exact z6)
    (by rw [wB_apply]; show σ.val (R 0) + 2 ≤ cap; omega)
  simp only [wB_apply] at x1
  change WExec cap (bitLenM (wB R)) σ (σ.setv (R 4) L) (60 * v + 60) at x1
  set σ1 := σ.setv (R 4) L with hσ1
  have x2 := FinalPass.Hash4.wcopyR_spec cap (R 4) (R 5) (R 6) (rne 4 5 (by decide)) (rne 4 6 (by decide))
    (rne 5 6 (by decide)) σ1 (by simp [hσ1, rne 5 4 (by decide), z5]) (by simp [hσ1, rne 6 4 (by decide), z6])
    (by simp [hσ1]; omega)
  have hL1 : σ1.val (R 4) = L := by simp [hσ1]
  rw [hL1] at x2
  set σ2 := σ1.setv (R 5) L with hσ2
  have x3 := onesW_spec cap O (R 5) L σ2 (by simp [hσ2]) (by omega) (by simp [hσ2, hσ1, hO])
  set σ3 := (appS σ2 O (List.replicate L true)).setv (R 5) 0 with hσ3
  have x4 := emitW_app cap O false σ3 (by simp [hσ3])
  set σ4 := appS σ3 O [false] with hσ4
  have x5 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 1) (R 6) (rne 0 1 (by decide)) (rne 0 6 (by decide))
    (rne 1 6 (by decide)) σ4 (by simp [hσ4, hσ3, hσ2, hσ1, rne 1 5 (by decide), rne 1 4 (by decide), z1])
    (by simp [hσ4, hσ3, hσ2, hσ1, rne 6 5 (by decide), rne 6 4 (by decide), z6])
    (by simp [hσ4, hσ3, hσ2, hσ1, rne 0 5 (by decide), rne 0 4 (by decide)]; omega)
  have hv4 : σ4.val (R 0) = v := by simp [hσ4, hσ3, hσ2, hσ1, rne 0 5 (by decide), rne 0 4 (by decide), hv]
  rw [hv4] at x5
  set σ5 := σ4.setv (R 1) v with hσ5
  have x6 := FinalPass.Hash4.wcopyR_spec cap (R 4) (R 5) (R 6) (rne 4 5 (by decide)) (rne 4 6 (by decide))
    (rne 5 6 (by decide)) σ5 (by simp [hσ5, hσ4, hσ3, rne 5 1 (by decide)])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 6 1 (by decide), rne 6 5 (by decide), rne 6 4 (by decide), z6])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 4 1 (by decide), rne 4 5 (by decide)]; omega)
  have hL5 : σ5.val (R 4) = L := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, rne 4 1 (by decide), rne 4 5 (by decide)]
  rw [hL5] at x6
  set σ6 := σ5.setv (R 5) L with hσ6
  have x7 := payW_spec cap O (R 1) (R 2) (R 3) (R 5) (rne 1 2 (by decide)) (rne 1 3 (by decide))
    (rne 2 3 (by decide)) (rne 5 1 (by decide)) (rne 5 2 (by decide)) (rne 5 3 (by decide)) (by omega) L σ6 v
    (by simp [hσ6]) (by simp [hσ6, hσ5, rne 1 5 (by decide)])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, rne 2 5 (by decide), rne 2 1 (by decide), rne 2 4 (by decide), z2])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, rne 3 5 (by decide), rne 3 1 (by decide), rne 3 4 (by decide), z3])
    (by omega) (by omega) (by simp [hσ6, hσ5, hσ4, hσ3]; omega)
  set σ7 := ((appS σ6 O ((List.range L).map fun i => v.testBit i)).setv (R 1) (v / 2 ^ L)).setv (R 5) 0 with hσ7
  have hv0 : v / 2 ^ L = 0 := Nat.div_eq_of_lt hvL
  have hL7 : σ7.val (R 4) = L := by
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, rne 4 1 (by decide), rne 4 5 (by decide)]
  have x8 := wclear_spec (cap := cap) (R 4) L σ7 hL7 (by rw [hL7]; omega)
  have hw8 : (σ7.setv (R 4) 0).val (R 1) = 0 := by simp [hσ7, rne 1 4 (by decide), rne 1 5 (by decide), hv0]
  have x9 := wclear_spec (cap := cap) (R 1) 0 (σ7.setv (R 4) 0) hw8 (by rw [hw8]; omega)
  have hcost : 60 * v + 60 + 1 + (18 * L + 3 + 1 + (7 * L + 1 + 1 + (3 + 1 + (18 * v + 3 + 1 + (18 * L + 3 + 1 +
      (L * (9 * v + 25) + 1 + 1 + (3 * L + 1 + 1 + (3 * 0 + 1)))))))) = rawCost v := rfl
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6
    (WExec.seq x7 (WExec.seq x8 x9)))))))) ?_ (le_of_eq hcost)
  have hword : RepairRepresentation.natWord v =
      List.replicate L true ++ [false] ++ (List.range L).map fun i => v.testBit i := by
    rw [PrimAsm.ParseNat.natWord_eq, fixedWidth_eq, ← hL]; simp
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hword]; ring
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hword, List.append_assoc]
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj]
  · funext j
    by_cases h1 : j = R 1
    · subst h1; simp [Function.update_apply, z1]
    · by_cases h4 : j = R 4
      · subst h4; simp [Function.update_apply, h1, z4]
      · by_cases h5 : j = R 5
        · subst h5; simp [hσ7, Function.update_apply, h1, h4, z5]
        · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h1, h4, h5]
  · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
