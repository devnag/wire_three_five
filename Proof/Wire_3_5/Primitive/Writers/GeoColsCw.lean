import Proof.Wire_3_5.Primitive.Writers.GeoNums
import Proof.Wire_3_5.Primitive.Writers.GeoColsV

/-! # PA (d): the columns writer, part 1 (register framing, the codeword loop)

P3:1212-1216 (star:partition): "A fixed linear basis of each code gives polynomial-time encoding"; the columns of `φ`
in a block are the code's basis vectors at the data positions. For a data position `i < b`, the program `cwM`
streams the basis vector `(cwBit i q)_{q<b}` (`GeoColsV.cwBit_data` / `cwBit_par`: `[q = i]` off the parity positions,
bit `t` of `i+1` at the parity position `2^t − 1`), each bit as `[1,1,1,bit]`.

* `namesR` / `namesS`, **`val_keep`**, **`st_keep`**: a run keeps every register and stream its program never names;
* `emF`, `dblW`, `hitStep`, `cwStep` with specs; **`cwM_spec`**: `cwM` appends
  `(range b).flatMap (e4 ∘ cwBit i)`, every register other than the output counter back to its entry value.

Paper quantity of the main type: the basis vector `cwBit i` of data position `i` (P3:1216). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoColsCw
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.WireExponent3_5.PrimAsm.GeoNums
open NearCubicWires.WireExponent3_5.PrimAsm.GeoColsV

/-! ## Framing -/

section Frame
variable {ns nr : ℕ} (cap : ℕ)

/-- Whether a program names register `r`. -/
def namesR (r : Fin nr) : WM ns nr → Bool
  | .skip => false
  | .inc r' => decide (r' = r)
  | .dec r' => decide (r' = r)
  | .fwd _ => false
  | .bwd _ => false
  | .wr _ _ => false
  | .setc _ => false
  | .seq P Q => namesR r P || namesR r Q
  | .ifr r' P Q => decide (r' = r) || namesR r P || namesR r Q
  | .ifs _ P Q => namesR r P || namesR r Q
  | .whr r' P => decide (r' = r) || namesR r P
  | .whs _ P => namesR r P

/-- Whether a program names stream `i`. -/
def namesS (i : Fin (ns + 1)) : WM ns nr → Bool
  | .skip => false
  | .inc _ => false
  | .dec _ => false
  | .fwd i' => decide (i' = i)
  | .bwd i' => decide (i' = i)
  | .wr i' _ => decide (i' = i)
  | .setc _ => false
  | .seq P Q => namesS i P || namesS i Q
  | .ifr _ P Q => namesS i P || namesS i Q
  | .ifs i' P Q => decide (i' = i) || namesS i P || namesS i Q
  | .whr _ P => namesS i P
  | .whs i' P => decide (i' = i) || namesS i P

/-- **A run keeps every register its program never names.** -/
theorem val_keep {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (r : Fin nr)
    (hP : namesR r P = false) : τ.val r = σ.val r := by
  induction h with
  | skip => rfl
  | inc r' σ _ =>
    have hr : r ≠ r' := fun e => by subst e; simp [namesR] at hP
    simp [Function.update_of_ne hr]
  | dec r' σ _ =>
    have hr : r ≠ r' := fun e => by subst e; simp [namesR] at hP
    simp [Function.update_of_ne hr]
  | fwd => rfl
  | bwd => rfl
  | wr => rfl
  | setc => rfl
  | seq _ _ ih1 ih2 =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    rw [ih2 hP.2, ih1 hP.1]
  | ifrT _ _ ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact ih hP.1.2
  | ifrF _ _ ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | ifsT _ _ ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact ih hP.1
  | ifsF _ _ ih =>
    simp only [namesR, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | whrF _ => rfl
  | whrT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesR, Bool.or_eq_false_iff] at hP'
    rw [ih2 hP, ih1 hP'.2]
  | whsF _ => rfl
  | whsT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesR] at hP'
    rw [ih2 hP, ih1 hP']
  | mono _ _ ih => exact ih hP

/-- **A run keeps every stream its program never names.** -/
theorem st_keep {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (i : Fin (ns + 1))
    (hP : namesS i P = false) : τ.st i = σ.st i ∧ τ.sh i = σ.sh i := by
  induction h with
  | skip => exact ⟨rfl, rfl⟩
  | inc => exact ⟨rfl, rfl⟩
  | dec => exact ⟨rfl, rfl⟩
  | fwd i' σ =>
    have hi : i ≠ i' := fun e => by subst e; simp [namesS] at hP
    simp [Function.update_of_ne hi]
  | bwd i' σ =>
    have hi : i ≠ i' := fun e => by subst e; simp [namesS] at hP
    simp [Function.update_of_ne hi]
  | wr i' b σ =>
    have hi : i ≠ i' := fun e => by subst e; simp [namesS] at hP
    simp [Function.update_of_ne hi]
  | setc => exact ⟨rfl, rfl⟩
  | seq _ _ ih1 ih2 =>
    simp only [namesS, Bool.or_eq_false_iff] at hP
    exact ⟨(ih2 hP.2).1.trans (ih1 hP.1).1, (ih2 hP.2).2.trans (ih1 hP.1).2⟩
  | ifrT _ _ ih =>
    simp only [namesS, Bool.or_eq_false_iff] at hP
    exact ih hP.1
  | ifrF _ _ ih =>
    simp only [namesS, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | ifsT _ _ ih =>
    simp only [namesS, Bool.or_eq_false_iff] at hP
    exact ih hP.1.2
  | ifsF _ _ ih =>
    simp only [namesS, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | whrF _ => exact ⟨rfl, rfl⟩
  | whrT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesS] at hP'
    exact ⟨(ih2 hP).1.trans (ih1 hP').1, (ih2 hP).2.trans (ih1 hP').2⟩
  | whsF _ => exact ⟨rfl, rfl⟩
  | whsT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesS, Bool.or_eq_false_iff] at hP'
    exact ⟨(ih2 hP).1.trans (ih1 hP'.2).1, (ih2 hP).2.trans (ih1 hP'.2).2⟩
  | mono _ _ ih => exact ih hP

end Frame

/-! ## The registers -/

abbrev rB : Fin GR := 42
abbrev rR2 : Fin GR := 43
abbrev rT2 : Fin GR := 44
abbrev rK1 : Fin GR := 45
abbrev rPre : Fin GR := 46
abbrev rPost : Fin GR := 47
abbrev rK2 : Fin GR := 48
abbrev rDist : Fin GR := 49
abbrev rPw : Fin GR := 50
abbrev rI1 : Fin GR := 51
abbrev rK3 : Fin GR := 52
abbrev rDq : Fin GR := 53
abbrev rPwq : Fin GR := 54
abbrev rRem : Fin GR := 55
abbrev rCi : Fin GR := 56
abbrev rHit : Fin GR := 57
abbrev rRb : Fin GR := 58
abbrev rQ : Fin GR := 59
abbrev rU : Fin GR := 60
abbrev rPU : Fin GR := 61
abbrev rQU : Fin GR := 62
abbrev rZ : Fin GR := 63

/-! ## Small programs -/

variable (cap : ℕ)

/-- One column bit `[1,1,1,b]`. -/
def emB (b : Bool) : WM GS GR := emitW gOUT rOP (e4 b)

/-- Emit `[1,1,1,f≠0]` and clear the flag `f ∈ {0,1}`. -/
def emF (f : Fin GR) : WM GS GR := .ifr f (.seq (emB true) (.dec f)) (emB false)

theorem emF_spec (f : Fin GR) (hfO : f ≠ rOP) (σ : WState GS GR) (hf : σ.val f ≤ 1)
    (ho : σ.sh gOUT = (σ.st gOUT).length) (hc : σ.val rOP + 4 ≤ cap) :
    WExec cap (emF f) σ ((appendO σ gOUT rOP (e4 (decide (σ.val f = 1)))).setv f 0) 40 := by
  have hc' : σ.val rOP + (e4 true).length ≤ cap := by simp [e4]; omega
  by_cases h1 : σ.val f = 1
  · have e1 := emitW_spec cap gOUT rOP (e4 true) σ ho hc'
    have e2 := WExec.dec (cap := cap) f (appendO σ gOUT rOP (e4 true))
      (by rw [appendO_val, Function.update_of_ne hfO]; omega)
    have e := WExec.ifrT (r := f) (Q := emB false) (by omega) (WExec.seq e1 e2)
    rw [show (appendO σ gOUT rOP (e4 true)).val f - 1 = 0 by rw [appendO_val, Function.update_of_ne hfO]; omega] at e
    simp only [h1, decide_true]
    exact WExec.mono e (by simp [e4])
  · have h0 : σ.val f = 0 := by omega
    have e1 := emitW_spec cap gOUT rOP (e4 false) σ ho (by simp [e4] at hc' ⊢; omega)
    have e := WExec.ifrF (P := .seq (emB true) (.dec f)) h0 e1
    have hs : (appendO σ gOUT rOP (e4 false)).setv f 0 = appendO σ gOUT rOP (e4 false) := by
      rw [show (0 : ℕ) = (appendO σ gOUT rOP (e4 false)).val f by simp [Function.update_of_ne hfO, h0]]
      exact wsetv_same _ _
    simp only [h1, decide_false, hs]
    exact WExec.mono e (by simp [e4])

/-- `d := pw − 1`, `pw := 2·pw` (for `d = 0`, through `rT2`). -/
def dblW (pw d : Fin GR) : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR pw d rT2) (.seq (addTo d pw rT2) (.dec d))

theorem dblW_spec (pw d : Fin GR) (hpd : pw ≠ d) (hpt : pw ≠ rT2) (hdt : d ≠ rT2) (σ : WState GS GR)
    (hd : σ.val d = 0) (ht : σ.val rT2 = 0) (hc : 2 * σ.val pw ≤ cap) :
    WExec cap (dblW pw d) σ ((σ.setv d (σ.val pw - 1)).setv pw (2 * σ.val pw)) (40 * σ.val pw + 20) := by
  have e1 := FinalPass.Hash4.wcopyR_spec cap pw d rT2 hpd hpt hdt σ hd ht (by omega)
  have e2 := addTo_spec cap d pw rT2 (Ne.symm hpd) hdt hpt (σ.setv d (σ.val pw))
    (by simp [Function.update_of_ne (Ne.symm hdt), ht]) (by simp; omega)
    (by simp [Function.update_of_ne hpd]; omega)
  have e3 := WExec.dec (cap := cap) d ((σ.setv d (σ.val pw)).setv pw ((σ.setv d (σ.val pw)).val pw +
    (σ.setv d (σ.val pw)).val d)) (by simp [Function.update_of_ne (Ne.symm hpd)]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by simp; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases hj : j = d
  · subst hj; simp [Function.update_of_ne (Ne.symm hpd)]
  · by_cases hjp : j = pw
    · subst hjp; simp [Function.update_of_ne hpd]; omega
    · simp [Function.update_of_ne hj, Function.update_of_ne hjp]

/-- `ci := ci − 1`; `hit := [ci = 1]` (for `hit = 0`). -/
def hitStep : WM GS GR := .ifr rCi (.seq (.dec rCi) (.ifr rCi .skip (.inc rHit))) .skip

theorem hitStep_spec (σ : WState GS GR) (hh : σ.val rHit = 0) (hc : σ.val rCi ≤ cap) (hc1 : 1 ≤ cap) :
    ∃ τ c, WExec cap hitStep σ τ c ∧ τ.val rCi = σ.val rCi - 1 ∧
      τ.val rHit = (if σ.val rCi = 1 then 1 else 0) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      (∀ r, r ≠ rCi → r ≠ rHit → τ.val r = σ.val r) ∧ c ≤ 10 := by
  by_cases h0 : σ.val rCi = 0
  · refine ⟨σ, 1, WExec.ifrF h0 (WExec.skip σ), by omega, by simp [h0, hh], rfl, rfl, fun _ _ _ => rfl, by omega⟩
  · have e1 := WExec.dec (cap := cap) rCi σ hc
    by_cases h1 : σ.val rCi = 1
    · have v1 : (σ.setv rCi (σ.val rCi - 1)).val rCi = 0 := by simp; omega
      have e2 := WExec.inc (cap := cap) rHit (σ.setv rCi (σ.val rCi - 1))
        (by simp [Function.update_apply, Fin.ext_iff, GR, hh]; omega)
      refine ⟨_, _, WExec.ifrT h0 (WExec.seq e1 (WExec.ifrF v1 e2)), ?_, ?_, rfl, rfl, ?_, by omega⟩
      · simp [Function.update_apply, Fin.ext_iff, GR]
      · simp [Function.update_apply, Fin.ext_iff, GR, h1, hh]
      · intro r h1 h2; simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · have v1 : (σ.setv rCi (σ.val rCi - 1)).val rCi ≠ 0 := by simp; omega
      refine ⟨_, _, WExec.ifrT h0 (WExec.seq e1 (WExec.ifrT v1 (WExec.skip _))), ?_, ?_, rfl, rfl, ?_, by omega⟩
      · simp
      · simp [Function.update_apply, Fin.ext_iff, GR, h1, hh]
      · intro r h1 h2; simp [Function.update_of_ne h1]

/-- A data position of the codeword: `dq := dq − 1`, emit `[q = i]` (the flag `hit`). -/
def dataQ : WM GS GR := .seq (.dec rDq) (emF rHit)

/-- A parity position: emit the low bit of `rem`, `rem := rem/2`, and step the power. -/
def parQ : WM GS GR := .seq (halveM rRem rQ rRb) (.seq (emF rRb) (dblW rPwq rDq))

/-- **One codeword bit.** -/
def cwStep : WM GS GR := .seq hitStep (.ifr rDq dataQ parQ)

/-- The codeword step's cost bound. -/
def cwStepCost (pw rem : ℕ) : ℕ := 50 * (pw + rem) + 200

theorem cwStep_spec (σ : WState GS GR) (hh : σ.val rHit = 0) (hq : σ.val rQ = 0) (hrb : σ.val rRb = 0)
    (ht : σ.val rT2 = 0) (ho : σ.sh gOUT = (σ.st gOUT).length) (hc : σ.val rOP + 4 ≤ cap)
    (hc2 : 2 * σ.val rPwq ≤ cap) (hc3 : σ.val rCi ≤ cap) (hc4 : σ.val rRem ≤ cap) (hc5 : σ.val rDq ≤ cap)
    (hc1 : 1 ≤ cap) (hpar : σ.val rDq = 0 → σ.val rCi ≠ 1) :
    ∃ τ c, WExec cap cwStep σ τ c ∧
      τ.st gOUT = σ.st gOUT ++ e4 (if σ.val rDq = 0 then decide (σ.val rRem % 2 = 1) else decide (σ.val rCi = 1)) ∧
      τ.sh gOUT = (τ.st gOUT).length ∧ τ.val rOP = σ.val rOP + 4 ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
      τ.val rCi = σ.val rCi - 1 ∧ τ.val rHit = 0 ∧ τ.val rQ = 0 ∧ τ.val rRb = 0 ∧ τ.val rT2 = 0 ∧
      τ.val rDq = (if σ.val rDq = 0 then σ.val rPwq - 1 else σ.val rDq - 1) ∧
      τ.val rPwq = (if σ.val rDq = 0 then 2 * σ.val rPwq else σ.val rPwq) ∧
      τ.val rRem = (if σ.val rDq = 0 then σ.val rRem / 2 else σ.val rRem) ∧
      (∀ r, r ≠ rCi → r ≠ rHit → r ≠ rDq → r ≠ rPwq → r ≠ rRem → r ≠ rQ → r ≠ rRb → r ≠ rT2 → r ≠ rOP →
        τ.val r = σ.val r) ∧
      c ≤ cwStepCost (σ.val rPwq) (σ.val rRem) := by
  obtain ⟨σ1, c1, e1, v1C, v1H, s1, h1, k1, c1le⟩ := hitStep_spec cap σ hh hc3 hc1
  have k1' : ∀ r, r ≠ rCi → r ≠ rHit → σ1.val r = σ.val r := k1
  have d1 : σ1.val rDq = σ.val rDq := k1 _ (by decide) (by decide)
  have p1 : σ1.val rPwq = σ.val rPwq := k1 _ (by decide) (by decide)
  have m1 : σ1.val rRem = σ.val rRem := k1 _ (by decide) (by decide)
  have q1 : σ1.val rQ = 0 := by rw [k1 _ (by decide) (by decide), hq]
  have b1 : σ1.val rRb = 0 := by rw [k1 _ (by decide) (by decide), hrb]
  have t1 : σ1.val rT2 = 0 := by rw [k1 _ (by decide) (by decide), ht]
  have o1 : σ1.val rOP = σ.val rOP := k1 _ (by decide) (by decide)
  have ho1 : σ1.sh gOUT = (σ1.st gOUT).length := by rw [s1, h1]; exact ho
  by_cases hd : σ.val rDq = 0
  · -- parity
    have hH : σ1.val rHit = 0 := by rw [v1H, if_neg (hpar hd)]
    have e2 := halveM_spec cap rRem rQ rRb (by decide) (by decide) (by decide) σ1 q1 b1 (by omega) hc1
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (σ1.setv rRem (σ1.val rRem / 2)).setv rRb (σ1.val rRem % 2) := ⟨_, rfl⟩
    rw [← hσ2] at e2
    have v2b : σ2.val rRb = σ.val rRem % 2 := by rw [hσ2]; simp [m1]
    have v2r : σ2.val rRem = σ.val rRem / 2 := by rw [hσ2]; simp [Function.update_apply, Fin.ext_iff, GR, m1]
    have k2 : ∀ r, r ≠ rRem → r ≠ rRb → σ2.val r = σ1.val r := by
      intro r a b; rw [hσ2]; simp [Function.update_of_ne a, Function.update_of_ne b]
    have ho2 : σ2.sh gOUT = (σ2.st gOUT).length := by rw [hσ2]; simpa using ho1
    have o2 : σ2.val rOP = σ.val rOP := by rw [k2 _ (by decide) (by decide), o1]
    have e3 := emF_spec cap rRb (by decide) σ2 (by rw [v2b]; omega) ho2 (by omega)
    obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = (appendO σ2 gOUT rOP (e4 (decide (σ2.val rRb = 1)))).setv rRb 0 := ⟨_, rfl⟩
    rw [← hσ3] at e3
    have k3 : ∀ r, r ≠ rRb → r ≠ rOP → σ3.val r = σ2.val r := by
      intro r a b; rw [hσ3]; simp [Function.update_of_ne a, Function.update_of_ne b]
    have p3 : σ3.val rPwq = σ.val rPwq := by rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), p1]
    have d3 : σ3.val rDq = 0 := by rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), d1, hd]
    have t3 : σ3.val rT2 = 0 := by rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), t1]
    have e4' := dblW_spec cap rPwq rDq (by decide) (by decide) (by decide) σ3 d3 t3 (by rw [p3]; exact hc2)
    obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = (σ3.setv rDq (σ3.val rPwq - 1)).setv rPwq (2 * σ3.val rPwq) := ⟨_, rfl⟩
    rw [← hσ4] at e4'
    have k4 : ∀ r, r ≠ rDq → r ≠ rPwq → σ4.val r = σ3.val r := by
      intro r a b; rw [hσ4]; simp [Function.update_of_ne a, Function.update_of_ne b]
    have s4 : σ4.st = σ3.st := by rw [hσ4]; rfl
    have sh4 : σ4.sh = σ3.sh := by rw [hσ4]; rfl
    have st3 : σ3.st gOUT = σ.st gOUT ++ e4 (decide (σ.val rRem % 2 = 1)) := by
      rw [hσ3, v2b]; simp [hσ2, s1]
    refine ⟨σ4, _, WExec.seq e1 (WExec.ifrF (by rw [d1]; exact hd) (WExec.seq e2 (WExec.seq e3 e4'))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s4, st3, if_pos hd]
    · rw [s4, sh4, hσ3]; simp [hσ2, ho1, e4]
    · rw [k4 _ (by decide) (by decide), hσ3]; simp [Function.update_apply, Fin.ext_iff, GR, o2, e4]
    · intro s hs
      rw [s4, hσ3]; simp [Function.update_of_ne hs, hσ2, s1]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), v1C]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), hH]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), hσ2]
      simp [Function.update_apply, Fin.ext_iff, GR, q1]
    · rw [k4 _ (by decide) (by decide), hσ3]; simp
    · rw [k4 _ (by decide) (by decide), t3]
    · rw [hσ4, if_pos hd]; simp [Function.update_apply, Fin.ext_iff, GR, p3]
    · rw [hσ4, if_pos hd]; simp [p3]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), v2r, if_pos hd]
    · intro r a1 a2 a3 a4 a5 a6 a7 a8 a9
      rw [k4 r a3 a4, k3 r a7 a9, k2 r a5 a7, k1 r a1 a2]
    · simp only [cwStepCost]
      rw [m1] at e2
      have : c1 ≤ 10 := c1le
      omega
  · -- data
    have e2 := WExec.dec (cap := cap) rDq σ1 (by rw [d1]; exact hc5)
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setv rDq (σ1.val rDq - 1) := ⟨_, rfl⟩
    rw [← hσ2] at e2
    have k2 : ∀ r, r ≠ rDq → σ2.val r = σ1.val r := by
      intro r a; rw [hσ2]; simp [Function.update_of_ne a]
    have ho2 : σ2.sh gOUT = (σ2.st gOUT).length := by rw [hσ2]; exact ho1
    have o2 : σ2.val rOP = σ.val rOP := by rw [k2 _ (by decide), o1]
    have hH2 : σ2.val rHit = if σ.val rCi = 1 then 1 else 0 := by rw [k2 _ (by decide), v1H]
    have e3 := emF_spec cap rHit (by decide) σ2 (by rw [hH2]; split_ifs <;> omega) ho2 (by omega)
    obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = (appendO σ2 gOUT rOP (e4 (decide (σ2.val rHit = 1)))).setv rHit 0 := ⟨_, rfl⟩
    rw [← hσ3] at e3
    have k3 : ∀ r, r ≠ rHit → r ≠ rOP → σ3.val r = σ2.val r := by
      intro r a b; rw [hσ3]; simp [Function.update_of_ne a, Function.update_of_ne b]
    have hbit : decide (σ2.val rHit = 1) = decide (σ.val rCi = 1) := by
      rw [hH2]; by_cases hh1 : σ.val rCi = 1 <;> simp [hh1]
    refine ⟨σ3, _, WExec.seq e1 (WExec.ifrT (by rw [d1]; exact hd) (WExec.seq e2 e3)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ3, if_neg hd, ← hbit]; simp [hσ2, s1]
    · rw [hσ3]; simp [ho1, hσ2, e4]
    · rw [hσ3]; simp [Function.update_apply, Fin.ext_iff, GR, o2, e4]
    · intro s hs; rw [hσ3]; simp [Function.update_of_ne hs, hσ2, s1]
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), v1C]
    · rw [hσ3]; simp
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), q1]
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), b1]
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), t1]
    · rw [k3 _ (by decide) (by decide), hσ2, if_neg hd]; simp [d1]
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), p1, if_neg hd]
    · rw [k3 _ (by decide) (by decide), k2 _ (by decide), m1, if_neg hd]
    · intro r a1 a2 a3 a4 a5 a6 a7 a8 a9
      rw [k3 r a2 a9, k2 r a3, k1 r a1 a2]
    · simp only [cwStepCost]
      have : c1 ≤ 10 := c1le
      omega

/-! ## The codeword loop -/

theorem not_pow_of_between (k t : ℕ) (h1 : k + 1 < 2 ^ t) (h2 : 2 ^ t < 2 * (k + 1)) : ∀ t', k + 1 ≠ 2 ^ t' := by
  intro t' e
  have hlt : 2 ^ t' < 2 ^ t := by rw [← e]; exact h1
  have ht : t' < t := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hle : 2 ^ (t' + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  rw [Nat.pow_succ] at hle
  omega

theorem b_succ_pow (P : StarParams) : P.b + 1 = 2 ^ P.s := by
  have := Nat.one_le_two_pow (n := P.s)
  rw [b_eqC]; omega

/-- **The streamed bit is the codeword bit**: at step `k` with the power `2^t` (`k+1 ≤ 2^t < 2(k+1)`), the remainder
`(i+1)/2^t` and the countdown `i+1−k`. -/
theorem cw_bit_step (P : StarParams) (i k t : ℕ) (hi : i < P.b) (hpar : PrimT.C4Geo.isPar P i = false)
    (hk : k < P.b) (hlo : k + 1 ≤ 2 ^ t) (hhi : 2 ^ t < 2 * (k + 1)) :
    (if 2 ^ t - (k + 1) = 0 then decide ((i + 1) / 2 ^ t % 2 = 1) else decide (i + 1 - k = 1)) =
      PrimT.C4Geo.cwBit P i k := by
  by_cases hd : 2 ^ t - (k + 1) = 0
  · have e : k + 1 = 2 ^ t := by omega
    have hbs := b_succ_pow P
    have hlt : 2 ^ t < 2 ^ P.s := by omega
    have hts : t < P.s := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    have hki : k ≠ i := by
      intro h
      subst h
      have := (isPar_iff P k hi).2 ⟨t, e⟩
      rw [hpar] at this
      exact Bool.false_ne_true this
    rw [if_pos hd, cwBit_par P i k t e hts hki, Nat.testBit_eq_decide_div_mod_eq]
  · rw [if_neg hd, cwBit_data P i k (not_pow_of_between k t (by omega) hhi)]
    by_cases h : k = i
    · subst h; simp
    · have : i + 1 - k ≠ 1 := by omega
      simp [h, this]

theorem t_final (P : StarParams) (t : ℕ) (h1 : P.b + 1 ≤ 2 ^ t) (h2 : 2 ^ t < 2 * (P.b + 1)) :
    2 ^ t = P.b + 1 := by
  have hbs := b_succ_pow P
  rw [hbs] at h1 h2 ⊢
  have ha : P.s ≤ t := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h3 : 2 ^ t < 2 ^ (P.s + 1) := by rw [Nat.pow_succ]; omega
  have hb : t < P.s + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have : t = P.s := by omega
  rw [this]

/-- The codeword loop's start: `rem := i+1`, `ci := i+1`, `pwq := 1`, `K3 := b`. -/
def cwInit : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR rI1 rRem rT2) (.seq (FinalPass.Hash4.wcopyR rI1 rCi rT2)
    (.seq (.inc rPwq) (FinalPass.Hash4.wcopyR rB rK3 rT2)))

/-- The codeword loop. -/
def cwLoop : WM GS GR := .whr rK3 (.seq (.dec rK3) cwStep)

/-- **The codeword writer** of the data position `rI1 − 1`. -/
def cwM : WM GS GR := .seq cwInit (.seq cwLoop (WM.clear rPwq))

/-- The codeword writer's cost bound. -/
def cwCost (b : ℕ) : ℕ := b * (150 * b + 200 + 4) + 60 * b + 30

/-- The codeword loop's invariant after `q` bits. -/
def cwInv (P : StarParams) (i : ℕ) (σ : WState GS GR) (q : ℕ) (τ : WState GS GR) : Prop :=
  τ.st gOUT = σ.st gOUT ++ (List.range q).flatMap (fun q' => e4 (PrimT.C4Geo.cwBit P i q')) ∧
  τ.sh gOUT = (τ.st gOUT).length ∧ τ.val rOP = σ.val rOP + 4 * q ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
  (∀ r, r ≠ rCi → r ≠ rHit → r ≠ rDq → r ≠ rPwq → r ≠ rRem → r ≠ rQ → r ≠ rRb → r ≠ rT2 → r ≠ rOP → r ≠ rK3 →
    τ.val r = σ.val r) ∧
  τ.val rCi = i + 1 - q ∧ τ.val rHit = 0 ∧ τ.val rQ = 0 ∧ τ.val rRb = 0 ∧ τ.val rT2 = 0 ∧
  ∃ t, τ.val rPwq = 2 ^ t ∧ q + 1 ≤ 2 ^ t ∧ 2 ^ t < 2 * (q + 1) ∧ τ.val rDq = 2 ^ t - (q + 1) ∧
    τ.val rRem = (i + 1) / 2 ^ t

theorem cwLoop_step (P : StarParams) (i : ℕ) (hi : i < P.b) (hpar : PrimT.C4Geo.isPar P i = false)
    (σ : WState GS GR) (hc : σ.val rOP + 4 * P.b ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap) :
    ∀ k < P.b, ∀ τ, cwInv P i σ k τ → τ.val rK3 = P.b - k →
      ∃ ρ, WExec cap cwStep (τ.setv rK3 (P.b - k - 1)) ρ (150 * P.b + 200) ∧ cwInv P i σ (k + 1) ρ ∧
        ρ.val rK3 = P.b - k - 1 := by
  intro k hk τ hInv _
  obtain ⟨iS, iSh, iOP, iO, iF, iC, iH, iQ, iRb, iT, t, iPw, iLo, iHi, iDq, iRem⟩ := hInv
  obtain ⟨τ', hτ'⟩ : ∃ x, x = τ.setv rK3 (P.b - k - 1) := ⟨_, rfl⟩
  have kv : ∀ r, r ≠ rK3 → τ'.val r = τ.val r := fun r h => by rw [hτ']; simp [Function.update_of_ne h]
  have sv : τ'.st = τ.st := by rw [hτ']; rfl
  have shv : τ'.sh = τ.sh := by rw [hτ']; rfl
  have hpwb : 2 ^ t < 2 * P.b + 1 := by omega
  have hrem : (i + 1) / 2 ^ t ≤ i + 1 := Nat.div_le_self _ _
  obtain ⟨ρ, c, e, rS, rSh, rOP', rO, rC, rH, rQ', rRb', rT', rDq', rPw', rRem', rF, rc⟩ :=
    cwStep_spec cap τ' (by rw [kv _ (by decide), iH]) (by rw [kv _ (by decide), iQ])
      (by rw [kv _ (by decide), iRb]) (by rw [kv _ (by decide), iT]) (by rw [sv, shv]; exact iSh)
      (by rw [kv _ (by decide), iOP]; omega) (by rw [kv _ (by decide), iPw]; omega)
      (by rw [kv _ (by decide), iC]; omega) (by rw [kv _ (by decide), iRem]; omega)
      (by rw [kv _ (by decide), iDq]; omega) (by omega)
      (by
        rw [kv _ (by decide), kv _ (by decide), iDq, iC]
        intro hd
        have e2 : k + 1 = 2 ^ t := by omega
        intro h1
        have hki : k = i := by omega
        subst hki
        have := (isPar_iff P k hi).2 ⟨t, e2⟩
        rw [hpar] at this
        exact Bool.false_ne_true this)
  have hD : τ'.val rDq = 2 ^ t - (k + 1) := by rw [kv _ (by decide), iDq]
  have hR : τ'.val rRem = (i + 1) / 2 ^ t := by rw [kv _ (by decide), iRem]
  have hCi : τ'.val rCi = i + 1 - k := by rw [kv _ (by decide), iC]
  have hP : τ'.val rPwq = 2 ^ t := by rw [kv _ (by decide), iPw]
  have hbit := cw_bit_step P i k t hi hpar hk iLo iHi
  rw [hD, hR, hCi] at rS
  rw [hbit] at rS
  rw [hτ'] at e
  refine ⟨ρ, WExec.mono e ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, rH, rQ', rRb', rT', ?_⟩, ?_⟩
  · have : c ≤ cwStepCost (2 ^ t) ((i + 1) / 2 ^ t) := by rw [← hR, ← hP]; exact rc
    unfold cwStepCost at this
    omega
  · rw [rS, sv, iS, List.range_succ, List.flatMap_append, List.append_assoc]
    simp
  · exact rSh
  · rw [rOP', kv _ (by decide), iOP]; ring
  · intro s hs; rw [rO s hs, sv, iO s hs]
  · intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    rw [rF r a1 a2 a3 a4 a5 a6 a7 a8 a9, kv r a10, iF r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10]
  · rw [rC, hCi]; omega
  · by_cases hd : 2 ^ t - (k + 1) = 0
    · refine ⟨t + 1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rPw', hD, if_pos hd, hP, Nat.pow_succ]; ring
      · rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ]; omega
      · rw [rDq', hD, if_pos hd, hP, Nat.pow_succ]; omega
      · rw [rRem', hD, if_pos hd, hR, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rPw', hD, if_neg hd, hP]
      · omega
      · omega
      · rw [rDq', hD, if_neg hd]; omega
      · rw [rRem', hD, if_neg hd, hR]
  · rw [rF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hτ']
    simp

/-- **The codeword writer's run**: for a data position `i < b` (`rI1 = i+1`, `rB = b`, the loop registers `0`), `cwM`
appends `(range b).flatMap (e4 ∘ cwBit i)`; every register other than the output counter ends at its entry value. -/
theorem cwM_spec (P : StarParams) (i : ℕ) (hi : i < P.b) (hpar : PrimT.C4Geo.isPar P i = false)
    (σ : WState GS GR) (hI : σ.val rI1 = i + 1) (hB : σ.val rB = P.b) (z1 : σ.val rRem = 0) (z2 : σ.val rCi = 0)
    (z3 : σ.val rPwq = 0) (z4 : σ.val rDq = 0) (z5 : σ.val rHit = 0) (z6 : σ.val rRb = 0) (z7 : σ.val rQ = 0)
    (z8 : σ.val rT2 = 0) (z9 : σ.val rK3 = 0) (ho : σ.sh gOUT = (σ.st gOUT).length)
    (hc : σ.val rOP + 4 * P.b ≤ cap) (hc2 : 4 * (P.b + 1) ≤ cap) :
    ∃ τ c, WExec cap cwM σ τ c ∧
      τ.st gOUT = σ.st gOUT ++ (List.range P.b).flatMap (fun q => e4 (PrimT.C4Geo.cwBit P i q)) ∧
      τ.sh gOUT = (τ.st gOUT).length ∧ τ.val rOP = σ.val rOP + 4 * P.b ∧ (∀ s, s ≠ gOUT → τ.st s = σ.st s) ∧
      (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ c ≤ cwCost P.b := by
  -- the start
  have e1 := FinalPass.Hash4.wcopyR_spec cap rI1 rRem rT2 (by decide) (by decide) (by decide) σ z1 z8 (by omega)
  obtain ⟨σ1, h1⟩ : ∃ x, x = σ.setv rRem (σ.val rI1) := ⟨_, rfl⟩
  rw [← h1] at e1
  have k1 : ∀ r, r ≠ rRem → σ1.val r = σ.val r := fun r h => by rw [h1]; simp [Function.update_of_ne h]
  have e2 := FinalPass.Hash4.wcopyR_spec cap rI1 rCi rT2 (by decide) (by decide) (by decide) σ1
    (by rw [k1 _ (by decide), z2]) (by rw [k1 _ (by decide), z8]) (by rw [k1 _ (by decide)]; omega)
  obtain ⟨σ2, h2⟩ : ∃ x, x = σ1.setv rCi (σ1.val rI1) := ⟨_, rfl⟩
  rw [← h2] at e2
  have k2 : ∀ r, r ≠ rCi → σ2.val r = σ1.val r := fun r h => by rw [h2]; simp [Function.update_of_ne h]
  have e3 := WExec.inc (cap := cap) rPwq σ2 (by rw [k2 _ (by decide), k1 _ (by decide), z3]; omega)
  obtain ⟨σ3, h3⟩ : ∃ x, x = σ2.setv rPwq (σ2.val rPwq + 1) := ⟨_, rfl⟩
  rw [← h3] at e3
  have k3 : ∀ r, r ≠ rPwq → σ3.val r = σ2.val r := fun r h => by rw [h3]; simp [Function.update_of_ne h]
  have e4' := FinalPass.Hash4.wcopyR_spec cap rB rK3 rT2 (by decide) (by decide) (by decide) σ3
    (by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z9])
    (by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z8])
    (by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hB]; omega)
  obtain ⟨σ4, h4⟩ : ∃ x, x = σ3.setv rK3 (σ3.val rB) := ⟨_, rfl⟩
  rw [← h4] at e4'
  have k4 : ∀ r, r ≠ rK3 → σ4.val r = σ3.val r := fun r h => by rw [h4]; simp [Function.update_of_ne h]
  have s4 : σ4.st = σ.st := by rw [h4, h3, h2, h1]; rfl
  have sh4 : σ4.sh = σ.sh := by rw [h4, h3, h2, h1]; rfl
  have hK4 : σ4.val rK3 = P.b := by
    rw [h4]; simp only [WState.setv_val, Function.update_self]
    rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hB]
  have inv0 : cwInv P i σ 0 σ4 := by
    refine ⟨by rw [s4]; simp, by rw [s4, sh4]; exact ho, ?_, fun s _ => by rw [s4], ?_, ?_, ?_, ?_, ?_, ?_, 0, ?_,
      by simp, by simp, ?_, ?_⟩
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]; simp
    · intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      rw [k4 r a10, k3 r a4, k2 r a1, k1 r a5]
    · rw [k4 _ (by decide), k3 _ (by decide), h2]; simp [k1 _ (show rI1 ≠ rRem by decide), hI]
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z5]
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z7]
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z6]
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z8]
    · rw [k4 _ (by decide), h3]; simp [k2 _ (show rPwq ≠ rCi by decide), k1 _ (show rPwq ≠ rRem by decide), z3]
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), z4]; rfl
    · rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), h1]; simp [hI]
  -- the loop
  obtain ⟨τ, eL, invF, hKF⟩ := UnionMachine.Round.wloopE cap rK3 cwStep (150 * P.b + 200) P.b (cwInv P i σ)
    (by omega) (cwLoop_step cap P i hi hpar σ hc hc2) σ4 inv0 hK4
  obtain ⟨iS, iSh, iOP, iO, iF, iC, iH, iQ, iRb, iT, t, iPw, iLo, iHi, iDq, iRem⟩ := invF
  have ht := t_final P t iLo iHi
  have hbs := b_succ_pow P
  -- the end
  have e5 := wclear_spec cap rPwq (P.b + 1) τ (by rw [iPw, ht]) (by rw [iPw, ht]; omega)
  refine ⟨τ.setv rPwq 0, _, WExec.seq (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4')))
    (WExec.seq eL e5), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.setv_st]; exact iS
  · simp only [WState.setv_st, WState.setv_sh]; exact iSh
  · simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), iOP]
  · intro s hs; simp only [WState.setv_st]; exact iO s hs
  · intro r hr
    simp only [WState.setv_val]
    by_cases hPw : r = rPwq
    · subst hPw; simp [z3]
    rw [Function.update_of_ne hPw]
    by_cases hCi' : r = rCi
    · subst hCi'; rw [iC, z2]; omega
    by_cases hH' : r = rHit
    · subst hH'; rw [iH, z5]
    by_cases hD' : r = rDq
    · subst hD'; rw [iDq, ht, z4]; omega
    by_cases hR' : r = rRem
    · subst hR'
      rw [iRem, ht, z1]
      exact Nat.div_eq_of_lt (by omega)
    by_cases hQ' : r = rQ
    · subst hQ'; rw [iQ, z7]
    by_cases hRb' : r = rRb
    · subst hRb'; rw [iRb, z6]
    by_cases hT' : r = rT2
    · subst hT'; rw [iT, z8]
    by_cases hK' : r = rK3
    · subst hK'; rw [hKF, z9]
    exact iF r hCi' hH' hD' hPw hR' hQ' hRb' hT' hr hK'
  · unfold cwCost
    have hI1 : σ.val rI1 ≤ P.b := by omega
    have hA : σ1.val rI1 = σ.val rI1 := k1 _ (by decide)
    have hB3 : σ3.val rB = P.b := by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hB]
    rw [hA, hB3]
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.GeoColsCw
