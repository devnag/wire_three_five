import Proof.Wire_3_5.Primitive.SeedFix.CtrMath
import Proof.Wire_3_5.Primitive.SeedFix.FlipsDec
import Proof.Wire_3_5.FinalPass.HashTable
import Proof.Wire_3_5.FinalPass.WordLib
import Proof.Wire_3_5.Primitive.Writers.GeoColsCw

/-! # X3, part 2: the center writer's layout and small programs (P3:1206-1216)

The center at `(row, col)` (P3:1206-1216, `C4Geo.centerAt`) is written by a register-language program on a small
layout (`WM 3 26`): the offset (`zOff`), the row (`zRow`), the column (`zCol`), the center (`zCtr`), and 26 registers
(the star numbers `b, s, r/2, hL, hR` and scratch). It is lifted to any layout by C5's `WM.liftW`. Here:

* `namesC` / `cell_keep` (a program without `setc` keeps the cell), `Keep` (registers and streams outside two lists
  kept) with `keep_of` (from `val_keep` / `st_keep`);
* `togR` (a flag toggled), `readB` (the next framed bit read into `rgZ`), `wrC` / `pairC` (a framed bit written on
  the center stream, overwriting), **`emitX`** (the bit `X ⊕ offset` framed on the center stream: one center
  coordinate), `halfW` (a register halved, its low bit out), `back_spec` (a stream moved back by a counted distance).

Paper quantity of the main types: one coordinate of the center, `ctr ⊕ offset` (P3:1206-1209). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoColsCw (namesR namesS val_keep st_keep)

/-! ## The layout -/

/-- The center writer's programs and states. -/
abbrev CM := WM 3 26
abbrev CS := WState 3 26

scoped notation "zOff" => (0 : Fin 4)
scoped notation "zRow" => (1 : Fin 4)
scoped notation "zCol" => (2 : Fin 4)
scoped notation "zCtr" => (3 : Fin 4)

scoped notation "rgB" => (0 : Fin 26)
scoped notation "rgS" => (1 : Fin 26)
scoped notation "rgH" => (2 : Fin 26)
scoped notation "rgHL" => (3 : Fin 26)
scoped notation "rgHR" => (4 : Fin 26)
scoped notation "rgKB" => (5 : Fin 26)
scoped notation "rgKQ" => (6 : Fin 26)
scoped notation "rgKT" => (7 : Fin 26)
scoped notation "rgNP" => (8 : Fin 26)
scoped notation "rgE" => (9 : Fin 26)
scoped notation "rgPW" => (10 : Fin 26)
scoped notation "rgCD" => (11 : Fin 26)
scoped notation "rgF" => (12 : Fin 26)
scoped notation "rgACC" => (13 : Fin 26)
scoped notation "rgZ" => (14 : Fin 26)
scoped notation "rgPAR" => (15 : Fin 26)
scoped notation "rgT" => (16 : Fin 26)
scoped notation "rgT2" => (17 : Fin 26)
scoped notation "rgRWC" => (18 : Fin 26)
scoped notation "rgHQ" => (19 : Fin 26)
scoped notation "rgBIT" => (20 : Fin 26)
scoped notation "rgROWC" => (21 : Fin 26)
scoped notation "rgCOLC" => (22 : Fin 26)
scoped notation "rgOFFC" => (23 : Fin 26)
scoped notation "rgOC" => (24 : Fin 26)
scoped notation "rgKU" => (25 : Fin 26)

/-! ## Kept registers and streams -/

section Names
variable {ns nr : ℕ} {cap : ℕ}

/-- Whether a program writes stream `i`. -/
def namesW (i : Fin (ns + 1)) : WM ns nr → Bool
  | .wr i' _ => decide (i' = i)
  | .seq P Q => namesW i P || namesW i Q
  | .ifr _ P Q => namesW i P || namesW i Q
  | .ifs _ P Q => namesW i P || namesW i Q
  | .whr _ P => namesW i P
  | .whs _ P => namesW i P
  | _ => false

theorem wr_keep {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (i : Fin (ns + 1))
    (hP : namesW i P = false) : τ.st i = σ.st i := by
  induction h with
  | skip => rfl
  | inc => rfl
  | dec => rfl
  | fwd => rfl
  | bwd => rfl
  | wr i' b σ =>
    have hi : i ≠ i' := fun e => by subst e; simp [namesW] at hP
    simp [Function.update_of_ne hi]
  | setc => rfl
  | seq _ _ ih1 ih2 =>
    simp only [namesW, Bool.or_eq_false_iff] at hP
    rw [ih2 hP.2, ih1 hP.1]
  | ifrT _ _ ih =>
    simp only [namesW, Bool.or_eq_false_iff] at hP
    exact ih hP.1
  | ifrF _ _ ih =>
    simp only [namesW, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | ifsT _ _ ih =>
    simp only [namesW, Bool.or_eq_false_iff] at hP
    exact ih hP.1
  | ifsF _ _ ih =>
    simp only [namesW, Bool.or_eq_false_iff] at hP
    exact ih hP.2
  | whrF _ => rfl
  | whrT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesW] at hP'
    rw [ih2 hP, ih1 hP']
  | whsF _ => rfl
  | whsT _ _ _ ih1 ih2 =>
    have hP' := hP
    simp only [namesW] at hP'
    rw [ih2 hP, ih1 hP']
  | mono _ _ ih => exact ih hP

end Names

/-! ## Small programs -/

section Small
variable (cap : ℕ)

/-- A flag toggled. -/
def togR (F : Fin 26) : CM := .ifr F (.dec F) (.inc F)

theorem togR_spec (F : Fin 26) (σ : CS) (hF : σ.val F ≤ 1) (hc : 1 ≤ cap) :
    WExec cap (togR F) σ (σ.setv F (1 - σ.val F)) 4 := by
  by_cases h : σ.val F = 0
  · have e := WExec.inc (cap := cap) F σ (by omega)
    refine WExec.cast cap (WExec.ifrF h e) ?_ (by omega)
    rw [h]
  · have e := WExec.dec (cap := cap) F σ (by omega)
    refine WExec.cast cap (WExec.ifrT h e) ?_ (by omega)
    have h1 : σ.val F = 1 := by omega
    rw [h1]

/-- The next framed bit of `R` read into `rgZ` (`rgZ = 0` before), counted twice in `cnt`. -/
def readB (R : Fin 4) (cnt : Fin 26) : CM :=
  .seq (.fwd R) (.seq (.ifs R (.inc rgZ) .skip) (.seq (.fwd R) (.seq (.inc cnt) (.inc cnt))))

theorem readB_spec (R : Fin 4) (cnt : Fin 26) (hc : cnt ≠ rgZ) (σ : CS) (hz : σ.val rgZ = 0)
    (hcnt : σ.val cnt + 2 ≤ cap) (hcap : 1 ≤ cap) :
    ∃ τ, WExec cap (readB R cnt) σ τ 20 ∧ τ.sh R = σ.sh R + 2 ∧
      τ.val rgZ = (readTapeBit (σ.st R) (σ.sh R + 1)).toNat ∧ τ.val cnt = σ.val cnt + 2 ∧
      τ.st = σ.st ∧ (∀ i, i ≠ R → τ.sh i = σ.sh i) ∧ (∀ r, r ≠ rgZ → r ≠ cnt → τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  have e1 := WExec.fwd (cap := cap) R σ
  have hw : wbit (σ.seth R (σ.sh R + 1)) R = readTapeBit (σ.st R) (σ.sh R + 1) := wsbit_seth σ R _
  obtain ⟨σ2, e2, h2⟩ : ∃ σ2, WExec cap (.ifs R (.inc rgZ) .skip) (σ.seth R (σ.sh R + 1)) σ2 4 ∧
      σ2 = (σ.seth R (σ.sh R + 1)).setv rgZ (readTapeBit (σ.st R) (σ.sh R + 1)).toNat := by
    cases hb : readTapeBit (σ.st R) (σ.sh R + 1)
    · refine ⟨_, WExec.mono (WExec.ifsF (by rw [hw, hb]) (WExec.skip _)) (by omega), ?_⟩
      refine WState.eq rfl rfl ?_ rfl
      funext q
      by_cases hq : q = rgZ
      · subst hq
        simp [hz]
      · simp [Function.update_apply, hq]
    · have ei := WExec.inc (cap := cap) rgZ (σ.seth R (σ.sh R + 1)) (by simp [hz]; omega)
      refine ⟨_, WExec.mono (WExec.ifsT (by rw [hw, hb]) ei) (by omega), ?_⟩
      simp [hz]
  subst h2
  have e3 := WExec.fwd (cap := cap) R ((σ.seth R (σ.sh R + 1)).setv rgZ (readTapeBit (σ.st R) (σ.sh R + 1)).toNat)
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = ((σ.seth R (σ.sh R + 1)).setv rgZ (readTapeBit (σ.st R) (σ.sh R + 1)).toNat).seth R
      ((((σ.seth R (σ.sh R + 1)).setv rgZ (readTapeBit (σ.st R) (σ.sh R + 1)).toNat)).sh R + 1) := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have c3 : σ3.val cnt = σ.val cnt := by
    rw [hσ3]; simp [Function.update_apply, hc]
  have e4 := WExec.inc (cap := cap) cnt σ3 (by omega)
  have e5 := WExec.inc (cap := cap) cnt (σ3.setv cnt (σ3.val cnt + 1)) (by simp; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [hσ3]
  · simp [hσ3, Function.update_apply, Ne.symm hc]
  · simp [c3]
  · simp [hσ3]
  · intro i hi
    simp [hσ3, Function.update_apply, hi]
  · intro r h1 h2
    simp [hσ3, Function.update_apply, h1, h2]
  · simp [hσ3]

/-- One cell written on the center stream (overwriting), counted in `rgOC`. -/
def wrC (v : Bool) : CM := .seq (.wr zCtr v) (.seq (.fwd zCtr) (.inc rgOC))

theorem wtb_app (A B : List Bool) (v : Bool) : writeTapeBit (A ++ B) A.length v = A ++ v :: B.drop 1 := by
  cases B with
  | nil => simpa using writeTapeBit_end' A v
  | cons b B => simpa using writeTapeBit_mid' A B b v

theorem wrC_spec (v : Bool) (σ : CS) (A B : List Bool) (hst : σ.st zCtr = A ++ B) (hsh : σ.sh zCtr = A.length)
    (hoc : σ.val rgOC < cap) :
    ∃ τ, WExec cap (wrC v) σ τ 7 ∧ τ.st zCtr = A ++ v :: B.drop 1 ∧ τ.sh zCtr = A.length + 1 ∧
      τ.val rgOC = σ.val rgOC + 1 ∧ (∀ i, i ≠ zCtr → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ rgOC → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have e1 := WExec.wr (cap := cap) zCtr v σ
  rw [hst, hsh, wtb_app] at e1
  have e2 := WExec.fwd (cap := cap) zCtr (σ.sets zCtr (A ++ v :: B.drop 1))
  have e3 := WExec.inc (cap := cap) rgOC ((σ.sets zCtr (A ++ v :: B.drop 1)).seth zCtr
    ((σ.sets zCtr (A ++ v :: B.drop 1)).sh zCtr + 1)) (by simpa using hoc)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [hsh]
  · simp
  · intro i hi
    simp [Function.update_apply, hi]
  · intro r hr
    simp [Function.update_apply, hr]
  · simp

/-- A framed bit `[1, v]` written on the center stream. -/
def pairC (v : Bool) : CM := .seq (wrC true) (wrC v)

theorem pairC_spec (v : Bool) (σ : CS) (A B : List Bool) (hst : σ.st zCtr = A ++ B) (hsh : σ.sh zCtr = A.length)
    (hoc : σ.val rgOC + 2 ≤ cap) :
    ∃ τ, WExec cap (pairC v) σ τ 15 ∧ τ.st zCtr = A ++ true :: v :: B.drop 2 ∧ τ.sh zCtr = A.length + 2 ∧
      τ.val rgOC = σ.val rgOC + 2 ∧ (∀ i, i ≠ zCtr → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ rgOC → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, e1, a1, b1, c1, d1, f1, g1⟩ := wrC_spec cap true σ A B hst hsh (by omega)
  obtain ⟨τ2, e2, a2, b2, c2, d2, f2, g2⟩ := wrC_spec cap v τ1 (A ++ [true]) (B.drop 1)
    (by rw [a1]; simp) (by rw [b1]; simp) (by omega)
  refine ⟨τ2, WExec.mono (WExec.seq e1 e2) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a2]; simp [List.drop_drop]
  · rw [b2]; simp
  · omega
  · intro i hi
    exact ⟨(d2 i hi).1.trans (d1 i hi).1, (d2 i hi).2.trans (d1 i hi).2⟩
  · intro r hr
    rw [f2 r hr, f1 r hr]
  · rw [g2, g1]

/-- **One center coordinate**: the offset's next framed bit `o` read, the framed bit `X ⊕ o` written on the center
stream (`X ∈ {0, 1}`). -/
def emitX (X : Fin 26) : CM :=
  .seq (.fwd zOff) (.seq (.ifs zOff (.ifr X (pairC false) (pairC true)) (.ifr X (pairC true) (pairC false)))
    (.seq (.fwd zOff) (.seq (.inc rgOFFC) (.inc rgOFFC))))

theorem emitX_spec (X : Fin 26) (hXO : X ≠ rgOC) (hXF : X ≠ rgOFFC) (σ : CS) (hX : σ.val X ≤ 1)
    (A B : List Bool) (hst : σ.st zCtr = A ++ B) (hsh : σ.sh zCtr = A.length)
    (hoc : σ.val rgOC + 2 ≤ cap) (hof : σ.val rgOFFC + 2 ≤ cap) :
    ∃ τ, WExec cap (emitX X) σ τ 40 ∧
      τ.st zCtr = A ++ true :: xor (decide (σ.val X = 1)) (readTapeBit (σ.st zOff) (σ.sh zOff + 1)) :: B.drop 2 ∧
      τ.sh zCtr = A.length + 2 ∧ τ.val rgOC = σ.val rgOC + 2 ∧ τ.sh zOff = σ.sh zOff + 2 ∧
      τ.val rgOFFC = σ.val rgOFFC + 2 ∧ τ.st zOff = σ.st zOff ∧
      (∀ i, i ≠ zCtr → i ≠ zOff → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ rgOC → r ≠ rgOFFC → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have e1 := WExec.fwd (cap := cap) zOff σ
  have hw : wbit (σ.seth zOff (σ.sh zOff + 1)) zOff = readTapeBit (σ.st zOff) (σ.sh zOff + 1) := wsbit_seth σ zOff _
  set σ1 := σ.seth zOff (σ.sh zOff + 1) with hσ1
  have s1 : σ1.st zCtr = A ++ B := by simp [hσ1, hst]
  have h1 : σ1.sh zCtr = A.length := by simp [hσ1, hsh]
  have o1 : σ1.val rgOC + 2 ≤ cap := by simpa [hσ1] using hoc
  -- the pair
  obtain ⟨σ2, e2, a2, b2, c2, d2, f2, g2⟩ : ∃ σ2, WExec cap (.ifs zOff (.ifr X (pairC false) (pairC true))
      (.ifr X (pairC true) (pairC false))) σ1 σ2 17 ∧
      σ2.st zCtr = A ++ true :: xor (decide (σ.val X = 1)) (readTapeBit (σ.st zOff) (σ.sh zOff + 1)) :: B.drop 2 ∧
      σ2.sh zCtr = A.length + 2 ∧ σ2.val rgOC = σ1.val rgOC + 2 ∧
      (∀ i, i ≠ zCtr → σ2.st i = σ1.st i ∧ σ2.sh i = σ1.sh i) ∧ (∀ r, r ≠ rgOC → σ2.val r = σ1.val r) ∧
      σ2.cell = σ1.cell := by
    have vX : σ1.val X = σ.val X := by simp [hσ1]
    cases hb : readTapeBit (σ.st zOff) (σ.sh zOff + 1)
    · by_cases hx : σ.val X = 1
      · obtain ⟨τ, e, a, b, c, d, f, g⟩ := pairC_spec cap true σ1 A B s1 h1 o1
        refine ⟨τ, WExec.mono (WExec.ifsF (by rw [hw, hb]) (WExec.ifrT (by rw [vX]; omega) e)) (by omega),
          ?_, b, c, d, f, g⟩
        rw [a, hx]; rfl
      · obtain ⟨τ, e, a, b, c, d, f, g⟩ := pairC_spec cap false σ1 A B s1 h1 o1
        refine ⟨τ, WExec.mono (WExec.ifsF (by rw [hw, hb]) (WExec.ifrF (by rw [vX]; omega) e)) (by omega),
          ?_, b, c, d, f, g⟩
        rw [a]; simp [hx]
    · by_cases hx : σ.val X = 1
      · obtain ⟨τ, e, a, b, c, d, f, g⟩ := pairC_spec cap false σ1 A B s1 h1 o1
        refine ⟨τ, WExec.mono (WExec.ifsT (by rw [hw, hb]) (WExec.ifrT (by rw [vX]; omega) e)) (by omega),
          ?_, b, c, d, f, g⟩
        rw [a, hx]; rfl
      · obtain ⟨τ, e, a, b, c, d, f, g⟩ := pairC_spec cap true σ1 A B s1 h1 o1
        refine ⟨τ, WExec.mono (WExec.ifsT (by rw [hw, hb]) (WExec.ifrF (by rw [vX]; omega) e)) (by omega),
          ?_, b, c, d, f, g⟩
        rw [a]; simp [hx]
  have sO2 : σ2.sh zOff = σ.sh zOff + 1 := by rw [(d2 zOff (by decide)).2]; simp [hσ1]
  have e3 := WExec.fwd (cap := cap) zOff σ2
  set σ3 := σ2.seth zOff (σ2.sh zOff + 1) with hσ3
  have v3 : σ3.val rgOFFC = σ.val rgOFFC := by simp [hσ3, f2 rgOFFC (by decide), hσ1]
  have e4 := WExec.inc (cap := cap) rgOFFC σ3 (by omega)
  have e5 := WExec.inc (cap := cap) rgOFFC (σ3.setv rgOFFC (σ3.val rgOFFC + 1)) (by simp; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ3, a2]
  · simp [hσ3, Function.update_apply, b2]
  · simp [hσ3, c2, hσ1]
  · simp [hσ3, sO2]
  · simp [v3]
  · simp [hσ3, (d2 zOff (by decide)).1, hσ1]
  · intro i i1 i2
    have := d2 i i1
    simp [hσ3, Function.update_apply, i2, this.1, this.2, hσ1]
  · intro r r1 r2
    simp [hσ3, Function.update_apply, r2, f2 r r1, hσ1]
  · simp [hσ3, g2, hσ1]

/-- A register halved: `rgBIT += rgPAR mod 2`-style, `2·rgHQ + rgBIT` gains `rgPAR`, `rgPAR := 0`. -/
def halfW : CM := .whr rgPAR (.seq (.dec rgPAR) (.ifr rgBIT (.seq (.dec rgBIT) (.inc rgHQ)) (.inc rgBIT)))

theorem halfW_spec : ∀ (k : ℕ) (σ : CS), σ.val rgPAR = k → σ.val rgBIT ≤ 1 → σ.val rgPAR ≤ cap →
    σ.val rgHQ + k < cap → 1 ≤ cap →
    ∃ τ, WExec cap halfW σ τ (14 * k + 1) ∧ τ.val rgPAR = 0 ∧
      2 * τ.val rgHQ + τ.val rgBIT = 2 * σ.val rgHQ + σ.val rgBIT + k ∧ τ.val rgBIT ≤ 1 ∧
      τ.val rgHQ ≤ σ.val rgHQ + k ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      (∀ r, r ≠ rgPAR → r ≠ rgBIT → r ≠ rgHQ → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, σ, hk, _, _, _, _ =>
    ⟨σ, WExec.mono (WExec.whrF hk) (by omega), hk, by omega, by omega, by omega, rfl, rfl, fun _ _ _ _ => rfl, rfl⟩
  | k + 1, σ, hk, hb, hp, hq, hc => by
    have e1 := WExec.dec (cap := cap) rgPAR σ hp
    set σ1 := σ.setv rgPAR (σ.val rgPAR - 1) with hσ1
    obtain ⟨σ2, e2, v2P, v2B, v2Q, v2o⟩ : ∃ σ2, WExec cap (.ifr rgBIT (.seq (.dec rgBIT) (.inc rgHQ)) (.inc rgBIT))
        σ1 σ2 9 ∧ σ2.val rgPAR = k ∧ σ2.val rgBIT = 1 - σ.val rgBIT ∧
        σ2.val rgHQ = σ.val rgHQ + σ.val rgBIT ∧ (σ2.st = σ.st ∧ σ2.sh = σ.sh ∧
          (∀ r, r ≠ rgPAR → r ≠ rgBIT → r ≠ rgHQ → σ2.val r = σ.val r) ∧ σ2.cell = σ.cell) := by
      by_cases h0 : σ.val rgBIT = 0
      · have ei := WExec.inc (cap := cap) rgBIT σ1 (by simp [hσ1, h0]; omega)
        refine ⟨_, WExec.mono (WExec.ifrF (by simp [hσ1, h0]) ei) (by omega), ?_, ?_, ?_, ?_⟩
        · simp [hσ1, Function.update_apply]; omega
        · simp [hσ1, h0]
        · simp [hσ1, h0]
        · refine ⟨rfl, rfl, fun r r1 r2 r3 => by simp [hσ1, Function.update_apply, r1, r2], rfl⟩
      · have ed := WExec.dec (cap := cap) rgBIT σ1 (by simp [hσ1]; omega)
        have ei := WExec.inc (cap := cap) rgHQ (σ1.setv rgBIT (σ1.val rgBIT - 1)) (by simp [hσ1]; omega)
        refine ⟨_, WExec.mono (WExec.ifrT (by simp [hσ1]; omega) (WExec.seq ed ei)) (by omega), ?_, ?_, ?_, ?_⟩
        · simp [hσ1, Function.update_apply]; omega
        · simp [hσ1]; omega
        · simp [hσ1]; omega
        · refine ⟨rfl, rfl, fun r r1 r2 r3 => by simp [hσ1, Function.update_apply, r1, r2, r3], rfl⟩
    obtain ⟨τ, e3, t1, t2, t3, t4, t5, t6, t7, t8⟩ := halfW_spec k σ2 v2P (by omega) (by omega) (by omega) hc
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq e1 e2) e3) (by ring_nf; omega), t1, by omega, t3,
      by omega, t5.trans v2o.1, t6.trans v2o.2.1, fun r r1 r2 r3 => (t7 r r1 r2 r3).trans (v2o.2.2.1 r r1 r2 r3),
      t8.trans v2o.2.2.2⟩

end Small

/-! ## Moving back by a counted distance -/

section Back
variable {ns nr : ℕ} (cap : ℕ)

theorem back_spec (I : Fin (ns + 1)) (r : Fin nr) (c : ℕ) :
    ∀ (σ : WState ns nr) (b0 : ℕ), σ.val r = c → σ.sh I = b0 + c → c ≤ cap →
      ∃ τ, WExec cap (Flips.rew1 I r) σ τ (c * 5 + 1) ∧ τ.sh I = b0 ∧ τ.val r = 0 ∧ τ.st = σ.st ∧
        (∀ i, i ≠ I → τ.sh i = σ.sh i) ∧ (∀ q, q ≠ r → τ.val q = σ.val q) ∧ τ.cell = σ.cell := by
  induction c with
  | zero =>
    intro σ b0 hv hI _
    exact ⟨σ, WExec.mono (WExec.whrF hv) (by omega), by omega, hv, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | succ c ih =>
    intro σ b0 hv hI hc
    have s1 := WExec.bwd (cap := cap) I σ
    have s2 := WExec.dec (cap := cap) r (σ.seth I (σ.sh I - 1)) (by show σ.val r ≤ cap; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ x, x = (σ.seth I (σ.sh I - 1)).setv r ((σ.seth I (σ.sh I - 1)).val r - 1) := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have f2 : σ2.val r = c ∧ σ2.sh I = b0 + c ∧ σ2.st = σ.st ∧ (∀ i, i ≠ I → σ2.sh i = σ.sh i) ∧
        (∀ q, q ≠ r → σ2.val q = σ.val q) ∧ σ2.cell = σ.cell := by
      rw [hσ2]
      refine ⟨by simp [WState.seth, WState.setv, hv], by simp [WState.seth, WState.setv, hI], rfl,
        fun i hi => by simp [WState.seth, WState.setv, Function.update_apply, hi],
        fun q hq => by simp [WState.seth, WState.setv, Function.update_apply, hq], rfl⟩
    obtain ⟨τ, e, t1, t2, t3, t4, t5, t6⟩ := ih σ2 b0 f2.1 f2.2.1 (by omega)
    exact ⟨τ, WExec.mono (WExec.whrT (by rw [hv]; omega) (WExec.seq s1 s2) e) (by ring_nf; omega), t1, t2,
      t3.trans f2.2.2.1, fun i hi => (t4 i hi).trans (f2.2.2.2.1 i hi),
      fun q hq => (t5 q hq).trans (f2.2.2.2.2.1 q hq), t6.trans f2.2.2.2.2.2⟩

end Back

end NearCubicWires.WireExponent3_5.PrimT.Ctr
