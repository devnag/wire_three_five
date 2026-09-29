import Proof.Wire_3_5.UnionMachine.FrontTWEmit

/-! # C6 front, U5: one monomial's calls, four nested digit loops (P3:3685-3691)

A monomial `κ_j ∏_k F_{j,k}` of `(tr:tests)` calls the primitive once per four-tuple of atoms in the supports of its
factors (`FrontTableRef.lexProd`, `cand`). The machine runs one loop per factor, the last outermost: a constant or
parity factor has one candidate, a grid factor `S_X` runs over the grid entries `X·s + a` (`a < s`) of nonzero sign
(`readSign`: the entry's sign word `b 1 0 x`, `x` = nonzero, `b` = negative). The innermost step writes the call's
entry (`FrontTWEmit.emitCall`).

The digit registers (`E_k` entry index, `NB_k` sign bit, `A_k` loop counter) and `OK` are carried by **`regsOf`**;
a level's contract (**`LevelSpec`**) says: from any digits outside the level's fresh range and any `OK ≤ 1`, the
level appends `W E NB` and conjoins `Bf E NB`, restoring every register. **`sLevel`** builds a grid factor's level
from the level inside it; **`emitLevel`** is the innermost. **`blockT`**: the four levels append
`(lexProd candM).flatMap` of the calls' entries.

Paper quantity of the main statement: one monomial's calls (their table entries), in the product order. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef (FK lexProd)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

variable (cap : ℕ) (src : Fin 11 → List Bool)

/-! ## The digit registers -/

/-- The registers with the digits `E`, `NB`, the loop counters `A` and `OK` over the base `v0`. -/
def regsOf (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) : Fin NR → ℕ := fun r =>
  if r = rOK then ok
  else if h : 24 ≤ r.val ∧ r.val < 28 then E ⟨r.val - 24, by omega⟩
  else if h : 28 ≤ r.val ∧ r.val < 32 then NB ⟨r.val - 28, by omega⟩
  else if h : 32 ≤ r.val ∧ r.val < 36 then A ⟨r.val - 32, by omega⟩
  else v0 r

theorem rE_val (k : Fin 4) : (rE k).val = 24 + k.val := rfl
theorem rNB_val (k : Fin 4) : (rNB k).val = 28 + k.val := rfl
theorem rA_val (k : Fin 4) : (rA k).val = 32 + k.val := rfl
theorem rOK_val : (rOK).val = 12 := by decide

/-- A register outside the digit and `OK` ranges. -/
def Plain (r : Fin NR) : Prop := r ≠ rOK ∧ (r.val < 24 ∨ 36 ≤ r.val)

theorem regsOf_plain (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (r : Fin NR) (hr : Plain r) :
    regsOf v0 E NB A ok r = v0 r := by
  obtain ⟨h1, h2⟩ := hr
  simp only [regsOf, if_neg h1]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

theorem regsOf_OK (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) : regsOf v0 E NB A ok rOK = ok := by
  simp [regsOf]

theorem regsOf_E (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) : regsOf v0 E NB A ok (rE k) = E k := by
  have hk := k.isLt
  have h1 : rE k ≠ rOK := fun h => by
    have e : (rE k).val = (rOK).val := congrArg Fin.val h
    rw [rE_val, rOK_val] at e; omega
  simp only [regsOf, if_neg h1, rE_val]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

theorem regsOf_NB (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) :
    regsOf v0 E NB A ok (rNB k) = NB k := by
  have hk := k.isLt
  have h1 : rNB k ≠ rOK := fun h => by
    have e : (rNB k).val = (rOK).val := congrArg Fin.val h
    rw [rNB_val, rOK_val] at e; omega
  simp only [regsOf, if_neg h1, rNB_val]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1; ext; simp

theorem regsOf_A (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) : regsOf v0 E NB A ok (rA k) = A k := by
  have hk := k.isLt
  have h1 : rA k ≠ rOK := fun h => by
    have e : (rA k).val = (rOK).val := congrArg Fin.val h
    rw [rA_val, rOK_val] at e; omega
  simp only [regsOf, if_neg h1, rA_val]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1; ext; simp

theorem regsOf_updE (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) (x : ℕ) :
    Function.update (regsOf v0 E NB A ok) (rE k) x = regsOf v0 (Function.update E k x) NB A ok := by
  funext r
  by_cases hr : r = rE k
  · subst hr; rw [Function.update_self, regsOf_E, Function.update_self]
  · have hk : ∀ h : 24 ≤ r.val ∧ r.val < 28, (⟨r.val - 24, by omega⟩ : Fin 4) ≠ k := by
      intro h e; apply hr; subst e; ext; simp [rE_val]; omega
    rw [Function.update_of_ne hr]
    simp only [regsOf]
    split_ifs with h1 h2 <;> try rfl
    rw [Function.update_of_ne (hk h2)]

theorem regsOf_updNB (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) (x : ℕ) :
    Function.update (regsOf v0 E NB A ok) (rNB k) x = regsOf v0 E (Function.update NB k x) A ok := by
  funext r
  by_cases hr : r = rNB k
  · subst hr; rw [Function.update_self, regsOf_NB, Function.update_self]
  · have hk : ∀ h : 28 ≤ r.val ∧ r.val < 32, (⟨r.val - 28, by omega⟩ : Fin 4) ≠ k := by
      intro h e; apply hr; subst e; ext; simp [rNB_val]; omega
    rw [Function.update_of_ne hr]
    simp only [regsOf]
    split_ifs with h1 h2 h3 <;> try rfl
    rw [Function.update_of_ne (hk h3)]

theorem regsOf_updA (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (k : Fin 4) (x : ℕ) :
    Function.update (regsOf v0 E NB A ok) (rA k) x = regsOf v0 E NB (Function.update A k x) ok := by
  funext r
  by_cases hr : r = rA k
  · subst hr; rw [Function.update_self, regsOf_A, Function.update_self]
  · have hk : ∀ h : 32 ≤ r.val ∧ r.val < 36, (⟨r.val - 32, by omega⟩ : Fin 4) ≠ k := by
      intro h e; apply hr; subst e; ext; simp [rA_val]; omega
    rw [Function.update_of_ne hr]
    simp only [regsOf]
    split_ifs with h1 h2 h3 h4 <;> try rfl
    rw [Function.update_of_ne (hk h4)]

theorem regsOf_updOK (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok x : ℕ) :
    Function.update (regsOf v0 E NB A ok) rOK x = regsOf v0 E NB A x := by
  funext r
  by_cases hr : r = rOK
  · subst hr; simp [regsOf]
  · rw [Function.update_of_ne hr]; simp [regsOf, hr]

theorem regsOf_updPlain (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (r : Fin NR) (hr : Plain r) (x : ℕ) :
    Function.update (regsOf v0 E NB A ok) r x = regsOf (Function.update v0 r x) E NB A ok := by
  funext r'
  by_cases h : r' = r
  · subst h; rw [Function.update_self, regsOf_plain _ _ _ _ _ _ hr, Function.update_self]
  · rw [Function.update_of_ne h]
    simp only [regsOf]
    split_ifs <;> try rfl
    rw [Function.update_of_ne h]

/-! ## Levels -/

/-- Digits `j < n` are fresh (zero), ready for the levels inside. -/
def Fresh (n : ℕ) (E NB A : Fin 4 → ℕ) : Prop := ∀ j : Fin 4, j.val < n → E j = 0 ∧ NB j = 0 ∧ A j = 0

/-- **A level's contract**: from fresh digits below `n`, digits `E, NB` meeting `Pre` and any `OK ≤ 1`, the program
appends `W E NB` and conjoins `Bf E NB` into `OK`; every register is restored. -/
def LevelSpec (P : WM 10 NR) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (n : ℕ)
    (Pre : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Prop) (W : (Fin 4 → ℕ) → (Fin 4 → ℕ) → List Bool)
    (Bf : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Bool) (bo c : ℕ) : Prop :=
  ∀ (o : List Bool) (E NB A : Fin 4 → ℕ) (ok : ℕ), ok ≤ 1 → Fresh n E NB A → Pre E NB →
    o.length + (W E NB).length ≤ bo →
    WExec cap P (ts src h o (regsOf v0 E NB A ok) cl)
      (ts src h (o ++ W E NB) (regsOf v0 E NB A (if Bf E NB then ok else 0)) cl) c

/-! ## The innermost level: one call -/

/-- The sign bit from the digits' sign registers. -/
def negBitE (κn : Bool) (NB : Fin 4 → ℕ) : Bool :=
  κn ^^ decide (NB 0 ≠ 0) ^^ decide (NB 1 ≠ 0) ^^ decide (NB 2 ≠ 0) ^^ decide (NB 3 ≠ 0)

/-- A digit's code word from the digits. -/
def codeWE (d : TWData) (v0 : Fin NR → ℕ) (E : Fin 4 → ℕ) : FK → Fin 4 → List Bool
  | .one, _ => d.cc
  | .par, _ => d.pcs.getD (v0 rX) []
  | .sx, k => natWord (d.es.getD (E k) (false, false, 0)).2.2
  | .sy, k => natWord (d.es.getD (E k) (false, false, 0)).2.2

/-- A digit's flag from the digits. -/
def flagVE (d : TWData) (v0 : Fin NR → ℕ) (E : Fin 4 → ℕ) : FK → Fin 4 → Bool
  | .one, _ => decide (v0 rCDF ≠ 0)
  | .par, _ => d.pf.getD (v0 rX) false
  | .sx, k => d.df.getD (E k) false
  | .sy, k => d.df.getD (E k) false

/-- A digit's indices from the digits. -/
def IdxOKE (d : TWData) (v0 : Fin NR → ℕ) (E : Fin 4 → ℕ) : FK → Fin 4 → Prop
  | .one, _ => True
  | .par, _ => v0 rX < d.pcs.length ∧ v0 rX < d.pf.length
  | .sx, k => E k < d.es.length ∧ E k < d.df.length
  | .sy, k => E k < d.es.length ∧ E k < d.df.length

/-- The call's word from the digits. -/
def callWordE (d : TWData) (v0 : Fin NR → ℕ) (E : Fin 4 → ℕ) (pat : Fin 4 → FK) (two : Bool) : List Bool :=
  d.hd ++ codeWE d v0 E (pat 0) 0 ++ codeWE d v0 E (pat 1) 1 ++ codeWE d v0 E (pat 2) 2 ++ codeWE d v0 E (pat 3) 3 ++
    natWord (if two then 2 else 1) ++ d.crs.getD (v0 rX) [] ++ (if two then d.crs.getD (v0 rY) [] else []) ++ d.tl

/-- The call's admissibility from the digits. -/
def callOkE (d : TWData) (v0 : Fin NR → ℕ) (E : Fin 4 → ℕ) (pat : Fin 4 → FK) (two : Bool) : Bool :=
  flagVE d v0 E (pat 0) 0 && flagVE d v0 E (pat 1) 1 && flagVE d v0 E (pat 2) 2 && flagVE d v0 E (pat 3) 3 &&
    d.ef.getD (v0 rX) false && (!two || d.ef.getD (v0 rY) false)

theorem plain_X : Plain rX := ⟨by decide, by decide⟩
theorem plain_Y : Plain rY := ⟨by decide, by decide⟩
theorem plain_CDF : Plain rCDF := ⟨by decide, by decide⟩

theorem negBit_regs (κn : Bool) (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) :
    negBit κn (regsOf v0 E NB A ok) = negBitE κn NB := by
  simp only [negBit, negBitE, nbv, regsOf_NB]

theorem codeW_regs (d : TWData) (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (f : FK) (k : Fin 4) :
    codeW d (regsOf v0 E NB A ok) f k = codeWE d v0 E f k := by
  cases f <;> simp only [codeW, codeWE, regsOf_E, regsOf_plain _ _ _ _ _ _ plain_X]

theorem flagV_regs (d : TWData) (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (f : FK) (k : Fin 4) :
    flagV d (regsOf v0 E NB A ok) f k = flagVE d v0 E f k := by
  cases f <;> simp only [flagV, flagVE, regsOf_E, regsOf_plain _ _ _ _ _ _ plain_X, regsOf_plain _ _ _ _ _ _ plain_CDF]

theorem idx_regs (d : TWData) (v0 : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (f : FK) (k : Fin 4)
    (h : IdxOKE d v0 E f k) : IdxOK d (regsOf v0 E NB A ok) f k := by
  cases f <;> simpa only [IdxOK, IdxOKE, regsOf_E, regsOf_plain _ _ _ _ _ _ plain_X] using h

theorem scr_regs (v0 : Fin NR → ℕ) (hs : Scr v0) (E NB A : Fin 4 → ℕ) (ok : ℕ) : Scr (regsOf v0 E NB A ok) :=
  ⟨by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.t,
    by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.f,
    by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.c,
    by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.z,
    by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.fl,
    by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.neg⟩

/-- **The innermost level**: one call's entry and admissibility. -/
theorem emitLevel (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool)
    (hX : v0 rX < d.crs.length ∧ v0 rX < d.ef.length) (hY : two = true → v0 rY < d.crs.length ∧ v0 rY < d.ef.length)
    (bo : ℕ) (hcapB : B + 1 ≤ cap) (hbo : bo + 30 * B + 40 ≤ cap) (hM : v0 rMAG ≤ cap) :
    LevelSpec cap src (emitCall kd κn pat two) h cl v0 0 (fun E _ => ∀ k, IdxOKE d v0 E (pat k) k)
      (fun E NB => entryW kd (negBitE κn NB) (v0 rMAG) (callWordE d v0 E pat two))
      (fun E _ => callOkE d v0 E pat two) bo (emitCost B (v0 rMAG)) := by
  intro o E NB A ok hok _ hpre hlen
  beta_reduce at hpre hlen
  have hMv : regsOf v0 E NB A ok rMAG = v0 rMAG := regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩
  have hBv : regsOf v0 E NB A ok rBIG = B := by rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hBIG
  have hXv : regsOf v0 E NB A ok rX = v0 rX := regsOf_plain _ _ _ _ _ _ plain_X
  have hYv : regsOf v0 E NB A ok rY = v0 rY := regsOf_plain _ _ _ _ _ _ plain_Y
  have hent : v0 rMAG + 6 ≤ (entryW kd (negBitE κn NB) (v0 rMAG) (callWordE d v0 E pat two)).length := by
    simp only [entryW, List.length_append, List.length_cons, List.length_replicate, List.length_nil,
      FrontTWKit.frame_length]; omega
  have := emitCallT cap src d hd B hB h o (regsOf v0 E NB A ok) cl (scr_regs v0 hs E NB A ok) hBv kd κn pat two
    (fun k => idx_regs d v0 E NB A ok _ k (hpre k)) (by rw [hXv]; exact hX) (by rw [hYv]; exact hY)
    (by rw [regsOf_OK]; exact hok) hcapB (by rw [hMv]; omega) (by rw [hMv]; exact hM)
  have e1 : callWordW d (regsOf v0 E NB A ok) pat two = callWordE d v0 E pat two := by
    simp only [callWordW, callWordE, codeW_regs, hXv, hYv]
  have e2 : callOkV d (regsOf v0 E NB A ok) pat two = callOkE d v0 E pat two := by
    simp only [callOkV, callOkE, flagV_regs, hXv, hYv]
  rw [negBit_regs, hMv, e1, e2, regsOf_OK, regsOf_updOK] at this
  exact this

/-! ## Reading a grid entry's sign -/

/-- Read entry `E_k`'s sign word `b 1 0 x`: `NB_k := b`, `NZ := x`; rewind the witness. -/
def readSign (k : Fin 4) : WM 10 NR :=
  .seq (skipEntK (rE k)) (.seq (.ifs sW (.inc (rNB k)) .skip) (.seq (.fwd sW) (.seq (.fwd sW) (.seq (.fwd sW)
    (.seq (.ifs sW (.inc rNZ) .skip) (rewB sW rBIG rT))))))

/-- An entry's sign bit and nonzero bit. -/
def bbOf (d : TWData) (e : ℕ) : Bool := (d.es.getD e (false, false, 0)).1
def xbOf (d : TWData) (e : ℕ) : Bool := (d.es.getD e (false, false, 0)).2.1

theorem plain_NZ : Plain rNZ := ⟨by decide, by decide⟩

/-- The cost of reading a sign. -/
def rsCost (B : ℕ) : ℕ := 20 * B * B + 60 * B + 40

theorem readSignT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (cl : Bool)
    (v0 : Fin NR → ℕ) (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (k : Fin 4) (E NB A : Fin 4 → ℕ) (ok : ℕ)
    (he : E k < d.es.length) (hNB : NB k = 0) (hcapB : B + 1 ≤ cap) :
    WExec cap (readSign k) (ts src h o (regsOf v0 E NB A ok) cl)
      (ts src h o (regsOf (Function.update v0 rNZ (xbOf d (E k)).toNat) E (Function.update NB k (bbOf d (E k)).toNat) A ok) cl)
      (rsCost B) := by
  obtain ⟨r, hr⟩ := hd.es
  have hl := hB.es
  have hcm := codeMax_le d.es
  have hlenE := length_le_entsW d.es
  obtain ⟨hr1, hr2, hr3, hr4, -, -⟩ := rE_ne k
  set v := regsOf v0 E NB A ok with hv
  have hvE : v (rE k) = E k := regsOf_E _ _ _ _ _ _
  have hvT : v rT = 0 := by rw [hv, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.t
  have hvF : v rF = 0 := by rw [hv, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.f
  have hvC : v rC = 0 := by rw [hv, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hs.c
  have hvB : v rBIG = B := by rw [hv, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩]; exact hBIG
  set e := d.es.getD (E k) (false, false, 0) with hee
  have hsplit := entsW_split d.es (E k) he
  set p := (entsW (d.es.take (E k))).length with hp
  have s1 := skipEntK_spec cap (ts src h o v cl) (rE k) hr1 hr2 hr3 d.es r
    (by rw [ts_st _ _ _ _ _ _ (show sW ≠ sOut by decide)]; exact hr)
    (ts_sh_src src h o v cl sW (by decide) (by decide))
    (by rw [ts_val _ _ _ _ _ rF (by decide)]; exact hvF) (by rw [ts_val _ _ _ _ _ rC (by decide)]; exact hvC)
    (by rw [ts_val _ _ _ _ _ rT (by decide)]; exact hvT) (by rw [ts_val _ _ _ _ _ _ hr4, hvE]; omega)
    (by rw [ts_val _ _ _ _ _ _ hr4, hvE]; omega) (by omega)
  rw [ts_val _ _ _ _ _ _ hr4, hvE] at s1
  have hread : ∀ i, i < 4 → readTapeBit (src sW) (p + i) = ([e.1, true, false, e.2.1] : List Bool).getD i false := by
    intro i hi
    rw [hr, hsplit, ← hee]
    simp only [entW, readTapeBit, List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), show p + i - (entsW (List.take (E k) d.es)).length = i by omega]
    rw [List.getElem?_append_left (by simp; omega)]
  have eNB : ∀ x, ((ts src h o v cl).seth sW p).setv (rNB k) x =
      (ts src h o (regsOf v0 E (Function.update NB k x) A ok) cl).seth sW p := by
    intro x
    rw [wseth_setv, ts_setv _ _ _ _ _ _ (rNB_ne_OP k), hv, regsOf_updNB]
  have s2 : WExec cap (.ifs sW (.inc (rNB k)) .skip) ((ts src h o v cl).seth sW p)
      ((ts src h o (regsOf v0 E (Function.update NB k (bbOf d (E k)).toNat) A ok) cl).seth sW p) 4 := by
    have hb : wbit ((ts src h o v cl).seth sW p) sW = e.1 := by
      have := hread 0 (by omega)
      simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, ts_st _ _ _ _ _ _ (show sW ≠ sOut by decide)]
      simpa using this
    cases hbb : bbOf d (E k)
    · have e0 : Function.update NB k (false).toNat = NB := by rw [Function.update_eq_self_iff]; simp [hNB]
      rw [e0]
      have hb' : e.1 = false := by rw [hee]; exact hbb
      exact WExec.mono (WExec.ifsF (by rw [hb, hb']) (WExec.skip _)) (by omega)
    · have hb' : e.1 = true := by rw [hee]; exact hbb
      have hi := WExec.inc (cap := cap) (rNB k) ((ts src h o v cl).seth sW p)
        (by rw [WState.seth_val, ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv, regsOf_NB, hNB]; omega)
      rw [WState.seth_val, ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv, regsOf_NB, hNB, Nat.zero_add] at hi
      rw [← hv, eNB] at hi
      exact WExec.ifsT (by rw [hb, hb']) hi
  set v1 := regsOf v0 E (Function.update NB k (bbOf d (E k)).toNat) A ok with hv1
  have f1 := WExec.fwd (cap := cap) sW ((ts src h o v1 cl).seth sW p)
  have f2 := WExec.fwd (cap := cap) sW (((ts src h o v1 cl).seth sW p).seth sW (((ts src h o v1 cl).seth sW p).sh sW + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f1 f2
  have f3 := WExec.fwd (cap := cap) sW ((ts src h o v1 cl).seth sW (p + 1 + 1))
  simp only [wseth_seth, WState.seth_sh, Function.update_self] at f3
  have s6 : WExec cap (.ifs sW (.inc rNZ) .skip) ((ts src h o v1 cl).seth sW (p + 1 + 1 + 1))
      ((ts src h o (regsOf (Function.update v0 rNZ (xbOf d (E k)).toNat) E (Function.update NB k (bbOf d (E k)).toNat)
        A ok) cl).seth sW (p + 1 + 1 + 1)) 4 := by
    have hb : wbit ((ts src h o v1 cl).seth sW (p + 1 + 1 + 1)) sW = e.2.1 := by
      have := hread 3 (by omega)
      simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, ts_st _ _ _ _ _ _ (show sW ≠ sOut by decide)]
      rw [show p + 1 + 1 + 1 = p + 3 by omega]
      simpa using this
    cases hxb : xbOf d (E k)
    · have e0 : Function.update v0 rNZ (false).toNat = v0 := by rw [Function.update_eq_self_iff]; simp [hNZ]
      rw [e0]
      have hb' : e.2.1 = false := by rw [hee]; exact hxb
      exact WExec.mono (WExec.ifsF (by rw [hb, hb']) (WExec.skip _)) (by omega)
    · have hb' : e.2.1 = true := by rw [hee]; exact hxb
      have hi := WExec.inc (cap := cap) rNZ ((ts src h o v1 cl).seth sW (p + 1 + 1 + 1))
        (by rw [WState.seth_val, ts_val _ _ _ _ _ rNZ (by decide), hv1, regsOf_plain _ _ _ _ _ _ plain_NZ, hNZ]; omega)
      rw [WState.seth_val, ts_val _ _ _ _ _ rNZ (by decide), hv1, regsOf_plain _ _ _ _ _ _ plain_NZ, hNZ, Nat.zero_add,
        wseth_setv, ts_setv _ _ _ _ _ rNZ (by decide), regsOf_updPlain _ _ _ _ _ _ plain_NZ] at hi
      exact WExec.ifsT (by rw [hb, hb']) hi
  set v2 := regsOf (Function.update v0 rNZ (xbOf d (E k)).toNat) E (Function.update NB k (bbOf d (E k)).toNat) A ok
    with hv2
  have hpB : p + 1 + 1 + 1 ≤ v2 rBIG := by
    rw [hv2, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide), hBIG]
    have := congrArg List.length hsplit
    simp only [List.length_append, entW, List.length_cons, List.length_nil] at this
    omega
  have s7 := rewT cap src h o v2 cl sW (by decide) (by decide) (p + 1 + 1 + 1)
    (by rw [hv2, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide)]; exact hs.t) hpB
    (by rw [hv2, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide), hBIG]; omega)
  rw [hv2, regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide), hBIG] at s7
  have hEk : E k ≤ B := by omega
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq f1 (WExec.seq f2 (WExec.seq f3 (WExec.seq s6 s7)))))) ?_
  unfold rsCost
  nlinarith

/-! ## A grid factor's level -/

/-- The grid entries of nonzero sign among `zs, …, zs + j − 1`. -/
def candBelow (d : TWData) (zs j : ℕ) : List ℕ :=
  (List.range j).filterMap fun a => if xbOf d (zs + a) then some (zs + a) else none

theorem candBelow_zero (d : TWData) (zs : ℕ) : candBelow d zs 0 = [] := rfl

theorem candBelow_succ (d : TWData) (zs j : ℕ) :
    candBelow d zs (j + 1) = candBelow d zs j ++ (if xbOf d (zs + j) then [zs + j] else []) := by
  unfold candBelow
  rw [List.range_succ, List.filterMap_append]
  by_cases h : xbOf d (zs + j) <;> simp [h]

theorem mem_candBelow (d : TWData) (zs j : ℕ) (a : ℕ) (ha : a < j) (hx : xbOf d (zs + a) = true) :
    zs + a ∈ candBelow d zs j := by
  unfold candBelow
  rw [List.mem_filterMap]
  exact ⟨a, List.mem_range.2 ha, by simp [hx]⟩

/-- One round of a grid factor's loop: read entry `E_k`'s sign; if nonzero, run the inner levels; clear `NB_k`;
step `E_k`. -/
def sBody (k : Fin 4) (inner : WM 10 NR) : WM 10 NR :=
  .seq (readSign k) (.seq (.ifr rNZ (.seq (.dec rNZ) inner) .skip) (.seq (.ifr (rNB k) (.dec (rNB k)) .skip) (.inc (rE k))))

/-- **A grid factor's loop** over the `s` entries from `ZS` (`A_k := s`, `E_k := ZS`, then `s` rounds). -/
def sLoop (k : Fin 4) (ZS : Fin NR) (inner : WM 10 NR) : WM 10 NR :=
  .seq (cloop rSS rT (.inc (rA k))) (.seq (cloop ZS rT (.inc (rE k)))
    (.seq (.whr (rA k) (.seq (.dec (rA k)) (sBody k inner))) (WM.clear (rE k))))

/-- The cost of a grid factor's loop. -/
def sCost (s zs cb : ℕ) : ℕ := s * (cb + 4) + 21 * s + 21 * zs + 20

theorem plain_SS : Plain rSS := ⟨by decide, by decide⟩
theorem plain_T : Plain rT := ⟨by decide, by decide⟩
theorem rA_ne_OP (k : Fin 4) : rA k ≠ rOP := by fin_cases k <;> decide

/-- **A counted increment**: `R := R + K` through `cloop K T (inc R)`, for a family `g j` of register vectors with
`R = j` and `K`, `T` fixed. -/
theorem cloopIncT (h : ℕ) (o : List Bool) (cl : Bool) (K R : Fin NR) (hK1 : K ≠ rOP) (hKT : K ≠ rT) (hR1 : R ≠ rOP)
    (hRK : R ≠ K) (hRT : R ≠ rT) (g : ℕ → Fin NR → ℕ) (hg : ∀ j, Function.update (g j) R (j + 1) = g (j + 1))
    (hgR : ∀ j, g j R = j) (hgK : ∀ j, g j K = g 0 K) (hgT : ∀ j, g j rT = 0) (hcap : g 0 K + 1 ≤ cap) :
    WExec cap (cloop K rT (.inc R)) (ts src h o (g 0) cl) (ts src h o (g (g 0 K)) cl) (18 * g 0 K + 3) := by
  set n := g 0 K with hn
  have hTK : rT ≠ K := Ne.symm hKT
  have key := cloop_spec cap K rT hKT (.inc R) n 3 (fun j => ts src h o (g j) cl) (by omega) (by
    intro j hj
    have hi := WExec.inc (cap := cap) R (((ts src h o (g j) cl).setv K (n - j - 1)).setv rT (j + 1))
      (by rw [WState.setv_val, WState.setv_val, Function.update_of_ne hRT, Function.update_of_ne hRK,
        ts_val _ _ _ _ _ _ hR1, hgR]; omega)
    refine WExec.cast cap hi ?_ le_rfl
    rw [WState.setv_val, WState.setv_val, Function.update_of_ne hRT, Function.update_of_ne hRK, ts_val _ _ _ _ _ _ hR1,
      hgR, ts_setv _ _ _ _ _ _ hK1, ts_setv _ _ _ _ _ _ (by decide), ts_setv _ _ _ _ _ _ hR1,
      ts_setv _ _ _ _ _ _ hK1, ts_setv _ _ _ _ _ _ (by decide)]
    congr 1
    rw [Function.update_comm (Ne.symm hRT), Function.update_comm (Ne.symm hRK), hg])
  have e0 : ((ts src h o (g 0) cl).setv K n).setv rT 0 = ts src h o (g 0) cl := by
    rw [ts_setv _ _ _ _ _ _ hK1, ts_setv _ _ _ _ _ _ (by decide)]
    congr 1
    rw [Function.update_eq_self_iff.2 (by rw [Function.update_of_ne hTK, hgT]), Function.update_eq_self_iff.2 hn]
  have e1 : ((ts src h o (g n) cl).setv K n).setv rT 0 = ts src h o (g n) cl := by
    rw [ts_setv _ _ _ _ _ _ hK1, ts_setv _ _ _ _ _ _ (by decide)]
    congr 1
    rw [Function.update_eq_self_iff.2 (by rw [Function.update_of_ne hTK, hgT]),
      Function.update_eq_self_iff.2 (by rw [hgK])]
  rw [e0, e1] at key
  exact WExec.mono key (by omega)

theorem rE_ne_OP (k : Fin 4) : rE k ≠ rOP := (rE_ne k).2.2.2.1
theorem rE_ne_T (k : Fin 4) : rE k ≠ rT := (rE_ne k).1
theorem rA_ne_T (k : Fin 4) : rA k ≠ rT := by fin_cases k <;> decide
theorem plain_ne_rE (r : Fin NR) (hr : Plain r) (k : Fin 4) : rE k ≠ r := by
  intro h; subst h; have := hr.2; rw [rE_val] at this; have := k.isLt; omega
theorem plain_ne_rA (r : Fin NR) (hr : Plain r) (k : Fin 4) : rA k ≠ r := by
  intro h; subst h; have := hr.2; rw [rA_val] at this; have := k.isLt; omega

/-- One round of a grid factor's loop, as a step of its invariant. -/
theorem sBodyT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (k : Fin 4) (inner : WM 10 NR)
    (Pre' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Prop) (W' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → List Bool)
    (Bf' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Bool) (bo c' : ℕ) (hin : LevelSpec cap src inner h cl v0 k.val Pre' W' Bf' bo c')
    (hcapB : B + 1 ≤ cap) (o : List Bool) (E NB A : Fin 4 → ℕ) (okj : ℕ) (hok : okj ≤ 1)
    (hfr : Fresh k.val E NB A) (hNBk : NB k = 0) (he : E k < d.es.length) (hEc : E k + 1 ≤ cap)
    (hpre : xbOf d (E k) = true → Pre' E (Function.update NB k (bbOf d (E k)).toNat))
    (hlen : xbOf d (E k) = true → o.length + (W' E (Function.update NB k (bbOf d (E k)).toNat)).length ≤ bo) :
    WExec cap (sBody k inner) (ts src h o (regsOf v0 E NB A okj) cl)
      (ts src h (o ++ (if xbOf d (E k) then W' E (Function.update NB k (bbOf d (E k)).toNat) else []))
        (regsOf v0 (Function.update E k (E k + 1)) NB A
          (if xbOf d (E k) then (if Bf' E (Function.update NB k (bbOf d (E k)).toNat) then okj else 0) else okj)) cl)
      (rsCost B + c' + 20) := by
  set b := bbOf d (E k) with hb
  set x := xbOf d (E k) with hx
  have s1 := readSignT cap src d hd B hB h o cl v0 hs hBIG hNZ k E NB A okj he hNBk hcapB
  rw [← hb, ← hx] at s1
  set NB' := Function.update NB k b.toNat with hNB'
  -- the nonzero branch
  have s2 : WExec cap (.ifr rNZ (.seq (.dec rNZ) inner) .skip)
      (ts src h o (regsOf (Function.update v0 rNZ x.toNat) E NB' A okj) cl)
      (ts src h (o ++ (if x then W' E NB' else [])) (regsOf v0 E NB' A (if x then (if Bf' E NB' then okj else 0) else okj)) cl)
      (c' + 4) := by
    have hNZv : regsOf (Function.update v0 rNZ x.toNat) E NB' A okj rNZ = x.toNat := by
      rw [regsOf_plain _ _ _ _ _ _ plain_NZ, Function.update_self]
    cases hxv : x
    · have e0 : Function.update v0 rNZ (false).toNat = v0 := by rw [Function.update_eq_self_iff]; simp [hNZ]
      rw [hxv] at hNZv
      simp only [Bool.false_eq_true, if_false, List.append_nil]
      rw [e0] at hNZv ⊢
      exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ rNZ (by decide), hNZv]; rfl) (WExec.skip _)) (by omega)
    · rw [hxv] at hNZv
      simp only [if_true]
      have hdec := WExec.dec (cap := cap) rNZ (ts src h o (regsOf (Function.update v0 rNZ (true).toNat) E NB' A okj) cl)
        (by rw [ts_val _ _ _ _ _ rNZ (by decide), hNZv]; simp; omega)
      rw [ts_val _ _ _ _ _ rNZ (by decide), hNZv, ts_setv _ _ _ _ _ rNZ (by decide),
        regsOf_updPlain _ _ _ _ _ _ plain_NZ, Function.update_idem] at hdec
      rw [show Function.update v0 rNZ ((true).toNat - 1) = v0 by rw [Function.update_eq_self_iff]; simp [hNZ]] at hdec
      have hfr' : Fresh k.val E NB' A := fun j hj => by
        obtain ⟨a1, a2, a3⟩ := hfr j hj
        refine ⟨a1, ?_, a3⟩
        rw [hNB', Function.update_of_ne (by intro e; subst e; omega)]; exact a2
      have hi := hin o E NB' A okj hok hfr' (hpre hxv) (hlen hxv)
      exact WExec.mono (WExec.ifrT (by rw [ts_val _ _ _ _ _ rNZ (by decide), hNZv]; simp) (WExec.seq hdec hi))
        (by omega)
  set okn := if x then (if Bf' E NB' then okj else 0) else okj with hokn
  -- clearing the sign register
  have s3 : WExec cap (.ifr (rNB k) (.dec (rNB k)) .skip)
      (ts src h (o ++ (if x then W' E NB' else [])) (regsOf v0 E NB' A okn) cl)
      (ts src h (o ++ (if x then W' E NB' else [])) (regsOf v0 E NB A okn) cl) 2 := by
    have hv : regsOf v0 E NB' A okn (rNB k) = b.toNat := by rw [regsOf_NB, hNB', Function.update_self]
    cases hbv : b
    · rw [hbv] at hv
      have e0 : NB' = NB := by rw [hNB', hbv, Function.update_eq_self_iff]; simp [hNBk]
      rw [e0]; rw [e0] at hv
      exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv]; rfl) (WExec.skip _)) (by omega)
    · rw [hbv] at hv
      have hdec := WExec.dec (cap := cap) (rNB k) (ts src h (o ++ (if x then W' E NB' else [])) (regsOf v0 E NB' A okn) cl)
        (by rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv]; simp; omega)
      rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv, ts_setv _ _ _ _ _ _ (rNB_ne_OP k), regsOf_updNB, hNB',
        Function.update_idem, show (true).toNat - 1 = 0 by rfl,
        show Function.update NB k 0 = NB from Function.update_eq_self_iff.2 hNBk.symm] at hdec
      exact WExec.ifrT (by rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k), hv]; simp) hdec
  -- stepping the entry index
  have s4 := WExec.inc (cap := cap) (rE k) (ts src h (o ++ (if x then W' E NB' else [])) (regsOf v0 E NB A okn) cl)
    (by rw [ts_val _ _ _ _ _ _ (rE_ne_OP k), regsOf_E]; omega)
  rw [ts_val _ _ _ _ _ _ (rE_ne_OP k), regsOf_E, ts_setv _ _ _ _ _ _ (rE_ne_OP k), regsOf_updE] at s4
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega)

/-- **A grid factor's level**: from the level inside it (at the digits below `k`), the loop over the `s` entries from
`ZS` appends, for each entry of nonzero sign in order, the inner level's output at that digit, and conjoins its
admissibility. -/
theorem sLevel (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (k : Fin 4) (ZS : Fin NR) (hZS : Plain ZS) (hZT : ZS ≠ rT)
    (hZO : ZS ≠ rOP) (inner : WM 10 NR) (Pre' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Prop)
    (W' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → List Bool) (Bf' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Bool) (bo c' : ℕ)
    (hin : LevelSpec cap src inner h cl v0 k.val Pre' W' Bf' bo c')
    (hzs : v0 ZS + v0 rSS ≤ d.es.length) (hcapB : B + 1 ≤ cap) (hcapS : v0 ZS + v0 rSS + 1 ≤ cap) :
    LevelSpec cap src (sLoop k ZS inner) h cl v0 (k.val + 1)
      (fun E NB => ∀ e ∈ candBelow d (v0 ZS) (v0 rSS),
        Pre' (Function.update E k e) (Function.update NB k (bbOf d e).toNat))
      (fun E NB => (candBelow d (v0 ZS) (v0 rSS)).flatMap fun e =>
        W' (Function.update E k e) (Function.update NB k (bbOf d e).toNat))
      (fun E NB => (candBelow d (v0 ZS) (v0 rSS)).all fun e =>
        Bf' (Function.update E k e) (Function.update NB k (bbOf d e).toNat))
      bo (sCost (v0 rSS) (v0 ZS) (rsCost B + c' + 20)) := by
  intro o E NB A ok hok hfr hpre hlen
  beta_reduce at hpre hlen
  set s := v0 rSS with hsd
  set zs := v0 ZS with hzsd
  obtain ⟨hEk, hNBk, hAk⟩ := hfr k (by omega)
  set F : ℕ → List Bool := fun e => W' (Function.update E k e) (Function.update NB k (bbOf d e).toNat) with hF
  set G : ℕ → Bool := fun e => Bf' (Function.update E k e) (Function.update NB k (bbOf d e).toNat) with hG
  set Wpre : ℕ → List Bool := fun j => (candBelow d zs j).flatMap F with hWpre
  set okp : ℕ → ℕ := fun j => if (candBelow d zs j).all G then ok else 0 with hokp
  have hWsucc : ∀ j, Wpre (j + 1) = Wpre j ++ (if xbOf d (zs + j) then F (zs + j) else []) := by
    intro j; simp only [hWpre, candBelow_succ, List.flatMap_append]
    by_cases hx : xbOf d (zs + j) <;> simp [hx]
  have hoksucc : ∀ j, okp (j + 1) = if xbOf d (zs + j) then (if G (zs + j) then okp j else 0) else okp j := by
    intro j; simp only [hokp, candBelow_succ, List.all_append]
    by_cases hx : xbOf d (zs + j) <;> by_cases hg : G (zs + j) <;> simp [hx, hg]
  have hWmono : ∀ j, j ≤ s → (Wpre j).length ≤ (Wpre s).length := by
    intro j hj
    induction hsj : s - j generalizing j with
    | zero => rw [show j = s by omega]
    | succ m ih =>
      have := ih (j + 1) (by omega) (by omega)
      rw [hWsucc] at this
      simp only [List.length_append] at this
      omega
  have hokp1 : ∀ j, okp j ≤ 1 := fun j => by simp only [hokp]; split_ifs <;> omega
  have hT0 : ∀ E' NB' A' ok', regsOf v0 E' NB' A' ok' rT = 0 := fun _ _ _ _ => by
    rw [regsOf_plain _ _ _ _ _ _ plain_T]; exact hs.t
  -- A_k := s
  have st1 := cloopIncT cap src h o cl rSS (rA k) (by decide) (by decide) (rA_ne_OP k) (plain_ne_rA _ plain_SS k)
    (rA_ne_T k) (fun j => regsOf v0 E NB (Function.update A k j) ok)
    (fun j => by beta_reduce; rw [regsOf_updA, Function.update_idem])
    (fun j => by beta_reduce; rw [regsOf_A, Function.update_self])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ plain_SS, regsOf_plain _ _ _ _ _ _ plain_SS])
    (fun j => hT0 _ _ _ _) (by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ plain_SS]; omega)
  simp only [regsOf_plain _ _ _ _ _ _ plain_SS] at st1
  rw [show Function.update A k 0 = A from Function.update_eq_self_iff.2 hAk.symm] at st1
  -- E_k := zs
  have st2 := cloopIncT cap src h o cl ZS (rE k) hZO hZT (rE_ne_OP k) (plain_ne_rE _ hZS k) (rE_ne_T k)
    (fun j => regsOf v0 (Function.update E k j) NB (Function.update A k s) ok)
    (fun j => by beta_reduce; rw [regsOf_updE, Function.update_idem])
    (fun j => by beta_reduce; rw [regsOf_E, Function.update_self])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ hZS, regsOf_plain _ _ _ _ _ _ hZS])
    (fun j => hT0 _ _ _ _) (by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ hZS]; omega)
  simp only [regsOf_plain _ _ _ _ _ _ hZS] at st2
  rw [show Function.update E k 0 = E from Function.update_eq_self_iff.2 hEk.symm] at st2
  -- the rounds
  set S : ℕ → TS := fun j => ts src h (o ++ Wpre j)
    (regsOf v0 (Function.update E k (zs + j)) NB (Function.update A k (s - j)) (okp j)) cl with hS
  have hS0 : S 0 = ts src h o (regsOf v0 (Function.update E k zs) NB (Function.update A k s) ok) cl := by
    simp [S, hWpre, hokp, candBelow_zero]
  have hSK : ∀ j ≤ s, (S j).val (rA k) = s - j := fun j _ => by
    simp only [S]; rw [ts_val _ _ _ _ _ _ (rA_ne_OP k), regsOf_A, Function.update_self]
  have hbody : ∀ j < s, WExec cap (sBody k inner) ((S j).setv (rA k) (s - j - 1)) (S (j + 1)) (rsCost B + c' + 20) := by
    intro j hj
    have e0 : (S j).setv (rA k) (s - j - 1) =
        ts src h (o ++ Wpre j) (regsOf v0 (Function.update E k (zs + j)) NB (Function.update A k (s - j - 1)) (okp j)) cl := by
      simp only [S]; rw [ts_setv _ _ _ _ _ _ (rA_ne_OP k), regsOf_updA, Function.update_idem]
    rw [e0]
    have hfr' : Fresh k.val (Function.update E k (zs + j)) NB (Function.update A k (s - j - 1)) := fun j' hj' => by
      obtain ⟨a1, a2, a3⟩ := hfr j' (by omega)
      have hne : j' ≠ k := by intro e; subst e; omega
      exact ⟨by rw [Function.update_of_ne hne]; exact a1, a2, by rw [Function.update_of_ne hne]; exact a3⟩
    have hEv : Function.update E k (zs + j) k = zs + j := Function.update_self _ _ _
    have hb := sBodyT cap src d hd B hB h cl v0 hs hBIG hNZ k inner Pre' W' Bf' bo c' hin hcapB (o ++ Wpre j)
      (Function.update E k (zs + j)) NB (Function.update A k (s - j - 1)) (okp j) (hokp1 j) hfr' hNBk
      (by rw [hEv]; omega) (by rw [hEv]; omega)
      (fun hx => by
        rw [hEv]
        exact hpre (zs + j) (mem_candBelow d zs s j hj (by rw [hEv] at hx; exact hx)))
      (fun hx => by
        rw [hEv] at hx ⊢
        have h1 := hWmono (j + 1) (by omega)
        rw [hWsucc, if_pos hx] at h1
        simp only [List.length_append] at h1 ⊢
        have e1 : (F (zs + j)).length =
            (W' (Function.update E k (zs + j)) (Function.update NB k (bbOf d (zs + j)).toNat)).length := rfl
        have e2 : (Wpre s).length = (List.flatMap (fun e => W' (Function.update E k e)
            (Function.update NB k (bbOf d e).toNat)) (candBelow d zs s)).length := rfl
        have e3 : (List.flatMap F (candBelow d zs s)).length = (List.flatMap (fun e => W' (Function.update E k e)
            (Function.update NB k (bbOf d e).toNat)) (candBelow d zs s)).length := rfl
        omega)
    simp only [hEv, Function.update_idem] at hb
    refine WExec.cast cap hb ?_ le_rfl
    simp only [S]
    rw [hWsucc, hoksucc, show s - (j + 1) = s - j - 1 by omega, show zs + (j + 1) = zs + j + 1 by omega]
    simp only [hF, hG, List.append_assoc]
  have hl := Round.wloop cap (rA k) (sBody k inner) (rsCost B + c' + 20) s S hSK (by omega) hbody
  rw [hS0] at hl
  -- clearing E_k
  have hSs : (S s).val (rE k) = zs + s := by
    simp only [S]; rw [ts_val _ _ _ _ _ _ (rE_ne_OP k), regsOf_E, Function.update_self]
  have hcl := wclear_spec cap (rE k) (zs + s) (S s) hSs (by omega)
  have e1 : (S s).setv (rE k) 0 = ts src h (o ++ (candBelow d zs s).flatMap F) (regsOf v0 E NB A (okp s)) cl := by
    simp only [S]
    rw [ts_setv _ _ _ _ _ _ (rE_ne_OP k), regsOf_updE, Function.update_idem, Nat.sub_self,
      show Function.update E k 0 = E from Function.update_eq_self_iff.2 hEk.symm,
      show Function.update A k 0 = A from Function.update_eq_self_iff.2 hAk.symm]
  rw [e1] at hcl
  refine WExec.mono (WExec.seq st1 (WExec.seq st2 (WExec.seq hl hcl))) ?_
  unfold sCost
  nlinarith

/-! ## A factor's level, and one monomial's block -/

/-- A factor's loop: a constant or parity factor has one candidate (no loop); a grid factor loops over `X`'s or `Y`'s
entries. -/
def digP (k : Fin 4) : FK → WM 10 NR → WM 10 NR
  | .one, inner => inner
  | .par, inner => inner
  | .sx, inner => sLoop k rXS inner
  | .sy, inner => sLoop k rYS inner

/-- A factor's candidates (entry indices; `0` for a constant or parity factor). -/
def candOf (d : TWData) (v0 : Fin NR → ℕ) : FK → List ℕ
  | .one => [0]
  | .par => [0]
  | .sx => candBelow d (v0 rXS) (v0 rSS)
  | .sy => candBelow d (v0 rYS) (v0 rSS)

/-- A candidate's sign bit. -/
def nbOfF (d : TWData) : FK → ℕ → Bool
  | .one, _ => false
  | .par, _ => false
  | .sx, e => bbOf d e
  | .sy, e => bbOf d e

/-- A factor's level cost. -/
def lvlCost (f : FK) (s zX zY rc c : ℕ) : ℕ :=
  match f with
  | .one => c
  | .par => c
  | .sx => sCost s zX (rc + c + 20)
  | .sy => sCost s zY (rc + c + 20)

theorem plain_XS : Plain rXS := ⟨by decide, by decide⟩
theorem plain_YS : Plain rYS := ⟨by decide, by decide⟩

/-- A constant or parity factor's level: the inner level itself, at digit `0`. -/
theorem idLevel (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (k : Fin 4) (inner : WM 10 NR)
    (Pre' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Prop) (W' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → List Bool)
    (Bf' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Bool) (bo c' : ℕ) (hin : LevelSpec cap src inner h cl v0 k.val Pre' W' Bf' bo c') :
    LevelSpec cap src inner h cl v0 (k.val + 1)
      (fun E NB => Pre' (Function.update E k 0) (Function.update NB k (false).toNat))
      (fun E NB => W' (Function.update E k 0) (Function.update NB k (false).toNat))
      (fun E NB => Bf' (Function.update E k 0) (Function.update NB k (false).toNat)) bo c' := by
  intro o E NB A ok hok hfr hpre hlen
  beta_reduce at hpre hlen ⊢
  obtain ⟨hEk, hNBk, -⟩ := hfr k (by omega)
  have eE : Function.update E k 0 = E := Function.update_eq_self_iff.2 hEk.symm
  have eN : Function.update NB k (false).toNat = NB := Function.update_eq_self_iff.2 (by simp [hNBk])
  rw [eE, eN] at hpre hlen ⊢
  exact hin o E NB A ok hok (fun j hj => hfr j (by omega)) hpre hlen

/-- **A factor's level** from the level inside it. -/
theorem digLevel (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (k : Fin 4) (f : FK) (inner : WM 10 NR)
    (Pre' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Prop) (W' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → List Bool)
    (Bf' : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Bool) (bo c' : ℕ) (hin : LevelSpec cap src inner h cl v0 k.val Pre' W' Bf' bo c')
    (hX : v0 rXS + v0 rSS ≤ d.es.length) (hY : v0 rYS + v0 rSS ≤ d.es.length) (hcapB : B + 1 ≤ cap)
    (hcX : v0 rXS + v0 rSS + 1 ≤ cap) (hcY : v0 rYS + v0 rSS + 1 ≤ cap) :
    LevelSpec cap src (digP k f inner) h cl v0 (k.val + 1)
      (fun E NB => ∀ e ∈ candOf d v0 f, Pre' (Function.update E k e) (Function.update NB k (nbOfF d f e).toNat))
      (fun E NB => (candOf d v0 f).flatMap fun e => W' (Function.update E k e) (Function.update NB k (nbOfF d f e).toNat))
      (fun E NB => (candOf d v0 f).all fun e => Bf' (Function.update E k e) (Function.update NB k (nbOfF d f e).toNat))
      bo (lvlCost f (v0 rSS) (v0 rXS) (v0 rYS) (rsCost B) c') := by
  cases f
  · have := idLevel cap src h cl v0 k inner Pre' W' Bf' bo c' hin
    simpa [candOf, nbOfF, lvlCost, digP] using this
  · have := idLevel cap src h cl v0 k inner Pre' W' Bf' bo c' hin
    simpa [candOf, nbOfF, lvlCost, digP] using this
  · exact sLevel cap src d hd B hB h cl v0 hs hBIG hNZ k _ plain_XS (by decide) (by decide) inner Pre' W' Bf'
      bo c' hin hX hcapB hcX
  · exact sLevel cap src d hd B hB h cl v0 hs hBIG hNZ k _ plain_YS (by decide) (by decide) inner Pre' W' Bf'
      bo c' hin hY hcapB hcY

/-- **One monomial's block**: the four factor loops (the last outermost) around one call. -/
def blockP (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool) : WM 10 NR :=
  digP 3 (pat 3) (digP 2 (pat 2) (digP 1 (pat 1) (digP 0 (pat 0) (emitCall kd κn pat two))))

/-- The block's cost. -/
def blockCost (B M s zX zY : ℕ) (pat : Fin 4 → FK) : ℕ :=
  lvlCost (pat 3) s zX zY (rsCost B) (lvlCost (pat 2) s zX zY (rsCost B) (lvlCost (pat 1) s zX zY (rsCost B)
    (lvlCost (pat 0) s zX zY (rsCost B) (emitCost B M))))

/-- The four digits' sign bits of a tuple of candidates. -/
def nbVec (d : TWData) (pat : Fin 4 → FK) (t : Fin 4 → ℕ) : Fin 4 → ℕ := fun k => (nbOfF d (pat k) (t k)).toNat

/-- **One monomial's calls, as the block writes them**: the product of the factors' candidates (the last outermost),
each call's entry. -/
def blockW (d : TWData) (v0 : Fin NR → ℕ) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool) : List Bool :=
  (lexProd fun k => candOf d v0 (pat k)).flatMap fun t =>
    entryW kd (negBitE κn (nbVec d pat t)) (v0 rMAG) (callWordE d v0 t pat two)

/-- The block's admissibility. -/
def blockOk (d : TWData) (v0 : Fin NR → ℕ) (pat : Fin 4 → FK) (two : Bool) : Bool :=
  (lexProd fun k => candOf d v0 (pat k)).all fun t => callOkE d v0 t pat two

theorem lexProd_flatMap {α β : Type} (S : Fin 4 → List α) (g : (Fin 4 → α) → List β) :
    (lexProd S).flatMap g = (S 3).flatMap fun t3 => (S 2).flatMap fun t2 => (S 1).flatMap fun t1 =>
      (S 0).flatMap fun t0 => g ![t0, t1, t2, t3] := by
  simp [lexProd, List.flatMap_assoc, List.flatMap_map, Function.comp_def]

theorem lexProd_all {α : Type} (S : Fin 4 → List α) (g : (Fin 4 → α) → Bool) :
    (lexProd S).all g = (S 3).all fun t3 => (S 2).all fun t2 => (S 1).all fun t1 => (S 0).all fun t0 => g ![t0, t1, t2, t3] := by
  simp [lexProd, List.all_flatMap, List.all_map, Function.comp_def]

theorem upd4 (e0 e1 e2 e3 : ℕ) :
    Function.update (Function.update (Function.update (Function.update (fun _ : Fin 4 => 0) 3 e3) 2 e2) 1 e1) 0 e0 =
      ![e0, e1, e2, e3] := by
  funext k; fin_cases k <;> rfl

theorem cand_lt (d : TWData) (v0 : Fin NR → ℕ) (zs e : ℕ) (he : e ∈ candBelow d zs (v0 rSS)) : e < zs + v0 rSS := by
  unfold candBelow at he
  rw [List.mem_filterMap] at he
  obtain ⟨a, ha, hx⟩ := he
  split_ifs at hx
  simp only [Option.some.injEq] at hx
  rw [List.mem_range] at ha
  omega

theorem idx_of_cand (d : TWData) (v0 : Fin NR → ℕ) (hX : v0 rXS + v0 rSS ≤ d.es.length)
    (hY : v0 rYS + v0 rSS ≤ d.es.length) (hdf : d.es.length ≤ d.df.length)
    (hpar : v0 rX < d.pcs.length ∧ v0 rX < d.pf.length) (f : FK) (k : Fin 4) (E : Fin 4 → ℕ)
    (he : E k ∈ candOf d v0 f) : IdxOKE d v0 E f k := by
  cases f
  · trivial
  · exact hpar
  · have := cand_lt d v0 _ _ he; exact ⟨by omega, by omega⟩
  · have := cand_lt d v0 _ _ he; exact ⟨by omega, by omega⟩

/-- The block's cost bound's inputs are the registers `SS`, `XS`, `YS`, `MAG`. -/
theorem blockT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool)
    (hX : v0 rXS + v0 rSS ≤ d.es.length) (hY : v0 rYS + v0 rSS ≤ d.es.length) (hdf : d.es.length ≤ d.df.length)
    (hpar : v0 rX < d.pcs.length ∧ v0 rX < d.pf.length) (hXc : v0 rX < d.crs.length ∧ v0 rX < d.ef.length)
    (hYc : two = true → v0 rY < d.crs.length ∧ v0 rY < d.ef.length) (hcapB : B + 1 ≤ cap)
    (hcX : v0 rXS + v0 rSS + 1 ≤ cap) (hcY : v0 rYS + v0 rSS + 1 ≤ cap) (hM : v0 rMAG ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1) (hlen : o.length + (blockW d v0 kd κn pat two).length + 30 * B + 40 ≤ cap) :
    WExec cap (blockP kd κn pat two) (ts src h o (regsOf v0 (fun _ => 0) (fun _ => 0) (fun _ => 0) ok) cl)
      (ts src h (o ++ blockW d v0 kd κn pat two)
        (regsOf v0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (if blockOk d v0 pat two then ok else 0)) cl)
      (blockCost B (v0 rMAG) (v0 rSS) (v0 rXS) (v0 rYS) pat) := by
  set bo := cap - (30 * B + 40) with hbo
  have L0 := emitLevel cap src d hd B hB h cl v0 hs hBIG kd κn pat two hXc hYc bo hcapB (by omega) hM
  have L1 := digLevel cap src d hd B hB h cl v0 hs hBIG hNZ 0 (pat 0) _ _ _ _ bo _ L0 hX hY hcapB hcX hcY
  have L2 := digLevel cap src d hd B hB h cl v0 hs hBIG hNZ 1 (pat 1) _ _ _ _ bo _ L1 hX hY hcapB hcX hcY
  have L3 := digLevel cap src d hd B hB h cl v0 hs hBIG hNZ 2 (pat 2) _ _ _ _ bo _ L2 hX hY hcapB hcX hcY
  have L4 := digLevel cap src d hd B hB h cl v0 hs hBIG hNZ 3 (pat 3) _ _ _ _ bo _ L3 hX hY hcapB hcX hcY
  have eW : blockW d v0 kd κn pat two = (candOf d v0 (pat 3)).flatMap fun e3 =>
      (candOf d v0 (pat 2)).flatMap fun e2 => (candOf d v0 (pat 1)).flatMap fun e1 =>
        (candOf d v0 (pat 0)).flatMap fun e0 =>
          entryW kd (negBitE κn (Function.update (Function.update (Function.update (Function.update (fun _ => 0) 3
            (nbOfF d (pat 3) e3).toNat) 2 (nbOfF d (pat 2) e2).toNat) 1 (nbOfF d (pat 1) e1).toNat) 0
              (nbOfF d (pat 0) e0).toNat)) (v0 rMAG)
            (callWordE d v0 (Function.update (Function.update (Function.update (Function.update (fun _ => 0) 3 e3) 2 e2)
              1 e1) 0 e0) pat two) := by
    unfold blockW
    rw [lexProd_flatMap]
    simp only [upd4]
    have hnb : ∀ e0 e1 e2 e3, nbVec d pat ![e0, e1, e2, e3] = ![(nbOfF d (pat 0) e0).toNat,
        (nbOfF d (pat 1) e1).toNat, (nbOfF d (pat 2) e2).toNat, (nbOfF d (pat 3) e3).toNat] := by
      intro e0 e1 e2 e3; funext k; fin_cases k <;> rfl
    simp only [hnb]
  have eB : blockOk d v0 pat two = (candOf d v0 (pat 3)).all fun e3 =>
      (candOf d v0 (pat 2)).all fun e2 => (candOf d v0 (pat 1)).all fun e1 =>
        (candOf d v0 (pat 0)).all fun e0 =>
          callOkE d v0 (Function.update (Function.update (Function.update (Function.update (fun _ => 0) 3 e3) 2 e2)
              1 e1) 0 e0) pat two := by
    unfold blockOk
    rw [lexProd_all]
    simp only [upd4]
  have hpre : ∀ e3 ∈ candOf d v0 (pat 3), ∀ e2 ∈ candOf d v0 (pat 2), ∀ e1 ∈ candOf d v0 (pat 1),
      ∀ e0 ∈ candOf d v0 (pat 0), ∀ k, IdxOKE d v0 (Function.update (Function.update (Function.update
        (Function.update (fun _ => 0) 3 e3) 2 e2) 1 e1) 0 e0) (pat k) k := by
    intro e3 h3 e2 h2 e1 h1 e0 h0 k
    rw [upd4]
    apply idx_of_cand d v0 hX hY hdf hpar
    fin_cases k <;> assumption
  have key := L4 o (fun _ => 0) (fun _ => 0) (fun _ => 0) ok hok (fun _ _ => ⟨rfl, rfl, rfl⟩)
    (by beta_reduce; intro e3 h3 e2 h2 e1 h1 e0 h0; exact hpre e3 h3 e2 h2 e1 h1 e0 h0)
    (by beta_reduce; rw [← eW]; omega)
  beta_reduce at key
  rw [eW, eB]
  exact key

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW

