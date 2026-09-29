import Proof.Wire_3_5.UnionMachine.FrontTWBase
import Proof.Wire_3_5.UnionMachine.FrontTableRef

/-! # C6 front, U5: one call's table entry (P3:3685-3691)

For one call of `(tr:tests)` the union machine writes the table entry the schedule loop reads
(`Entry.entryWord`): the test's kind, the sign of `c·s⁴`, its magnitude in unary, and the framed request word
`frame req.word` (P3:3083-3094: the tuple's four circuits, its named carriers, the common translation). It also
conjoins into `OK` the call's physical admissibility: each circuit's description envelope and each named carrier's
envelope (`I.Call`, P3:3083-3086; F4).

The request word is assembled by copying: its fixed head `natWord q ++ [mode] ++ natWord 4`, each circuit's code
(the constant's, a parity's, or a guessed atom's field in the witness), `natWord (#carriers)`, each carrier's code,
and the fixed tail `natListWord translation`. **`emitCallT`**: from the writer's state, `emitCall` appends
`entryW kd neg mag word` and updates `OK`.

Paper quantity of the main statement: one call's table entry (`entryWord`) and its admissibility bit. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef (FK)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

variable (cap : ℕ) (src : Fin 11 → List Bool)

/-! ## The sources -/

/-- **The writer's sources**: the fixed head and tail, the constant's code, the parities' and the carriers' codes,
the grid entries, and the three flag strings. -/
structure TWData where
  hd : List Bool
  tl : List Bool
  cc : List Bool
  pcs : List (List Bool)
  crs : List (List Bool)
  es : List (Bool × Bool × ℕ)
  df : List Bool
  pf : List Bool
  ef : List Bool

/-- The sources sit at the starts of their streams. -/
structure TWData.Holds (d : TWData) (src : Fin 11 → List Bool) : Prop where
  hd : ∃ r, src sHd = frItems [d.hd] ++ r
  tl : ∃ r, src sTl = frItems [d.tl] ++ r
  cc : ∃ r, src sCC = frItems [d.cc] ++ r
  pc : ∃ r, src sPC = frItems d.pcs ++ r
  cr : ∃ r, src sCR = frItems d.crs ++ r
  es : ∃ r, src sW = entsW d.es ++ r
  df : ∃ r, src sDF = d.df ++ r
  pf : ∃ r, src sPF = d.pf ++ r
  ef : ∃ r, src sEF = d.ef ++ r

/-- Every source within `B` cells. -/
structure TWData.Bnd (d : TWData) (B : ℕ) : Prop where
  hd : (frItems [d.hd]).length ≤ B
  tl : (frItems [d.tl]).length ≤ B
  cc : (frItems [d.cc]).length ≤ B
  pc : (frItems d.pcs).length ≤ B
  cr : (frItems d.crs).length ≤ B
  es : (entsW d.es).length ≤ B
  df : d.df.length ≤ B
  pf : d.pf.length ≤ B
  ef : d.ef.length ≤ B

/-! ## Flag bits and the admissibility register -/

/-- Read bit `K` of stream `s` into `R` (from `R = 0`), then rewind `s`. -/
def bitAt (s : Fin 11) (K R : Fin NR) : WM 10 NR := .seq (fwdK s K rT) (.seq (.ifs s (.inc R) .skip) (rewB s rBIG rT))

theorem bitAtT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO)
    (K R : Fin NR) (hK1 : K ≠ rT) (hK2 : K ≠ rOP) (hR1 : R ≠ rOP) (hR2 : R ≠ rT) (hR3 : R ≠ rBIG)
    (bits rest : List Bool) (hsrc : src s = bits ++ rest) (hk : v K < bits.length) (hT : v rT = 0) (hR : v R = 0)
    (hB : bits.length ≤ v rBIG) (hcapB : v rBIG ≤ cap) (hcapK : v K ≤ cap) (hcap1 : 1 ≤ cap) :
    WExec cap (bitAt s K R) (ts src h o v c)
      (ts src h o (Function.update v R (if bits.getD (v K) false then 1 else 0)) c) (16 * v K + 16 * v rBIG + 12) := by
  have s1 := fwdK_spec cap s K rT hK1 (ts src h o v c) (by rw [ts_val _ _ _ _ _ rT (by decide)]; exact hT)
    (by rw [ts_val _ _ _ _ _ K hK2]; exact hcapK)
  rw [ts_sh_src src h o v c s h1 h2, ts_val _ _ _ _ _ K hK2, Nat.zero_add] at s1
  have hbit : wbit ((ts src h o v c).seth s (v K)) s = bits.getD (v K) false := by
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, ts_st _ _ _ _ _ _ h1, hsrc, readTapeBit,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have eR : ∀ x, ((ts src h o v c).seth s (v K)).setv R x = (ts src h o (Function.update v R x) c).seth s (v K) := by
    intro x; rw [wseth_setv, ts_setv _ _ _ _ _ R hR1]
  have s2 : WExec cap (.ifs s (.inc R) .skip) ((ts src h o v c).seth s (v K))
      ((ts src h o (Function.update v R (if bits.getD (v K) false then 1 else 0)) c).seth s (v K)) 4 := by
    cases hb : bits.getD (v K) false
    · have e : Function.update v R (if false = true then 1 else 0) = v := by
        simp only [Bool.false_eq_true, if_false]; rw [← hR]; exact Function.update_eq_self R v
      rw [e]
      exact WExec.mono (WExec.ifsF (by rw [hbit, hb]) (WExec.skip _)) (by omega)
    · have hi := WExec.inc (cap := cap) R ((ts src h o v c).seth s (v K))
        (by rw [WState.seth_val, ts_val _ _ _ _ _ R hR1, hR]; omega)
      rw [WState.seth_val, ts_val _ _ _ _ _ R hR1, hR, eR] at hi
      exact WExec.ifsT (by rw [hbit, hb]) hi
  have s3 := rewT cap src h o (Function.update v R (if bits.getD (v K) false then 1 else 0)) c s h1 h2 (v K)
    (by rw [Function.update_of_ne (Ne.symm hR2)]; exact hT) (by rw [Function.update_of_ne (Ne.symm hR3)]; omega)
    (by rw [Function.update_of_ne (Ne.symm hR3)]; exact hcapB)
  rw [Function.update_of_ne (Ne.symm hR3)] at s3
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

/-- `OK := OK ∧ R`, `R := 0` (flags in `{0, 1}`). -/
def okAnd (R : Fin NR) : WM 10 NR := .ifr R (.dec R) (WM.clear rOK)

theorem okAndT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (R : Fin NR) (hR1 : R ≠ rOP) (hR2 : R ≠ rOK)
    (hR : v R ≤ 1) (hok : v rOK ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (okAnd R) (ts src h o v c)
      (ts src h o (Function.update (Function.update v R 0) rOK (if v R ≠ 0 then v rOK else 0)) c) 5 := by
  by_cases h0 : v R = 0
  · have hc := wclear_spec cap rOK (v rOK) (ts src h o v c) (by rw [ts_val _ _ _ _ _ rOK (by decide)])
      (by rw [ts_val _ _ _ _ _ rOK (by decide)]; omega)
    rw [ts_setv _ _ _ _ _ rOK (by decide)] at hc
    have e : Function.update (Function.update v R 0) rOK (if v R ≠ 0 then v rOK else 0) = Function.update v rOK 0 := by
      rw [if_neg (by simpa using h0), show (0 : ℕ) = v R from h0.symm, Function.update_eq_self]
    rw [e]
    exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ R hR1]; exact h0) hc) (by omega)
  · have hd := WExec.dec (cap := cap) R (ts src h o v c) (by rw [ts_val _ _ _ _ _ R hR1]; omega)
    rw [ts_val _ _ _ _ _ R hR1, ts_setv _ _ _ _ _ R hR1, show v R - 1 = 0 by omega] at hd
    have e : Function.update (Function.update v R 0) rOK (if v R ≠ 0 then v rOK else 0) = Function.update v R 0 := by
      rw [if_pos h0]
      conv_rhs => rw [← Function.update_eq_self rOK (Function.update v R 0)]
      rw [Function.update_of_ne (Ne.symm hR2)]
    rw [e]
    exact WExec.mono (WExec.ifrT (by rw [ts_val _ _ _ _ _ R hR1]; exact h0) hd) (by omega)

/-- `OK := OK ∧ R`, `R` kept. -/
def okKeep (R : Fin NR) : WM 10 NR := .ifr R .skip (WM.clear rOK)

theorem okKeepT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (R : Fin NR) (hR1 : R ≠ rOP)
    (hok : v rOK ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (okKeep R) (ts src h o v c) (ts src h o (Function.update v rOK (if v R ≠ 0 then v rOK else 0)) c) 5 := by
  by_cases h0 : v R = 0
  · have hc := wclear_spec cap rOK (v rOK) (ts src h o v c) (by rw [ts_val _ _ _ _ _ rOK (by decide)])
      (by rw [ts_val _ _ _ _ _ rOK (by decide)]; omega)
    rw [ts_setv _ _ _ _ _ rOK (by decide)] at hc
    rw [if_neg (by simpa using h0)]
    exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ R hR1]; exact h0) hc) (by omega)
  · rw [if_pos h0, Function.update_eq_self]
    exact WExec.mono (WExec.ifrT (by rw [ts_val _ _ _ _ _ R hR1]; exact h0) (WExec.skip _)) (by omega)

/-! ## The sign bit -/

/-- `R := 1 − R` (for `R ∈ {0, 1}`). -/
def toggle (R : Fin NR) : WM 10 NR := .ifr R (.dec R) (.inc R)

theorem toggleT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (R : Fin NR) (hR1 : R ≠ rOP) (b : Bool)
    (hR : v R = b.toNat) (hcap : 1 ≤ cap) :
    WExec cap (toggle R) (ts src h o v c) (ts src h o (Function.update v R (!b).toNat) c) 4 := by
  cases b
  · have hi := WExec.inc (cap := cap) R (ts src h o v c) (by rw [ts_val _ _ _ _ _ R hR1, hR]; simp; omega)
    rw [ts_val _ _ _ _ _ R hR1, ts_setv _ _ _ _ _ R hR1, hR] at hi
    exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ R hR1, hR]; rfl) hi) (by omega)
  · have hd := WExec.dec (cap := cap) R (ts src h o v c) (by rw [ts_val _ _ _ _ _ R hR1, hR]; simp; omega)
    rw [ts_val _ _ _ _ _ R hR1, ts_setv _ _ _ _ _ R hR1, hR] at hd
    exact WExec.mono (WExec.ifrT (by rw [ts_val _ _ _ _ _ R hR1, hR]; simp) hd) (by omega)

/-- Toggle `NEG` when digit `k`'s sign register is set. -/
def negStep (k : Fin 4) : WM 10 NR := .ifr (rNB k) (toggle rNEG) .skip

theorem rNB_ne_OP (k : Fin 4) : rNB k ≠ rOP := by fin_cases k <;> decide
theorem rNB_ne_NEG (k : Fin 4) : rNB k ≠ rNEG := by fin_cases k <;> decide

/-- The sign register of digit `k` as a bit. -/
def nbv (v : Fin NR → ℕ) (k : Fin 4) : Bool := decide (v (rNB k) ≠ 0)

theorem negStepT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (k : Fin 4) (b : Bool) (hN : v rNEG = b.toNat)
    (hcap : 1 ≤ cap) :
    WExec cap (negStep k) (ts src h o v c) (ts src h o (Function.update v rNEG (b ^^ nbv v k).toNat) c) 5 := by
  by_cases h0 : v (rNB k) = 0
  · have e : Function.update v rNEG (b ^^ nbv v k).toNat = v := by
      simp only [nbv, h0, ne_eq, not_true_eq_false, decide_false, Bool.xor_false]
      rw [Function.update_eq_self_iff]; simp [hN]
    rw [e]
    exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k)]; exact h0) (WExec.skip _)) (by omega)
  · have e : (b ^^ nbv v k) = !b := by simp [nbv, h0]
    rw [e]
    exact WExec.mono (WExec.ifrT (by rw [ts_val _ _ _ _ _ _ (rNB_ne_OP k)]; exact h0)
      (toggleT cap src h o v c rNEG (by decide) b hN hcap)) (by omega)

/-- **The sign bit**: `NEG := κn ⊕ NB₀ ⊕ NB₁ ⊕ NB₂ ⊕ NB₃`, emitted raw, `NEG` cleared. -/
def negP (κn : Bool) : WM 10 NR :=
  .seq (if κn then .inc rNEG else .skip) (.seq (negStep 0) (.seq (negStep 1) (.seq (negStep 2) (.seq (negStep 3)
    (.seq (.ifr rNEG (emitC sOut rOP true) (emitC sOut rOP false)) (.ifr rNEG (.dec rNEG) .skip))))))

/-- The emitted sign bit. -/
def negBit (κn : Bool) (v : Fin NR → ℕ) : Bool := κn ^^ nbv v 0 ^^ nbv v 1 ^^ nbv v 2 ^^ nbv v 3

theorem signT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (κn : Bool) (hN : v rNEG = 0) (hcap1 : 1 ≤ cap)
    (hcap : o.length < cap) :
    WExec cap (negP κn) (ts src h o v c) (ts src h (o ++ [negBit κn v]) v c) 60 := by
  have hnb : ∀ (w : Fin NR → ℕ) (k : Fin 4) (x : ℕ), nbv (Function.update w rNEG x) k = nbv w k := by
    intro w k x; simp only [nbv, Function.update_of_ne (rNB_ne_NEG k)]
  have s0 : WExec cap (if κn then .inc rNEG else .skip) (ts src h o v c) (ts src h o (Function.update v rNEG κn.toNat) c) 3 := by
    cases κn
    · have e : Function.update v rNEG (false).toNat = v := by rw [Function.update_eq_self_iff]; simp [hN]
      rw [e]; exact WExec.mono (WExec.skip _) (by omega)
    · have hi := WExec.inc (cap := cap) rNEG (ts src h o v c) (by rw [ts_val _ _ _ _ _ rNEG (by decide), hN]; omega)
      rw [ts_val _ _ _ _ _ rNEG (by decide), ts_setv _ _ _ _ _ rNEG (by decide), hN] at hi
      exact hi
  have s1 := negStepT cap src h o (Function.update v rNEG κn.toNat) c 0 κn (by simp) hcap1
  rw [Function.update_idem, hnb] at s1
  have s2 := negStepT cap src h o (Function.update v rNEG (κn ^^ nbv v 0).toNat) c 1 (κn ^^ nbv v 0) (by simp) hcap1
  rw [Function.update_idem, hnb] at s2
  have s3 := negStepT cap src h o (Function.update v rNEG (κn ^^ nbv v 0 ^^ nbv v 1).toNat) c 2 (κn ^^ nbv v 0 ^^ nbv v 1)
    (by simp) hcap1
  rw [Function.update_idem, hnb] at s3
  have s4 := negStepT cap src h o (Function.update v rNEG (κn ^^ nbv v 0 ^^ nbv v 1 ^^ nbv v 2).toNat) c 3
    (κn ^^ nbv v 0 ^^ nbv v 1 ^^ nbv v 2) (by simp) hcap1
  rw [Function.update_idem, hnb] at s4
  set w := Function.update v rNEG (negBit κn v).toNat with hw
  have hwN : w rNEG = (negBit κn v).toNat := by simp [w]
  have s5 : WExec cap (.ifr rNEG (emitC sOut rOP true) (emitC sOut rOP false)) (ts src h o w c)
      (ts src h (o ++ [negBit κn v]) w c) 8 := by
    cases hb : negBit κn v
    · exact WExec.ifrF (by rw [ts_val _ _ _ _ _ rNEG (by decide), hwN, hb]; rfl) (emitRawT cap src h o w c false hcap)
    · exact WExec.ifrT (by rw [ts_val _ _ _ _ _ rNEG (by decide), hwN, hb]; simp)
        (emitRawT cap src h o w c true hcap)
  have s6 : WExec cap (.ifr rNEG (.dec rNEG) .skip) (ts src h (o ++ [negBit κn v]) w c)
      (ts src h (o ++ [negBit κn v]) v c) 2 := by
    cases hb : negBit κn v
    · have e : w = v := by
        simp only [w, hb, Bool.toNat_false]; rw [Function.update_eq_self_iff]; simp [hN]
      rw [e]
      exact WExec.mono (WExec.ifrF (by rw [ts_val _ _ _ _ _ rNEG (by decide), hN]) (WExec.skip _)) (by omega)
    · have hd := WExec.dec (cap := cap) rNEG (ts src h (o ++ [true]) w c)
        (by rw [ts_val _ _ _ _ _ rNEG (by decide), hwN, hb]; simp; omega)
      rw [ts_val _ _ _ _ _ rNEG (by decide), ts_setv _ _ _ _ _ rNEG (by decide), hwN, hb] at hd
      have e : Function.update w rNEG ((true).toNat - 1) = v := by
        simp only [w, Function.update_idem, Bool.toNat_true, Nat.sub_self]; rw [Function.update_eq_self_iff]; simp [hN]
      rw [e] at hd
      exact WExec.ifrT (by rw [ts_val _ _ _ _ _ rNEG (by decide), hwN, hb]; simp) hd
  have e4 : Function.update v rNEG (κn ^^ nbv v 0 ^^ nbv v 1 ^^ nbv v 2 ^^ nbv v 3).toNat = w := rfl
  rw [e4] at s4
  exact WExec.mono (WExec.seq s0 (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))))
    (by omega)

/-! ## Raw ones and constant words -/

theorem emitOnesT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (hT : v rT = 0)
    (hcap : o.length + v rMAG ≤ cap) (hM : v rMAG ≤ cap) :
    WExec cap (emitOnes sOut rOP rMAG rT) (ts src h o v c) (ts src h (o ++ List.replicate (v rMAG) true) v c)
      (v rMAG * 15 + 3 + 7 * v rMAG) := by
  have e := emitOnes_spec cap sOut rOP rMAG rT (by decide) (by decide) (by decide) (ts src h o v c)
    (by rw [ts_val _ _ _ _ _ rT (by decide)]; exact hT) (by simp) (by simp [ts_val _ _ _ _ _ rMAG (by decide)]; omega)
    (by rw [ts_val _ _ _ _ _ rMAG (by decide)]; exact hM)
  rw [ts_val _ _ _ _ _ rMAG (by decide), appendO_ts] at e
  exact e

theorem emitWordT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (u : List Bool)
    (hcap : o.length + 2 * u.length ≤ cap) :
    WExec cap (emitWordM sOut rOP u) (ts src h o v c) (ts src h (o ++ marks u) v c) (16 * u.length) := by
  have e := emitWordM_spec cap sOut rOP u (ts src h o v c) (by simp) (by simpa using hcap)
  rwa [appendO_ts] at e

/-! ## One call -/

/-- A digit's code copy: the constant's item, parity item `X`, or grid entry `E_k`'s field. -/
def codeP : FK → Fin 4 → WM 10 NR
  | .one, _ => copyItem sCC rZ
  | .par, _ => copyItem sPC rX
  | .sx, k => copyEnt (rE k)
  | .sy, k => copyEnt (rE k)

/-- A digit's code word. -/
def codeW (d : TWData) (v : Fin NR → ℕ) : FK → Fin 4 → List Bool
  | .one, _ => d.cc
  | .par, _ => d.pcs.getD (v rX) []
  | .sx, k => natWord (d.es.getD (v (rE k)) (false, false, 0)).2.2
  | .sy, k => natWord (d.es.getD (v (rE k)) (false, false, 0)).2.2

/-- A digit's indices are in range. -/
def IdxOK (d : TWData) (v : Fin NR → ℕ) : FK → Fin 4 → Prop
  | .one, _ => True
  | .par, _ => v rX < d.pcs.length ∧ v rX < d.pf.length
  | .sx, k => v (rE k) < d.es.length ∧ v (rE k) < d.df.length
  | .sy, k => v (rE k) < d.es.length ∧ v (rE k) < d.df.length

/-- The scratch registers are clear. -/
structure Scr (v : Fin NR → ℕ) : Prop where
  t : v rT = 0
  f : v rF = 0
  c : v rC = 0
  z : v rZ = 0
  fl : v rFL = 0
  neg : v rNEG = 0

theorem rE_ne (k : Fin 4) : rE k ≠ rT ∧ rE k ≠ rF ∧ rE k ≠ rC ∧ rE k ≠ rOP ∧ rE k ≠ rOK ∧ rE k ≠ rFL := by
  fin_cases k <;> decide

theorem codeMax_le (es : List (Bool × Bool × ℕ)) : codeMax es ≤ (entsW es).length := by
  induction es with
  | nil => simp [codeMax]
  | cons e es ih =>
    have h1 : natBitLength e.2.2 ≤ (natWord e.2.2).length := by rw [natWord_length]; omega
    simp only [codeMax, List.map_cons, List.foldr_cons] at ih ⊢
    simp only [entsW, List.map_cons, List.flatten_cons, List.length_append, entW] at ih ⊢
    exact max_le (by simp; omega) (by omega)

theorem length_le_entsW (es : List (Bool × Bool × ℕ)) : es.length ≤ (entsW es).length := by
  induction es with
  | nil => simp [entsW]
  | cons e es ih =>
    simp only [entsW, List.map_cons, List.flatten_cons, List.length_append, List.length_cons, entW] at ih ⊢
    omega

theorem length_le_frItems (ws : List (List Bool)) : ws.length ≤ (frItems ws).length := by
  induction ws with
  | nil => simp [frItems]
  | cons w ws ih =>
    simp only [frItems, List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      FrontTWKit.frame_length] at ih ⊢
    omega

theorem codeP_T (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (f : FK) (k : Fin 4) (hi : IdxOK d v f k) (hcapB : B + 1 ≤ cap)
    (hcapO : o.length + 2 * B + 2 ≤ cap) :
    WExec cap (codeP f k) (ts src h o v c) (ts src h (o ++ marks (codeW d v f k)) v c) (20 * B * B + 200 * B + 100) := by
  cases f
  · obtain ⟨r, hr⟩ := hd.cc
    have hl := hB.cc
    have := copyItemT cap src h o v c sCC (by decide) (by decide) rZ (by decide) (by decide) [d.cc] r hr
      (by rw [hs.z]; simp) hs.t (by rw [hBIG]; exact hl) (by omega) (by rw [hs.z]; omega) (by omega)
    rw [hs.z] at this
    simp only [List.getD_cons_zero] at this
    exact WExec.mono this (by rw [hBIG]; nlinarith)
  · obtain ⟨r, hr⟩ := hd.pc
    have hl := hB.pc
    have h1 : v rX ≤ B := by have := length_le_frItems d.pcs; have := hi.1; omega
    have := copyItemT cap src h o v c sPC (by decide) (by decide) rX (by decide) (by decide) d.pcs r hr hi.1 hs.t
      (by rw [hBIG]; exact hl) (by omega) (by omega) (by omega)
    refine WExec.mono this ?_
    rw [hBIG]
    nlinarith
  all_goals
    obtain ⟨r, hr⟩ := hd.es
    have hl := hB.es
    have hcm := codeMax_le d.es
    obtain ⟨hr1, hr2, hr3, hr4, -, -⟩ := rE_ne k
    have h1 : v (rE k) ≤ B := by have := length_le_entsW d.es; have := hi.1; omega
    have := copyEntT cap src h o v c (rE k) hr1 hr2 hr3 hr4 d.es r hr hi.1 hs.f hs.c hs.t (by rw [hBIG]; exact hl)
      (by omega) (by omega) (by omega) (by omega)
    refine WExec.mono this ?_
    rw [hBIG]
    nlinarith

/-- A digit's flag check. -/
def flagP : FK → Fin 4 → WM 10 NR
  | .one, _ => okKeep rCDF
  | .par, _ => .seq (bitAt sPF rX rFL) (okAnd rFL)
  | .sx, k => .seq (bitAt sDF (rE k) rFL) (okAnd rFL)
  | .sy, k => .seq (bitAt sDF (rE k) rFL) (okAnd rFL)

/-- A digit's flag. -/
def flagV (d : TWData) (v : Fin NR → ℕ) : FK → Fin 4 → Bool
  | .one, _ => decide (v rCDF ≠ 0)
  | .par, _ => d.pf.getD (v rX) false
  | .sx, k => d.df.getD (v (rE k)) false
  | .sy, k => d.df.getD (v (rE k)) false

/-- A flag bit read into `FL`, conjoined into `OK`. -/
theorem bitOkT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO)
    (K : Fin NR) (hK1 : K ≠ rT) (hK2 : K ≠ rOP) (bits rest : List Bool)
    (hsrc : src s = bits ++ rest) (hk : v K < bits.length) (hT : v rT = 0) (hFL : v rFL = 0)
    (hB : bits.length ≤ v rBIG) (hcapB : v rBIG ≤ cap) (hcapK : v K ≤ cap) (hcap1 : 1 ≤ cap) (hok : v rOK ≤ 1) :
    WExec cap (.seq (bitAt s K rFL) (okAnd rFL)) (ts src h o v c)
      (ts src h o (Function.update v rOK (if bits.getD (v K) false then v rOK else 0)) c) (16 * v K + 16 * v rBIG + 18) := by
  have s1 := bitAtT cap src h o v c s h1 h2 K rFL hK1 hK2 (by decide) (by decide) (by decide) bits rest hsrc hk hT hFL hB
    hcapB hcapK hcap1
  set w := Function.update v rFL (if bits.getD (v K) false then 1 else 0) with hw
  have s2 := okAndT cap src h o w c rFL (by decide) (by decide) (by simp [w]; split_ifs <;> omega)
    (by simp [w, Function.update_of_ne (show rOK ≠ rFL by decide)]; exact hok) hcap1
  have e : Function.update (Function.update w rFL 0) rOK (if w rFL ≠ 0 then w rOK else 0) =
      Function.update v rOK (if bits.getD (v K) false then v rOK else 0) := by
    have e1 : Function.update w rFL 0 = v := by
      rw [hw, Function.update_idem, Function.update_eq_self_iff]; exact hFL.symm
    have e2 : w rFL = if bits.getD (v K) false then 1 else 0 := by simp [hw]
    have e3 : w rOK = v rOK := by simp [hw, Function.update_of_ne (show rOK ≠ rFL by decide)]
    rw [e1, e2, e3]
    cases bits.getD (v K) false <;> simp
  rw [e] at s2
  exact WExec.mono (WExec.seq s1 s2) (by omega)

theorem flagP_T (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (f : FK) (k : Fin 4) (hi : IdxOK d v f k) (hcapB : B + 1 ≤ cap)
    (hok : v rOK ≤ 1) :
    WExec cap (flagP f k) (ts src h o v c)
      (ts src h o (Function.update v rOK (if flagV d v f k then v rOK else 0)) c) (32 * B + 20) := by
  cases f
  · have := okKeepT cap src h o v c rCDF (by decide) hok (by omega)
    simp only [flagV, decide_eq_true_eq]
    exact WExec.mono this (by omega)
  · obtain ⟨r, hr⟩ := hd.pf
    have := bitOkT cap src h o v c sPF (by decide) (by decide) rX (by decide) (by decide) d.pf r
      hr hi.2 hs.t hs.fl (by rw [hBIG]; exact hB.pf) (by omega) (by have := hB.pf; have := hi.2; omega) (by omega) hok
    exact WExec.mono this (by have := hB.pf; have := hi.2; omega)
  all_goals
    obtain ⟨r, hr⟩ := hd.df
    obtain ⟨hr1, -, -, hr4, -, -⟩ := rE_ne k
    have := bitOkT cap src h o v c sDF (by decide) (by decide) (rE k) hr1 hr4 d.df r hr hi.2 hs.t hs.fl
      (by rw [hBIG]; exact hB.df) (by omega) (by have := hB.df; have := hi.2; omega) (by omega) hok
    exact WExec.mono this (by have := hB.df; have := hi.2; omega)

/-- A named carrier's envelope flag. -/
def carFlag (R : Fin NR) : WM 10 NR := .seq (bitAt sEF R rFL) (okAnd rFL)

/-! ## The entry -/

/-- **One table entry** (`Entry.entryWord`): the kind's flag bits, the sign, the magnitude in unary, the framed
request word. -/
def entryW (kd : Fin 3) (neg : Bool) (mag : ℕ) (word : List Bool) : List Bool :=
  [true, Entry.kindHi kd, Entry.kindLo kd, neg] ++ List.replicate mag true ++ false :: frame word

theorem frame_eq_marks (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih, marks]

/-- The request word the call copies. -/
def callWordW (d : TWData) (v : Fin NR → ℕ) (pat : Fin 4 → FK) (two : Bool) : List Bool :=
  d.hd ++ codeW d v (pat 0) 0 ++ codeW d v (pat 1) 1 ++ codeW d v (pat 2) 2 ++ codeW d v (pat 3) 3 ++
    natWord (if two then 2 else 1) ++ d.crs.getD (v rX) [] ++ (if two then d.crs.getD (v rY) [] else []) ++ d.tl

/-- The call's admissibility: every circuit's and every named carrier's envelope flag. -/
def callOkV (d : TWData) (v : Fin NR → ℕ) (pat : Fin 4 → FK) (two : Bool) : Bool :=
  flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 && flagV d v (pat 3) 3 &&
    d.ef.getD (v rX) false && (!two || d.ef.getD (v rY) false)

/-! ## The call's four parts -/

/-- The entry's head: `1`, the kind's two bits, the sign, `1^mag`, `0`. -/
def headP (kd : Fin 3) (κn : Bool) : WM 10 NR :=
  .seq (emitC sOut rOP true) (.seq (emitC sOut rOP (Entry.kindHi kd)) (.seq (emitC sOut rOP (Entry.kindLo kd))
    (.seq (negP κn) (.seq (emitOnes sOut rOP rMAG rT) (emitC sOut rOP false)))))

theorem headT (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (kd : Fin 3) (κn : Bool) (hs : Scr v)
    (hcap : o.length + v rMAG + 10 ≤ cap) (hM : v rMAG ≤ cap) :
    WExec cap (headP kd κn) (ts src h o v c)
      (ts src h (o ++ [true] ++ [Entry.kindHi kd] ++ [Entry.kindLo kd] ++ [negBit κn v] ++
        List.replicate (v rMAG) true ++ [false]) v c) (22 * v rMAG + 100) := by
  have s1 := emitRawT cap src h o v c true (by omega)
  have s2 := emitRawT cap src h (o ++ [true]) v c (Entry.kindHi kd) (by simp; omega)
  have s3 := emitRawT cap src h (o ++ [true] ++ [Entry.kindHi kd]) v c (Entry.kindLo kd) (by simp; omega)
  have s4 := signT cap src h (o ++ [true] ++ [Entry.kindHi kd] ++ [Entry.kindLo kd]) v c κn hs.neg (by omega)
    (by simp; omega)
  have s5 := emitOnesT cap src h (o ++ [true] ++ [Entry.kindHi kd] ++ [Entry.kindLo kd] ++ [negBit κn v]) v c hs.t
    (by simp; omega) hM
  have s6 := emitRawT cap src h (o ++ [true] ++ [Entry.kindHi kd] ++ [Entry.kindLo kd] ++ [negBit κn v] ++
    List.replicate (v rMAG) true) v c false (by simp; omega)
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) (by omega)

theorem codeW_le (d : TWData) (B : ℕ) (hB : d.Bnd B) (v : Fin NR → ℕ) (f : FK) (k : Fin 4) (hi : IdxOK d v f k) :
    (codeW d v f k).length ≤ B := by
  cases f
  · have := hB.cc; simp [codeW, frItems, FrontTWKit.frame_length] at this ⊢; omega
  · have := hB.pc
    have hsp := congrArg List.length (frItems_split d.pcs (v rX) hi.1)
    simp only [List.length_append, FrontTWKit.frame_length] at hsp
    simp only [codeW]; omega
  all_goals
    have := hB.es
    have hsp := congrArg List.length (entsW_split d.es (v (rE k)) hi.1)
    simp only [List.length_append, entW, List.length_cons, List.length_nil] at hsp
    simp only [codeW]; omega

theorem item_le (ws : List (List Bool)) (B : ℕ) (hB : (frItems ws).length ≤ B) (j : ℕ) (hj : j < ws.length) :
    (ws.getD j []).length ≤ B := by
  have hsp := congrArg List.length (frItems_split ws j hj)
  simp only [List.length_append, FrontTWKit.frame_length] at hsp
  omega

/-- The request word's head and the four circuits' codes. -/
def codesP (pat : Fin 4 → FK) : WM 10 NR :=
  .seq (copyItem sHd rZ) (.seq (codeP (pat 0) 0) (.seq (codeP (pat 1) 1) (.seq (codeP (pat 2) 2) (codeP (pat 3) 3))))

theorem codesT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (pat : Fin 4 → FK) (hi : ∀ k, IdxOK d v (pat k) k)
    (hcapB : B + 1 ≤ cap) (hcapO : o.length + 12 * B + 2 ≤ cap) :
    WExec cap (codesP pat) (ts src h o v c)
      (ts src h (o ++ marks d.hd ++ marks (codeW d v (pat 0) 0) ++ marks (codeW d v (pat 1) 1) ++
        marks (codeW d v (pat 2) 2) ++ marks (codeW d v (pat 3) 3)) v c) (100 * B * B + 1000 * B + 510) := by
  obtain ⟨r, hr⟩ := hd.hd
  have hhd : d.hd.length ≤ B := by have := hB.hd; simp [frItems, FrontTWKit.frame_length] at this; omega
  have l0 := codeW_le d B hB v _ 0 (hi 0)
  have l1 := codeW_le d B hB v _ 1 (hi 1)
  have l2 := codeW_le d B hB v _ 2 (hi 2)
  have s1 := copyItemT cap src h o v c sHd (by decide) (by decide) rZ (by decide) (by decide) [d.hd] r hr
    (by rw [hs.z]; simp) hs.t (by rw [hBIG]; exact hB.hd) (by omega) (by rw [hs.z]; omega) (by have := hB.hd; omega)
  rw [hs.z] at s1
  simp only [List.getD_cons_zero] at s1
  have s2 := codeP_T cap src d hd B hB h (o ++ marks d.hd) v c hs hBIG (pat 0) 0 (hi 0) hcapB (by simp; omega)
  have s3 := codeP_T cap src d hd B hB h (o ++ marks d.hd ++ marks (codeW d v (pat 0) 0)) v c hs hBIG (pat 1) 1 (hi 1)
    hcapB (by simp; omega)
  have s4 := codeP_T cap src d hd B hB h (o ++ marks d.hd ++ marks (codeW d v (pat 0) 0) ++
    marks (codeW d v (pat 1) 1)) v c hs hBIG (pat 2) 2 (hi 2) hcapB (by simp; omega)
  have s5 := codeP_T cap src d hd B hB h (o ++ marks d.hd ++ marks (codeW d v (pat 0) 0) ++
    marks (codeW d v (pat 1) 1) ++ marks (codeW d v (pat 2) 2)) v c hs hBIG (pat 3) 3 (hi 3) hcapB (by simp; omega)
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
  rw [hBIG]
  have := hB.hd
  nlinarith

/-- The request word's carriers and tail, and the frame's end. -/
def tailP (two : Bool) : WM 10 NR :=
  .seq (emitWordM sOut rOP (natWord (if two then 2 else 1))) (.seq (copyItem sCR rX)
    (.seq (if two then copyItem sCR rY else .skip) (.seq (copyItem sTl rZ) (emitC sOut rOP false))))

theorem natWord_len_small (two : Bool) : (natWord (if two then 2 else 1)).length ≤ 5 := by cases two <;> decide

theorem tailT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (two : Bool) (hX : v rX < d.crs.length)
    (hY : two = true → v rY < d.crs.length) (hcapB : B + 1 ≤ cap) (hcapO : o.length + 10 * B + 20 ≤ cap) :
    WExec cap (tailP two) (ts src h o v c)
      (ts src h (o ++ marks (natWord (if two then 2 else 1)) ++ marks (d.crs.getD (v rX) []) ++
        (if two then marks (d.crs.getD (v rY) []) else []) ++ marks d.tl ++ [false]) v c)
      (60 * B * B + 600 * B + 400) := by
  obtain ⟨rc, hrc⟩ := hd.cr
  obtain ⟨rt, hrt⟩ := hd.tl
  have hn := natWord_len_small two
  have hcr := hB.cr
  have hX' : v rX ≤ B := by have := length_le_frItems d.crs; omega
  have lX := item_le d.crs B hB.cr (v rX) hX
  have htl : d.tl.length ≤ B := by have := hB.tl; simp [frItems, FrontTWKit.frame_length] at this; omega
  have s1 := emitWordT cap src h o v c (natWord (if two then 2 else 1)) (by omega)
  set o1 := o ++ marks (natWord (if two then 2 else 1)) with ho1
  have s2 := copyItemT cap src h o1 v c sCR (by decide) (by decide) rX (by decide) (by decide) d.crs rc hrc hX hs.t
    (by rw [hBIG]; exact hcr) (by omega) (by omega) (by simp only [o1, List.length_append, Streaming.marks_length]; omega)
  set o2 := o1 ++ marks (d.crs.getD (v rX) []) with ho2
  have ho2l : o2.length ≤ o.length + 10 + 2 * B := by
    simp only [o2, o1, List.length_append, Streaming.marks_length]; omega
  have s3 : WExec cap (if two then copyItem sCR rY else .skip) (ts src h o2 v c)
      (ts src h (o2 ++ (if two then marks (d.crs.getD (v rY) []) else [])) v c) (20 * B * B + 200 * B + 100) := by
    cases two
    · simp only [Bool.false_eq_true, if_false, List.append_nil]
      exact WExec.mono (WExec.skip _) (by omega)
    · simp only [if_true]
      have hY' := hY rfl
      have hY'' : v rY ≤ B := by have := length_le_frItems d.crs; omega
      have := copyItemT cap src h o2 v c sCR (by decide) (by decide) rY (by decide) (by decide) d.crs rc hrc hY' hs.t
        (by rw [hBIG]; exact hcr) (by omega) (by omega) (by omega)
      refine WExec.mono this ?_
      rw [hBIG]; nlinarith
  set o3 := o2 ++ (if two then marks (d.crs.getD (v rY) []) else []) with ho3
  have ho3l : o3.length ≤ o.length + 10 + 4 * B := by
    have lY : (if two then marks (d.crs.getD (v rY) []) else []).length ≤ 2 * B := by
      cases two
      · simp
      · simp only [if_true, Streaming.marks_length]; have := item_le d.crs B hB.cr (v rY) (hY rfl); omega
    simp only [o3, o2, o1, List.length_append, Streaming.marks_length] at lY ⊢; omega
  have s4 := copyItemT cap src h o3 v c sTl (by decide) (by decide) rZ (by decide) (by decide) [d.tl] rt hrt
    (by rw [hs.z]; simp) hs.t (by rw [hBIG]; exact hB.tl) (by omega) (by rw [hs.z]; omega) (by have := hB.tl; omega)
  rw [hs.z] at s4
  simp only [List.getD_cons_zero] at s4
  have s5 := emitRawT cap src h (o3 ++ marks d.tl) v c false (by simp only [List.length_append, Streaming.marks_length]; omega)
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
  rw [hBIG]
  have := hB.tl
  nlinarith

/-- The call's admissibility checks: the four circuits' flags, then the named carriers'. -/
def flagsP (pat : Fin 4 → FK) (two : Bool) : WM 10 NR :=
  .seq (flagP (pat 0) 0) (.seq (flagP (pat 1) 1) (.seq (flagP (pat 2) 2) (.seq (flagP (pat 3) 3)
    (.seq (carFlag rX) (if two then carFlag rY else .skip)))))

theorem flagV_upd (d : TWData) (v : Fin NR → ℕ) (x : ℕ) (f : FK) (k : Fin 4) :
    flagV d (Function.update v rOK x) f k = flagV d v f k := by
  obtain ⟨-, -, -, -, h5, -⟩ := rE_ne k
  cases f <;> simp [flagV, Function.update_of_ne (show rCDF ≠ rOK by decide), Function.update_of_ne (show rX ≠ rOK by decide),
    Function.update_of_ne h5]

theorem okUpd_eq (v : Fin NR → ℕ) (acc b : Bool) :
    Function.update (Function.update v rOK (if acc then v rOK else 0)) rOK
      (if b then (Function.update v rOK (if acc then v rOK else 0)) rOK else 0) =
      Function.update v rOK (if (acc && b) then v rOK else 0) := by
  rw [Function.update_idem, Function.update_self]
  cases acc <;> cases b <;> simp

theorem scr_upd (v : Fin NR → ℕ) (hs : Scr v) (x : ℕ) : Scr (Function.update v rOK x) :=
  ⟨by rw [Function.update_of_ne (by decide)]; exact hs.t, by rw [Function.update_of_ne (by decide)]; exact hs.f,
    by rw [Function.update_of_ne (by decide)]; exact hs.c, by rw [Function.update_of_ne (by decide)]; exact hs.z,
    by rw [Function.update_of_ne (by decide)]; exact hs.fl, by rw [Function.update_of_ne (by decide)]; exact hs.neg⟩

theorem idx_upd (d : TWData) (v : Fin NR → ℕ) (x : ℕ) (f : FK) (k : Fin 4) (hi : IdxOK d v f k) :
    IdxOK d (Function.update v rOK x) f k := by
  obtain ⟨-, -, -, -, h5, -⟩ := rE_ne k
  cases f
  · trivial
  · simp only [IdxOK, Function.update_of_ne (show rX ≠ rOK by decide)] at hi ⊢; exact hi
  · simp only [IdxOK, Function.update_of_ne h5] at hi ⊢; exact hi
  · simp only [IdxOK, Function.update_of_ne h5] at hi ⊢; exact hi

theorem flagStep (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (f : FK) (k : Fin 4) (hi : IdxOK d v f k) (hcapB : B + 1 ≤ cap)
    (hok : v rOK ≤ 1) (acc : Bool) :
    WExec cap (flagP f k) (ts src h o (Function.update v rOK (if acc then v rOK else 0)) c)
      (ts src h o (Function.update v rOK (if (acc && flagV d v f k) then v rOK else 0)) c) (32 * B + 20) := by
  have := flagP_T cap src d hd B hB h o (Function.update v rOK (if acc then v rOK else 0)) c (scr_upd v hs _)
    (by rw [Function.update_of_ne (by decide)]; exact hBIG) f k (idx_upd d v _ f k hi) hcapB (by simp; split_ifs <;> omega)
  rwa [flagV_upd, okUpd_eq] at this

theorem carStep (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (R : Fin NR) (hR1 : R ≠ rT) (hR2 : R ≠ rOP) (hR3 : R ≠ rOK)
    (hk : v R < d.ef.length) (hcapB : B + 1 ≤ cap) (hok : v rOK ≤ 1) (acc : Bool) :
    WExec cap (carFlag R) (ts src h o (Function.update v rOK (if acc then v rOK else 0)) c)
      (ts src h o (Function.update v rOK (if (acc && d.ef.getD (v R) false) then v rOK else 0)) c) (32 * B + 20) := by
  obtain ⟨r, hr⟩ := hd.ef
  have hRv : (Function.update v rOK (if acc then v rOK else 0)) R = v R := Function.update_of_ne hR3 _ _
  have := bitOkT cap src h o (Function.update v rOK (if acc then v rOK else 0)) c sEF (by decide) (by decide) R hR1 hR2
    d.ef r hr (by rw [hRv]; exact hk) (by rw [Function.update_of_ne (by decide)]; exact hs.t)
    (by rw [Function.update_of_ne (by decide)]; exact hs.fl)
    (by rw [Function.update_of_ne (by decide), hBIG]; exact hB.ef) (by rw [Function.update_of_ne (by decide), hBIG]; omega)
    (by rw [hRv]; have := hB.ef; omega) (by omega) (by simp; split_ifs <;> omega)
  rw [hRv, okUpd_eq] at this
  refine WExec.mono this ?_
  have := hB.ef
  rw [Function.update_of_ne (by decide), hBIG]; omega

theorem flagsT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (pat : Fin 4 → FK) (two : Bool) (hi : ∀ k, IdxOK d v (pat k) k)
    (hX : v rX < d.ef.length) (hY : two = true → v rY < d.ef.length) (hcapB : B + 1 ≤ cap) (hok : v rOK ≤ 1) :
    WExec cap (flagsP pat two) (ts src h o v c)
      (ts src h o (Function.update v rOK (if callOkV d v pat two then v rOK else 0)) c) (200 * B + 200) := by
  have e0 : Function.update v rOK (if true then v rOK else 0) = v := by simp
  have s1 := flagStep cap src d hd B hB h o v c hs hBIG (pat 0) 0 (hi 0) hcapB hok true
  rw [e0] at s1
  have s2 := flagStep cap src d hd B hB h o v c hs hBIG (pat 1) 1 (hi 1) hcapB hok (true && flagV d v (pat 0) 0)
  have s3 := flagStep cap src d hd B hB h o v c hs hBIG (pat 2) 2 (hi 2) hcapB hok
    (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1)
  have s4 := flagStep cap src d hd B hB h o v c hs hBIG (pat 3) 3 (hi 3) hcapB hok
    (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2)
  have s5 := carStep cap src d hd B hB h o v c hs hBIG rX (by decide) (by decide) (by decide) hX hcapB hok
    (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 && flagV d v (pat 3) 3)
  have s6 : WExec cap (if two then carFlag rY else .skip)
      (ts src h o (Function.update v rOK (if (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 &&
        flagV d v (pat 3) 3 && d.ef.getD (v rX) false) then v rOK else 0)) c)
      (ts src h o (Function.update v rOK (if callOkV d v pat two then v rOK else 0)) c) (32 * B + 20) := by
    cases two
    · have e : callOkV d v pat false = (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 &&
          flagV d v (pat 3) 3 && d.ef.getD (v rX) false) := by simp [callOkV]
      rw [e]; exact WExec.mono (WExec.skip _) (by omega)
    · have := carStep cap src d hd B hB h o v c hs hBIG rY (by decide) (by decide) (by decide) (hY rfl) hcapB hok
        (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 && flagV d v (pat 3) 3 &&
          d.ef.getD (v rX) false)
      have e : callOkV d v pat true = (true && flagV d v (pat 0) 0 && flagV d v (pat 1) 1 && flagV d v (pat 2) 2 &&
          flagV d v (pat 3) 3 && d.ef.getD (v rX) false && d.ef.getD (v rY) false) := by simp [callOkV]
      rw [e]; exact this
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) (by omega)

/-- **One call**: its table entry, then its admissibility checks. -/
def emitCall (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool) : WM 10 NR :=
  .seq (headP kd κn) (.seq (codesP pat) (.seq (tailP two) (flagsP pat two)))

/-- The cost of one call. -/
def emitCost (B M : ℕ) : ℕ := 200 * B * B + 2000 * B + 30 * M + 2000

/-- **One call's entry and admissibility bit**: `emitCall` appends `entryW kd neg mag word` (the sign `negBit`, the
magnitude register, the request word `callWordW` copied from the sources) and conjoins the call's envelope flags
(`callOkV`) into `OK`; every other register is unchanged. -/
theorem emitCallT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ)
    (c : Bool) (hs : Scr v) (hBIG : v rBIG = B) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool)
    (hi : ∀ k, IdxOK d v (pat k) k) (hX : v rX < d.crs.length ∧ v rX < d.ef.length)
    (hY : two = true → v rY < d.crs.length ∧ v rY < d.ef.length) (hok : v rOK ≤ 1) (hcapB : B + 1 ≤ cap)
    (hcapO : o.length + v rMAG + 30 * B + 40 ≤ cap) (hM : v rMAG ≤ cap) :
    WExec cap (emitCall kd κn pat two) (ts src h o v c)
      (ts src h (o ++ entryW kd (negBit κn v) (v rMAG) (callWordW d v pat two))
        (Function.update v rOK (if callOkV d v pat two then v rOK else 0)) c) (emitCost B (v rMAG)) := by
  have s1 := headT cap src h o v c kd κn hs (by omega) hM
  set o1 := o ++ [true] ++ [Entry.kindHi kd] ++ [Entry.kindLo kd] ++ [negBit κn v] ++ List.replicate (v rMAG) true ++
    [false] with ho1
  have ho1l : o1.length = o.length + v rMAG + 5 := by simp [o1]; omega
  have s2 := codesT cap src d hd B hB h o1 v c hs hBIG pat hi hcapB (by omega)
  set o2 := o1 ++ marks d.hd ++ marks (codeW d v (pat 0) 0) ++ marks (codeW d v (pat 1) 1) ++
    marks (codeW d v (pat 2) 2) ++ marks (codeW d v (pat 3) 3) with ho2
  have ho2l : o2.length ≤ o1.length + 10 * B := by
    have l0 := codeW_le d B hB v _ 0 (hi 0)
    have l1 := codeW_le d B hB v _ 1 (hi 1)
    have l2 := codeW_le d B hB v _ 2 (hi 2)
    have l3 := codeW_le d B hB v _ 3 (hi 3)
    have lh : d.hd.length ≤ B := by have := hB.hd; simp [frItems, FrontTWKit.frame_length] at this; omega
    simp only [o2, List.length_append, Streaming.marks_length]; omega
  have s3 := tailT cap src d hd B hB h o2 v c hs hBIG two hX.1 (fun h2 => (hY h2).1) hcapB (by omega)
  have s4 := flagsT cap src d hd B hB h (o2 ++ marks (natWord (if two then 2 else 1)) ++ marks (d.crs.getD (v rX) []) ++
    (if two then marks (d.crs.getD (v rY) []) else []) ++ marks d.tl ++ [false]) v c hs hBIG pat two hi hX.2
    (fun h2 => (hY h2).2) hcapB hok
  have e : o2 ++ marks (natWord (if two then 2 else 1)) ++ marks (d.crs.getD (v rX) []) ++
      (if two then marks (d.crs.getD (v rY) []) else []) ++ marks d.tl ++ [false] =
      o ++ entryW kd (negBit κn v) (v rMAG) (callWordW d v pat two) := by
    simp only [o2, o1, entryW, callWordW, frame_eq_marks]
    cases two <;> simp [List.append_assoc]
  rw [e] at s3 s4
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_
  unfold emitCost
  nlinarith

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
