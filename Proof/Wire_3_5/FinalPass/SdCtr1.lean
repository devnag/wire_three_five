import Proof.Wire_3_5.FinalPass.SdCnt
import Proof.Wire_3_5.Primitive.SeedFix.CtrLift

/-! # S4 (the seeds phase), part 10: the center loop's pieces on the body's layout (P3:1206-1216)

On the body's layout: the one-stream pieces run exactly on a stream with three registers (**`liftUB`**); the table
position counters `row` on `tRow` (`bst 25`, registers `197 … 199`, flag `fR = 198`) and `col` on `tCol` (`bst 26`,
registers `194 … 196`, flag `fC = 195`): **`cnt_inc`**, **`cnt_max`**, **`cnt_rst`**; the center writer on the offset
(word `0`), `tRow`, `tCol` and the center `tC`, registers `168 … 193` (**`ctrB_spec`**); `tI` rewound by its counter
(**`rewI_spec`**).

Paper quantity of the main type: the cell center at table position `(row, col)` (P3:1206-1209), on the body. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.ThrPt (USt UProg)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)
open NearCubicWires.WireExponent3_5.Shared

section Lay
variable {nw nn nsc nrs : ℕ}

/-! ## One-stream pieces on the body -/

def fsU1 (X : Fin (bns nw nsc + 1)) (_ : Fin 1) : Fin (bns nw nsc + 1) := X

def frU1 (c r k : Fin (bnr nn nrs)) : Fin 3 → Fin (bnr nn nrs) := ![c, r, k]

theorem fsU1_inj (X : Fin (bns nw nsc + 1)) : Function.Injective (fsU1 X) := fun a b _ => Subsingleton.elim a b

theorem frU1_inj (c r k : Fin (bnr nn nrs)) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) :
    Function.Injective (frU1 c r k) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frU1]

/-- The one-stream record read off the body. -/
def toUB (ω : BS nw nn nsc nrs) (X : Fin (bns nw nsc + 1)) (c r k : Fin (bnr nn nrs)) : USt :=
  ⟨ω.st X, ω.sh X, ω.val c, ω.val r, ω.val k, ω.cell⟩

theorem liftUB_view (ω : BS nw nn nsc nrs) (X : Fin (bns nw nsc + 1)) (c r k : Fin (bnr nn nrs)) :
    LiftW (fsU1 X) (frU1 c r k) ω (toUB ω X c r k).w :=
  ⟨fun i => by fin_cases i; rfl, fun i => by fin_cases i; rfl, fun q => by fin_cases q <;> rfl, rfl⟩

/-- The body after a one-stream piece. -/
def uOut (ω : BS nw nn nsc nrs) (X : Fin (bns nw nsc + 1)) (c r k : Fin (bnr nn nrs)) (s : List Bool)
    (h c' r' k' : ℕ) : BS nw nn nsc nrs :=
  ((((ω.sets X s).seth X h).setv c c').setv r r').setv k k'

theorem liftUB (cap : ℕ) (X : Fin (bns nw nsc + 1)) (c r k : Fin (bnr nn nrs)) (hcr : c ≠ r) (hck : c ≠ k)
    (hrk : r ≠ k) {P : UProg} (ω : BS nw nn nsc nrs) (s : List Bool) (h c' r' k' n : ℕ)
    (e : WExec cap P (toUB ω X c r k).w ({ toUB ω X c r k with s := s, h := h, c := c', r := r', k := k' } : USt).w
      n) :
    WExec cap (P.liftW (fsU1 X) (frU1 c r k)) ω (uOut ω X c r k s h c' r' k') n := by
  rw [ThrPt.u_upd (toUB ω X c r k) s h c' r' k'] at e
  have hi := frU1_inj c r k hcr hck hrk
  have e2 := ThrPt.WExec.liftW_upd cap (fsU1_inj X) hi e ω (liftUB_view ω X c r k)
  rw [ThrPt.updW_setv (fsU1_inj X) hi, ThrPt.updW_setv (fsU1_inj X) hi, ThrPt.updW_setv (fsU1_inj X) hi,
    ThrPt.updW_seth (fsU1_inj X) hi, ThrPt.updW_sets (fsU1_inj X) hi,
    ThrPt.updW_self (fsU1_inj X) hi (liftUB_view ω X c r k)] at e2
  exact e2

theorem upd_back {α β : Type} [DecidableEq α] (f : α → β) (a b : α) (v : β) (h : a ≠ b) :
    Function.update (Function.update f a v) b (f b) = Function.update f a v := by
  rw [Function.update_comm h, Function.update_eq_self]

/-! ## The table position counters -/

def tRow : Fin (bns nw nsc + 1) := bst 25 (by omega)
def tCol : Fin (bns nw nsc + 1) := bst 26 (by omega)

/-- A counter's registers: position `c`, flag `r`, spare `k`. -/
def cC (row : Bool) : Fin (bnr nn nrs) := brg (if row then 197 else 194) (by split <;> omega)
def cF (row : Bool) : Fin (bnr nn nrs) := brg (if row then 198 else 195) (by split <;> omega)
def cK (row : Bool) : Fin (bnr nn nrs) := brg (if row then 199 else 196) (by split <;> omega)

/-- A counter's stream. -/
def cT (row : Bool) : Fin (bns nw nsc + 1) := bst (if row then 25 else 26) (by split <;> omega)

theorem cCF (row : Bool) : (cC row : Fin (bnr nn nrs)) ≠ cF row := by
  simp only [cC, cF]; apply brg_ne; split <;> omega
theorem cCK (row : Bool) : (cC row : Fin (bnr nn nrs)) ≠ cK row := by
  simp only [cC, cK]; apply brg_ne; split <;> omega
theorem cFK (row : Bool) : (cF row : Fin (bnr nn nrs)) ≠ cK row := by
  simp only [cF, cK]; apply brg_ne; split <;> omega

/-- The counter's increment, all-ones test and reset on the body. -/
def cntInc (row : Bool) : BP nw nn nsc nrs := Sd.incB.liftW (fsU1 (cT row)) (frU1 (cC row) (cF row) (cK row))
def cntMax (row : Bool) : BP nw nn nsc nrs := maxB.liftW (fsU1 (cT row)) (frU1 (cC row) (cF row) (cK row))
def cntRst (row : Bool) : BP nw nn nsc nrs := resetB.liftW (fsU1 (cT row)) (frU1 (cC row) (cF row) (cK row))

theorem cnt_inc (cap : ℕ) (row : Bool) (d x T : ℕ) (hx : x + 1 < 2 ^ d) (hT : x + 1 < 2 ^ T) (ω : BS nw nn nsc nrs)
    (hs : ω.st (cT row) = frame (binary d x)) (hh : ω.sh (cT row) = 0) (hc : ω.val (cC row) = 0)
    (hcap : 2 * T + 2 < cap) :
    WExec cap (cntInc row) ω (ω.sets (cT row) (frame (binary d (x + 1)))) (incCost T) := by
  have e := Sd.incB_spec cap d T x hx hT [] (toUB ω (cT row) (cC row) (cF row) (cK row))
    (by show ω.st (cT row) = _; rw [hs, frame_eq_frameP]) hh hc hcap
  have e2 := liftUB cap (cT row) (cC row) (cF row) (cK row) (cCF row) (cCK row) (cFK row) ω
    (frameP (binary d (x + 1)) ++ false :: []) (ω.sh (cT row)) (ω.val (cC row)) (ω.val (cF row)) (ω.val (cK row))
    (incCost T) e
  refine WExec.cast cap e2 ?_ le_rfl
  apply WState.eq
  · simp only [uOut, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_eq_self]
  · simp only [uOut, WState.setv_st, WState.seth_st, WState.sets_st, frame_eq_frameP]
  · simp only [uOut, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_eq_self]
  · rfl

theorem cnt_max (cap : ℕ) (row : Bool) (d x : ℕ) (hx : x < 2 ^ d) (ω : BS nw nn nsc nrs)
    (hs : ω.st (cT row) = frame (binary d x)) (hh : ω.sh (cT row) = 0) (hc : ω.val (cC row) = 0)
    (hr : ω.val (cF row) = 0) (hcap : 2 * d + 1 ≤ cap) :
    WExec cap (cntMax row) ω (ω.setv (cF row) (if x + 1 = 2 ^ d then 0 else 1))
      (d * 20 + 1 + 1 + (5 * (2 * d) + 1)) := by
  have e := maxB_spec cap d x hx [] (toUB ω (cT row) (cC row) (cF row) (cK row))
    (by show ω.st (cT row) = _; rw [hs, frame_eq_frameP]) hh hc hr hcap
  have e2 := liftUB cap (cT row) (cC row) (cF row) (cK row) (cCF row) (cCK row) (cFK row) ω
    (ω.st (cT row)) (ω.sh (cT row)) (ω.val (cC row)) (if x + 1 = 2 ^ d then 0 else 1) (ω.val (cK row)) _ e
  refine WExec.cast cap e2 ?_ le_rfl
  apply WState.eq
  · simp only [uOut, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_eq_self]
  · simp only [uOut, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_eq_self]
  · simp only [uOut, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_eq_self]
    exact upd_back _ _ _ _ (cFK row)
  · rfl

theorem cnt_rst (cap : ℕ) (row : Bool) (d x : ℕ) (ω : BS nw nn nsc nrs)
    (hs : ω.st (cT row) = frame (binary d x)) (hh : ω.sh (cT row) = 0) (hc : ω.val (cC row) = 0)
    (hcap : 2 * d + 1 ≤ cap) :
    WExec cap (cntRst row) ω (ω.sets (cT row) (frame (binary d 0))) (d * 20 + 1 + 1 + (5 * (2 * d) + 1)) := by
  have e := resetB_spec cap d x [] (toUB ω (cT row) (cC row) (cF row) (cK row))
    (by show ω.st (cT row) = _; rw [hs, frame_eq_frameP]) hh hc hcap
  have e2 := liftUB cap (cT row) (cC row) (cF row) (cK row) (cCF row) (cCK row) (cFK row) ω
    (frameP (binary d 0) ++ false :: []) (ω.sh (cT row)) (ω.val (cC row)) (ω.val (cF row)) (ω.val (cK row)) _ e
  refine WExec.cast cap e2 ?_ le_rfl
  apply WState.eq
  · simp only [uOut, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_eq_self]
  · simp only [uOut, WState.setv_st, WState.seth_st, WState.sets_st, frame_eq_frameP]
  · simp only [uOut, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_eq_self]
  · rfl

/-! ## The center writer -/

/-- The center writer's streams: the offset (word `0`), `tRow`, `tCol`, the center `tC`. -/
def ctrSv : Fin 4 → ℕ := ![30, 25, 26, 1]

def ctrS (i : Fin 4) : Fin (bns nw nsc + 1) := bst (ctrSv i) (by fin_cases i <;> simp [ctrSv])

theorem ctrS_inj : Function.Injective (ctrS (nw := nw) (nsc := nsc)) := by
  intro a b h
  have e := congrArg Fin.val h
  simp only [ctrS, bst] at e
  revert e
  fin_cases a <;> fin_cases b <;> simp [ctrSv]

/-- The center writer's registers: `168 … 193`. -/
def ctrR : Fin 26 ↪ Fin (bnr nn nrs) :=
  ⟨fun q => brg (168 + q.val) (by have := q.isLt; omega), fun a b h => Fin.ext (by
    have e := congrArg Fin.val h
    simp only [brg] at e
    omega)⟩

/-- **The center writer on the body.** -/
def ctrB : BP nw nn nsc nrs := PrimT.Ctr.ctrW ctrS ctrR

theorem ctrB_spec (cap : ℕ) (P : StarParams) (σT : P.Translation) (row col : ℕ) (ω : BS nw nn nsc nrs)
    (hoff : ω.st (ctrS 0) = frameP (List.ofFn (offset P σT)) ++ [false])
    (hrow : ω.st tRow = frame (binary (dRow P) row)) (hcol : ω.st tCol = frame (binary (dR P) col))
    (hctr : (ω.st tC).length ≤ 2 * P.n + 1) (hsh : ∀ i, ω.sh (ctrS i) = 0)
    (hB : ω.val (ctrR 0) = P.b) (hs : ω.val (ctrR 1) = P.s) (hH : ω.val (ctrR 2) = P.r / 2)
    (hHL : ω.val (ctrR 3) = hL P) (hHR : ω.val (ctrR 4) = P.n - P.r * P.b - hL P)
    (hz : ∀ i : Fin 26, 5 ≤ i.val → ω.val (ctrR i) = 0) (hcap : 8 * (P.n + 2) ≤ cap) :
    ∃ ω', WExec cap ctrB ω ω' (PrimT.Ctr.ctrCost P) ∧
      ω'.st tC = frameP (List.ofFn (centerAt P σT row col)) ++ [false] ∧ (∀ i, i ≠ tC → ω'.st i = ω.st i) ∧
      ω'.sh = ω.sh ∧ ω'.val = ω.val ∧ ω'.cell = ω.cell := by
  obtain ⟨ω', e, hc, hh, hst, hv, hcell, hO⟩ := PrimT.Ctr.ctrW_spec cap P σT row col ctrS ctrS_inj ctrR ω hoff
    hrow hcol hctr hsh hB hs hH hHL hHR hz hcap
  have h3 : ctrS 3 = (tC : Fin (bns nw nsc + 1)) := rfl
  refine ⟨ω', e, hc, fun i hi => ?_, ?_, ?_, hcell⟩
  · by_cases hj : ∃ k, ctrS k = i
    · obtain ⟨k, rfl⟩ := hj
      exact hst k (fun h => hi (by rw [h, h3]))
    · exact (hO.1 i (fun k h => hj ⟨k, h⟩)).2
  · funext i
    by_cases hj : ∃ k, ctrS k = i
    · obtain ⟨k, rfl⟩ := hj
      rw [hh k, hsh k]
    · exact (hO.1 i (fun k h => hj ⟨k, h⟩)).1
  · funext q
    by_cases hj : ∃ r, ctrR r = q
    · obtain ⟨r, rfl⟩ := hj
      exact hv r
    · exact hO.2 q (fun r h => hj ⟨r, h⟩)

/-! ## The pairs' word rewound -/

/-- `tI` back to its start by stage 0's counter. -/
def rewI : BP nw nn nsc nrs := WM.rewind tI rgX

theorem rewI_spec (cap p : ℕ) (ω : BS nw nn nsc nrs) (hX : ω.val rgX = p) (hI : ω.sh tI = p) (hc : p ≤ cap) :
    WExec cap rewI ω ((ω.setv rgX 0).seth tI 0) (5 * p + 1) := by
  have e := wrewind_spec cap tI rgX p ω hX (by rw [hX]; exact hc)
  rwa [hI, Nat.sub_self] at e

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
