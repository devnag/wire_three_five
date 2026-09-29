import Proof.Wire_3_5.FinalPass.ThrPtTape
import Proof.Wire_3_5.FinalPass.ThrPtLayC

/-! # S2 (THR per point), part 13: the unary writers and erasers on the evaluator's layout

The one-stream pieces (`eraseU`, `writeU`, `blankR`) lifted exactly onto any stream `X` of the evaluator's layout,
with a head counter `c`, a value register `r` and a count register `k` (distinct): **`eraseUL_spec`**,
**`writeUL_spec`**, **`blankRL_spec`** (the stream, its head and the three registers written out; nothing else moves).
Paper quantity: none beyond the machine model (the reports' word and the loop-safe scratch). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The one-stream piece's stream on the layout. -/
def fsU (X : Fin 17) : Fin 1 → Fin 17 := fun _ => X

/-- The one-stream piece's registers on the layout. -/
def frU (c r k : Fin 118) : Fin 3 → Fin 118 := ![c, r, k]

theorem fsU_inj (X : Fin 17) : Function.Injective (fsU X) := fun a b _ => Subsingleton.elim a b

theorem frU_inj (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) : Function.Injective (frU c r k) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [frU]

/-- The one-stream record read off the layout. -/
def toU (ω : WState 16 118) (X : Fin 17) (c r k : Fin 118) : USt :=
  ⟨ω.st X, ω.sh X, ω.val c, ω.val r, ω.val k, ω.cell⟩

theorem liftU (ω : WState 16 118) (X : Fin 17) (c r k : Fin 118) : LiftW (fsU X) (frU c r k) ω (toU ω X c r k).w :=
  ⟨fun i => by fin_cases i; rfl, fun i => by fin_cases i; rfl, fun q => by fin_cases q <;> rfl, rfl⟩

theorem u_upd (u : USt) (s : List Bool) (h c r k : ℕ) :
    ({ u with s := s, h := h, c := c, r := r, k := k } : USt).w = ((((u.w.sets 0 s).seth 0 h).setv 0 c).setv 1 r).setv 2 k := by
  apply WState.eq
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i; rfl
  · funext q; fin_cases q <;> rfl
  · rfl

/-- The layout after a one-stream piece: the stream, its head and the three registers written. -/
def ustOut (ω : WState 16 118) (X : Fin 17) (c r k : Fin 118) (s : List Bool) (h c' r' k' : ℕ) : WState 16 118 :=
  ((((ω.sets X s).seth X h).setv c c').setv r r').setv k k'

theorem liftU_upd (cap : ℕ) (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k)
    {P : UProg} (ω : WState 16 118) (s : List Bool) (h c' r' k' n : ℕ)
    (e : WExec cap P (toU ω X c r k).w ({ toU ω X c r k with s := s, h := h, c := c', r := r', k := k' } : USt).w n) :
    WExec cap (P.liftW (fsU X) (frU c r k)) ω (ustOut ω X c r k s h c' r' k') n := by
  rw [u_upd (toU ω X c r k) s h c' r' k'] at e
  have e2 := WExec.liftW_upd cap (fsU_inj X) (frU_inj c r k hcr hck hrk) e ω (liftU ω X c r k)
  rw [updW_setv (fsU_inj X) (frU_inj c r k hcr hck hrk), updW_setv (fsU_inj X) (frU_inj c r k hcr hck hrk),
    updW_setv (fsU_inj X) (frU_inj c r k hcr hck hrk), updW_seth (fsU_inj X) (frU_inj c r k hcr hck hrk),
    updW_sets (fsU_inj X) (frU_inj c r k hcr hck hrk), updW_self (fsU_inj X) (frU_inj c r k hcr hck hrk)
    (liftU ω X c r k)] at e2
  exact e2

variable (cap : ℕ)

theorem eraseUL_spec (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) (A B : List Bool)
    (n : ℕ) (ω : WState 16 118) (hs : ω.st X = A ++ (ListEval.unary n ++ B)) (hh : ω.sh X = A.length)
    (hc : ω.val c + n + 1 ≤ cap) :
    WExec cap (eraseU.liftW (fsU X) (frU c r k)) ω
      (ustOut ω X c r k (A ++ List.replicate (n + 1) false ++ B) (ω.sh X + n + 1) (ω.val c + n + 1) (ω.val r)
        (ω.val k)) (9 * n + 1 + 1 + 7) :=
  liftU_upd cap X c r k hcr hck hrk ω _ _ _ _ _ _ (eraseU_spec cap A B n (toU ω X c r k) hs hh hc)

theorem writeUL_spec (X : Fin 17) (c r k : Fin 118) (hcr : c ≠ r) (hck : c ≠ k) (hrk : r ≠ k) (A B : List Bool)
    (n : ℕ) (ω : WState 16 118) (hs : ω.st X = A ++ B) (hh : ω.sh X = A.length) (hr : ω.val r = n)
    (hc : ω.val c + n + 1 ≤ cap) :
    WExec cap (writeU.liftW (fsU X) (frU c r k)) ω
      (ustOut ω X c r k (A ++ ListEval.unary n ++ B.drop (n + 1)) (ω.sh X + n + 1) (ω.val c + n + 1) 0 (ω.val k))
      (11 * n + 1 + 1 + 7) :=
  liftU_upd cap X c r k hcr hck hrk ω _ _ _ _ _ _ (writeU_spec cap A B n (toU ω X c r k) hs hh hr hc)

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
