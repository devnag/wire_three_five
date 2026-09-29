import Proof.Wire_3_5.FinalPass.ThrPtTSt

/-! # S2 (THR per point), part 15: one digit of the reports (P3:2596-2629)

At digit `D` of row `(g, p)`: the population of `Z⁺` (`popW true`), its report (`repM`), the report written in unary
on the reports' stream (`writeU`), then the same for `Z⁻`, and the digit counted. **`digBody_spec`**: from a working
state with the row word, the corner word, a population stream of `2M + 1` cells ending in `false`, a blank compared
state and the reports so far `A` followed by blanks (head at `|A|`), the reports' stream becomes
`A ++ 1^{t⁺} 0 1^{t⁻} 0` + blanks, with `t^± = reportRef (popZ ± D as X)` (the digit lists' reports at the point).
`BaseOK`: the base state's facts every stage needs (heads `0`, the constant and scratch registers).
Paper quantity: the reports `t_d^± = report(Z_d^±)` of row `(g, p)` (row:thr-reported, P3:2615-2629). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

/-- **The base state's facts**: every head at `0`; RowW's constants `a`, `τ₀`, `0` in `5`, `8`, `9`, its scratch
`10 … 52` zero; the population builder's `M` in `63`, its scratch `54 … 62` zero; the report machine's, stage 8's
and stage 2's registers zero; the cell `false`. -/
structure BaseOK (σB : WState 16 118) (a τ M : ℕ) : Prop where
  sh : ∀ j, σB.sh j = 0
  vA : σB.val 5 = a
  vT : σB.val 8 = τ
  vO : σB.val 9 = 0
  rowZ : ∀ q : Fin 118, 10 ≤ q.val → q.val ≤ 52 → σB.val q = 0
  vM : σB.val 63 = M
  popZ : ∀ q : Fin 118, 54 ≤ q.val → q.val ≤ 62 → σB.val q = 0
  stZ : ∀ q : Fin 118, 64 ≤ q.val → q.val ≤ 108 → σB.val q = 0
  cell : σB.cell = false

variable (cap : ℕ)

/-- Write register `82`'s report as `1^t 0` on the reports' stream (head counter `112`, spare `114`). -/
def writeRep : TProg := writeU.liftW (fsU 16) (frU 112 82 114)

/-- **One digit**: `Z⁺`, its report written; `Z⁻`, its report written; the digit counted. -/
def digBody : TProg :=
  .seq ((popW true).liftW fsP frP) (.seq (repM.liftW fsM frM) (.seq writeRep
    (.seq ((popW false).liftW fsP frP) (.seq (repM.liftW fsM frM) (.seq writeRep (.inc 53))))))

theorem tw_setc (σB : WState 16 118) (t : TSt) : (t.w σB).setc false = t.w σB := rfl

theorem frame_len (Z : List Bool) : frame Z = frameP Z ++ [false] := frame_eq_frameP Z

theorem other63 (σB : WState 16 118) (t : TSt) : (t.w σB).val 63 = σB.val 63 :=
  tw_val_other σB t 63 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem otherPop (σB : WState 16 118) (t : TSt) (q : Fin 118) (h1 : 54 ≤ q.val) (h2 : q.val ≤ 62) :
    (t.w σB).val q = σB.val q :=
  tw_val_other σB t q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem otherRep (σB : WState 16 118) (t : TSt) (q : Fin 118) (h1 : 64 ≤ q.val) (h2 : q.val ≤ 89)
    (h82 : q.val ≠ 82) : (t.w σB).val q = σB.val q :=
  tw_val_other σB t q (by omega) (by omega) (by omega) (by omega) h82 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The population of one sign on the working state. -/
theorem signPop_spec (sgn : Bool) (σB : WState 16 118) (a τ M : ℕ) (hB : BaseOK σB a τ M)
    (p r0 D A0 : ℕ) (as : List ℕ) (X restR restX zr0 : List Bool) (t : TSt)
    (hrw : t.rw = ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ restR)
    (hx : t.x = frameP X ++ restX) (hXl : X.length = 4 * as.length) (hz : t.z = zr0 ++ [false])
    (hzr : zr0.length = 2 * as.length) (hA0 : ∀ a ∈ as, a ≤ A0) (hMl : as.length = M)
    (hhRw : t.hRw = 0) (hd : t.d = D) (hc1 : popCap p r0 as.length A0 D ≤ cap) :
    WExec cap ((popW sgn).liftW fsP frP) (t.w σB) ({ t with z := frame (popZ sgn D as X) }.w σB)
      (popCost p r0 as.length A0 D) := by
  have e1 := popWL_spec cap sgn p r0 D A0 as X restR restX zr0 (t.w σB) (by rw [tw_st_rw, hrw]) (by rw [tw_st_x, hx])
    hXl (by rw [tw_st_z, hz]) hzr hA0 (by rw [tw_sh_hRw, hhRw])
    (by rw [tw_sh_other σB t 12 (by decide) (by decide) (by decide), hB.sh])
    (by rw [tw_sh_other σB t 14 (by decide) (by decide) (by decide), hB.sh]) (by rw [tw_val_d, hd])
    (by rw [other63, hB.vM, hMl]) (fun q h1 h2 => by rw [otherPop σB t q h1 h2]; exact hB.popZ q h1 h2) hc1
  rwa [tw_sets_z] at e1

/-- The report of the population on the working state. -/
theorem signRep_spec (σB : WState 16 118) (a τ M : ℕ) (hB : BaseOK σB a τ M)
    (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (hT5 : σB.st 9 = ListEval.levelWord DM DJ DW row)
    (Z : List Bool) (hZl : Z.length = M) (kS : ℕ) (t : TSt) (hz : t.z = frame Z)
    (hss : t.ss = List.replicate kS false) (hr : t.r82 = 0)
    (hrows : ∀ j ≤ DJ, (row j).length = M) (hc2 : ListEval.capOf DM DJ DW row M ≤ cap) :
    WExec cap (repM.liftW fsM frM) (t.w σB)
      ({ t with
        ss := List.replicate DM false ++ List.replicate (kS - DM) false,
        r82 := ListEval.reportRef DM DJ DW row Z }.w σB) (repCost DM (ListEval.capOf DM DJ DW row Z.length)) := by
  have e2 := repML_spec cap DM DJ DW row Z (fun j hj => by rw [hrows j hj, hZl]) (by rw [hZl]; exact hc2) kS (t.w σB)
    (fun q => by rw [tw_st_z, hz]) (by rw [tw_st_other σB t 9 (by decide), hT5]) (by rw [tw_st_ss, hss])
    (by rw [tw_sh_other σB t 14 (by decide) (by decide) (by decide), hB.sh])
    (by rw [tw_sh_other σB t 9 (by decide) (by decide) (by decide), hB.sh])
    (by rw [tw_sh_other σB t 15 (by decide) (by decide) (by decide), hB.sh])
    (by rw [tw_sh_other σB t 4 (by decide) (by decide) (by decide), hB.sh])
    (fun q h1 h2 => by
      by_cases hq : q = 82
      · subst hq; rw [tw_val_r82]; exact hr
      · have hq' : q.val ≠ 82 := fun e => hq (Fin.ext e)
        rw [otherRep σB t q h1 h2 hq']
        exact hB.stZ q h1 (by omega))
  rwa [tw_sets_ss, tw_setv_r82, tw_setc] at e2

/-- The report written on the reports' stream. -/
theorem signWr_spec (σB : WState 16 118) (A Bf : List Bool) (n : ℕ) (t : TSt) (hrep : t.rep = A ++ Bf)
    (hhRep : t.hRep = A.length) (hr : t.r82 = n) (hrH : t.rH = A.length) (hc3 : A.length + n + 1 ≤ cap) :
    WExec cap writeRep (t.w σB)
      ({ t with
        rep := A ++ ListEval.unary n ++ Bf.drop (n + 1), hRep := A.length + n + 1, rH := A.length + n + 1,
        r82 := 0 }.w σB) (11 * n + 1 + 1 + 7) := by
  have e3 := writeUL_spec cap 16 112 82 114 (by decide) (by decide) (by decide) A Bf n (t.w σB)
    (by rw [tw_st_rep, hrep]) (by rw [tw_sh_hRep, hhRep]) (by rw [tw_val_r82, hr]) (by rw [tw_val_rH, hrH]; exact hc3)
  unfold ustOut at e3
  rw [tw_sets_rep, tw_seth_hRep, tw_setv_rH, tw_setv_r82, tw_setv_kS] at e3
  refine WExec.cast cap e3 (tw_eq ?_) le_rfl
  simp only [tw_sh_hRep, tw_val_rH, tw_val_kS]
  obtain ⟨⟩ := t
  simp only at hhRep hrH hr ⊢
  simp only [TSt.mk.injEq, true_and, and_true]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
