import Proof.Wire_3_5.FinalPass.ThrPtLay
import Proof.Wire_3_5.FinalPass.CornerEval
import Proof.Wire_3_5.FinalPass.RowFinal

/-! # S2 (THR per point), part 10: stage 2 and the row word, lifted exactly (P3:1645-1650, 2587-2630)

On the evaluator's layout (`TProg`): **`cwL_spec`** (stage 2, C5's corner-word writer `cw`, verified: the corner
word of the tuple's gates on stream `12`, the accumulators `10`, `11` re-formatted in place) and **`rowWL_spec`**
(the RowW, verified: the row word `rowWord p r₀ as ws` of row `(g, p)` on stream `13`, from a blank stream of any
length — `wexec_pad` transports RowW's spec at `[]` exactly). Paper quantities: the occurrences' corner word at the
point (`occCorners`), the row's residue, reduced coefficients and digit weights. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-! ## Stage 2, lifted -/

/-- Stage 2's streams: the gate table, the point, the accumulators, the corner word. -/
def fsC : Fin 7 → Fin 17 := ![3, 0, 1, 2, 10, 11, 12]

/-- Stage 2's registers: `102 … 108`. -/
def frC : Fin 7 → Fin 118 := fun k => ⟨102 + k.val, by omega⟩

theorem fsC_inj' : Function.Injective fsC := by decide

theorem frC_inj' : Function.Injective frC := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp only [frC] at this; omega)

/-- Stage 2's record read off the layout (its point and output heads `0`). -/
def toC (ω : WState 16 118) : Corner.CSt :=
  ⟨ω.st 3, ω.st 0, ω.st 1, ω.st 2, ω.st 10, ω.st 11, ω.st 12, ω.sh 3, 0, 0, ω.val 102, ω.val 104, ω.val 105,
    ω.val 106, ω.cell⟩

theorem liftC (ω : WState 16 118) (h0 : ω.sh 0 = 0) (h1 : ω.sh 1 = 0) (h2 : ω.sh 2 = 0) (h10 : ω.sh 10 = 0)
    (h11 : ω.sh 11 = 0) (h12 : ω.sh 12 = 0) (h103 : ω.val 103 = 0) (h107 : ω.val 107 = 0)
    (h108 : ω.val 108 = 0) : LiftW fsC frC ω (toC ω).w := by
  refine ⟨fun i => ?_, fun i => by fin_cases i <;> rfl, fun r => ?_, rfl⟩
  · fin_cases i
    · rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h10
    · exact h11
    · exact h12
  · fin_cases r
    · rfl
    · exact h103
    · rfl
    · rfl
    · rfl
    · exact h107
    · exact h108

variable (cap : ℕ)

theorem cwL_spec (h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) (c u v : NearCubicWires.BitInput n)
    (A B : ℕ) (restP restN rest restC restU restV r ys : List Bool) (ω : WState 16 118)
    (hG : ω.st 3 = Corner.gatesW h G ++ rest) (h3 : ω.sh 3 = 0)
    (hgh : G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ (ω.st 3).length)
    (hC : ω.st 0 = frameP (List.ofFn c) ++ false :: restC) (hU : ω.st 1 = frameP (List.ofFn u) ++ restU)
    (hV : ω.st 2 = frameP (List.ofFn v) ++ restV)
    (hp : ω.st 10 = frameP (binary h A) ++ false :: restP) (hn : ω.st 11 = frameP (binary h B) ++ false :: restN)
    (hout : ω.st 12 = ys ++ false :: r) (hys : ys.length = 8 * G.length)
    (h0 : ω.sh 0 = 0) (h1 : ω.sh 1 = 0) (h2 : ω.sh 2 = 0) (h10 : ω.sh 10 = 0) (h11 : ω.sh 11 = 0)
    (h12 : ω.sh 12 = 0) (hz : ∀ k : Fin 118, 102 ≤ k.val → k.val ≤ 108 → ω.val k = 0)
    (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap) (hK : G.length * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ cap)
    (ho : 8 * G.length ≤ cap)
    (hov : ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A' B' : ℕ, WExec cap (Corner.cw.liftW fsC frC) ω
      (((ω.sets 10 (frameP (binary h A') ++ false :: restP)).sets 11 (frameP (binary h B') ++ false :: restN)).sets 12
        (frameP (NearCubicWires.WireExponent3_5.FinalPass.Pop.cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r))
      (Corner.cwCost h n G.length) := by
  have hL := liftC ω h0 h1 h2 h10 h11 h12 (hz 103 (by decide) (by decide)) (hz 107 (by decide) (by decide))
    (hz 108 (by decide) (by decide))
  have hgh' : (toC ω).gh + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ (toC ω).gw.length := by
    show ω.sh 3 + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ (ω.st 3).length
    rw [h3]; omega
  obtain ⟨A', B', e⟩ := Corner.cw_spec cap h G c u v (toC ω) A B restP restN rest restC restU restV r ys
    (by show (ω.st 3).drop (ω.sh 3) = _; rw [h3, List.drop_zero, hG]) hgh'
    hC hU hV rfl hp hn hout hys rfl (hz 102 (by decide) (by decide)) (hz 104 (by decide) (by decide))
    (hz 105 (by decide) (by decide)) (hz 106 (by decide) (by decide)) hc hR hnc hK ho hov
  refine ⟨A', B', ?_⟩
  have hx : ({ toC ω with
      pos := frameP (binary h A') ++ false :: restP, neg := frameP (binary h B') ++ false :: restN,
      out := frameP (NearCubicWires.WireExponent3_5.FinalPass.Pop.cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r } :
        Corner.CSt).w =
      (((toC ω).w.sets 4 (frameP (binary h A') ++ false :: restP)).sets 5 (frameP (binary h B') ++ false :: restN)).sets
        6 (frameP (NearCubicWires.WireExponent3_5.FinalPass.Pop.cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r) := by
    cst_eq
  rw [hx] at e
  have e2 := WExec.liftW_upd cap fsC_inj' frC_inj' e ω hL
  rw [updW_sets fsC_inj' frC_inj', updW_sets fsC_inj' frC_inj', updW_sets fsC_inj' frC_inj',
    updW_self fsC_inj' frC_inj' hL] at e2
  exact e2

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
