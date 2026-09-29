import Proof.Wire_3_5.FinalPass.CornerEval
import Proof.Wire_3_5.FinalPass.LiftR

/-! # S3, part 1: the SYM per-point evaluator's layout and stage 2 in it (P3:3170-3178)

"Evaluate the reported lookups at the sampled pairs" (P3:3046-3048): at a sampled point, one SYM circuit's factor is
stage 8's test of the circuit's corner word (stage 2) and the amplified list's reports of its populations (stage 3,
the majority machine). The evaluator runs the stages on one word layout (`WM 13 32`): the gate tables (`sG`), the
center (`sC`), the error vectors (`sU`, `sV`), stage 2's accumulators (`sPos`, `sNeg`), the corner word (`sX`), the
population (`sZ`), the signs (`sSp`, `sSm`), the majority machine's streams (`sT5`, `sSS`, `sFT`), the top table
(`sTop`); registers `0 … 25` every stage's scratch, `26`/`27` the reports, `28` the factor, `29` the accumulator.
Here: stage 2 lifted (`cwS`), **`cwS_spec`**: the corner word `cornerWord (G.map eval) c u v` on `sX`, relationally
(every other stream, every head and register back, nothing else moves).

Paper quantity of the main type: the corner word of a gate list at a sampled point (stage 2, P3:1224). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop

/-! ## The layout -/

/-- The evaluator's programs and states. -/
abbrev SM := WM 13 32
abbrev SS := WState 13 32

scoped notation "sG" => (0 : Fin 14)
scoped notation "sC" => (1 : Fin 14)
scoped notation "sU" => (2 : Fin 14)
scoped notation "sV" => (3 : Fin 14)
scoped notation "sPos" => (4 : Fin 14)
scoped notation "sNeg" => (5 : Fin 14)
scoped notation "sX" => (6 : Fin 14)
scoped notation "sZ" => (7 : Fin 14)
scoped notation "sSp" => (8 : Fin 14)
scoped notation "sSm" => (9 : Fin 14)
scoped notation "sT5" => (10 : Fin 14)
scoped notation "sSS" => (11 : Fin 14)
scoped notation "sFT" => (12 : Fin 14)
scoped notation "sTop" => (13 : Fin 14)

/-! ## Stage 2 lifted -/

/-- Stage 2's streams: the first seven. -/
def fsC : Fin 7 → Fin 14 := fun i => Fin.castLE (by norm_num) i
/-- Stage 2's registers: the first seven. -/
def frC : Fin 7 → Fin 32 := fun i => Fin.castLE (by norm_num) i

theorem fsC_inj : Function.Injective fsC := fun a b h => Fin.castLE_injective _ h
theorem frC_inj : Function.Injective frC := fun a b h => Fin.castLE_injective _ h

/-- **Stage 2 on the evaluator's layout.** -/
def cwS : SM := cw.liftW fsC frC

theorem fsC_val (i : Fin 7) : (fsC i).val = i.val := rfl
theorem frC_val (i : Fin 7) : (frC i).val = i.val := rfl

theorem cwS_spec (cap h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) (c u v : BitInput n) (ω : SS) (A B : ℕ)
    (restP restN rest restC restU restV r ys : List Bool)
    (hG : (ω.st sG).drop (ω.sh sG) = gatesW h G ++ rest)
    (hgh : ω.sh sG + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ (ω.st sG).length)
    (hC : ω.st sC = frameP (List.ofFn c) ++ false :: restC) (hU : ω.st sU = frameP (List.ofFn u) ++ restU)
    (hV : ω.st sV = frameP (List.ofFn v) ++ restV)
    (hp : ω.st sPos = frameP (binary h A) ++ false :: restP) (hn : ω.st sNeg = frameP (binary h B) ++ false :: restN)
    (hout : ω.st sX = ys ++ false :: r) (hys : ys.length = 8 * G.length)
    (hsh : ∀ i : Fin 14, 1 ≤ i.val → i.val < 7 → ω.sh i = 0) (hr : ∀ i : Fin 32, i.val < 7 → ω.val i = 0)
    (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap) (hK : G.length * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ cap)
    (ho : 8 * G.length ≤ cap)
    (hov : ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ ω' A' B', WExec cap cwS ω ω' (cwCost h n G.length) ∧
      ω'.st sX = frameP (cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r ∧
      ω'.st sPos = frameP (binary h A') ++ false :: restP ∧ ω'.st sNeg = frameP (binary h B') ++ false :: restN ∧
      (∀ i : Fin 14, i ≠ sPos → i ≠ sNeg → i ≠ sX → ω'.st i = ω.st i) ∧ (∀ i, ω'.sh i = ω.sh i) ∧
      (∀ q, ω'.val q = ω.val q) ∧ ω'.cell = ω.cell := by
  let x : CSt := ⟨ω.st 0, ω.st 1, ω.st 2, ω.st 3, ω.st 4, ω.st 5, ω.st 6, ω.sh 0, 0, 0, 0, 0, 0, 0, ω.cell⟩
  have hL : LiftW fsC frC ω x.w := by
    refine ⟨fun i => ?_, fun i => ?_, fun q => ?_, rfl⟩
    · fin_cases i
      · rfl
      all_goals (simp only [CSt.w, x]; exact hsh _ (by decide) (by decide))
    · fin_cases i <;> rfl
    · fin_cases q <;> (simp only [CSt.w, x]; exact hr _ (by decide))
  obtain ⟨A', B', hcw⟩ := cw_spec cap h G c u v x A B restP restN rest restC restU restV r ys hG hgh hC hU hV rfl
    hp hn hout hys rfl rfl rfl rfl rfl hc hR hnc hK ho hov
  obtain ⟨ω', e, hL', hO'⟩ := WExec.liftW cap cap le_rfl fsC fsC_inj frC frC_inj hcw ω hL
  have hin : ∀ i : Fin 14, i.val < 7 → ∃ j : Fin 7, fsC j = i := fun i hi => ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  have hout' : ∀ i : Fin 14, 7 ≤ i.val → ∀ j : Fin 7, fsC j ≠ i := fun i hi j e => by
    have := congrArg Fin.val e; rw [fsC_val] at this; have := j.isLt; omega
  have hinr : ∀ q : Fin 32, q.val < 7 → ∃ j : Fin 7, frC j = q := fun q hq => ⟨⟨q.val, hq⟩, Fin.ext rfl⟩
  have houtr : ∀ q : Fin 32, 7 ≤ q.val → ∀ j : Fin 7, frC j ≠ q := fun q hq j e => by
    have := congrArg Fin.val e; rw [frC_val] at this; have := j.isLt; omega
  refine ⟨ω', A', B', e, ?_, ?_, ?_, fun i i1 i2 i3 => ?_, fun i => ?_, fun q => ?_, ?_⟩
  · exact hL'.st 6
  · exact hL'.st 4
  · exact hL'.st 5
  · by_cases hi : i.val < 4
    · have e1 := hL'.st ⟨i.val, by omega⟩
      have e2 : fsC ⟨i.val, by omega⟩ = i := Fin.ext rfl
      rw [e2] at e1
      rw [e1]
      obtain ⟨k, hk⟩ := i
      simp only at hi
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rfl
    · by_cases hi7 : i.val < 7
      · exfalso
        have : i = 4 ∨ i = 5 ∨ i = 6 := by
          rcases i with ⟨k, hk⟩
          simp only [Fin.ext_iff] at hi hi7 ⊢
          omega
        rcases this with rfl | rfl | rfl
        · exact i1 rfl
        · exact i2 rfl
        · exact i3 rfl
      · exact (hO'.1 i (hout' i (by omega))).2
  · by_cases hi : i.val < 7
    · obtain ⟨j, rfl⟩ := hin i hi
      rw [hL'.sh j, hL.sh j]
      rfl
    · exact (hO'.1 i (hout' i (by omega))).1
  · by_cases hq : q.val < 7
    · obtain ⟨j, rfl⟩ := hinr q hq
      rw [hL'.val j, hL.val j]
      rfl
    · exact hO'.2 q (houtr q (by omega))
  · rw [hL'.cell]
    rfl

end NearCubicWires.WireExponent3_5.PrimT.S3
