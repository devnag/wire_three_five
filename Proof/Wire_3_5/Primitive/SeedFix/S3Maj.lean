import Proof.Wire_3_5.Primitive.SeedFix.S3Lay
import Proof.Wire_3_5.FinalPass.MajMain

/-! # S3, part 2: the majority machine on the evaluator's layout (P3:1512-1520, 3170-3178)

"The amplified list's report" (list:flatten, P3:1512-1520): C5's majority machine `majM` (`majM_spec`)
reads the framed population `Z` (on `sZ`), a stage-5 template (`sT5`), a blank compared state (`sSS`) and the list
seed's flat table (`sFT`), and leaves the report `flatReportFast P e Z` in its register `18`. Lifted to the
evaluator's layout (streams `sZ, sT5, sSS, sFT`, registers `0 … 25`): **`majS_spec`**, relationally (the population and
the flat table kept, the template holding rows of the same length, the compared state blank, every other register
of `0 … 25` back at `0`, nothing outside moves).

Paper quantity of the main type: the amplified list's report `flatReportFast P e Z`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Flat

/-- The majority machine's streams: the population, the template, the compared state, the flat table. -/
def fsM : Fin 4 → Fin 14 := ![7, 10, 11, 12]
/-- The majority machine's registers: the first twenty-six. -/
def frM : Fin 26 → Fin 32 := fun i => Fin.castLE (by norm_num) i

theorem fsM_inj : Function.Injective fsM := by decide
theorem frM_inj : Function.Injective frM := fun a b h => Fin.castLE_injective _ h

/-- **The majority machine on the evaluator's layout.** -/
def majS : SM := Maj.majM.liftW fsM frM

theorem mst_val_zero (pt t5 ss ft : List Bool) (c : Bool) (r : Fin 26) :
    (⟨pt, t5, 0, ss, 0, ft, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c⟩ : Maj.MSt).w.val r = 0 := by
  fin_cases r <;> rfl

theorem majS_spec (cap : ℕ) (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (Z : List Bool) (hZ : Z.length = L)
    (hc : Maj.MajCap P e L cap) (rowsT : ℕ → List Bool) (hrows : ∀ j ≤ P.base.J, (rowsT j).length = L) (k : ℕ)
    (ω : SS) (hpt : ω.st sZ = frame Z) (ht5 : ω.st sT5 = levelWord P.M P.base.J P.base.W rowsT)
    (hss : ω.st sSS = List.replicate k false) (hft : ω.st sFT = flatTable P e L)
    (hsh : ω.sh sZ = 0 ∧ ω.sh sT5 = 0 ∧ ω.sh sSS = 0 ∧ ω.sh sFT = 0) (hr : ∀ q : Fin 32, q.val < 26 → ω.val q = 0) :
    ∃ ω' n, n ≤ Maj.majBound P e L ∧ WExec cap majS ω ω' n ∧ ω'.val 18 = flatReportFast P e Z ∧
      (∀ q : Fin 32, q.val < 26 → q ≠ 18 → ω'.val q = 0) ∧ ω'.st sZ = ω.st sZ ∧ ω'.st sFT = ω.st sFT ∧
      ω'.st sSS = List.replicate P.M false ++ List.replicate (k - P.M) false ∧
      (∃ rowsF : ℕ → List Bool, (∀ j ≤ P.base.J, (rowsF j).length = L) ∧
        ω'.st sT5 = levelWord P.M P.base.J P.base.W rowsF) ∧
      ω'.sh sZ = 0 ∧ ω'.sh sT5 = 0 ∧ ω'.sh sSS = 0 ∧ ω'.sh sFT = 0 ∧
      (∀ i : Fin 14, i ≠ sZ → i ≠ sT5 → i ≠ sSS → i ≠ sFT → ω'.st i = ω.st i ∧ ω'.sh i = ω.sh i) ∧
      (∀ q : Fin 32, 26 ≤ q.val → ω'.val q = ω.val q) := by
  obtain ⟨h1, h2, h3, h4⟩ := hsh
  let x : Maj.MSt := ⟨ω.st 7, ω.st 10, 0, ω.st 11, 0, ω.st 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ω.cell⟩
  have hL : LiftW fsM frM ω x.w := by
    refine ⟨fun i => ?_, fun i => ?_, fun q => ?_, rfl⟩
    · fin_cases i
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · fin_cases i <;> rfl
    · rw [mst_val_zero]
      exact hr _ q.isLt
  obtain ⟨rowsF, b, n, hn, hrF, hm⟩ := Maj.majM_spec cap P e L Z hZ hc rowsT hrows k x hpt ht5 rfl hss rfl hft rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨ω', e', hL', hO'⟩ := WExec.liftW cap cap le_rfl fsM fsM_inj frM frM_inj hm ω hL
  have hno : ∀ i : Fin 14, i ≠ sZ → i ≠ sT5 → i ≠ sSS → i ≠ sFT → ∀ j : Fin 4, fsM j ≠ i := by
    intro i i1 i2 i3 i4 j
    fin_cases j
    · exact fun e => i1 e.symm
    · exact fun e => i2 e.symm
    · exact fun e => i3 e.symm
    · exact fun e => i4 e.symm
  have hnr : ∀ q : Fin 32, 26 ≤ q.val → ∀ j : Fin 26, frM j ≠ q := fun q hq j e => by
    have := congrArg Fin.val e; simp only [frM, Fin.val_castLE] at this; have := j.isLt; omega
  refine ⟨ω', n, hn, e', ?_, fun q hq h18 => ?_, ?_, ?_, ?_, ⟨rowsF, hrF, ?_⟩, ?_, ?_, ?_, ?_,
    fun i i1 i2 i3 i4 => ?_, fun q hq => ?_⟩
  · exact hL'.val 18
  · have e1 := hL'.val ⟨q.val, hq⟩
    have e2 : frM ⟨q.val, hq⟩ = q := Fin.ext rfl
    rw [e2] at e1
    rw [e1]
    obtain ⟨k0, hk0⟩ := q
    have h18' : k0 ≠ 18 := fun e => h18 (Fin.ext e)
    simp only at hq
    interval_cases k0 <;> first | rfl | exact absurd rfl h18'
  · exact hL'.st 0
  · exact hL'.st 3
  · exact hL'.st 2
  · exact hL'.st 1
  · exact hL'.sh 0
  · exact hL'.sh 1
  · exact hL'.sh 2
  · exact hL'.sh 3
  · exact ⟨(hO'.1 i (hno i i1 i2 i3 i4)).2, (hO'.1 i (hno i i1 i2 i3 i4)).1⟩
  · exact hO'.2 q (hnr q hq)

end NearCubicWires.WireExponent3_5.PrimT.S3
