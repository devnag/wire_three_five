import Proof.Wire_3_5.FinalPass.ThrPtPopF
import Proof.Wire_3_5.FinalPass.ThrPtRep
import Proof.Wire_3_5.FinalPass.ThrPt8
import Proof.Wire_3_5.FinalPass.ThrPtLiftR

/-! # S2 (THR per point), part 9: the evaluator's layout and its stages lifted exactly (P3:3170-3178)

The THR per-point evaluator runs on one word layout `WM 16 118`: streams `0 … 2` the point `c, e_L(u), e_R(v)`,
`3` the tuple's gate table, `4 … 7` the payloads, `8` the primes, `9` stage 4's table (the call words), then the
scratch `10`/`11` stage 2's accumulators, `12` the corner word, `13` the row word, `14` the population, `15` the
compared state, `16` the reports; registers `0` the accumulator, `1 … 4` the numbers `a, |𝒢|, τ₀, |occs|`, `5 … 52`
RowW's, `53 … 63` the population builder's, `64 … 89` the report machine's, `90 … 101` stage 8's, `102 … 108`
stage 2's, `109 …` the loops'. Each stage's spec transports EXACTLY (`WExec.liftW_upd`, `RExec.liftR_upd`):
**`popWL_spec`** (the population stream becomes `frame (popZ …)`), **`repML_spec`** (the report in register `82`,
the compared state blank, the cell `false`), **`thr8L_spec`** (`[thrTermOk …]` in register `92`).
Paper quantities: the digit populations, their reports, the row's `R̂` at one point. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

/-- The THR per-point evaluator's internal programs. -/
abbrev TProg := WM 16 118

/-! ## The population builder, lifted -/

/-- The builder's streams: the row word, the corner word, the population. -/
def fsP : Fin 3 → Fin 17 := ![13, 12, 14]

/-- The builder's registers: `53 … 63`. -/
def frP : Fin 11 → Fin 118 := fun k => ⟨53 + k.val, by omega⟩

theorem fsP_inj : Function.Injective fsP := by decide

theorem frP_inj : Function.Injective frP := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp only [frP] at this; omega)

/-- The builder's record read off the layout. -/
def toP (ω : WState 16 118) : PSt :=
  ⟨ω.st 13, ω.st 12, ω.st 14, ω.sh 13, ω.sh 12, ω.sh 14, ω.val 53, ω.val 54, ω.val 55, ω.val 56, ω.val 57,
    ω.val 58, ω.val 59, ω.val 60, ω.val 61, ω.val 62, ω.val 63, ω.cell⟩

theorem liftP (ω : WState 16 118) : LiftW fsP frP ω (toP ω).w :=
  ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl, fun r => by fin_cases r <;> rfl, rfl⟩

variable (cap : ℕ)

theorem popWL_spec (sgn : Bool) (p r0 D A0 : ℕ) (as : List ℕ) (X restR restX zr0 : List Bool)
    (ω : WState 16 118)
    (hrw : ω.st 13 = ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ restR)
    (hX : ω.st 12 = frameP X ++ restX) (hXl : X.length = 4 * as.length) (hZ : ω.st 14 = zr0 ++ [false])
    (hzr : zr0.length = 2 * as.length) (hA0 : ∀ a ∈ as, a ≤ A0)
    (h13 : ω.sh 13 = 0) (h12 : ω.sh 12 = 0) (h14 : ω.sh 14 = 0) (hd : ω.val 53 = D) (hmm : ω.val 63 = as.length)
    (hz : ∀ k : Fin 118, 54 ≤ k.val → k.val ≤ 62 → ω.val k = 0) (hc : popCap p r0 as.length A0 D ≤ cap) :
    WExec cap ((popW sgn).liftW fsP frP) ω (ω.sets 14 (frame (popZ sgn D as X))) (popCost p r0 as.length A0 D) := by
  have e := popW_spec cap sgn p r0 D A0 as X restR restX zr0 (toP ω) hrw hX hXl hZ hzr hA0 h13 h12 h14
    (hz 59 (by decide) (by decide)) (hz 60 (by decide) (by decide)) (hz 61 (by decide) (by decide)) hd hmm
    (hz 54 (by decide) (by decide)) (hz 55 (by decide) (by decide)) (hz 56 (by decide) (by decide))
    (hz 58 (by decide) (by decide)) (hz 57 (by decide) (by decide)) (hz 62 (by decide) (by decide)) hc
  have e2 := WExec.liftW_upd cap fsP_inj frP_inj e ω (liftP ω)
  rw [← p_z, updW_sets fsP_inj frP_inj, updW_self fsP_inj frP_inj (liftP ω)] at e2
  exact e2

/-! ## The report machine, lifted -/

/-- The report machine's streams: the population, stage 4's table, the compared state, an unused read-only one. -/
def fsM : Fin 4 → Fin 17 := ![14, 9, 15, 4]

/-- The report machine's registers: `64 … 89`. -/
def frM : Fin 26 → Fin 118 := fun k => ⟨64 + k.val, by omega⟩

theorem fsM_inj' : Function.Injective fsM := by decide

theorem frM_inj' : Function.Injective frM := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp only [frM] at this; omega)

/-- The report machine's record read off the layout (its head counters `0`). -/
def toM (ω : WState 16 118) : Maj.MSt :=
  ⟨ω.st 14, ω.st 9, 0, ω.st 15, 0, ω.st 4, 0, ω.val 67, ω.val 79, ω.val 80, ω.val 81, ω.val 82, ω.val 83,
    ω.val 87, ω.val 88, ω.val 89, ω.cell⟩

theorem liftM (ω : WState 16 118) (h14 : ω.sh 14 = 0) (h9 : ω.sh 9 = 0) (h15 : ω.sh 15 = 0) (h4 : ω.sh 4 = 0)
    (hz : ∀ k : Fin 118, 64 ≤ k.val → k.val ≤ 78 → k.val ≠ 67 → ω.val k = 0) (h84 : ω.val 84 = 0)
    (h85 : ω.val 85 = 0) (h86 : ω.val 86 = 0) : LiftW fsM frM ω (toM ω).w := by
  refine ⟨fun i => ?_, fun i => by fin_cases i <;> rfl, fun r => ?_, rfl⟩
  · fin_cases i
    · exact h14
    · exact h9
    · exact h15
    · exact h4
  · fin_cases r
    all_goals first
      | rfl
      | exact h84
      | exact h85
      | exact h86
      | exact hz _ (by decide) (by decide) (by decide)

theorem repML_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hcap : ListEval.capOf M J W row Z.length ≤ cap) (k : ℕ)
    (ω : WState 16 118) (hpt : ∀ p, readTapeBit (ω.st 14) p = readTapeBit (frame Z) p)
    (ht5 : ω.st 9 = ListEval.levelWord M J W row) (hss : ω.st 15 = List.replicate k false)
    (h14 : ω.sh 14 = 0) (h9 : ω.sh 9 = 0) (h15 : ω.sh 15 = 0) (h4 : ω.sh 4 = 0)
    (hz : ∀ k : Fin 118, 64 ≤ k.val → k.val ≤ 89 → ω.val k = 0) :
    WExec cap (repM.liftW fsM frM) ω
      (((ω.sets 15 (List.replicate M false ++ List.replicate (k - M) false)).setv 82
        (ListEval.reportRef M J W row Z)).setc false) (repCost M (ListEval.capOf M J W row Z.length)) := by
  have hL := liftM ω h14 h9 h15 h4 (fun q h1 h2 _ => hz q h1 (by omega)) (hz 84 (by decide) (by decide))
    (hz 85 (by decide) (by decide)) (hz 86 (by decide) (by decide))
  have e := repM_spec cap M J W row Z hrows hcap k (toM ω) hpt ht5 rfl hss rfl (hz 67 (by decide) (by decide))
    (hz 81 (by decide) (by decide)) (hz 82 (by decide) (by decide)) (hz 83 (by decide) (by decide))
    (hz 89 (by decide) (by decide))
  have hx : ({ toM ω with
      ss := List.replicate M false ++ List.replicate (k - M) false,
      r := ListEval.reportRef M J W row Z, cell := false } : Maj.MSt).w =
      (((toM ω).w.sets 2 (List.replicate M false ++ List.replicate (k - M) false)).setv 18
        (ListEval.reportRef M J W row Z)).setc false := by
    rw [Maj.m_ss_wr, Maj.m_r, m_cell]
  rw [hx] at e
  have e2 := WExec.liftW_upd cap fsM_inj' frM_inj' e ω hL
  rw [updW_setc, updW_setv fsM_inj' frM_inj', updW_sets fsM_inj' frM_inj', updW_self fsM_inj' frM_inj' hL] at e2
  exact e2

/-! ## Stage 8, lifted -/

/-- Stage 8's streams: the corner word, the row word, the reports. -/
def fsT : Fin 3 → Fin 17 := ![12, 13, 16]

/-- Stage 8's registers: `90 … 101`. -/
def frT : Fin 12 → Fin 118 := fun k => ⟨90 + k.val, by omega⟩

theorem fsT_inj : Function.Injective fsT := by decide

theorem frT_inj : Function.Injective frT := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp only [frT] at this; omega)

theorem thr8L_spec (X : List Bool) (as ws tp tm : List ℕ) (L p r0 : ℕ) (rest0 rest1 rest2 : List Bool)
    (hl : X.length = 4 * L) (has : as.length = L) (h1l : ws.length = tp.length) (h2l : ws.length = tm.length)
    (hr0 : r0 < p) (ω : WState 16 118) (hX : ω.st 12 = frameP X ++ false :: rest0)
    (hT : ω.st 13 = Term.rowWord p r0 as ws ++ rest1) (hR : ω.st 16 = Term.repWord tp tm ++ rest2)
    (h12 : ω.sh 12 = 0) (h13 : ω.sh 13 = 0) (h16 : ω.sh 16 = 0)
    (hz : ∀ k : Fin 118, 90 ≤ k.val → k.val ≤ 101 → ω.val k = 0)
    (hcap : Term.capT p r0 L as ws tp tm ≤ cap) :
    WExec cap (thr8I.liftR fsT frT) ω (ω.setv 92 (Term.thrTermOk p r0 X as ws tp tm).toNat)
      (costTI p r0 L as ws tp tm) := by
  have e := thr8I_spec (fun i => ω.st (fsT i)) cap 0 0 0 X as ws tp tm L p r0 ω.cell rest0 rest1 rest2 hl has h1l
    h2l hr0 (by show (ω.st 12).drop 0 = _; rw [List.drop_zero, hX])
    (by show (ω.st 13).drop 0 = _; rw [List.drop_zero, hT]) (by show (ω.st 16).drop 0 = _; rw [List.drop_zero, hR]) hcap
  have hL : LiftRelR fsT frT (fun i => ω.st (fsT i)) ω (Term.S9 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ω.cell) := by
    refine ⟨fun i => ?_, fun i p => rfl, fun r => ?_, rfl⟩
    · fin_cases i
      · exact h12
      · exact h13
      · exact h16
    · fin_cases r <;> exact hz _ (by decide) (by decide)
  have e2 := RExec.liftR_upd _ cap cap le_rfl fsT_inj frT_inj e ω hL
  refine WExec.cast cap e2 ?_ le_rfl
  refine wstate_ext_img (fs := fsT) (fr := frT) (fun i => ?_) (fun j hj => ?_) (fun i => ?_) (fun j _ => ?_)
    (fun r => ?_) (fun q hq => ?_) rfl
  · rw [updR_sh_in fsT_inj]
    fin_cases i
    · exact h12.symm
    · exact h13.symm
    · exact h16.symm
  · rw [updR_sh_out _ _ j hj]; rfl
  · rfl
  · rfl
  · rw [updR_val_in frT_inj]
    fin_cases r <;> simp [Term.S9, frT] <;> exact (hz _ (by decide) (by decide)).symm
  · rw [updR_val_out _ _ q hq]
    have hne : q ≠ 92 := fun e => hq 2 (by rw [e]; rfl)
    simp [Function.update_of_ne hne]

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
