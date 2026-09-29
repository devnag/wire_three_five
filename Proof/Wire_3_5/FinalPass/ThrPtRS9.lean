import Proof.Wire_3_5.FinalPass.ThrPtRS8

/-! # S2 (THR per point), part 23: one row `(g, p)` at the point (P3:2587-2630)

`rowStep`: RowW writes row `(g, p)`'s word; the digits' reports (`digLoop`); the digit counter restored, the reports
rewound; stage 8's factor `[thrTermOk …]` (register `92`) added to the accumulator; both words erased.
`RowReady`: the working state between rows (the scratch blank, the counters at rest, the corner word in place).
**`rowStep_spec`**: from a `RowReady` state, the accumulator gains `[thrTermOk p r₀ X as ws tp tm]` at row `(g, p)`'s
residue, reduced coefficients and digit weights, with `tp`, `tm` the digits' reports of the populations
`popZ ± d as X`, and the state is `RowReady` again. Paper quantity: `R̂_{g,p}(c, u, v)` (row:thr-reported, through
`thrRhat_eq_termOk`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Pop

/-- **The working state between rows.** -/
structure RowReady (t : TSt) (M τ : ℕ) (X : List Bool) : Prop where
  rw : ∀ b ∈ t.rw, b = false
  hRw : t.hRw = 0
  rwH : t.rwH = 0
  z : ∃ zr0 : List Bool, t.z = zr0 ++ [false] ∧ zr0.length = 2 * M
  ss : ∀ b ∈ t.ss, b = false
  rep : ∀ b ∈ t.rep, b = false
  hRep : t.hRep = 0
  rH : t.rH = 0
  d : t.d = 0
  dRem : t.dRem = τ
  kS : t.kS = M
  rS : t.rS = 0
  r82 : t.r82 = 0
  w92 : t.w92 = 0
  x : t.x = frameP X ++ [false]

/-- **One row `(g, p)`.** -/
noncomputable def rowStep : TProg :=
  .seq (DigsBody.rowWImpl.prog payS 13 rowR) (.seq digLoop (.seq (WM.move 53 111) (.seq (WM.rewind 16 112)
    (.seq (thr8I.liftR fsT frT) (.seq (WM.move 92 0) (.seq erRepAll eraseRow))))))

/-- One row's step bound. -/
def rowCost (bW p r0 M A0 τ DM c5 : ℕ) (as ws tp tm : List ℕ) : ℕ :=
  bW + 1 + (digLoopCost τ p r0 M A0 τ DM c5 + 1 + ((7 * τ + 1) + 1 + ((5 * (Term.repWord tp tm).length + 1) + 1 +
    (costTI p r0 M as ws tp tm + 1 + (8 + 1 + ((τ * (18 * DM + 50) + 1 + 1 + ((7 * τ + 1) + 1 +
    (5 * (Term.repWord tp tm).length + 1))) + 1 + eraseRowCost p r0 M τ A0 (Term.rowWord p r0 as ws).length))))))

theorem eq_rep_false (l : List Bool) (h : ∀ b ∈ l, b = false) : l = List.replicate l.length false :=
  List.eq_replicate_iff.mpr ⟨rfl, h⟩

theorem payS_lt : ∀ i : Fin 4, (payS i).val < 10 := by decide
theorem payS_sh8 : ∀ i : Fin 4, (payS i).val ≠ 8 := by decide
theorem payS_sh13 : ∀ i : Fin 4, (payS i).val ≠ 13 := by decide
theorem payS_sh16 : ∀ i : Fin 4, (payS i).val ≠ 16 := by decide
theorem rowR_val (j : Fin Digs.digsK) : (rowR j).val = 5 + j.val := rfl

theorem tw_val_low (σB : WState 16 118) (t : TSt) (q : Fin 118) (h0 : q.val ≠ 0) (h6 : q.val ≠ 6) (h7 : q.val ≠ 7)
    (h : q.val < 53) : (t.w σB).val q = σB.val q :=
  tw_val_other σB t q h0 h6 h7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

theorem tRepL_le (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (sgn : Bool)
    (D : ℕ) : ∀ x ∈ tRepL DM DJ DW row as X sgn D, x ≤ DM := by
  intro x hx
  simp only [tRepL, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact tRep_le DM DJ DW row as X sgn i

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
