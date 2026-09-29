import Proof.Wire_3_5.Primitive.SeedFix.CtrPar

/-! # X3, part 6: the first pass, all `s` parity bits (P3:1202-1206)

"The syndrome `Hx` uniquely specifies `e`" (P3:1204-1206): the first pass of a block runs `scan1` for `t = 0 … s−1`
(`rgKT` counts down from `s`, `rgPW = 2^t`), leaving `rgPAR = packB (parL P zb)`, the block's parity bits, and the
stream at the block's start. Here: `T1I` (the loop's invariant), `t1_step`, `t1Loop_spec`, **`p1_spec`**.

Paper quantity of the main type: the block's parity bits `parL P zb` (the syndrome's bits). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo

section ParAll
variable (cap : ℕ)

/-- The first pass's loop over `t`. -/
def t1Loop (R : Fin 4) : CM := .whr rgKT (.seq (.dec rgKT) (scan1 R))

/-- The first pass. -/
def p1 (R : Fin 4) : CM :=
  .seq (.inc rgPW) (.seq (FinalPass.Hash4.wcopyR rgS rgKT rgT) (.seq (t1Loop R) (WM.clear rgPW)))

/-- The registers the first pass uses. -/
abbrev p1Regs : List (Fin 26) :=
  [rgPAR, rgPW, rgKT, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC, rgKQ]

/-- **The first pass's invariant** after `t` parity bits. -/
structure T1I (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (σ0 : CS) (b0 t : ℕ) (τ : CS) : Prop where
  kt : τ.val rgKT = P.s - t
  pw : τ.val rgPW = 2 ^ t
  par : τ.val rgPAR = packB ((List.range t).map (parB P zb))
  z : Zero1 τ
  shR : τ.sh R = b0
  st : τ.st = σ0.st
  sh : ∀ i, i ≠ R → τ.sh i = σ0.sh i
  oth : ∀ r, r ∉ p1Regs → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

theorem packB_range_succ (P : StarParams) (zb : ℕ → Bool) (t : ℕ) :
    packB ((List.range (t + 1)).map (parB P zb)) =
      packB ((List.range t).map (parB P zb)) + (parB P zb t).toNat * 2 ^ t := by
  rw [List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [packB_append, List.length_map, List.length_range]

theorem t1_step (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (σ0 : CS) (b0 : ℕ)
    (hzb : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m) (hb : σ0.val rgB = P.b)
    (t : ℕ) (ht : t < P.s) (τ : CS) (hI : T1I P zb R σ0 b0 t τ) (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap (.seq (.dec rgKT) (scan1 R)) τ τ' (scanCost P.b + 2) ∧ T1I P zb R σ0 b0 (t + 1) τ' := by
  have hbs := P.b_succ
  have hs1 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have e0 := WExec.dec (cap := cap) rgKT τ (by rw [hI.kt]; omega)
  obtain ⟨τ0, hτ0⟩ : ∃ y, y = τ.setv rgKT (τ.val rgKT - 1) := ⟨_, rfl⟩
  rw [← hτ0] at e0
  have g0 : ∀ r, r ≠ rgKT → τ0.val r = τ.val r := fun r hr => by rw [hτ0]; simp [Function.update_apply, hr]
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hI.z
  have hlt := packB_lt ((List.range t).map (parB P zb))
  rw [List.length_map, List.length_range] at hlt
  obtain ⟨τ1, e1, a1, b1, c1, d1, f1, g1, h1, k1⟩ := scan1_spec cap P zb t ht R b0 τ0
    (by rw [hτ0]; simp only [WState.setv_st]; rw [hI.st]; exact hzb) (by rw [hτ0]; simp [hI.shR])
    (by rw [g0 rgPW (by decide), hI.pw]) (by rw [g0 rgB (by decide), hI.oth rgB (by decide), hb])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [g0 _ (by decide)] <;> assumption)
    (by rw [g0 rgPAR (by decide), hI.par]; exact hlt) hcap
  refine ⟨τ1, WExec.mono (WExec.seq e0 e1) (by omega), ⟨?_, ?_, ?_, c1, d1, ?_, ?_, ?_, ?_⟩⟩
  · rw [h1 rgKT (by decide), hτ0]; simp [hI.kt]; omega
  · exact b1
  · rw [a1, g0 rgPAR (by decide), hI.par, packB_range_succ]
  · rw [f1, hτ0]; simp [hI.st]
  · intro i hi; rw [g1 i hi, hτ0]; simpa using hI.sh i hi
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h1 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2]), g0 r hr.2.2.1]
    exact hI.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2])
  · rw [k1, hτ0]; simpa using hI.cell

theorem t1Loop_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (σ0 : CS) (b0 : ℕ)
    (hzb : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m) (hb : σ0.val rgB = P.b)
    (hcap : 8 * (P.b + 2) ≤ cap) :
    ∀ (m t : ℕ) (τ : CS), t + m = P.s → T1I P zb R σ0 b0 t τ →
      ∃ τ', WExec cap (t1Loop R) τ τ' (m * (scanCost P.b + 4) + 1) ∧ T1I P zb R σ0 b0 P.s τ' := by
  intro m
  induction m with
  | zero =>
    intro t τ htm hI
    have : t = P.s := by omega
    subst this
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [hI.kt]; omega)) (by omega), hI⟩
  | succ m ih =>
    intro t τ htm hI
    obtain ⟨τ1, e1, h1⟩ := t1_step cap P zb R σ0 b0 hzb hb t (by omega) τ hI hcap
    obtain ⟨τ2, e2, h2⟩ := ih (t + 1) τ1 (by omega) h1
    exact ⟨τ2, WExec.mono (WExec.whrT (by rw [hI.kt]; omega) e1 e2) (by ring_nf; omega), h2⟩

/-- The first pass's steps. -/
def p1Cost (b s : ℕ) : ℕ := (s + 1) * (scanCost b + 100)

/-- **The first pass**: from the block's start, `rgPAR = packB (parL P zb)` (the block's parity bits), the stream
back at the block's start, every other scratch register back at `0`. -/
theorem p1_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (b0 : ℕ) (σ : CS)
    (hzb : ∀ m < dB P, readTapeBit (σ.st R) (b0 + 2 * m + 1) = zb m) (hR : σ.sh R = b0)
    (hb : σ.val rgB = P.b) (hs : σ.val rgS = P.s) (hz : Zero1 σ) (hpw : σ.val rgPW = 0) (hkt : σ.val rgKT = 0)
    (hpar : σ.val rgPAR = 0) (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ τ, WExec cap (p1 R) σ τ (p1Cost P.b P.s) ∧ τ.val rgPAR = packB (parL P zb) ∧ τ.val rgPW = 0 ∧
      τ.val rgKT = 0 ∧ Zero1 τ ∧ τ.sh R = b0 ∧ τ.st = σ.st ∧ (∀ i, i ≠ R → τ.sh i = σ.sh i) ∧
      (∀ r, r ∉ p1Regs → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hbs := P.b_succ
  have hs1 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10⟩ := hz
  have i1 := WExec.inc (cap := cap) rgPW σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rgPW (σ.val rgPW + 1) := ⟨_, rfl⟩
  rw [← hσ1] at i1
  have i2 := FinalPass.Hash4.wcopyR_spec cap rgS rgKT rgT (by decide) (by decide) (by decide) σ1
    (by rw [hσ1]; simp [hkt]) (by rw [hσ1]; simp [z7]) (by rw [hσ1]; simp [hs]; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = σ1.setv rgKT (σ1.val rgS) := ⟨_, rfl⟩
  rw [← hσ2] at i2
  have g2 : ∀ r, r ≠ rgPW → r ≠ rgKT → σ2.val r = σ.val r := by
    intro r r1 r2; rw [hσ2, hσ1]; simp [Function.update_apply, r1, r2]
  have hI0 : T1I P zb R σ b0 0 σ2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ2, hσ1]; simp [hs]
    · rw [hσ2, hσ1]; simp [hpw]
    · rw [g2 rgPAR (by decide) (by decide), hpar]; rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [g2 _ (by decide) (by decide)] <;> assumption
    · rw [hσ2, hσ1]; simp [hR]
    · rw [hσ2, hσ1]; simp
    · intro i hi; rw [hσ2, hσ1]; simp
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g2 r hr.2.1 hr.2.2.1
    · rw [hσ2, hσ1]; simp
  obtain ⟨σ3, i3, h3⟩ := t1Loop_spec cap P zb R σ b0 hzb hb hcap P.s 0 σ2 (by omega) hI0
  have i4 := wclear_spec cap rgPW (σ3.val rgPW) σ3 rfl (by rw [h3.pw]; omega)
  have hsc : 3 + 1 + (18 * σ1.val rgS + 3 + 1 + (P.s * (scanCost P.b + 4) + 1 + 1 + (3 * σ3.val rgPW + 1))) ≤
      p1Cost P.b P.s := by
    rw [h3.pw]
    have e1 : σ1.val rgS = P.s := by rw [hσ1]; simp [hs]
    rw [e1]
    unfold p1Cost scanCost
    nlinarith
  refine ⟨_, WExec.mono (WExec.seq i1 (WExec.seq i2 (WExec.seq i3 i4))) hsc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h3.par, parL]
  · simp
  · simp [h3.kt]
  · obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ := h3.z
    exact ⟨by simp [y1], by simp [y2], by simp [y3], by simp [y4], by simp [y5], by simp [y6], by simp [y7],
      by simp [y8], by simp [y9], by simp [y10]⟩
  · simp [h3.shR]
  · simp [h3.st]
  · intro i hi; simp [h3.sh i hi]
  · intro r hr
    have r1 : r ≠ rgPW := fun e => hr (by rw [e]; decide)
    simp [Function.update_apply, r1, h3.oth r hr]
  · simp [h3.cell]

end ParAll

end NearCubicWires.WireExponent3_5.PrimT.Ctr
