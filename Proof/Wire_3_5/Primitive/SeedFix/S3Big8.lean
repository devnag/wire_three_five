import Proof.Wire_3_5.Primitive.SeedFix.S3Big7

/-! # S3, part 14: one list seed's `R̂` added to the accumulator

`Σ_{e'} R̂_{e'}(c,u,v)` (P3:3170-3178; `rsumSym`, over the list seeds in base's enumeration, `rsum_seeds`): at the seed
`e'_i = seedOf k i` the evaluator sets the running product to `1`, counts the tuple into `qAc`, runs the four guarded
circuit steps, and moves the product into the accumulator (register `0`). **`seedBody_spec`**: the accumulator plus
`[circAt 0 ∧ circAt 1 ∧ circAt 2 ∧ circAt 3]` (= `R̂_{e'_i}`, `rhat4`), every table offset advanced by its circuit's
table length (inside the tuple), the running product and the tuple counter back at `0`, the invariant kept.

Paper quantity of the main type: the accumulator plus `R̂_{e'_i}(c,u,v)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

/-- The accumulator (register `0`). -/
def qAcc : Fin 67 := ⟨0, by omega⟩

/-- Setting a register outside the invariant's keeps the invariant. -/
theorem BodyInv.setv {k : SymCall} {c eu ev : BitInput k.P.n} {off : Fin 4 → ℕ} {ω : BS}
    (hI : BodyInv k c eu ev off ω) (r : Fin 67) (x : ℕ) (hr : r.val = 0 ∨ (51 ≤ r.val ∧ r.val ≤ 53)) :
    BodyInv k c eu ev off (ω.setv r x) := by
  have hn : ∀ r' : Fin 67, (r'.val ≠ r.val) → (ω.setv r x).val r' = ω.val r' := fun r' h => by
    rw [WState.setv_val, Function.update_of_ne (fun e => h (congrArg Fin.val e))]
  refine ⟨hI.words, hI.ptC, hI.ptU, hI.ptV, fun i => ?_, hI.sc, hI.scs, hI.whead, hI.thead, fun j => ?_, hI.pth,
    fun q => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn _ (by have := qN_lt i; show 1 + i.val ≠ r.val; omega)]; exact hI.nums i
  · rw [hn _ (by show 58 + j.val ≠ r.val; omega)]; exact hI.toff j
  · rw [hn _ (by show 19 + q.val ≠ r.val; omega)]; exact hI.hq q
  · rw [hn _ (by show 54 ≠ r.val; omega)]; exact hI.hct
  · rw [hn _ (by show 56 ≠ r.val; omega)]; exact hI.htp
  · rw [hn _ (by show 55 ≠ r.val; omega)]; exact hI.hbk
  · rw [hn _ (by show 57 ≠ r.val; omega)]; exact hI.hsk

/-- **One list seed's `R̂` into the accumulator.** -/
def seedBody : BM :=
  .seq (.inc qRh) (.seq (wcopyR (qN 0) qAc qTp) (.seq (guardJ 0) (.seq (guardJ 1) (.seq (guardJ 2)
    (.seq (guardJ 3) (WM.move qRh qAcc))))))

/-- The seed body's cost bound. -/
def bodyCost (k : SymCall) : ℕ := guardCost k 0 + guardCost k 1 + guardCost k 2 + guardCost k 3 + 100

theorem mul2_le (a b : Bool) : 1 * a.toNat * b.toNat ≤ 1 := by
  cases a <;> cases b <;> decide

theorem mul3_le (a b c : Bool) : 1 * a.toNat * b.toNat * c.toNat ≤ 1 := by
  cases a <;> cases b <;> cases c <;> decide

theorem bool4_toNat (b0 b1 b2 b3 : Bool) :
    1 * b0.toNat * b1.toNat * b2.toNat * b3.toNat = (b0 && b1 && b2 && b3).toNat := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem seedBody_spec (cap : ℕ) (k : SymCall) (c eu ev : BitInput k.P.n) (i : Fin (Fintype.card k.Pl.FlatSeed))
    (off : Fin 4 → ℕ) (ω : BS) (hI : BodyInv k c eu ev off ω)
    (hoff : ∀ j : Fin 4, j.val < k.a → off j = i.val * tabLen k j) (hrh : ω.val qRh = 0) (hac : ω.val qAc = 0)
    (hcap : ∀ j : Fin 4, j.val < k.a → CircCap cap k.Pl (seedOf k i) k.P.n (gatesJ k j) (topJ k j).length)
    (c1 : ∀ j : Fin 4, (templJ k j).length ≤ cap) (c2 : ∀ j : Fin 4, (i.val + 1) * tabLen k j ≤ cap)
    (c4 : 4 ≤ cap) (c5 : ω.val qAcc + 1 ≤ cap) :
    ∃ τ, WExec cap seedBody ω τ (bodyCost k) ∧ BodyInv k c eu ev (fun j => off j + adv k j) τ ∧
      τ.val qAcc = ω.val qAcc + (circAt k (seedOf k i) c eu ev 0 && circAt k (seedOf k i) c eu ev 1 &&
        circAt k (seedOf k i) c eu ev 2 && circAt k (seedOf k i) c eu ev 3).toNat ∧
      τ.val qRh = 0 ∧ τ.val qAc = 0 ∧
      (∀ r, r ≠ qRh → r ≠ qAc → r ≠ qAcc → (∀ j, r ≠ qOff j) → τ.val r = ω.val r) := by
  have hka := k.ha
  -- `qRh := 1`
  have e1 := WExec.inc (cap := cap) qRh ω (by rw [hrh]; omega)
  obtain ⟨ω1, hω1⟩ : ∃ y, y = ω.setv qRh (ω.val qRh + 1) := ⟨_, rfl⟩
  rw [← hω1] at e1
  have I1 : BodyInv k c eu ev off ω1 := by rw [hω1]; exact hI.setv _ _ (Or.inr ⟨by decide, by decide⟩)
  have v1 : ∀ r, r ≠ qRh → ω1.val r = ω.val r := fun r hr => by rw [hω1, WState.setv_val, Function.update_of_ne hr]
  have r1 : ω1.val qRh = 1 := by rw [hω1, WState.setv_val, Function.update_self, hrh]
  -- `qAc := a`
  have hN0 : ω1.val (qN 0) = k.a := by rw [I1.nums]; rfl
  have e2 := wcopyR_spec cap (qN 0) qAc qTp (qN_ne _ (by decide)) (qN_ne _ (by decide)) (by decide) ω1
    (by rw [v1 _ (by decide)]; exact hac) (by rw [I1.htp]) (by rw [hN0]; omega)
  obtain ⟨ω2, hω2⟩ : ∃ y, y = ω1.setv qAc (ω1.val (qN 0)) := ⟨_, rfl⟩
  rw [← hω2] at e2
  have I2 : BodyInv k c eu ev off ω2 := by rw [hω2]; exact I1.setv _ _ (Or.inr ⟨by decide, by decide⟩)
  have v2 : ∀ r, r ≠ qAc → ω2.val r = ω1.val r := fun r hr => by rw [hω2, WState.setv_val, Function.update_of_ne hr]
  have a2 : ω2.val qAc = k.a - (0 : Fin 4).val := by rw [hω2, WState.setv_val, Function.update_self, hN0]; rfl
  have r2 : ω2.val qRh = 1 := by rw [v2 _ (by decide), r1]
  -- the four guarded steps
  obtain ⟨ω3, e3, I3, r3, a3, o3, -, -⟩ := guardJ_spec cap k c eu ev i 0 off ω2 I2 (hoff 0) a2 (by rw [r2])
    (hcap 0) (c1 0) (c2 0) c4
  have b0 := (circAt k (seedOf k i) c eu ev 0).toNat_le
  obtain ⟨ω4, e4, I4, r4, a4, o4, -, -⟩ := guardJ_spec cap k c eu ev i 1 _ ω3 I3
    (fun h => by rw [Function.update_of_ne (by decide)]; exact hoff 1 h) a3 (by rw [r3, r2]; omega)
    (hcap 1) (c1 1) (c2 1) c4
  have b1 := (circAt k (seedOf k i) c eu ev 1).toNat_le
  obtain ⟨ω5, e5, I5, r5, a5, o5, -, -⟩ := guardJ_spec cap k c eu ev i 2 _ ω4 I4
    (fun h => by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hoff 2 h) a4
    (by rw [r4, r3, r2]; exact mul2_le _ _) (hcap 2) (c1 2) (c2 2) c4
  have b2 := (circAt k (seedOf k i) c eu ev 2).toNat_le
  obtain ⟨ω6, e6, I6, r6, a6, o6, -, -⟩ := guardJ_spec cap k c eu ev i 3 _ ω5 I5
    (fun h => by
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hoff 3 h) a5
    (by rw [r5, r4, r3, r2]; exact mul3_le _ _ _) (hcap 3) (c1 3) (c2 3) c4
  -- the product into the accumulator
  have hR : ω6.val qRh = (circAt k (seedOf k i) c eu ev 0 && circAt k (seedOf k i) c eu ev 1 &&
      circAt k (seedOf k i) c eu ev 2 && circAt k (seedOf k i) c eu ev 3).toNat := by
    rw [r6, r5, r4, r3, r2, bool4_toNat]
  have hsame : ∀ r, r ≠ qRh → r ≠ qAc → (∀ j, r ≠ qOff j) → ω6.val r = ω.val r := fun r h1 h2 h3 => by
    rw [o6 r h1 h2 (h3 3), o5 r h1 h2 (h3 2), o4 r h1 h2 (h3 1), o3 r h1 h2 (h3 0), v2 r h2, v1 r h1]
  have hA6 : ω6.val qAcc = ω.val qAcc := hsame _ (by decide) (by decide) (fun j => ne_qOff j (by decide))
  have hRle : ω6.val qRh ≤ 1 := by rw [hR]; exact Bool.toNat_le _
  have e7 := wmove_spec cap qRh qAcc (by decide) (ω6.val qRh) ω6 rfl (by omega) (by rw [hA6]; omega)
  obtain ⟨ω7, hω7⟩ : ∃ y, y = (ω6.setv qRh 0).setv qAcc (ω6.val qAcc + ω6.val qRh) := ⟨_, rfl⟩
  rw [← hω7] at e7
  have hoffe : Function.update (Function.update (Function.update (Function.update off 0 (off 0 + adv k 0)) 1
      (Function.update off 0 (off 0 + adv k 0) 1 + adv k 1)) 2
      (Function.update (Function.update off 0 (off 0 + adv k 0)) 1
        (Function.update off 0 (off 0 + adv k 0) 1 + adv k 1) 2 + adv k 2)) 3
      (Function.update (Function.update (Function.update off 0 (off 0 + adv k 0)) 1
        (Function.update off 0 (off 0 + adv k 0) 1 + adv k 1)) 2
        (Function.update (Function.update off 0 (off 0 + adv k 0)) 1
          (Function.update off 0 (off 0 + adv k 0) 1 + adv k 1) 2 + adv k 2) 3 + adv k 3) =
      fun j => off j + adv k j := by
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hoffe] at I6
  refine ⟨ω7, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · unfold bodyCost; rw [hN0] at *; omega
  · rw [hω7]
    exact (I6.setv _ _ (Or.inr ⟨by decide, by decide⟩)).setv _ _ (Or.inl rfl)
  · rw [hω7, WState.setv_val, Function.update_self, hA6, hR]
  · rw [hω7, WState.setv_val, Function.update_of_ne (by decide), WState.setv_val, Function.update_self]
  · rw [hω7, WState.setv_val, Function.update_of_ne (by decide), WState.setv_val, Function.update_of_ne (by decide), a6]
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    omega
  · rw [hω7, WState.setv_val, Function.update_of_ne h3, WState.setv_val, Function.update_of_ne h1]
    exact hsame r h1 h2 h4

end NearCubicWires.WireExponent3_5.PrimT.S3
