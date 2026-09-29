import Proof.Wire_3_5.Primitive.SeedFix.FlipsValue
import Proof.Wire_3_5.Primitive.Writers.GeoNums

/-! # FLIPS, part 7: the writer's set-up loops (P3:1206-1207, 3119-3120)

The flips writer reads the call's translation from the request word ("The algorithm receives polynomial-bit integer
circuit descriptions", P3:3119-3120) and writes the coset offset (P3:1206-1207: one coset per block, block `j`'s unit
vector at the code `t_j`). The loops, on the layout with the registers `50 … 59`:

* `skipNats` / `skipNats_spec` (skip framed `natWord`s, PA's `skipNatM`);
* `oneHotW` / `oneHotW_spec` (`frameP (oneHot b t)` appended, the code counted down);
* `transLoop` / `transLoop_spec` (read each code, emit its block: `frameP (ts.flatMap (oneHot b))`);
* `zerosW` / `zerosW_spec` (`frameP (replicate m false)`).

Paper quantity of the main types: the offset's blocks (`oneHot b t_j`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT)
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## Registers -/

def rJ : Fin GR := 50
def rFf : Fin GR := 51
def rCc : Fin GR := 52
def rTv : Fin GR := 53
def rPp : Fin GR := 54
def rTt : Fin GR := 55
def rBc : Fin GR := 56
def rOc : Fin GR := 57
def rTmp : Fin GR := 59

/-! ## Register disequalities -/

theorem fJ : rFf ≠ rJ := by decide
theorem cJ : rCc ≠ rJ := by decide

section Gen
variable (cap : ℕ)

/-! ## Skipping framed numbers -/

/-- Skip `cnt` framed `natWord`s on `gIN`. -/
def skipNats : WM GS GR := .whr rJ (.seq (.dec rJ) (PrimAsm.ParseNat.skipNatM true gIN rFf rCc))

/-- The skip's cost. -/
def skipCost (xs : List ℕ) : ℕ := (xs.map fun x => 20 * natBitLength x + 24).sum + 1

theorem skipNats_spec : ∀ (xs : List ℕ) (pre rest : List Bool) (σ : WState GS GR),
    σ.st gIN = pre ++ marks (xs.flatMap RepairRepresentation.natWord) ++ rest → σ.sh gIN = pre.length →
    σ.val rJ = xs.length → σ.val rFf = 0 → σ.val rCc = 0 → (∀ x ∈ xs, natBitLength x + 1 ≤ cap) →
    xs.length ≤ cap →
    ∃ τ, WExec cap skipNats σ τ (skipCost xs) ∧ τ.st = σ.st ∧
      τ.sh gIN = pre.length + 2 * (xs.flatMap RepairRepresentation.natWord).length ∧
      (∀ i, i ≠ gIN → τ.sh i = σ.sh i) ∧ τ.val rJ = 0 ∧ (∀ r, r ≠ rJ → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | [], pre, rest, σ, hst, hsh, hj, hf, hc, hx, hl => by
    refine ⟨σ, WExec.mono (WExec.whrF (by rw [hj]; rfl)) (by simp [skipCost]), rfl, by simp [hsh],
      fun _ _ => rfl, by rw [hj]; rfl, fun _ _ => rfl, rfl⟩
  | x :: xs, pre, rest, σ, hst, hsh, hj, hf, hc, hx, hl => by
    have s1 := WExec.dec (cap := cap) rJ σ (by rw [hj]; exact hl)
    obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rJ (σ.val rJ - 1) := ⟨_, rfl⟩
    rw [← hσ1] at s1
    have s2 := PrimAsm.ParseNat.skipNatM_spec cap true gIN rFf rCc (by decide) x pre
      (marks (xs.flatMap RepairRepresentation.natWord) ++ rest) σ1
      (by rw [hσ1]; show σ.st gIN = _; rw [hst]; simp [PrimAsm.ParseNat.enc, List.flatMap_cons, List.append_assoc])
      (by rw [hσ1]; exact hsh) (by rw [hσ1]; simp [WState.setv, Function.update_apply, fJ, hf])
      (by rw [hσ1]; simp [WState.setv, Function.update_apply, cJ, hc]) (hx x (by simp))
    obtain ⟨σ2, hσ2⟩ : ∃ y, y = σ1.seth gIN (pre.length + PrimAsm.ParseNat.stp true *
        (RepairRepresentation.natWord x).length) := ⟨_, rfl⟩
    rw [← hσ2] at s2
    obtain ⟨τ, e, t1, t2, t3, t4, t5, t6⟩ := skipNats_spec xs (pre ++ marks (RepairRepresentation.natWord x)) rest σ2
      (by rw [hσ2, hσ1]; show σ.st gIN = _; rw [hst]; simp [List.flatMap_cons, List.append_assoc])
      (by rw [hσ2]; simp [WState.seth, PrimAsm.ParseNat.stp])
      (by rw [hσ2, hσ1]; simp [WState.seth, WState.setv, hj])
      (by rw [hσ2, hσ1]; simp [WState.seth, WState.setv, Function.update_apply, fJ, hf])
      (by rw [hσ2, hσ1]; simp [WState.seth, WState.setv, Function.update_apply, cJ, hc])
      (fun y hy => hx y (by simp [hy])) (by simp at hl; omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hj]; simp) (WExec.seq s1 s2) e) (by simp [skipCost]; omega), ?_, ?_,
      ?_, t4, ?_, ?_⟩
    · rw [t1, hσ2, hσ1]; rfl
    · rw [t2]; simp [List.flatMap_cons]; ring
    · intro i hi; rw [t3 i hi, hσ2, hσ1]; simp [WState.seth, WState.setv, Function.update_apply, hi]
    · intro r hr; rw [t5 r hr, hσ2, hσ1]; simp [WState.seth, WState.setv, Function.update_apply, hr]
    · rw [t6, hσ2, hσ1]; rfl

/-! ## Emitting framed words at a stream's end -/

/-- The appended word so far: `O` holds `σ0`'s content and `w`, its head at the end; the other streams unchanged, the
registers outside `rs` unchanged. -/
structure App (O : Fin (GS + 1)) (rs : Fin GR → Prop) (σ0 σ : WState GS GR) (w : List Bool) : Prop where
  st : σ.st O = σ0.st O ++ w
  sh : σ.sh O = (σ.st O).length
  frS : ∀ i, i ≠ O → σ.st i = σ0.st i ∧ σ.sh i = σ0.sh i
  frR : ∀ r, ¬ rs r → σ.val r = σ0.val r
  cell : σ.cell = σ0.cell

theorem App.trans {O : Fin (GS + 1)} {rs : Fin GR → Prop} {σ0 σ τ : WState GS GR} {w w' : List Bool}
    (h1 : App O rs σ0 σ w) (h2 : App O rs σ τ w') : App O rs σ0 τ (w ++ w') :=
  ⟨by rw [h2.st, h1.st, List.append_assoc], h2.sh, fun i hi => ⟨(h2.frS i hi).1.trans (h1.frS i hi).1,
    (h2.frS i hi).2.trans (h1.frS i hi).2⟩, fun r hr => (h2.frR r hr).trans (h1.frR r hr), h2.cell.trans h1.cell⟩

theorem App.refl (O : Fin (GS + 1)) (rs : Fin GR → Prop) (σ : WState GS GR) (hO : σ.sh O = (σ.st O).length) :
    App O rs σ σ [] :=
  ⟨by simp, hO, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩

/-- The registers of the emitters. -/
def emR (r : Fin GR) : Prop := r = rJ ∨ r = rTv ∨ r = rBc ∨ r = rOc ∨ r = rFf ∨ r = rCc ∨ r = rPp ∨ r = rTt ∨
  r = rTmp

theorem oJ : rOc ≠ rJ := by decide

/-- One pair of zeros. -/
def zStep (O : Fin (GS + 1)) : WM GS GR :=
  .seq (.dec rJ) (.seq (emitW O true) (.seq (emitW O false) (.seq (.inc rOc) (.inc rOc))))

/-- **`m` framed zeros** appended to `O` (`m` in `rJ`, counted in `rOc`). -/
def zerosW (O : Fin (GS + 1)) : WM GS GR := .whr rJ (zStep O)

theorem zStep_spec (O : Fin (GS + 1)) (σ : WState GS GR) (hj : 1 ≤ σ.val rJ) (hjc : σ.val rJ ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val rOc + 2 ≤ cap) :
    ∃ τ, WExec cap (zStep O) σ τ 18 ∧ App O emR σ τ [true, false] ∧ τ.val rJ = σ.val rJ - 1 ∧
      τ.val rOc = σ.val rOc + 2 ∧ (∀ r, r ≠ rJ → r ≠ rOc → τ.val r = σ.val r) := by
  have s1 := WExec.dec (cap := cap) rJ σ hjc
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rJ (σ.val rJ - 1) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have hO1 : σ1.sh O = (σ1.st O).length := by rw [hσ1]; exact hO
  have s2 := emitW_spec (cap := cap) O true σ1 hO1
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = (σ1.sets O (σ1.st O ++ [true])).seth O ((σ1.st O).length + 1) := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have hO2 : σ2.sh O = (σ2.st O).length := by rw [hσ2]; simp [WState.sets, WState.seth]
  have s3 := emitW_spec (cap := cap) O false σ2 hO2
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ2.sets O (σ2.st O ++ [false])).seth O ((σ2.st O).length + 1) := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have v3 : σ3.val = σ1.val := by rw [hσ3, hσ2]; rfl
  have c3 : σ3.cell = σ.cell := by rw [hσ3, hσ2, hσ1]; rfl
  have st3 : σ3.st O = σ.st O ++ [true, false] := by
    rw [hσ3, hσ2, hσ1]; simp [WState.sets, WState.seth, WState.setv, List.append_assoc]
  have sh3 : σ3.sh O = (σ3.st O).length := by rw [hσ3]; simp [WState.sets, WState.seth]
  have fr3 : ∀ i, i ≠ O → σ3.st i = σ.st i ∧ σ3.sh i = σ.sh i := by
    intro i hi; rw [hσ3, hσ2, hσ1]; simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hi]
  have vo : σ3.val rOc = σ.val rOc := by rw [v3, hσ1]; simp [WState.setv, Function.update_apply, oJ]
  have s4 := WExec.inc (cap := cap) rOc σ3 (by rw [vo]; omega)
  have s5 := WExec.inc (cap := cap) rOc (σ3.setv rOc (σ3.val rOc + 1)) (by simp [WState.setv, vo]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) (by omega),
    ⟨by simp [WState.setv, st3], by simp [WState.setv, sh3], fun i hi => by simp [WState.setv, fr3 i hi],
      fun r hr => ?_, by simp [WState.setv, c3]⟩, ?_, ?_, fun r h1 h2 => ?_⟩
  · have h1 : r ≠ rJ := fun e => hr (Or.inl e)
    have h2 : r ≠ rOc := fun e => hr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    simp [WState.setv, Function.update_apply, h2, v3, hσ1, h1]
  · simp [WState.setv, Function.update_apply, Ne.symm oJ, v3, hσ1]
  · simp [WState.setv, Function.update_apply, vo]
  · simp [WState.setv, Function.update_apply, h2, v3, hσ1, h1]

theorem zerosW_spec (O : Fin (GS + 1)) (m : ℕ) : ∀ (σ : WState GS GR), σ.val rJ = m →
    σ.sh O = (σ.st O).length → σ.val rOc + 2 * m ≤ cap → m ≤ cap →
    ∃ τ, WExec cap (zerosW O) σ τ (m * 20 + 1) ∧ App O emR σ τ (frameP (List.replicate m false)) ∧
      τ.val rJ = 0 ∧ τ.val rOc = σ.val rOc + 2 * m ∧ (∀ r, r ≠ rJ → r ≠ rOc → τ.val r = σ.val r) := by
  induction m with
  | zero =>
    intro σ hj hO _ _
    exact ⟨σ, WExec.whrF hj, App.refl O emR σ hO, hj, by simp, fun _ _ _ => rfl⟩
  | succ m ih =>
    intro σ hj hO hc hm
    obtain ⟨τ1, e1, a1, j1, o1, f1⟩ := zStep_spec cap O σ (by omega) (by omega) hO (by omega)
    obtain ⟨τ, e2, a2, j2, o2, f2⟩ := ih τ1 (by rw [j1, hj]; rfl) a1.sh (by rw [o1]; omega) (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hj]; omega) e1 e2) (by omega), ?_, j2, by rw [o2, o1]; ring,
      fun r h1 h2 => (f2 r h1 h2).trans (f1 r h1 h2)⟩
    have e : frameP (List.replicate (m + 1) false) = [true, false] ++ frameP (List.replicate m false) := by
      simp [List.replicate_succ]
    rw [e]
    exact a1.trans a2

/-! ## One block of the offset -/

theorem oneHot_succ (m x : ℕ) :
    FinalPass.Sample.oneHot (m + 1) x = decide (x = 1) :: FinalPass.Sample.oneHot m (x - 1) := by
  unfold FinalPass.Sample.oneHot
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, List.cons.injEq, true_and]
  congr 1
  funext k
  apply decide_eq_decide.mpr
  omega

theorem bT : rBc ≠ rTv := by decide
theorem oT : rOc ≠ rTv := by decide
theorem oB : rOc ≠ rBc := by decide

/-- One bit of a block: `[x = 1]` for the count `x` in `rTv`, the count stepped down. -/
def ohStep (O : Fin (GS + 1)) : WM GS GR :=
  .seq (.dec rBc) (.seq (emitW O true) (.seq (.ifr rTv (.seq (.dec rTv) (.ifr rTv (emitW O false) (emitW O true)))
    (emitW O false)) (.seq (.inc rOc) (.inc rOc))))

/-- **One block**: `frameP (oneHot m x)` appended (`m` in `rBc`, `x` in `rTv`). -/
def oneHotW (O : Fin (GS + 1)) : WM GS GR := .whr rBc (ohStep O)

theorem ohStep_spec (O : Fin (GS + 1)) (x : ℕ) (σ : WState GS GR) (hb : 1 ≤ σ.val rBc) (hbc : σ.val rBc ≤ cap)
    (hx : σ.val rTv = x) (hxc : x ≤ cap) (hO : σ.sh O = (σ.st O).length) (hc : σ.val rOc + 2 ≤ cap) :
    ∃ τ, WExec cap (ohStep O) σ τ 22 ∧ App O emR σ τ [true, decide (x = 1)] ∧ τ.val rBc = σ.val rBc - 1 ∧
      τ.val rTv = x - 1 ∧ τ.val rOc = σ.val rOc + 2 ∧
      (∀ r, r ≠ rBc → r ≠ rTv → r ≠ rOc → τ.val r = σ.val r) := by
  have s1 := WExec.dec (cap := cap) rBc σ hbc
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rBc (σ.val rBc - 1) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have hO1 : σ1.sh O = (σ1.st O).length := by rw [hσ1]; exact hO
  have s2 := emitW_spec (cap := cap) O true σ1 hO1
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = (σ1.sets O (σ1.st O ++ [true])).seth O ((σ1.st O).length + 1) := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have hO2 : σ2.sh O = (σ2.st O).length := by rw [hσ2]; simp [WState.sets, WState.seth]
  have v2 : σ2.val = σ1.val := by rw [hσ2]; rfl
  have x2 : σ2.val rTv = x := by rw [v2, hσ1]; simp [WState.setv, Function.update_apply, Ne.symm bT, hx]
  -- the bit
  obtain ⟨σ3, s3, st3, sh3, fr3, v3, c3⟩ : ∃ σ3, WExec cap (.ifr rTv (.seq (.dec rTv) (.ifr rTv (emitW O false)
      (emitW O true))) (emitW O false)) σ2 σ3 8 ∧ σ3.st O = σ2.st O ++ [decide (x = 1)] ∧
      σ3.sh O = (σ3.st O).length ∧ (∀ i, i ≠ O → σ3.st i = σ2.st i ∧ σ3.sh i = σ2.sh i) ∧
      σ3.val = Function.update σ2.val rTv (x - 1) ∧ σ3.cell = σ2.cell := by
    rcases Nat.lt_or_ge x 1 with h0 | h1
    · have hx0 : x = 0 := by omega
      have e := emitW_spec (cap := cap) O false σ2 hO2
      refine ⟨_, WExec.mono (WExec.ifrF (by rw [x2]; omega) e) (by omega), by simp [WState.sets, WState.seth, hx0],
        by simp [WState.sets, WState.seth], fun i hi => by simp [WState.sets, WState.seth, Function.update_apply, hi],
        ?_, rfl⟩
      simp only [WState.sets, WState.seth]
      rw [hx0]
      funext r
      by_cases hr : r = rTv
      · subst hr; simp [x2, hx0]
      · simp [Function.update_apply, hr]
    · have d := WExec.dec (cap := cap) rTv σ2 (by rw [x2]; exact hxc)
      obtain ⟨σd, hσd⟩ : ∃ y, y = σ2.setv rTv (σ2.val rTv - 1) := ⟨_, rfl⟩
      rw [← hσd] at d
      have hOd : σd.sh O = (σd.st O).length := by rw [hσd]; exact hO2
      have xd : σd.val rTv = x - 1 := by rw [hσd]; simp [WState.setv, x2]
      by_cases hx1 : x = 1
      · have e := emitW_spec (cap := cap) O true σd hOd
        refine ⟨_, WExec.mono (WExec.ifrT (by rw [x2]; omega) (WExec.seq d (WExec.ifrF (by rw [xd, hx1]) e)))
          (by omega), by rw [hσd]; simp [WState.sets, WState.seth, WState.setv, hx1], by simp [WState.sets, WState.seth],
          fun i hi => by rw [hσd]; simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hi], ?_, ?_⟩
        · rw [hσd]; simp [WState.sets, WState.seth, WState.setv, x2]
        · rw [hσd]; rfl
      · have e := emitW_spec (cap := cap) O false σd hOd
        refine ⟨_, WExec.mono (WExec.ifrT (by rw [x2]; omega) (WExec.seq d (WExec.ifrT (by rw [xd]; omega) e)))
          (by omega), by rw [hσd]; simp [WState.sets, WState.seth, WState.setv, hx1], by simp [WState.sets, WState.seth],
          fun i hi => by rw [hσd]; simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hi], ?_, ?_⟩
        · rw [hσd]; simp [WState.sets, WState.seth, WState.setv, x2]
        · rw [hσd]; rfl
  have vo : σ3.val rOc = σ.val rOc := by
    rw [v3]; simp [Function.update_apply, oT, v2, hσ1, oB]
  have s4 := WExec.inc (cap := cap) rOc σ3 (by rw [vo]; omega)
  have s5 := WExec.inc (cap := cap) rOc (σ3.setv rOc (σ3.val rOc + 1)) (by simp [WState.setv, vo]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) (by omega),
    ⟨?_, ?_, ?_, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩
  · simp only [WState.setv]; rw [st3, hσ2, hσ1]; simp [WState.sets, WState.seth, WState.setv, List.append_assoc]
  · simp only [WState.setv]; exact sh3
  · intro i hi; simp only [WState.setv]; rw [(fr3 i hi).1, (fr3 i hi).2, hσ2, hσ1]
    simp [WState.sets, WState.seth, WState.setv, Function.update_apply, hi]
  · have h1 : r ≠ rBc := fun e => hr (Or.inr (Or.inr (Or.inl e)))
    have h2 : r ≠ rTv := fun e => hr (Or.inr (Or.inl e))
    have h3 : r ≠ rOc := fun e => hr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    simp [WState.setv, Function.update_apply, h3, v3, h2, v2, hσ1, h1]
  · simp only [WState.setv]; rw [c3, hσ2, hσ1]; rfl
  · simp [WState.setv, Function.update_apply, oB, Ne.symm oB, v3, bT, Ne.symm bT, v2, hσ1]
  · simp [WState.setv, Function.update_apply, oT, Ne.symm oT, v3]
  · simp [WState.setv, Function.update_apply, vo]
  · simp [WState.setv, Function.update_apply, h3, v3, h2, v2, hσ1, h1]

theorem oneHotW_spec (O : Fin (GS + 1)) (m : ℕ) : ∀ (x : ℕ) (σ : WState GS GR), σ.val rBc = m → σ.val rTv = x →
    σ.sh O = (σ.st O).length → σ.val rOc + 2 * m ≤ cap → m ≤ cap → x ≤ cap →
    ∃ τ, WExec cap (oneHotW O) σ τ (m * 24 + 1) ∧ App O emR σ τ (frameP (FinalPass.Sample.oneHot m x)) ∧
      τ.val rBc = 0 ∧ τ.val rTv = x - m ∧ τ.val rOc = σ.val rOc + 2 * m ∧
      (∀ r, r ≠ rBc → r ≠ rTv → r ≠ rOc → τ.val r = σ.val r) := by
  induction m with
  | zero =>
    intro x σ hb hx hO _ _ _
    exact ⟨σ, WExec.whrF hb, by simpa [FinalPass.Sample.oneHot] using App.refl O emR σ hO, hb, by simp [hx], by simp,
      fun _ _ _ _ => rfl⟩
  | succ m ih =>
    intro x σ hb hx hO hc hm hxc
    obtain ⟨τ1, e1, a1, b1, x1, o1, f1⟩ := ohStep_spec cap O x σ (by omega) (by omega) hx hxc hO (by omega)
    obtain ⟨τ, e2, a2, b2, x2, o2, f2⟩ := ih (x - 1) τ1 (by rw [b1, hb]; rfl) x1 a1.sh (by rw [o1]; omega) (by omega)
      (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hb]; omega) e1 e2) (by omega), ?_, b2, by rw [x2]; omega,
      by rw [o2, o1]; ring, fun r h1 h2 h3 => (f2 r h1 h2 h3).trans (f1 r h1 h2 h3)⟩
    rw [oneHot_succ, frameP_cons]
    exact a1.trans a2

/-! ## The offset's blocks from the codes -/

/-- The register holding `b` (PA's star register `5`, `RD 1`). -/
def bReg : Fin GR := 5

/-- The registers the code loop uses. -/
def tR (r : Fin GR) : Prop := r = rJ ∨ r = rTv ∨ r = rBc ∨ r = rOc

/-- One code: read it, copy `b`, emit its block. -/
def tStep : WM GS GR :=
  .seq (.dec rJ) (.seq (PrimAsm.ParseNat.readNatM true gIN rFf rCc rTv rPp rTt)
    (.seq (FinalPass.Hash4.wcopyR bReg rBc rTmp) (oneHotW sOFF)))

/-- **The code loop**: every code's block of the offset. -/
def transLoop : WM GS GR := .whr rJ tStep

/-- One code's cost. -/
def tCost (b t : ℕ) : ℕ := 1 + 1 + ((natBitLength t + 2) * (40 * 2 ^ natBitLength t + 40) + 1 + (18 * b + 3 + 1 +
  (b * 24 + 1))) + 2

/-- The code loop's cost. -/
def transCost (b : ℕ) (ts : List ℕ) : ℕ := (ts.map (tCost b)).sum + 1

/-- The code loop's state: the blocks so far appended to `sOFF`, the request's head past the codes read. -/
structure TAt (σ0 σ : WState GS GR) (w : List Bool) (hIN : ℕ) (j oc : ℕ) : Prop where
  stO : σ.st sOFF = σ0.st sOFF ++ w
  shO : σ.sh sOFF = (σ.st sOFF).length
  stI : σ.st gIN = σ0.st gIN
  shI : σ.sh gIN = hIN
  frS : ∀ i, i ≠ sOFF → i ≠ gIN → σ.st i = σ0.st i ∧ σ.sh i = σ0.sh i
  vJ : σ.val rJ = j
  vTv : σ.val rTv = 0
  vBc : σ.val rBc = 0
  vOc : σ.val rOc = oc
  frR : ∀ r, ¬ tR r → σ.val r = σ0.val r
  cell : σ.cell = σ0.cell

theorem transLoop_spec (b : ℕ) (σ0 : WState GS GR) (hb : σ0.val bReg = b) (hf : σ0.val rFf = 0)
    (hc : σ0.val rCc = 0) (hp : σ0.val rPp = 0) (ht : σ0.val rTt = 0) (hm : σ0.val rTmp = 0) (hbc : b ≤ cap) :
    ∀ (ts : List ℕ) (pre rest : List Bool) (σ : WState GS GR) (w : List Bool) (oc : ℕ),
      σ.st gIN = pre ++ marks (ts.flatMap RepairRepresentation.natWord) ++ rest →
      TAt σ0 σ w pre.length ts.length oc → (∀ t ∈ ts, t ≤ b) → (∀ t ∈ ts, 2 ^ (natBitLength t + 1) ≤ cap) →
      oc + 2 * b * ts.length ≤ cap → ts.length ≤ cap →
      ∃ τ, WExec cap transLoop σ τ (transCost b ts) ∧
        TAt σ0 τ (w ++ frameP (ts.flatMap (FinalPass.Sample.oneHot b)))
          (pre.length + 2 * (ts.flatMap RepairRepresentation.natWord).length) 0 (oc + 2 * b * ts.length)
  | [], pre, rest, σ, w, oc, hst, h, _, _, _, _ => by
    refine ⟨σ, WExec.mono (WExec.whrF h.vJ) (by simp [transCost]), ?_⟩
    simpa using h
  | t :: ts, pre, rest, σ, w, oc, hst, h, htb, htc, hoc, hl => by
    have hJT : rJ ≠ rTv := by decide
    have hJB : rJ ≠ rBc := by decide
    have hJO : rJ ≠ rOc := by decide
    -- the count
    have s1 := WExec.dec (cap := cap) rJ σ (by rw [h.vJ]; exact hl)
    obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rJ (σ.val rJ - 1) := ⟨_, rfl⟩
    rw [← hσ1] at s1
    have r1 : ∀ r, r ≠ rJ → σ1.val r = σ.val r := fun r hr => by
      rw [hσ1]; simp [WState.setv, Function.update_apply, hr]
    have z1 : ∀ r, ¬ tR r → σ1.val r = σ0.val r := fun r hr => by
      rw [r1 r (fun e => hr (Or.inl e)), h.frR r hr]
    -- the code
    have s2 := PrimAsm.ParseNat.readNatM_spec cap true gIN rFf rCc rTv rPp rTt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t pre
      (marks (ts.flatMap RepairRepresentation.natWord) ++ rest) σ1
      (by rw [hσ1]; show σ.st gIN = _; rw [hst]; simp [PrimAsm.ParseNat.enc, List.flatMap_cons, List.append_assoc])
      (by rw [hσ1]; exact h.shI) (by rw [z1 _ (by simp [tR]; decide), hf]) (by rw [z1 _ (by simp [tR]; decide), hc])
      (by rw [z1 _ (by simp [tR]; decide), hp]) (by rw [z1 _ (by simp [tR]; decide), ht])
      (by rw [r1 _ (Ne.symm hJT), h.vTv]; simpa using htc t (by simp))
    rw [r1 _ (Ne.symm hJT), h.vTv, Nat.zero_add] at s2
    obtain ⟨σ2, hσ2⟩ : ∃ y, y = (σ1.seth gIN (pre.length + PrimAsm.ParseNat.stp true *
        (RepairRepresentation.natWord t).length)).setv rTv t := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have r2 : ∀ r, r ≠ rTv → σ2.val r = σ1.val r := fun r hr => by
      rw [hσ2]; simp [WState.seth, WState.setv, Function.update_apply, hr]
    -- the width
    have s3 := FinalPass.Hash4.wcopyR_spec cap bReg rBc rTmp (by decide) (by decide) (by decide) σ2
      (by rw [r2 _ (by decide), r1 _ (by decide), h.vBc]) (by rw [r2 _ (by decide), z1 _ (by simp [tR]; decide), hm])
      (by rw [r2 _ (by decide), z1 _ (by simp [tR]; decide), hb]; exact hbc)
    rw [r2 _ (by decide), z1 _ (by simp [tR]; decide), hb] at s3
    obtain ⟨σ3, hσ3⟩ : ∃ y, y = σ2.setv rBc b := ⟨_, rfl⟩
    rw [← hσ3] at s3
    have r3 : ∀ r, r ≠ rBc → σ3.val r = σ2.val r := fun r hr => by
      rw [hσ3]; simp [WState.setv, Function.update_apply, hr]
    have sh3 : σ3.sh sOFF = (σ3.st sOFF).length := by
      rw [hσ3, hσ2, hσ1]; simp [WState.setv, WState.seth, Function.update_apply, show sOFF ≠ gIN by decide]
      exact h.shO
    -- the block
    obtain ⟨σ4, e4, a4, b4, x4, o4, f4⟩ := oneHotW_spec cap sOFF b t σ3 (by rw [hσ3]; simp [WState.setv])
      (by rw [r3 _ (by decide), hσ2]; simp [WState.setv]) sh3
      (by rw [r3 _ (by decide), r2 _ (by decide), r1 _ (by decide), h.vOc]; simp at hoc; nlinarith)
      hbc (le_trans (htb t (by simp)) hbc)
    have htb' : t ≤ b := htb t (by simp)
    -- the invariant
    have hT4 : TAt σ0 σ4 (w ++ frameP (FinalPass.Sample.oneHot b t))
        (pre ++ marks (RepairRepresentation.natWord t)).length ts.length (oc + 2 * b) := by
      refine ⟨?_, a4.sh, ?_, ?_, fun i h1 h2 => ?_, ?_, by rw [x4]; omega, b4, ?_, fun r hr => ?_, ?_⟩
      · rw [a4.st, hσ3, hσ2, hσ1]; simp [WState.setv, WState.seth, h.stO, List.append_assoc]
      · rw [(a4.frS gIN (by decide)).1, hσ3, hσ2, hσ1]; exact h.stI
      · rw [(a4.frS gIN (by decide)).2, hσ3, hσ2, hσ1]; simp [WState.setv, WState.seth, PrimAsm.ParseNat.stp]
      · rw [(a4.frS i h1).1, (a4.frS i h1).2, hσ3, hσ2, hσ1]
        simp [WState.setv, WState.seth, Function.update_apply, h2]
        exact h.frS i h1 h2
      · rw [f4 _ (by decide) (by decide) (by decide), r3 _ (by decide), r2 _ (by decide), hσ1]
        simp [WState.setv, h.vJ]
      · rw [o4, r3 _ (by decide), r2 _ (by decide), r1 _ (by decide), h.vOc]
      · have hB : r ≠ rBc := fun e => hr (Or.inr (Or.inr (Or.inl e)))
        have hT : r ≠ rTv := fun e => hr (Or.inr (Or.inl e))
        have hO : r ≠ rOc := fun e => hr (Or.inr (Or.inr (Or.inr e)))
        rw [f4 r hB hT hO, r3 r hB, r2 r hT]
        exact z1 r hr
      · rw [a4.cell, hσ3, hσ2, hσ1]; exact h.cell
    obtain ⟨τ, e5, h5⟩ := transLoop_spec b σ0 hb hf hc hp ht hm hbc ts (pre ++ marks (RepairRepresentation.natWord t))
      rest σ4 _ _ (by rw [(a4.frS gIN (by decide)).1, hσ3, hσ2, hσ1]; show σ.st gIN = _; rw [hst]
                      simp [List.flatMap_cons, List.append_assoc])
      hT4 (fun y hy => htb y (by simp [hy]))
      (fun y hy => htc y (by simp [hy])) (by simp at hoc; nlinarith) (by simp at hl; omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [h.vJ]; simp) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 e4))) e5)
      (by simp [transCost, tCost]; omega), ?_⟩
    have e1 : w ++ frameP (FinalPass.Sample.oneHot b t) ++ frameP (ts.flatMap (FinalPass.Sample.oneHot b)) =
        w ++ frameP ((t :: ts).flatMap (FinalPass.Sample.oneHot b)) := by
      simp [frameP, List.flatMap_cons, List.flatMap_append, List.append_assoc]
    have e2 : (pre ++ marks (RepairRepresentation.natWord t)).length +
        2 * (ts.flatMap RepairRepresentation.natWord).length =
        pre.length + 2 * ((t :: ts).flatMap RepairRepresentation.natWord).length := by
      simp [List.flatMap_cons]; ring
    have e3 : oc + 2 * b + 2 * b * ts.length = oc + 2 * b * (t :: ts).length := by simp; ring
    rw [e1, e2, e3] at h5
    exact h5

end Gen

end NearCubicWires.WireExponent3_5.PrimT.Flips
