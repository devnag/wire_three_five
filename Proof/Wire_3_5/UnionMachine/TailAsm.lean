import Proof.Wire_3_5.Primitive.SeedFix.C4Iface
import Proof.Wire_3_5.Primitive.SeedFix.TabDock
import Proof.Wire_3_5.Primitive.SeedFix.TabScan

/-! # C6 tail, item 1: the compiler's input assembler

"For each candidate child prefix, print its signed equation expression, reduce modulo the chosen power of two at each
column, and sum the recovered integers" (P3:3035-3037); the expression is the input of `alg:compiler`, whose
"construction takes (input description size + 𝒮) poly(n) deterministic bit operations" (P3:1903-1904). The compiler's
machine reads its request as one framed record of framed fields; per child, the expression field is the enumeration's
raw `exprWord V`, followed by any tail. This module builds the **`AsmStage`** (`PrimT.C4Iface`):
* `dm w = frameP (frameP w)`: each bit `b` as the cells `T T T b` (the frame of a frame, without its end markers);
* word programs that parse `exprWord V` by its term, factor and monomial record loops, stop at its final `false` (so
  the tail is never read), and append `dm` of what they read (**`cp_mexpr`**);
* `asmW`: `frameP PRE`, `dm (exprWord V)`, `[T, F]`, `frameP POST`, `F` on the output, which is
  `frame (PRE ++ frame (exprWord V) ++ POST)` (**`asm_exec`**);
* **`asmStage`**: the cell written, then the word program as a Step (`wm_step`), within `asmCost`.

Paper quantity of the main type: the compiler's input `frame (PRE ++ frame (exprWord V) ++ POST)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.TailAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord recW monoBits coefWord termWord exprWord)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.PrimT.C4Iface (AsmStage asmIn asmCost)

/-! ## Words -/

theorem rd0 (pre l : List Bool) : readTapeBit (pre ++ l) pre.length = l.getD 0 false := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

theorem fp_cons (b : Bool) (y : List Bool) : frameP (b :: y) = true :: b :: frameP y := by simp [frameP]

theorem fp_app (a b : List Bool) : frameP (a ++ b) = frameP a ++ frameP b := by simp [frameP]

theorem fpl (y : List Bool) : (frameP y).length = 2 * y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => simp only [fp_cons, List.length_cons, ih] <;> omega

/-- Each bit `b` as the four cells `T T T b`: the frame of a frame, without its end markers. -/
def dm (w : List Bool) : List Bool := frameP (frameP w)

@[simp] theorem dm_nil : dm [] = [] := rfl

@[simp] theorem dm_cons (b : Bool) (w : List Bool) : dm (b :: w) = true :: true :: true :: b :: dm w := by
  simp only [dm, fp_cons]

@[simp] theorem dm_app (a b : List Bool) : dm (a ++ b) = dm a ++ dm b := by simp only [dm, fp_app]

/-! ## Reading one stream, appending to another -/

section CpSec
variable {ns nr : ℕ}

/-- `τ` is `σ` with the word `u` read on `S` (its head `|u|` cells on, its cells kept) and `v` appended to `O` (its
head at the end); every other stream, the registers and the cell kept. -/
structure Cp (S O : Fin (ns + 1)) (σ τ : WState ns nr) (u v : List Bool) : Prop where
  st : τ.st S = σ.st S
  sh : τ.sh S = σ.sh S + u.length
  out : τ.st O = σ.st O ++ v
  endO : τ.sh O = (τ.st O).length
  same : ∀ j, j ≠ S → j ≠ O → Same σ τ j
  val : τ.val = σ.val
  cell : τ.cell = σ.cell

theorem Cp.refl (S O : Fin (ns + 1)) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) : Cp S O σ σ [] [] :=
  ⟨rfl, by simp, by simp, hO, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩

theorem Cp.tr {S O : Fin (ns + 1)} {σ τ ρ : WState ns nr} {u v u' v' U W : List Bool} (h1 : Cp S O σ τ u v)
    (h2 : Cp S O τ ρ u' v') (eu : u ++ u' = U) (ev : v ++ v' = W) : Cp S O σ ρ U W := by
  subst eu ev
  exact ⟨h2.st.trans h1.st, by rw [h2.sh, h1.sh, List.length_append, Nat.add_assoc],
    by rw [h2.out, h1.out, List.append_assoc], h2.endO, fun j a b => (h1.same j a b).trans' (h2.same j a b),
    h2.val.trans h1.val, h2.cell.trans h1.cell⟩

end CpSec

section Copy
variable {ns nr : ℕ} (cap : ℕ)

theorem cp_emit (S O : Fin (ns + 1)) (hSO : S ≠ O) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (emitW O b) σ τ 3 ∧ Cp S O σ τ [] [b] := by
  obtain ⟨τ, s, e, eh, o, v, c⟩ := emit_facts cap O b σ hO
  exact ⟨τ, s, ⟨(o S hSO).1, by simp [(o S hSO).2], e, eh, fun j _ hj => o j hj, v, c⟩⟩

theorem cp_fwd (S O : Fin (ns + 1)) (hSO : S ≠ O) (x : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (.fwd S) σ τ 1 ∧ Cp S O σ τ [x] [] := by
  obtain ⟨τ, s, e, eh, o, v, c⟩ := fwd_facts cap S σ
  have hOS : O ≠ S := fun h => hSO h.symm
  exact ⟨τ, s, ⟨e, by simp [eh], by simp [(o O hOS).1], by rw [(o O hOS).1, (o O hOS).2, hO],
    fun j hj _ => o j hj, v, c⟩⟩

/-- Copy the scanned bit to the end of `O`, then step past it. -/
def rbW (S O : Fin (ns + 1)) : WM ns nr := .seq (.ifs S (emitW O true) (emitW O false)) (.fwd S)

theorem cp_rb (S O : Fin (ns + 1)) (hSO : S ≠ O) (b : Bool) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (b :: rest)) (hh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (rbW S O) σ τ 6 ∧ Cp S O σ τ [b] [b] := by
  have hb : wbit σ S = b := by simp [wbit, hS, hh, rd0]
  obtain ⟨σ1, s1, c1⟩ := cp_emit cap S O hSO b σ hO
  obtain ⟨τ, s2, c2⟩ := cp_fwd cap S O hSO b σ1 c1.endO
  have s1' : WExec cap (.ifs S (emitW O true) (emitW O false)) σ σ1 4 := by
    cases b
    · exact WExec.ifsF hb s1
    · exact WExec.ifsT hb s1
  exact ⟨τ, WExec.seq s1' s2, c1.tr c2 (by simp) (by simp)⟩

/-- Copy the scanned bit `b` to the end of `O` as the cells `T T T b`, then step past it. -/
def mbW (S O : Fin (ns + 1)) : WM ns nr :=
  .seq (emitW O true) (.seq (emitW O true) (.seq (emitW O true) (rbW S O)))

theorem cp_mb (S O : Fin (ns + 1)) (hSO : S ≠ O) (b : Bool) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (b :: rest)) (hh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (mbW S O) σ τ 18 ∧ Cp S O σ τ [b] (dm [b]) := by
  obtain ⟨σ1, s1, c1⟩ := cp_emit cap S O hSO true σ hO
  obtain ⟨σ2, s2, c2⟩ := cp_emit cap S O hSO true σ1 c1.endO
  obtain ⟨σ3, s3, c3⟩ := cp_emit cap S O hSO true σ2 c2.endO
  have c13 := (c1.tr c2 rfl rfl).tr c3 rfl rfl
  obtain ⟨τ, s4, c4⟩ := cp_rb cap S O hSO b pre rest σ3 (by simp [c13.st, hS]) (by simp [c13.sh, hh]) c3.endO
  exact ⟨τ, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), c13.tr c4 (by simp) (by simp)⟩

/-- Copy the pairs `T b` of a framed word, up to its end marker, to the end of `O`. -/
def pairsW (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (rbW S O) (rbW S O))

theorem cp_pairs (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (frameP y ++ (false :: rest)) →
      σ.sh S = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (pairsW S O) σ τ (8 * (frameP y).length + 1) ∧ Cp S O σ τ (frameP y) (frameP y)
  | [], pre, σ, hS, hh, hO => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd0]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), Cp.refl S O σ hO⟩
  | b :: y, pre, σ, hS, hh, hO => by
    have hS1 : σ.st S = pre ++ (true :: (b :: (frameP y ++ (false :: rest)))) := by simp [hS, fp_cons]
    have hw : wbit σ S = true := by simp [wbit, hS1, hh, rd0]
    obtain ⟨σ1, s1, c1⟩ := cp_rb cap S O hSO true pre _ σ hS1 hh hO
    obtain ⟨σ2, s2, c2⟩ := cp_rb cap S O hSO b (pre ++ [true]) (frameP y ++ (false :: rest)) σ1
      (by simp [c1.st, hS1]) (by simp [c1.sh, hh]) c1.endO
    have c12 := c1.tr c2 rfl rfl
    obtain ⟨τ, s3, c3⟩ := cp_pairs S O hSO rest y (pre ++ [true, b]) σ2 (by simp [c12.st, hS1])
      (by simp [c12.sh, hh]) c2.endO
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, c12.tr c3 (by simp [fp_cons]) (by simp [fp_cons])⟩
    simp only [fp_cons, List.length_cons] <;> omega

/-- The pairs `T b` of a framed word, up to its end marker, each cell as `dm`. -/
def mpairsW (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (mbW S O) (mbW S O))

theorem cp_mpairs (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (frameP y ++ (false :: rest)) →
      σ.sh S = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (mpairsW S O) σ τ (24 * (frameP y).length + 1) ∧ Cp S O σ τ (frameP y) (dm (frameP y))
  | [], pre, σ, hS, hh, hO => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd0]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), Cp.refl S O σ hO⟩
  | b :: y, pre, σ, hS, hh, hO => by
    have hS1 : σ.st S = pre ++ (true :: (b :: (frameP y ++ (false :: rest)))) := by simp [hS, fp_cons]
    have hw : wbit σ S = true := by simp [wbit, hS1, hh, rd0]
    obtain ⟨σ1, s1, c1⟩ := cp_mb cap S O hSO true pre _ σ hS1 hh hO
    obtain ⟨σ2, s2, c2⟩ := cp_mb cap S O hSO b (pre ++ [true]) (frameP y ++ (false :: rest)) σ1
      (by simp [c1.st, hS1]) (by simp [c1.sh, hh]) c1.endO
    have c12 := c1.tr c2 rfl rfl
    obtain ⟨τ, s3, c3⟩ := cp_mpairs S O hSO rest y (pre ++ [true, b]) σ2 (by simp [c12.st, hS1])
      (by simp [c12.sh, hh]) c2.endO
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, c12.tr c3 (by simp [fp_cons]) (by simp [fp_cons])⟩
    simp only [fp_cons, List.length_cons] <;> omega

/-- A framed word, each cell as `dm`. -/
def mframeW (S O : Fin (ns + 1)) : WM ns nr := .seq (mpairsW S O) (mbW S O)

theorem cp_mframe (S O : Fin (ns + 1)) (hSO : S ≠ O) (y pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (frame y ++ rest)) (hh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (mframeW S O) σ τ (24 * (frame y).length) ∧ Cp S O σ τ (frame y) (dm (frame y)) := by
  have hS' : σ.st S = pre ++ (frameP y ++ (false :: rest)) := by simp [hS, frame_eq_frameP]
  obtain ⟨σ1, s1, c1⟩ := cp_mpairs cap S O hSO rest y pre σ hS' hh hO
  obtain ⟨τ, s2, c2⟩ := cp_mb cap S O hSO false (pre ++ frameP y) rest σ1 (by simp [c1.st, hS'])
    (by simp [c1.sh, hh]) c1.endO
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) ?_, c1.tr c2 (by rw [frame_eq_frameP]) (by rw [frame_eq_frameP, dm_app])⟩
  rw [frame_eq_frameP, List.length_append, List.length_singleton]; omega

/-- The monomial records `T frame(m)` of a polynomial word, up to its `F`, each cell as `dm`. -/
def mrecsW (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (mbW S O) (mframeW S O))

theorem cp_mrecs (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (ms : List (List ℕ)) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) → σ.sh S = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (mrecsW S O) σ τ (24 * (ms.flatMap recW).length + 1) ∧
        Cp S O σ τ (ms.flatMap recW) (dm (ms.flatMap recW))
  | [], pre, σ, hS, hh, hO => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd0]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), Cp.refl S O σ hO⟩
  | m :: ms, pre, σ, hS, hh, hO => by
    have hS1 : σ.st S = pre ++ (true :: (frame (monoBits m) ++ (ms.flatMap recW ++ (false :: rest)))) := by
      simp [hS, recW]
    have hw : wbit σ S = true := by simp [wbit, hS1, hh, rd0]
    obtain ⟨σ1, s1, c1⟩ := cp_mb cap S O hSO true pre _ σ hS1 hh hO
    obtain ⟨σ2, s2, c2⟩ := cp_mframe cap S O hSO (monoBits m) (pre ++ [true]) (ms.flatMap recW ++ (false :: rest))
      σ1 (by simp [c1.st, hS1]) (by simp [c1.sh, hh]) c1.endO
    have c12 := c1.tr c2 rfl rfl
    obtain ⟨τ, s3, c3⟩ := cp_mrecs S O hSO rest ms (pre ++ recW m) σ2 (by simp [c12.st, hS1, recW])
      (by simp [c12.sh, hh, recW] <;> omega) c2.endO
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, c12.tr c3 (by simp [recW]) (by simp [recW])⟩
    have hl : (recW m).length = (frame (monoBits m)).length + 1 := by simp only [recW, List.length_cons]
    simp only [List.flatMap_cons, List.length_append, hl] <;> omega

/-- A polynomial word, each cell as `dm`. -/
def mpolyW (S O : Fin (ns + 1)) : WM ns nr := .seq (mrecsW S O) (mbW S O)

theorem cp_mpoly (S O : Fin (ns + 1)) (hSO : S ≠ O) (ms : List (List ℕ)) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (polyWord ms ++ rest)) (hh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (mpolyW S O) σ τ (24 * (polyWord ms).length) ∧ Cp S O σ τ (polyWord ms) (dm (polyWord ms)) := by
  have hS' : σ.st S = pre ++ (ms.flatMap recW ++ (false :: rest)) := by simp [hS, polyWord]
  obtain ⟨σ1, s1, c1⟩ := cp_mrecs cap S O hSO rest ms pre σ hS' hh hO
  obtain ⟨τ, s2, c2⟩ := cp_mb cap S O hSO false (pre ++ ms.flatMap recW) rest σ1 (by simp [c1.st, hS'])
    (by simp [c1.sh, hh]) c1.endO
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) ?_, c1.tr c2 rfl (by rw [polyWord, dm_app])⟩
  have e : (polyWord ms).length = (ms.flatMap recW).length + 1 := by
    rw [polyWord, List.length_append, List.length_singleton]
  rw [e]; omega

/-- The factor records `T polyWord(f)` of a term word, up to its `F`, each cell as `dm`. -/
def mfacsW (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (mbW S O) (mpolyW S O))

theorem cp_mfacs (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (fs : List (List (List ℕ))) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ (fs.flatMap (fun f => true :: polyWord f) ++ (false :: rest)) → σ.sh S = pre.length →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (mfacsW S O) σ τ (24 * (fs.flatMap (fun f => true :: polyWord f)).length + 1) ∧
        Cp S O σ τ (fs.flatMap (fun f => true :: polyWord f)) (dm (fs.flatMap (fun f => true :: polyWord f)))
  | [], pre, σ, hS, hh, hO => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd0]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), Cp.refl S O σ hO⟩
  | f :: fs, pre, σ, hS, hh, hO => by
    have hS1 : σ.st S =
        pre ++ (true :: (polyWord f ++ (fs.flatMap (fun f => true :: polyWord f) ++ (false :: rest)))) := by
      simp [hS]
    have hw : wbit σ S = true := by simp [wbit, hS1, hh, rd0]
    obtain ⟨σ1, s1, c1⟩ := cp_mb cap S O hSO true pre _ σ hS1 hh hO
    obtain ⟨σ2, s2, c2⟩ := cp_mpoly cap S O hSO f (pre ++ [true])
      (fs.flatMap (fun f => true :: polyWord f) ++ (false :: rest)) σ1 (by simp [c1.st, hS1]) (by simp [c1.sh, hh])
      c1.endO
    have c12 := c1.tr c2 rfl rfl
    obtain ⟨τ, s3, c3⟩ := cp_mfacs S O hSO rest fs (pre ++ (true :: polyWord f)) σ2 (by simp [c12.st, hS1])
      (by simp [c12.sh, hh] <;> omega) c2.endO
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, c12.tr c3 (by simp) (by simp)⟩
    simp only [List.flatMap_cons, List.length_append, List.length_cons] <;> omega

/-- A term word, each cell as `dm`. -/
def mtermW (S O : Fin (ns + 1)) : WM ns nr := .seq (mframeW S O) (.seq (mfacsW S O) (mbW S O))

theorem cp_mterm (S O : Fin (ns + 1)) (hSO : S ≠ O) (t : ℤ × List (List (List ℕ))) (pre rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = pre ++ (termWord t ++ rest)) (hh : σ.sh S = pre.length)
    (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (mtermW S O) σ τ (24 * (termWord t).length) ∧ Cp S O σ τ (termWord t) (dm (termWord t)) := by
  have hS1 : σ.st S = pre ++ (coefWord t.1 ++ (t.2.flatMap (fun f => true :: polyWord f) ++ (false :: rest))) := by
    simp [hS, termWord]
  obtain ⟨σ1, s1, c1⟩ : ∃ τ, WExec cap (mframeW S O) σ τ (24 * (coefWord t.1).length) ∧
      Cp S O σ τ (coefWord t.1) (dm (coefWord t.1)) :=
    cp_mframe cap S O hSO (decide (t.1 < 0) :: Nat.bits t.1.natAbs) pre _ σ hS1 hh hO
  obtain ⟨σ2, s2, c2⟩ := cp_mfacs cap S O hSO rest t.2 (pre ++ coefWord t.1) σ1 (by simp [c1.st, hS1])
    (by simp [c1.sh, hh]) c1.endO
  have c12 := c1.tr c2 rfl rfl
  obtain ⟨τ, s3, c3⟩ := cp_mb cap S O hSO false (pre ++ (coefWord t.1 ++ t.2.flatMap (fun f => true :: polyWord f)))
    rest σ2 (by simp [c12.st, hS1]) (by simp [c12.sh, hh]) c2.endO
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) ?_, c12.tr c3 (by simp [termWord]) (by simp [termWord])⟩
  have e : (termWord t).length =
      (coefWord t.1).length + ((t.2.flatMap (fun f => true :: polyWord f)).length + 1) := by
    rw [termWord, List.length_append, List.length_append, List.length_singleton]
  rw [e]; omega

/-- The term records `T termWord(t)` of an expression word, up to its `F`, each cell as `dm`. -/
def mtermsW (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (mbW S O) (mtermW S O))

theorem cp_mterms (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (V : List (ℤ × List (List (List ℕ)))) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ (V.flatMap (fun t => true :: termWord t) ++ (false :: rest)) → σ.sh S = pre.length →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (mtermsW S O) σ τ (24 * (V.flatMap (fun t => true :: termWord t)).length + 1) ∧
        Cp S O σ τ (V.flatMap (fun t => true :: termWord t)) (dm (V.flatMap (fun t => true :: termWord t)))
  | [], pre, σ, hS, hh, hO => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd0]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by simp), Cp.refl S O σ hO⟩
  | t :: V, pre, σ, hS, hh, hO => by
    have hS1 : σ.st S =
        pre ++ (true :: (termWord t ++ (V.flatMap (fun t => true :: termWord t) ++ (false :: rest)))) := by
      simp [hS]
    have hw : wbit σ S = true := by simp [wbit, hS1, hh, rd0]
    obtain ⟨σ1, s1, c1⟩ := cp_mb cap S O hSO true pre _ σ hS1 hh hO
    obtain ⟨σ2, s2, c2⟩ := cp_mterm cap S O hSO t (pre ++ [true])
      (V.flatMap (fun t => true :: termWord t) ++ (false :: rest)) σ1 (by simp [c1.st, hS1]) (by simp [c1.sh, hh])
      c1.endO
    have c12 := c1.tr c2 rfl rfl
    obtain ⟨τ, s3, c3⟩ := cp_mterms S O hSO rest V (pre ++ (true :: termWord t)) σ2 (by simp [c12.st, hS1])
      (by simp [c12.sh, hh] <;> omega) c2.endO
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, c12.tr c3 (by simp) (by simp)⟩
    simp only [List.flatMap_cons, List.length_append, List.length_cons] <;> omega

/-- An expression word, each cell as `dm`; it stops at the expression's final `F`. -/
def mexprW (S O : Fin (ns + 1)) : WM ns nr := .seq (mtermsW S O) (mbW S O)

/-- **The expression, marked**: from `exprWord V ++ rest`, `dm (exprWord V)` appended, `rest` never read. -/
theorem cp_mexpr (S O : Fin (ns + 1)) (hSO : S ≠ O) (V : List (ℤ × List (List (List ℕ)))) (pre rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = pre ++ (exprWord V ++ rest)) (hh : σ.sh S = pre.length)
    (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (mexprW S O) σ τ (24 * (exprWord V).length) ∧ Cp S O σ τ (exprWord V) (dm (exprWord V)) := by
  have hS' : σ.st S = pre ++ (V.flatMap (fun t => true :: termWord t) ++ (false :: rest)) := by simp [hS, exprWord]
  obtain ⟨σ1, s1, c1⟩ := cp_mterms cap S O hSO rest V pre σ hS' hh hO
  obtain ⟨τ, s2, c2⟩ := cp_mb cap S O hSO false (pre ++ V.flatMap (fun t => true :: termWord t)) rest σ1
    (by simp [c1.st, hS']) (by simp [c1.sh, hh]) c1.endO
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) ?_, c1.tr c2 rfl (by rw [exprWord, dm_app])⟩
  have e : (exprWord V).length = (V.flatMap (fun t => true :: termWord t)).length + 1 := by
    rw [exprWord, List.length_append, List.length_singleton]
  rw [e]; omega

end Copy

/-! ## The assembler's word program -/

/-- The assembler's word program on the streams `0` (`frame PRE`), `1` (`frame POST`), `2` (`exprWord V ++ tail`)
and `3` (the output). -/
def asmW : WM 3 0 :=
  .seq (pairsW 0 3) (.seq (mexprW 2 3) (.seq (emitW 3 true) (.seq (emitW 3 false)
    (.seq (pairsW 1 3) (emitW 3 false)))))

/-- The assembler's entry state. -/
def σA (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail : List Bool) : WState 3 0 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame PRE else if i.val = 1 then frame POST
    else if i.val = 2 then exprWord V ++ tail else [], fun r => r.elim0, false⟩

section Entry
variable (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail : List Bool)

theorem σA_st0 : (σA PRE POST V tail).st 0 = frame PRE := rfl
theorem σA_st1 : (σA PRE POST V tail).st 1 = frame POST := rfl
theorem σA_st2 : (σA PRE POST V tail).st 2 = exprWord V ++ tail := rfl
theorem σA_st3 : (σA PRE POST V tail).st 3 = [] := rfl
theorem σA_sh (i : Fin 4) : (σA PRE POST V tail).sh i = 0 := rfl

/-- **The assembler's word program**: the output stream ends as the compiler's input, the field streams kept. -/
theorem asm_exec : ∃ τ : WState 3 0, WExec 0 asmW (σA PRE POST V tail) τ
      (16 * PRE.length + 24 * (exprWord V).length + 16 * POST.length + 16) ∧
    τ.st 3 = frame (PRE ++ frame (exprWord V) ++ POST) ∧ τ.st 0 = frame PRE ∧ τ.st 1 = frame POST := by
  obtain ⟨σ1, s1, c1⟩ := cp_pairs 0 (0 : Fin 4) 3 (by decide) [] PRE [] (σA PRE POST V tail)
    (by simp [σA_st0, frame_eq_frameP]) (σA_sh PRE POST V tail 0) rfl
  obtain ⟨σ2, s2, c2⟩ := cp_mexpr 0 (2 : Fin 4) 3 (by decide) V [] tail σ1
    (by simp [(c1.same 2 (by decide) (by decide)).1, σA_st2])
    (by simp [(c1.same 2 (by decide) (by decide)).2, σA_sh]) c1.endO
  obtain ⟨σ3, s3, c3⟩ := cp_emit 0 (1 : Fin 4) 3 (by decide) true σ2 c2.endO
  obtain ⟨σ4, s4, c4⟩ := cp_emit 0 (1 : Fin 4) 3 (by decide) false σ3 c3.endO
  obtain ⟨σ5, s5, c5⟩ := cp_pairs 0 (1 : Fin 4) 3 (by decide) [] POST [] σ4
    (by simp [c4.st, c3.st, (c2.same 1 (by decide) (by decide)).1, (c1.same 1 (by decide) (by decide)).1, σA_st1,
      frame_eq_frameP])
    (by simp [c4.sh, c3.sh, (c2.same 1 (by decide) (by decide)).2, (c1.same 1 (by decide) (by decide)).2, σA_sh])
    c4.endO
  obtain ⟨τ, s6, c6⟩ := cp_emit 0 (1 : Fin 4) 3 (by decide) false σ5 c5.endO
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_, ?_, ?_, ?_⟩
  · rw [fpl, fpl]; omega
  · simp [c6.out, c5.out, c4.out, c3.out, c2.out, c1.out, σA_st3, frame_eq_frameP, fp_app, fp_cons, dm]
  · exact (c6.same 0 (by decide) (by decide)).1.trans ((c5.same 0 (by decide) (by decide)).1.trans
      ((c4.same 0 (by decide) (by decide)).1.trans ((c3.same 0 (by decide) (by decide)).1.trans
      ((c2.same 0 (by decide) (by decide)).1.trans (c1.st.trans (σA_st0 PRE POST V tail))))))
  · exact c6.st.trans (c5.st.trans (c4.st.trans (c3.st.trans ((c2.same 1 (by decide) (by decide)).1.trans
      ((c1.same 1 (by decide) (by decide)).1.trans (σA_st1 PRE POST V tail))))))

end Entry

/-! ## The stage -/

theorem zeroH {N t : ℕ} (sl : Fin t → Fin N) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The cell `[false]` on a blank tape. -/
theorem cell_dock {N : ℕ} (c : Fin N) (B : Fin N → List Bool) (hc : B c = []) :
    Step (RecoveryFocus.machine (fun _ : Fin 1 => c) NearCubicWires.WireExponent3_5.PrimT.cellM) 1 (fun _ => 0) B
      (fun _ => 0) (install (fun _ : Fin 1 => c) B (fun _ => [false])) := by
  have d := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => c)
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B (fun _ => rfl) (fun _ => hc)
  rw [zeroH] at d
  exact d

/-- The assembler: the cell written on tape `1`, then the word program with its heads returned. -/
noncomputable def asmM :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (1 : Fin 6)) NearCubicWires.WireExponent3_5.PrimT.cellM)
    (Rewind.machine asmW.toProg.compile)

theorem asm_bank (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail : List Bool) :
    install (fun _ : Fin 1 => (1 : Fin 6)) (asmIn (0 : Fin 6) 2 3 PRE POST V tail) (fun _ => [false]) =
      Fin.addCases (m := 3 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σA PRE POST V tail)).A
        (fun _ => []) := by
  funext j
  by_cases h1 : j = 1
  · subst h1
    exact (install_slot (fun _ : Fin 1 => (1 : Fin 6)) (fun a b _ => Subsingleton.elim a b)
      (asmIn (0 : Fin 6) 2 3 PRE POST V tail) (fun _ => [false]) 0).trans rfl
  · rw [install_other (fun _ : Fin 1 => (1 : Fin 6)) (asmIn (0 : Fin 6) 2 3 PRE POST V tail) (fun _ => [false]) j
      (fun _ e => h1 e.symm)]
    fin_cases j <;> first | rfl | exact (h1 rfl).elim

/-- **The assembler runs**: the output port ends as the compiler's input, the field ports kept. -/
theorem asm_run (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail : List Bool) :
    ∃ A' : Fin 6 → List Bool,
      Step asmM (asmCost PRE POST V) (fun _ => 0) (asmIn (0 : Fin 6) 2 3 PRE POST V tail) (fun _ => 0) A' ∧
      A' 4 = frame (PRE ++ frame (exprWord V) ++ POST) ∧ A' 0 = frame PRE ∧ A' 2 = frame POST := by
  obtain ⟨τ, hw, e3, e0, e1⟩ := asm_exec PRE POST V tail
  obtain ⟨out, st, ho⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 asmW (σA PRE POST V tail) τ _ hw
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  have d1 := cell_dock (1 : Fin 6) (asmIn (0 : Fin 6) 2 3 PRE POST V tail) rfl
  have d2 : Step (Rewind.machine asmW.toProg.compile)
      (2 * (16 * PRE.length + 24 * (exprWord V).length + 16 * POST.length + 16) + 2) (fun _ => 0)
      (install (fun _ : Fin 1 => (1 : Fin 6)) (asmIn (0 : Fin 6) 2 3 PRE POST V tail) (fun _ => [false]))
      (fun _ => 0) out := by
    rw [asm_bank]; exact st
  refine ⟨out, (d1.seq d2).enlarge ?_, ?_, ?_, ?_⟩
  · unfold asmCost; omega
  · rw [show (4 : Fin 6) = Fin.castAdd 1 (4 : Fin 5) from rfl, ho]; exact e3
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho]; exact e0
  · rw [show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho]; exact e1

/-- **The compiler's input assembler**: the interface, built. -/
noncomputable def asmStage : AsmStage where
  t := 6
  s := _
  M := asmM
  pA := 0
  pB := 2
  pE := 3
  pO := 4
  hAB := by decide
  hAE := by decide
  hAO := by decide
  hBE := by decide
  hBO := by decide
  hEO := by decide
  run := asm_run

end NearCubicWires.WireExponent3_5.UnionMachine.TailAsm
