import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.Primitive.Writers.DataTabs

/-! # SB, part 1: raw unary emission from registers

S4's words `6` and `7` (`s4Core2`, P3:3170-3181) are raw unary words: `ListEval.unary t = 1^t 0` (the majority
threshold) and `Data.unaryList vs` (the small numbers `s4Small2`, each `1^v 0`). This module writes them onto an output
stream (head at its end) from registers, consuming the registers (the writer ends with every register `0`):

* `unaryLoop`, **`unaryLoop_spec`** (`1^v`), `emitU`, **`emitU_spec`** (`1^v 0`, cost `11v + 9`);
* `emitList`, `emitListCost`, **`emitList_spec`** (the registers `l` in order: `unaryList vs`, each register `0`).

Paper quantity of the main type: S4's unary words (the threshold and the small numbers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBEmit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ} (cap : ℕ)

/-- `1^v` from register `R` (consumed). -/
def unaryLoop (O : Fin (ns + 1)) (OP R : Fin nr) : WM ns nr := .whr R (.seq (.dec R) (emitC O OP true))

theorem appendO_one_setv (σ : WState ns nr) (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) (v : ℕ) (u : List Bool) :
    appendO ((appendO (σ.setv R v) O OP [true]).setv R 0) O OP u = appendO (σ.setv R 0) O OP (true :: u) := by
  rw [appendO_setv σ O OP R hR v [true], wsetv_setv, ← appendO_setv σ O OP R hR 0 [true], appendO_append]
  rfl

theorem unaryLoop_spec (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) :
    ∀ (v : ℕ) (σ : WState ns nr), σ.val R = v → σ.sh O = (σ.st O).length → σ.val OP + v ≤ cap →
      WExec cap (unaryLoop O OP R) σ (appendO (σ.setv R 0) O OP (List.replicate v true)) (11 * v + 1) := by
  intro v
  induction v with
  | zero =>
    intro σ hv _ _
    have e : appendO (σ.setv R 0) O OP (List.replicate 0 true) = σ := by
      rw [List.replicate_zero, appendO_nil, ← hv, wsetv_same]
    rw [e]
    exact WExec.whrF hv
  | succ v ih =>
    intro σ hv hO hc
    have h1 := WExec.dec (cap := cap) R σ (by omega)
    rw [hv] at h1
    have e1 : v + 1 - 1 = v := by omega
    rw [e1] at h1
    have hO1 : (σ.setv R v).sh O = ((σ.setv R v).st O).length := by simpa using hO
    have h2 := emitC_spec cap O OP true (σ.setv R v) hO1 (by simp [Function.update_apply, Ne.symm hR]; omega)
    have e2 : (((σ.setv R v).sets O (((σ.setv R v).st O) ++ [true])).seth O ((σ.setv R v).sh O + 1)).setv OP
        ((σ.setv R v).val OP + 1) = appendO (σ.setv R v) O OP [true] := rfl
    rw [e2] at h2
    set σ' := appendO (σ.setv R v) O OP [true] with hσ'
    have hv' : σ'.val R = v := by simp [hσ', Function.update_apply, hR]
    have hO' : σ'.sh O = (σ'.st O).length := by simp [hσ', hO]
    have hc' : σ'.val OP + v ≤ cap := by simp [hσ', Function.update_apply, Ne.symm hR]; omega
    have h3 := ih σ' hv' hO' hc'
    rw [hσ', appendO_one_setv σ O OP R hR v] at h3
    have hb := WExec.whrT (show σ.val R ≠ 0 by omega) (WExec.seq h1 h2) h3
    rw [← List.replicate_succ] at hb
    exact WExec.mono hb (by omega)

/-- `1^v 0` from register `R` (consumed). -/
def emitU (O : Fin (ns + 1)) (OP R : Fin nr) : WM ns nr := .seq (unaryLoop O OP R) (emitC O OP false)

theorem emitU_spec (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) (v : ℕ) (σ : WState ns nr) (hv : σ.val R = v)
    (hO : σ.sh O = (σ.st O).length) (hc : σ.val OP + v + 1 ≤ cap) :
    WExec cap (emitU O OP R) σ (appendO (σ.setv R 0) O OP (List.replicate v true ++ [false])) (11 * v + 9) := by
  have h1 := unaryLoop_spec cap O OP R hR v σ hv hO (by omega)
  set σ1 := appendO (σ.setv R 0) O OP (List.replicate v true) with hσ1
  have hO1 : σ1.sh O = (σ1.st O).length := by simp [hσ1, hO]
  have h2 := emitC_spec cap O OP false σ1 hO1 (by simp [hσ1, Function.update_apply, Ne.symm hR]; omega)
  have e2 : ((σ1.sets O ((σ1.st O) ++ [false])).seth O (σ1.sh O + 1)).setv OP (σ1.val OP + 1) =
      appendO (σ.setv R 0) O OP (List.replicate v true ++ [false]) := by
    rw [hσ1, ← appendO_append]; rfl
  rw [e2] at h2
  exact WExec.mono (WExec.seq h1 h2) (by omega)

/-- The registers `l` in order, each as `1^v 0`. -/
def emitList (O : Fin (ns + 1)) (OP : Fin nr) : List (Fin nr) → WM ns nr
  | [] => .skip
  | R :: l => .seq (emitU O OP R) (emitList O OP l)

def emitListCost : List ℕ → ℕ
  | [] => 0
  | v :: vs => 11 * v + 9 + 1 + emitListCost vs

/-- **The unary list**: from the registers `l` (values `vs`, distinct, none `OP`), the stream `O` (head at its end)
gets `unaryList vs`; the registers of `l` end at `0`, `OP` counts the written bits, every other register, stream and
head, and the cell, are kept. -/
theorem emitList_spec (O : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (l : List (Fin nr)) (vs : List ℕ) (σ : WState ns nr), l.length = vs.length → l.Nodup → (∀ R ∈ l, R ≠ OP) →
      (∀ i (h : i < l.length) (hv : i < vs.length), σ.val (l.get ⟨i, h⟩) = vs.get ⟨i, hv⟩) →
      σ.sh O = (σ.st O).length → σ.val OP + (Data.unaryList vs).length ≤ cap →
      ∃ τ : WState ns nr, WExec cap (emitList O OP l) σ τ (emitListCost vs) ∧
        τ.st O = σ.st O ++ Data.unaryList vs ∧ τ.sh O = (τ.st O).length ∧
        τ.val OP = σ.val OP + (Data.unaryList vs).length ∧ (∀ R ∈ l, τ.val R = 0) ∧
        (∀ r, r ∉ l → r ≠ OP → τ.val r = σ.val r) ∧ (∀ s, s ≠ O → τ.st s = σ.st s) ∧
        (∀ s, s ≠ O → τ.sh s = σ.sh s) ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro vs σ hlen _ _ _ hO _
    have hv0 : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hv0
    refine ⟨σ, WExec.skip σ, by simp [Data.unaryList], hO, by simp [Data.unaryList], fun R hR => by simp at hR,
      fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | cons R l ih =>
    intro vs σ hlen hnd hne hval hO hc
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hROP : R ≠ OP := hne R (by simp)
      have hnd' := List.nodup_cons.mp hnd
      have h0 : σ.val R = v := by simpa using hval 0 (by simp) (by simp)
      have hu : (Data.unaryList (v :: vs)).length = v + 1 + (Data.unaryList vs).length := by
        simp [Data.unaryList]; omega
      have e1 := emitU_spec cap O OP R hROP v σ h0 hO (by omega)
      set σ1 := appendO (σ.setv R 0) O OP (List.replicate v true ++ [false]) with hσ1
      have hO1 : σ1.sh O = (σ1.st O).length := by simp [hσ1, hO]
      have hval1 : ∀ i (h : i < l.length) (hv : i < vs.length), σ1.val (l.get ⟨i, h⟩) = vs.get ⟨i, hv⟩ := by
        intro i h hv
        have hne1 : l.get ⟨i, h⟩ ≠ R := fun e => hnd'.1 (e ▸ List.get_mem l ⟨i, h⟩)
        have hne2 : l.get ⟨i, h⟩ ≠ OP := hne _ (List.mem_cons_of_mem _ (List.get_mem l ⟨i, h⟩))
        have := hval (i + 1) (by simpa using h) (by simpa using hv)
        simp only [List.get_eq_getElem, List.getElem_cons_succ] at this
        simp only [List.get_eq_getElem] at hne1 hne2 ⊢
        simp [hσ1, Function.update_apply, hne1, hne2, this]
      have hc1 : σ1.val OP + (Data.unaryList vs).length ≤ cap := by
        simp [hσ1, Function.update_apply, Ne.symm hROP]; omega
      obtain ⟨τ, e2, hst, hsh, hop, hz, hkeep, hso, hsho, hcl⟩ :=
        ih vs σ1 (by simpa using hlen) hnd'.2 (fun R' hR' => hne R' (List.mem_cons_of_mem _ hR')) hval1 hO1 hc1
      refine ⟨τ, WExec.seq e1 e2, ?_, hsh, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst]; simp [hσ1, Data.unaryList]
      · rw [hop]; simp [hσ1, Function.update_apply, Ne.symm hROP]; omega
      · intro R' hR'
        rcases List.mem_cons.mp hR' with e | e
        · subst e
          rw [hkeep R' hnd'.1 hROP]; simp [hσ1, Function.update_apply, hROP]
        · exact hz R' e
      · intro r hr hrop
        have hr1 : r ≠ R := fun e => hr (e ▸ List.mem_cons_self)
        have hr2 : r ∉ l := fun e => hr (List.mem_cons_of_mem _ e)
        rw [hkeep r hr2 hrop]; simp [hσ1, Function.update_apply, hr1, hrop]
      · intro s hs; rw [hso s hs]; simp [hσ1, Function.update_apply, hs]
      · intro s hs; rw [hsho s hs]; simp [hσ1, Function.update_apply, hs]
      · rw [hcl]; simp [hσ1]

end NearCubicWires.WireExponent3_5.PrimAsm.SBEmit
