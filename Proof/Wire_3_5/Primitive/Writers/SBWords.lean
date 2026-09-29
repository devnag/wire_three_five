import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.Primitive.Writers.SBErase
import Proof.Wire_3_5.Primitive.Writers.FiltRec
import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # SB, part 5: small word writers and the list erase

The field phase of S4's words `4`, `5` (the trace mask and the modulus of `GF(2^ℓ)`, P3:2932-2941, 2053-2055) needs,
on blank streams, the unary degree `1^ℓ` (the modulus machine's input) and the zero words `frame (binary ℓ 0)` (the
trace program's output and work words), and afterwards the erase of the docked machine's and the trace's scratch:

* `onesW`, **`ones_spec`** (`[] ↦ 1^v`, head back at `0`);
* `zeroLoop`/`zeroLoop_spec`, `zeroW`, **`zero_spec`** (`[] ↦ reps v [true, false] ++ [false]`, head back at `0`);
* `eraseList`, **`eraseList_spec`** (every listed stream of length `≤ T`, head `0` ↦ `0^T`, head `0`; the bound
  reloaded from `RT` for each stream).

Paper quantity: none (plumbing for S4's field words). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ} (cap : ℕ)

/-- `1^v` on `O` from register `R` (consumed), head back at `0`. -/
def onesW (O : Fin (ns + 1)) (OP R : Fin nr) : WM ns nr := .seq (SBEmit.unaryLoop O OP R) (WM.rewind O OP)

theorem ones_spec (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) (v : ℕ) (σ : WState ns nr) (hv : σ.val R = v)
    (hO : σ.st O = []) (hh : σ.sh O = 0) (hop : σ.val OP = 0) (hc : v ≤ cap) :
    WExec cap (onesW O OP R) σ ((σ.sets O (List.replicate v true)).setv R 0) (16 * v + 3) := by
  have h1 := SBEmit.unaryLoop_spec cap O OP R hR v σ hv (by simp [hO, hh]) (by omega)
  set τ := appendO (σ.setv R 0) O OP (List.replicate v true) with hτ
  have h2 := wrewind_spec cap O OP v τ (by simp [hτ, Function.update_apply, Ne.symm hR, hop])
    (by simp [hτ, Function.update_apply, Ne.symm hR, hop]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hτ, hh]
    · simp [hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp [hτ, hO]
    · simp [hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = OP
    · subst hj; simp [hτ, Function.update_apply, Ne.symm hR, hop]
    · by_cases hj2 : j = R
      · subst hj2; simp [hτ, Function.update_apply, hj]
      · simp [hτ, Function.update_of_ne hj, Function.update_of_ne hj2]
  · simp [hτ]

/-- `v` framed zero bits (register `R` consumed). -/
def zeroLoop (O : Fin (ns + 1)) (OP R : Fin nr) : WM ns nr := .whr R (.seq (.dec R) (emitPair O OP false))

theorem zeroLoop_spec (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) :
    ∀ (v : ℕ) (σ : WState ns nr), σ.val R = v → σ.sh O = (σ.st O).length → σ.val OP + 2 * v ≤ cap →
      WExec cap (zeroLoop O OP R) σ (appendO (σ.setv R 0) O OP (FiltRec.reps v [true, false])) (19 * v + 1) := by
  intro v
  induction v with
  | zero =>
    intro σ hv _ _
    have e : appendO (σ.setv R 0) O OP (FiltRec.reps 0 [true, false]) = σ := by
      rw [show FiltRec.reps 0 [true, false] = [] from rfl, appendO_nil, ← hv, wsetv_same]
    rw [e]
    exact WExec.whrF hv
  | succ v ih =>
    intro σ hv hO hc
    have h1 := WExec.dec (cap := cap) R σ (by omega)
    rw [hv, show v + 1 - 1 = v by omega] at h1
    have hO1 : (σ.setv R v).sh O = ((σ.setv R v).st O).length := by simpa using hO
    have h2 := emitPair_spec cap O OP false (σ.setv R v) hO1 (by simp [Function.update_apply, Ne.symm hR]; omega)
    set σ' := appendO (σ.setv R v) O OP [true, false] with hσ'
    have hv' : σ'.val R = v := by simp [hσ', Function.update_apply, hR]
    have hO' : σ'.sh O = (σ'.st O).length := by simp [hσ', hO]
    have hc' : σ'.val OP + 2 * v ≤ cap := by simp [hσ', Function.update_apply, Ne.symm hR]; omega
    have h3 := ih σ' hv' hO' hc'
    have e3 : appendO (σ'.setv R 0) O OP (FiltRec.reps v [true, false]) =
        appendO (σ.setv R 0) O OP (FiltRec.reps (v + 1) [true, false]) := by
      rw [hσ', appendO_setv σ O OP R hR v [true, false], wsetv_setv, ← appendO_setv σ O OP R hR 0 [true, false],
        appendO_append]
      rfl
    rw [e3] at h3
    exact WExec.mono (WExec.whrT (show σ.val R ≠ 0 by omega) (WExec.seq h1 h2) h3) (by omega)

/-- **The zero word** `reps v [true, false] ++ [false]` on `O` (register `R` consumed), head back at `0`. -/
def zeroW (O : Fin (ns + 1)) (OP R : Fin nr) : WM ns nr :=
  .seq (zeroLoop O OP R) (.seq (emitC O OP false) (WM.rewind O OP))

theorem zero_spec (O : Fin (ns + 1)) (OP R : Fin nr) (hR : R ≠ OP) (v : ℕ) (σ : WState ns nr) (hv : σ.val R = v)
    (hO : σ.st O = []) (hh : σ.sh O = 0) (hop : σ.val OP = 0) (hc : 2 * v + 1 ≤ cap) :
    WExec cap (zeroW O OP R) σ ((σ.sets O (FiltRec.reps v [true, false] ++ [false])).setv R 0) (29 * v + 16) := by
  have h1 := zeroLoop_spec cap O OP R hR v σ hv (by simp [hO, hh]) (by omega)
  set τ := appendO (σ.setv R 0) O OP (FiltRec.reps v [true, false]) with hτ
  have hlen : (FiltRec.reps v [true, false]).length = 2 * v := by
    simp [FiltRec.reps, List.length_flatten]; ring
  have h2 := emitC_spec cap O OP false τ (by simp [hτ, hO, hh]) (by simp [hτ, Function.update_apply, Ne.symm hR, hop]; omega)
  set τ2 := ((τ.sets O ((τ.st O) ++ [false])).seth O (τ.sh O + 1)).setv OP (τ.val OP + 1) with hτ2
  have hτ2OP : τ2.val OP = 2 * v + 1 := by
    simp only [hτ2, hτ, WState.setv_val, appendO_val, WState.seth_val, WState.sets_val, Function.update_self,
      Function.update_of_ne (Ne.symm hR), hop, hlen]
    omega
  have h3 := wrewind_spec cap O OP (2 * v + 1) τ2 hτ2OP (by rw [hτ2OP]; exact hc)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hτ2, hτ, hh, hlen]
    · simp [hτ2, hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp [hτ2, hτ, hO]
    · simp [hτ2, hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = OP
    · subst hj; simp [hτ2, hτ, Function.update_apply, Ne.symm hR, hop]
    · by_cases hj2 : j = R
      · subst hj2; simp [hτ2, hτ, Function.update_apply, hj]
      · simp [hτ2, hτ, Function.update_of_ne hj, Function.update_of_ne hj2]
  · simp [hτ2, hτ]

/-- Erase every listed stream to `0^T` (`T` in `RT`, reloaded into `c` for each stream). -/
def eraseList (RT c d t : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | i :: l => .seq (FinalPass.Hash4.wcopyR RT c t) (.seq (SBErase.eraseW i c d) (eraseList RT c d t l))

def eraseListCost (T : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: l => UnaryPow.sq cap + 1 + (16 * T + 3 + 1 + eraseListCost T l)

theorem eraseList_spec (RT c d t : Fin nr) (h1 : RT ≠ c) (h2 : RT ≠ t) (h3 : c ≠ t) (h4 : c ≠ d) (h5 : RT ≠ d)
    (h6 : d ≠ t) (T : ℕ) (hT : T ≤ cap) :
    ∀ (l : List (Fin (ns + 1))) (σ : WState ns nr), σ.val RT = T → σ.val c = 0 → σ.val d = 0 → σ.val t = 0 →
      (∀ i ∈ l, σ.sh i = 0 ∧ (σ.st i).length ≤ T) →
      ∃ τ : WState ns nr, WExec cap (eraseList RT c d t l) σ τ (eraseListCost cap T (l.map fun i => i.val)) ∧
        (∀ i ∈ l, τ.st i = List.replicate T false ∧ τ.sh i = 0) ∧
        (∀ i, i ∉ l → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro σ _ _ _ _ _
    exact ⟨σ, WExec.skip σ, fun i hi => by simp at hi, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | cons i l ih =>
    intro σ hRT hc hd ht hl
    have e1 := SparseNum.copy1 cap RT c t h1 h2 h3 T σ hRT hc ht hT
    obtain ⟨hsh, hlen⟩ := hl i (by simp)
    have e2 := SBErase.erase_spec cap i c d h4 T (σ.setv c T) (by simp) (by simp [Function.update_of_ne (Ne.symm h4), hd])
      (by simpa using hsh) (by simpa using hlen) hT
    set σ2 := ((σ.setv c T).sets i (List.replicate T false)).setv c 0 with hσ2
    have hval2 : σ2.val = σ.val := by
      funext j; by_cases hj : j = c
      · subst hj; simp [hσ2, hc]
      · simp [hσ2, Function.update_of_ne hj]
    have hl2 : ∀ i' ∈ l, σ2.sh i' = 0 ∧ (σ2.st i').length ≤ T := by
      intro i' hi'
      by_cases hii : i' = i
      · subst hii
        exact ⟨by simpa [hσ2] using hsh, by simp [hσ2]⟩
      · obtain ⟨a, b⟩ := hl i' (List.mem_cons_of_mem _ hi')
        exact ⟨by simpa [hσ2] using a, by simpa [hσ2, Function.update_of_ne hii] using b⟩
    obtain ⟨τ, e3, hin, hout, hv, hcl⟩ := ih σ2 (by rw [hval2]; exact hRT) (by rw [hval2]; exact hc)
      (by rw [hval2]; exact hd) (by rw [hval2]; exact ht) hl2
    refine ⟨τ, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_⟩
    · intro i' hi'
      rcases List.mem_cons.mp hi' with e | e
      · subst e
        by_cases hil : i' ∈ l
        · exact hin i' hil
        · obtain ⟨a, b⟩ := hout i' hil
          exact ⟨by rw [a]; simp [hσ2], by rw [b]; simp [hσ2, hsh]⟩
      · exact hin i' e
    · intro i' hi'
      have hne : i' ≠ i := fun e => hi' (e ▸ List.mem_cons_self)
      have hnl : i' ∉ l := fun e => hi' (List.mem_cons_of_mem _ e)
      obtain ⟨a, b⟩ := hout i' hnl
      exact ⟨by rw [a]; simp [hσ2, Function.update_of_ne hne], by rw [b]; simp [hσ2]⟩
    · rw [hv, hval2]
    · rw [hcl]; simp [hσ2]

end NearCubicWires.WireExponent3_5.PrimAsm.SBWords
