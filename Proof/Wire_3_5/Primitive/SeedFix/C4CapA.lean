import Proof.Wire_3_5.Primitive.SeedFix.C4SI
import Proof.Wire_3_5.Primitive.SeedFix.C4Front

/-! # C4 cap re-type, part 1: two unary word programs for the numbers machine's capacity

"`ℓ ≥ max(k, ⌈log₂(Q+1)⌉)`" and `Q` from `samp:q` (P3:2929-2941, 2994-3000): the SYM/THR numbers machine holds `Q`
and the enumeration's counter `n_T·2^w` in its registers, so its capacity must exceed them; they are `2^{O(kh)}·poly(n)`,
superpolynomial at row B. The capacity is `2^m` with `m = C·(B+1)²`, `B` the bit length of `n` (part 2); this part has
the two word programs of that chain, each as a masked-reset machine on `1 + 2 + 0 + 1` tapes (`C4Set.cpS`'s form):
* `ldW` (the leading ones of stream `0` onto stream `1`), `ld_spec`, **`ldS`**: from `w = 1^B 0 …`, `1^B`;
* `tsW` (unary to the CapReader source), `cl_spec`, `ts_spec`, **`tsS`**: from `1^m`, `srcWord m = 1^{m+1} 0 0^m 1`.

Paper quantity of the main types: the capacity's exponent `m` in unary and as `srcWord m`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Cap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm

abbrev CS := WState 1 0
abbrev CW := WM 1 0

/-- The two-stream state: stream `0` (head `h0`), stream `1` (head `h1`). -/
def cst (a b : List Bool) (h0 h1 : ℕ) : CS := ⟨![h0, h1], ![a, b], Fin.elim0, false⟩

theorem getD_rep : ∀ (a i : ℕ) (l : List Bool), i < a → (List.replicate a true ++ l).getD i false = true
  | 0, i, l, h => by omega
  | a + 1, 0, l, _ => by simp [List.replicate_succ]
  | a + 1, i + 1, l, h => by
    simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ]
    exact getD_rep a i l (by omega)

section Progs
variable (cap : ℕ)

/-- Copy the ones of stream `0` (from its head) onto stream `1` (at its end). -/
def ldW : CW := .whs 0 (.seq (.wr 1 true) (.seq (.fwd 1) (.fwd 0)))

theorem ld_body (w pre : List Bool) (i : ℕ) :
    WExec cap (.seq (.wr 1 true) (.seq (.fwd 1) (.fwd 0)) : CW)
      (cst w (pre ++ List.replicate i true) i (pre.length + i))
      (cst w (pre ++ List.replicate (i + 1) true) (i + 1) (pre.length + (i + 1))) 5 := by
  have t := WExec.seq (WExec.wr (cap := cap) 1 true (cst w (pre ++ List.replicate i true) i (pre.length + i)))
    (WExec.seq (WExec.fwd (cap := cap) 1 _) (WExec.fwd (cap := cap) 0 _))
  refine WExec.cast cap t ?_ (by omega)
  have ew : writeTapeBit (pre ++ List.replicate i true) (pre.length + i) true = pre ++ List.replicate (i + 1) true := by
    have := C4Pipe.write_end (pre ++ List.replicate i true) true
    simp only [List.length_append, List.length_replicate] at this
    rw [this, List.replicate_succ', List.append_assoc]
  apply WState.eq
  · funext j; fin_cases j <;> simp [cst, Function.update_apply] <;> omega
  · funext j; fin_cases j <;> simp [cst, Function.update_apply, ew]
  · funext r; exact r.elim0
  · rfl

theorem ld_spec (w pre : List Bool) (L : ℕ) (hw : ∀ i < L, w.getD i false = true) (hL : w.getD L false = false) :
    ∀ i, i ≤ L → WExec cap ldW (cst w (pre ++ List.replicate i true) i (pre.length + i))
      (cst w (pre ++ List.replicate L true) L (pre.length + L)) ((L - i) * 7 + 1)
  | i, hi => by
    by_cases hiL : i = L
    · subst hiL
      have hb : wbit (cst w (pre ++ List.replicate i true) i (pre.length + i)) 0 = false := by
        simp only [wbit, cst]; simpa [readTapeBit] using hL
      exact WExec.mono (WExec.whsF hb) (by omega)
    · have hlt : i < L := by omega
      have hb : wbit (cst w (pre ++ List.replicate i true) i (pre.length + i)) 0 = true := by
        simp only [wbit, cst]; simpa [readTapeBit] using hw i hlt
      have ih := ld_spec w pre L hw hL (i + 1) (by omega)
      refine WExec.cast cap (WExec.whsT hb (ld_body cap w pre i) ih) rfl ?_
      have : L - i = (L - (i + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
  termination_by i => L - i

/-- Clear stream `0` from its head back to cell `0`, appending a `0` to stream `1` per cleared one. -/
def clW : CW := .whs 0 (.seq (.wr 0 false) (.seq (.wr 1 false) (.seq (.fwd 1) (.bwd 0))))

/-- The clearing state after `k` of the `m` ones. -/
def est (m k : ℕ) : CS :=
  cst (List.replicate (m - k) true ++ List.replicate k false) (List.replicate (m + 1) true ++ false :: List.replicate k false)
    (m - 1 - k) (m + 2 + k)

theorem cl_body (m k : ℕ) (hk : k < m) :
    WExec cap (.seq (.wr 0 false) (.seq (.wr 1 false) (.seq (.fwd 1) (.bwd 0))) : CW) (est m k) (est m (k + 1)) 7 := by
  have t := WExec.seq (WExec.wr (cap := cap) 0 false (est m k))
    (WExec.seq (WExec.wr (cap := cap) 1 false _) (WExec.seq (WExec.fwd (cap := cap) 1 _) (WExec.bwd (cap := cap) 0 _)))
  refine WExec.cast cap t ?_ (by omega)
  have e0 : writeTapeBit (List.replicate (m - k) true ++ List.replicate k false) (m - 1 - k) false =
      List.replicate (m - (k + 1)) true ++ List.replicate (k + 1) false := by
    have hs : List.replicate (m - k) true ++ List.replicate k false =
        List.replicate (m - 1 - k) true ++ true :: List.replicate k false := by
      rw [show m - k = (m - 1 - k) + 1 by omega, List.replicate_succ', List.append_assoc]; rfl
    have := C4Front.write_mid' (List.replicate (m - 1 - k) true) (List.replicate k false) true false
    rw [List.length_replicate] at this
    rw [hs, this, show m - (k + 1) = m - 1 - k by omega, List.replicate_succ]
  have e1 : writeTapeBit (List.replicate (m + 1) true ++ false :: List.replicate k false) (m + 2 + k) false =
      List.replicate (m + 1) true ++ false :: List.replicate (k + 1) false := by
    have := C4Pipe.write_end (List.replicate (m + 1) true ++ false :: List.replicate k false) false
    simp only [List.length_append, List.length_replicate, List.length_cons] at this
    rw [show m + 2 + k = m + 1 + (k + 1) by omega, this, List.replicate_succ']
    simp
  apply WState.eq
  · funext j; fin_cases j <;> simp [est, cst, Function.update_apply] <;> omega
  · funext j; fin_cases j <;> simp [est, cst, Function.update_apply, e0, e1]
  · funext r; exact r.elim0
  · rfl

theorem cl_spec (m : ℕ) : ∀ k, k ≤ m → WExec cap clW (est m k) (est m m) ((m - k) * 9 + 1)
  | k, hk => by
    by_cases hkm : k = m
    · subst hkm
      have hb : wbit (est k k) 0 = false := by
        simp only [wbit, est, cst]
        simp [readTapeBit]
      exact WExec.mono (WExec.whsF hb) (by omega)
    · have hlt : k < m := by omega
      have hb : wbit (est m k) 0 = true := by
        simp only [wbit, est, cst]
        simp only [Matrix.cons_val_zero, readTapeBit]
        exact getD_rep _ _ _ (by omega)
      have ih := cl_spec m (k + 1) (by omega)
      refine WExec.cast cap (WExec.whsT hb (cl_body cap m k hlt) ih) rfl ?_
      have : m - k = (m - (k + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
  termination_by k => m - k

/-- **Unary to the CapReader source**: `1^m` on stream `0` becomes `srcWord m = 1^{m+1} 0 0^m 1` on stream `1`. -/
def tsW : CW :=
  .seq (.wr 1 true) (.seq (.fwd 1) (.seq ldW (.seq (.wr 1 false) (.seq (.fwd 1) (.seq (.bwd 0)
    (.seq clW (.wr 1 true)))))))

/-- Its step bound. -/
def tsCost (m : ℕ) : ℕ := 1 + 1 + (1 + 1 + ((m * 7 + 1) + 1 + (1 + 1 + (1 + 1 + (1 + 1 + ((m * 9 + 1) + 1 + 1))))))

theorem ts_spec (m : ℕ) : ∃ τ : CS, WExec cap tsW (cst (List.replicate m true) [] 0 0) τ (tsCost m) ∧
    τ.st 1 = PrimAsm.NumsX.srcWord m := by
  have s1 := WExec.wr (cap := cap) 1 true (cst (List.replicate m true) [] 0 0)
  have s2 := WExec.fwd (cap := cap) 1 ((cst (List.replicate m true) [] 0 0).sets 1
    (writeTapeBit ((cst (List.replicate m true) [] 0 0).st 1) ((cst (List.replicate m true) [] 0 0).sh 1) true))
  have e2 : ((cst (List.replicate m true) [] 0 0).sets 1
      (writeTapeBit ((cst (List.replicate m true) [] 0 0).st 1) ((cst (List.replicate m true) [] 0 0).sh 1) true)).seth 1
      (((cst (List.replicate m true) [] 0 0).sets 1 (writeTapeBit ((cst (List.replicate m true) [] 0 0).st 1)
        ((cst (List.replicate m true) [] 0 0).sh 1) true)).sh 1 + 1) =
      cst (List.replicate m true) ([true] ++ List.replicate 0 true) 0 ([true].length + 0) := by
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply]
    · funext j; fin_cases j <;> simp [cst, Function.update_apply, writeTapeBit]
    · funext r; exact r.elim0
    · rfl
  rw [e2] at s2
  have s3 := ld_spec cap (List.replicate m true) [true] m (fun i hi => by simp [hi]) (by simp) 0 (by omega)
  set σ3 := cst (List.replicate m true) ([true] ++ List.replicate m true) m ([true].length + m) with hσ3
  have s4 := WExec.wr (cap := cap) 1 false σ3
  have e4 : writeTapeBit (σ3.st 1) (σ3.sh 1) false = List.replicate (m + 1) true ++ [false] := by
    have := C4Pipe.write_end ([true] ++ List.replicate m true) false
    simp only [List.length_append, List.length_singleton, List.length_replicate] at this
    simp only [σ3, cst, Matrix.cons_val_one, Matrix.cons_val_zero, List.length_singleton]
    rw [this, List.replicate_succ]; rfl
  rw [e4] at s4
  have s5 := WExec.fwd (cap := cap) 1 (σ3.sets 1 (List.replicate (m + 1) true ++ [false]))
  have s6 := WExec.bwd (cap := cap) 0 ((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).seth 1
    ((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).sh 1 + 1))
  have e6 : (((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).seth 1
      ((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).sh 1 + 1)).seth 0
      (((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).seth 1
        ((σ3.sets 1 (List.replicate (m + 1) true ++ [false])).sh 1 + 1)).sh 0 - 1)) = est m 0 := by
    apply WState.eq
    · funext j; fin_cases j <;> simp [σ3, est, cst, Function.update_apply] <;> omega
    · funext j; fin_cases j <;> simp [σ3, est, cst, Function.update_apply]
    · funext r; exact r.elim0
    · rfl
  rw [e6] at s6
  have s7 := cl_spec cap m 0 (by omega)
  have s8 := WExec.wr (cap := cap) 1 true (est m m)
  refine ⟨_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) rfl (by unfold tsCost; omega), ?_⟩
  have e8 : writeTapeBit ((est m m).st 1) ((est m m).sh 1) true = PrimAsm.NumsX.srcWord m := by
    have := C4Pipe.write_end (List.replicate (m + 1) true ++ false :: List.replicate m false) true
    simp only [List.length_append, List.length_replicate, List.length_cons] at this
    simp only [est, cst, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show m + 2 + m = m + 1 + (m + 1) by omega, this]
    simp [PrimAsm.NumsX.srcWord, PrimAsm.NumsX.reps_single, List.replicate_succ]
  simp [e8]

end Progs

/-! ## As machines, every head back at `0` -/

/-- The source machine. -/
noncomputable def tsZ := MaskedReset.machine tsW.toProg.compile (fun _ => true)

/-- **`srcWord m` from `1^m`** on tape `0`: `srcWord m` on tape `2`. -/
theorem tsS (m : ℕ) : ∃ tout : Fin (1 + 2 + 0 + 1) → List Bool,
    Step tsZ (2 * tsCost m + 2) (fun _ => 0) (fun j => if j.val = 0 then List.replicate m true else []) (fun _ => 0) tout ∧
      tout ⟨2, by omega⟩ = PrimAsm.NumsX.srcWord m := by
  obtain ⟨τ, hx, hτ⟩ := ts_spec 0 m
  obtain ⟨A', hs, hA⟩ := C4Pipe.wm_blank 0 (tsCost m) tsW (cst (List.replicate m true) [] 0 0) τ _ hx
    (fun i => by fin_cases i <;> rfl) (fun r => r.elim0) rfl le_rfl
  refine ⟨A', hs.congr_in rfl ?_, ?_⟩
  · funext j
    fin_cases j <;> rfl
  · exact (hA 1).trans hτ

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
