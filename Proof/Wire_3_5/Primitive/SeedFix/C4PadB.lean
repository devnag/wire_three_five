import Proof.Wire_3_5.Primitive.SeedFix.C4PadA
import Proof.Wire_3_5.Primitive.SeedFix.C4CapA

/-! # (c′) (B), part 2: the two word programs of the degenerate branch

The stage's tape word of a call's entries is `blockWord ents` (P3:3011-3016). With no rows every entry is empty,
`vE E = (true false)^E false`; with rows its second bit is `true` (a row record starts with `true`). The branch reads
that bit (**`testW`**) and, on the empty word, writes the padded word (**`padW`**: every entry `true false` becomes
`true :: rowRec constRow ++ [false]`, the terminator stays), as masked-reset machines on `1 + 2 + 0 + 1` tapes
(`C4Set.cpS`'s form): **`testS`**, **`padS`**.

Paper quantity of the main types: the degenerate call's tape word, padded by the constant row. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Pad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.PrimT.C4Cap (CS CW cst)

/-! ## The words -/

/-- The tape word of `E` empty entries. -/
def vE (E : ℕ) : List Bool := (List.replicate E [true, false]).flatten ++ [false]

/-- A padded entry's record without its terminator. -/
def W1 : List Bool := true :: rowRec constRow

/-- The first `k` padded entry records. -/
def pk (k : ℕ) : List Bool := (List.replicate k (W1 ++ [false])).flatten

theorem vE_succ (E : ℕ) : vE (E + 1) = true :: false :: vE E := by
  simp [vE, List.replicate_succ]

theorem vE_get : ∀ (E k : ℕ), k ≤ E → (vE E).getD (2 * k) false = decide (k < E)
  | 0, 0, _ => rfl
  | E + 1, 0, _ => by rw [vE_succ]; simp
  | E + 1, k + 1, hk => by
    rw [vE_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    simp only [List.getD_cons_succ]
    rw [vE_get E k (by omega)]
    simp

theorem vE_one (E : ℕ) (hE : 1 ≤ E) : (vE E).getD 1 false = false := by
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  rw [vE_succ]; rfl

theorem pk_succ (k : ℕ) : pk (k + 1) = pk k ++ (W1 ++ [false]) := by
  simp [pk, List.replicate_succ', List.flatten_append]

theorem vE_eq (E : ℕ) : vE E = blockWord (List.replicate E []) := (blockWord_empty E).symm

theorem pk_eq (E : ℕ) : pk E ++ [false] = blockWord (padEnts (List.replicate E [])) := by
  rw [blockWord_pad]; rfl

/-! ## The test -/

section Progs
variable (cap : ℕ)

/-- **The test**: stream `1` gets the second bit of stream `0`. -/
def testW : CW := .seq (.fwd 0) (.ifs 0 (.wr 1 true) (.wr 1 false))

theorem test_spec (v : List Bool) : WExec cap testW (cst v [] 0 0) (cst v [v.getD 1 false] 1 0) 4 := by
  have t1 : WExec cap (.fwd 0 : CW) (cst v [] 0 0) (cst v [] 1 0) 1 := by
    refine WExec.cast cap (WExec.fwd 0 _) ?_ le_rfl
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply]
    · rfl
    · funext r; exact r.elim0
    · rfl
  have t2 : ∀ b : Bool, WExec cap (.wr 1 b : CW) (cst v [] 1 0) (cst v [b] 1 0) 1 := by
    intro b
    refine WExec.cast cap (WExec.wr 1 b _) ?_ le_rfl
    apply WState.eq
    · rfl
    · funext j; fin_cases j <;> simp [cst, Function.update_apply, writeTapeBit]
    · funext r; exact r.elim0
    · rfl
  cases hb : v.getD 1 false
  · have hw : wbit (cst v [] 1 0) 0 = false := by simp only [wbit, cst]; simpa [readTapeBit] using hb
    exact WExec.cast cap (WExec.seq t1 (WExec.ifsF hw (t2 false))) rfl le_rfl
  · have hw : wbit (cst v [] 1 0) 0 = true := by simp only [wbit, cst]; simpa [readTapeBit] using hb
    exact WExec.cast cap (WExec.seq t1 (WExec.ifsT hw (t2 true))) rfl le_rfl

/-! ## The padded copy -/

/-- Write a fixed word at stream `1`'s end. -/
def wword : List Bool → CW
  | [] => .skip
  | b :: bs => .seq (.wr 1 b) (.seq (.fwd 1) (wword bs))

theorem wword_spec (a : List Bool) (h0 : ℕ) : ∀ (bs pre : List Bool),
    WExec cap (wword bs) (cst a pre h0 pre.length) (cst a (pre ++ bs) h0 (pre ++ bs).length) (4 * bs.length)
  | [], pre => WExec.cast cap (WExec.skip _) (by simp) (by simp)
  | b :: bs, pre => by
    have t1 : WExec cap (.wr 1 b : CW) (cst a pre h0 pre.length) (cst a (pre ++ [b]) h0 pre.length) 1 := by
      refine WExec.cast cap (WExec.wr 1 b _) ?_ le_rfl
      apply WState.eq
      · rfl
      · funext j; fin_cases j <;> simp [cst, Function.update_apply, C4Pipe.write_end]
      · funext r; exact r.elim0
      · rfl
    have t2 : WExec cap (.fwd 1 : CW) (cst a (pre ++ [b]) h0 pre.length)
        (cst a (pre ++ [b]) h0 (pre ++ [b]).length) 1 := by
      refine WExec.cast cap (WExec.fwd 1 _) ?_ le_rfl
      apply WState.eq
      · funext j; fin_cases j <;> simp [cst, Function.update_apply]
      · rfl
      · funext r; exact r.elim0
      · rfl
    have t3 := wword_spec a h0 bs (pre ++ [b])
    refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3)) ?_ ?_
    · rw [List.append_assoc, List.singleton_append]
    · simp only [List.length_cons]; omega

/-- One padded entry. -/
def body : CW := .seq (wword W1) (.seq (.fwd 0) (.seq (.wr 1 false) (.seq (.fwd 1) (.fwd 0))))

/-- **The padded copy**: every entry `true false` of stream `0` as `W1 ++ [false]` on stream `1`, then the terminator. -/
def padW : CW := .seq (.whs 0 body) (.wr 1 false)

theorem body_spec (v : List Bool) (k : ℕ) :
    WExec cap body (cst v (pk k) (2 * k) (pk k).length) (cst v (pk (k + 1)) (2 * (k + 1)) (pk (k + 1)).length)
      (4 * W1.length + 8) := by
  have t1 := wword_spec cap v (2 * k) W1 (pk k)
  have t2 : WExec cap (.fwd 0 : CW) (cst v (pk k ++ W1) (2 * k) (pk k ++ W1).length)
      (cst v (pk k ++ W1) (2 * k + 1) (pk k ++ W1).length) 1 := by
    refine WExec.cast cap (WExec.fwd 0 _) ?_ le_rfl
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply]
    · rfl
    · funext r; exact r.elim0
    · rfl
  have t3 : WExec cap (.wr 1 false : CW) (cst v (pk k ++ W1) (2 * k + 1) (pk k ++ W1).length)
      (cst v (pk k ++ W1 ++ [false]) (2 * k + 1) (pk k ++ W1).length) 1 := by
    refine WExec.cast cap (WExec.wr 1 false _) ?_ le_rfl
    apply WState.eq
    · rfl
    · funext j
      fin_cases j
      · rfl
      · show writeTapeBit (pk k ++ W1) (pk k ++ W1).length false = pk k ++ W1 ++ [false]
        exact C4Pipe.write_end _ _
    · funext r; exact r.elim0
    · rfl
  have t4 : WExec cap (.fwd 1 : CW) (cst v (pk k ++ W1 ++ [false]) (2 * k + 1) (pk k ++ W1).length)
      (cst v (pk k ++ W1 ++ [false]) (2 * k + 1) (pk k ++ W1 ++ [false]).length) 1 := by
    refine WExec.cast cap (WExec.fwd 1 _) ?_ le_rfl
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply] <;> omega
    · rfl
    · funext r; exact r.elim0
    · rfl
  have t5 : WExec cap (.fwd 0 : CW) (cst v (pk k ++ W1 ++ [false]) (2 * k + 1) (pk k ++ W1 ++ [false]).length)
      (cst v (pk k ++ W1 ++ [false]) (2 * (k + 1)) (pk k ++ W1 ++ [false]).length) 1 := by
    refine WExec.cast cap (WExec.fwd 0 _) ?_ le_rfl
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply]; omega
    · rfl
    · funext r; exact r.elim0
    · rfl
  have e : pk k ++ W1 ++ [false] = pk (k + 1) := by rw [pk_succ, List.append_assoc]
  rw [← e]
  exact WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 t5)))) rfl (by omega)

theorem loop_spec (E : ℕ) : ∀ k, k ≤ E →
    WExec cap (.whs 0 body) (cst (vE E) (pk k) (2 * k) (pk k).length) (cst (vE E) (pk E) (2 * E) (pk E).length)
      ((E - k) * (4 * W1.length + 10) + 1)
  | k, hk => by
    by_cases hkE : k = E
    · subst hkE
      have hb : wbit (cst (vE k) (pk k) (2 * k) (pk k).length) 0 = false := by
        simp only [wbit, cst]
        have := vE_get k k le_rfl
        simpa [readTapeBit] using this
      exact WExec.mono (WExec.whsF hb) (by omega)
    · have hlt : k < E := by omega
      have hb : wbit (cst (vE E) (pk k) (2 * k) (pk k).length) 0 = true := by
        simp only [wbit, cst]
        have := vE_get E k hk
        rw [decide_eq_true hlt] at this
        simpa [readTapeBit] using this
      have ih := loop_spec E (k + 1) (by omega)
      refine WExec.cast cap (WExec.whsT hb (body_spec cap (vE E) k) ih) rfl ?_
      have : E - k = (E - (k + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
  termination_by k => E - k

theorem pad_spec (E : ℕ) :
    WExec cap padW (cst (vE E) [] 0 0) (cst (vE E) (pk E ++ [false]) (2 * E) (pk E).length)
      (E * (4 * W1.length + 10) + 3) := by
  have t1 := loop_spec cap E 0 (Nat.zero_le _)
  have e0 : pk 0 = [] := rfl
  rw [e0] at t1
  have t2 : WExec cap (.wr 1 false : CW) (cst (vE E) (pk E) (2 * E) (pk E).length)
      (cst (vE E) (pk E ++ [false]) (2 * E) (pk E).length) 1 := by
    refine WExec.cast cap (WExec.wr 1 false _) ?_ le_rfl
    apply WState.eq
    · rfl
    · funext j; fin_cases j <;> simp [cst, Function.update_apply, C4Pipe.write_end]
    · funext r; exact r.elim0
    · rfl
  exact WExec.cast cap (WExec.seq t1 t2) rfl (by simp only [Nat.sub_zero, List.length_nil]; omega)

end Progs

/-! ## As machines, every head back at `0` -/

/-- The test machine. -/
noncomputable def testZ := MaskedReset.machine testW.toProg.compile (fun _ => true)

/-- **The test**: from `v` on tape `0`, `[v₁]` on tape `2`, `v` kept. -/
theorem testS (v : List Bool) : ∃ tout : Fin (1 + 2 + 0 + 1) → List Bool,
    Step testZ (2 * 4 + 2) (fun _ => 0) (fun j => if j.val = 0 then v else []) (fun _ => 0) tout ∧
      tout ⟨0, by omega⟩ = v ∧ tout ⟨2, by omega⟩ = [v.getD 1 false] := by
  obtain ⟨A', hs, hA⟩ := C4Pipe.wm_blank 0 4 testW (cst v [] 0 0) _ _ (test_spec 0 v)
    (fun i => by fin_cases i <;> rfl) (fun r => r.elim0) rfl le_rfl
  refine ⟨A', hs.congr_in rfl ?_, ?_, ?_⟩
  · funext j
    fin_cases j <;> rfl
  · exact hA 0
  · exact hA 1

/-- The padded copy's step bound. -/
def padCost (E : ℕ) : ℕ := 2 * (E * (4 * W1.length + 10) + 3) + 2

/-- The padding machine. -/
noncomputable def padZ := MaskedReset.machine padW.toProg.compile (fun _ => true)

/-- **The padded copy**: from `vE E` on tape `0`, the padded word on tape `2`, `vE E` kept. -/
theorem padS (E : ℕ) : ∃ tout : Fin (1 + 2 + 0 + 1) → List Bool,
    Step padZ (padCost E) (fun _ => 0) (fun j => if j.val = 0 then vE E else []) (fun _ => 0) tout ∧
      tout ⟨0, by omega⟩ = vE E ∧ tout ⟨2, by omega⟩ = blockWord (padEnts (List.replicate E [])) := by
  obtain ⟨A', hs, hA⟩ := C4Pipe.wm_blank 0 (E * (4 * W1.length + 10) + 3) padW (cst (vE E) [] 0 0) _ _
    (pad_spec 0 E) (fun i => by fin_cases i <;> rfl) (fun r => r.elim0) rfl le_rfl
  refine ⟨A', hs.congr_in rfl ?_, ?_, ?_⟩
  · funext j
    fin_cases j <;> rfl
  · exact hA 0
  · exact (hA 1).trans (pk_eq E)

end NearCubicWires.WireExponent3_5.PrimT.C4Pad
