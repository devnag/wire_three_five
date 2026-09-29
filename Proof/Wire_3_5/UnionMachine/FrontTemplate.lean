import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front: the unary template `0 1^q 0` of the Theorem 2.5 repository's decoder

The Theorem 2.5 repository's circuit decoder reads the arity `q` as the template `UnaryTemplate.tape q = 0 1^q 0` with its head on the first
`1` (base `CloseoutRowsCircuit.heads`, tape `1674`). A register program (C5's `WM`) writes it from `1^q`.
Main statement: **`tmpl_spec`**. Paper quantity: the arity `q` of the guessed atoms, as the decoder reads it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTemplate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout: streams `Q` (`1^q`) and `T` (the template); registers `PQ PT` -/

local notation "sQ" => (0 : Fin 2)
local notation "sT" => (1 : Fin 2)
local notation "rPQ" => (0 : Fin 2)
local notation "rPT" => (1 : Fin 2)

/-- The state: `1^q` read up to `pq`, the template written so far `t` (head at its end `pt`). -/
def st (q pq pt : ℕ) (t : List Bool) (c : Bool) : WState 1 2 :=
  ⟨![pq, pt], ![List.replicate q true, t], ![pq, pt], c⟩

variable (cap : ℕ)

/-- **The template writer**: `0`, a `1` per `1` of `1^q`, `0`; both streams rewound, the template's head then on its
first `1`. -/
def tmplP : WM 1 2 :=
  .seq (emitC sT rPT false) (.seq (.whs sQ (.seq (WM.fwdC sQ rPQ) (emitC sT rPT true)))
    (.seq (emitC sT rPT false) (.seq (WM.rewind sQ rPQ) (.seq (WM.rewind sT rPT) (WM.fwdC sT rPT)))))

theorem emit_st (q pq : ℕ) (t : List Bool) (b c : Bool) (ht : t.length < cap) :
    WExec cap (emitC sT rPT b) (st q pq t.length t c) (st q pq (t.length + 1) (t ++ [b]) c) 7 := by
  refine WExec.cast cap (emitC_spec cap sT rPT b (st q pq t.length t c) rfl (by simpa [st] using ht)) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ ?_ <;>
    first
      | rfl
      | (funext i; fin_cases i <;> simp [st, WState.sets, WState.seth, WState.setv, Function.update_apply])

theorem loop_spec (q : ℕ) (c : Bool) (hq : q + 2 ≤ cap) :
    ∀ j, j ≤ q → WExec cap (.whs sQ (.seq (WM.fwdC sQ rPQ) (emitC sT rPT true)))
      (st q j (j + 1) (false :: List.replicate j true) c) (st q q (q + 1) (false :: List.replicate q true) c)
      (15 * (q - j) + 1) := by
  intro j
  induction h : q - j generalizing j with
  | zero =>
    intro hj
    have hjq : j = q := by omega
    subst hjq
    exact WExec.whsF (by simp [wbit, st, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_replicate])
  | succ m ih =>
    intro hj
    have hlt : j < q := by omega
    have s1 : WExec cap (WM.fwdC sQ rPQ) (st q j (j + 1) (false :: List.replicate j true) c)
        (st q (j + 1) (j + 1) (false :: List.replicate j true) c) 5 := by
      refine WExec.cast cap (wfwdC_spec cap sQ rPQ _ (by simp [st]; omega)) ?_ le_rfl
      refine WState.eq ?_ ?_ ?_ ?_ <;>
        first
          | rfl
          | (funext i; fin_cases i <;> simp [st, WState.seth, WState.setv, Function.update_apply])
    have s2 := emit_st cap q (j + 1) (false :: List.replicate j true) true c (by simp; omega)
    have e : (false :: List.replicate j true) ++ [true] = false :: List.replicate (j + 1) true := by
      rw [List.replicate_succ']; rfl
    rw [e] at s2
    simp only [List.length_cons, List.length_replicate] at s2
    have s3 := ih (j + 1) (by omega) (by omega)
    refine WExec.mono (WExec.whsT (by simp [wbit, st, readTapeBit, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, hlt]) (s1.seq s2) s3) (by omega)

/-- **The template from `1^q`**: `UnaryTemplate.tape q`, its head on position `1`; `1^q` kept and rewound. -/
theorem tmpl_spec (q : ℕ) (c : Bool) (hq : q + 3 ≤ cap) :
    WExec cap tmplP (st q 0 0 [] c) ⟨![0, 1], ![List.replicate q true, UnaryTemplate.tape q], ![0, 1], c⟩
      (40 * (q + 2)) := by
  have s1 := emit_st cap q 0 [] false c (by simp; omega)
  have s2 := loop_spec cap q c (by omega) 0 (by omega)
  simp only [List.nil_append, List.length_nil, List.replicate_zero] at s1 s2
  have s3 := emit_st cap q q (false :: List.replicate q true) false c (by simp; omega)
  simp only [List.length_cons, List.length_replicate] at s3
  have s4 : WExec cap (WM.rewind sQ rPQ) (st q q (q + 1 + 1) (false :: List.replicate q true ++ [false]) c)
      (st q 0 (q + 1 + 1) (false :: List.replicate q true ++ [false]) c) (5 * q + 1) := by
    refine WExec.cast cap (wrewind_spec cap sQ rPQ q _ rfl (by simp [st]; omega)) ?_ le_rfl
    refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, WState.seth, WState.setv, Function.update_apply])
  have s5 : WExec cap (WM.rewind sT rPT) (st q 0 (q + 1 + 1) (false :: List.replicate q true ++ [false]) c)
      (st q 0 0 (false :: List.replicate q true ++ [false]) c) (5 * (q + 1 + 1) + 1) := by
    refine WExec.cast cap (wrewind_spec cap sT rPT (q + 1 + 1) _ rfl (by simp [st]; omega)) ?_ le_rfl
    refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, WState.seth, WState.setv, Function.update_apply])
  have s6 : WExec cap (WM.fwdC sT rPT) (st q 0 0 (false :: List.replicate q true ++ [false]) c)
      ⟨![0, 1], ![List.replicate q true, UnaryTemplate.tape q], ![0, 1], c⟩ 5 := by
    refine WExec.cast cap (wfwdC_spec cap sT rPT _ (by simp [st]; omega)) ?_ le_rfl
    refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext i; fin_cases i <;> simp [st, UnaryTemplate.tape, WState.seth, WState.setv, Function.update_apply])
  exact WExec.mono (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))) (by omega)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTemplate
