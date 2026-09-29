import Proof.Wire_3_5.Selection.GateMain
import Proof.Wire_3_5.Selection.Plan

/-! # C1.5: the word function from one register-machine run (P3:1324-1362, 3673)

Paper: "Select a minimum objective" (P3:1360); the union machine "selects the common star translation" (P3:3673).
C1's run residual `C1Run` (Plan) asks for the compiled machine's `Step` from the word function's entry bank (the framed
request on tape `0`, every other tape empty, every head at `0`) to a bank with every head at `0` whose output tape
holds `cosetWord (selArgmin R)`. This module reduces it to ONE register-machine run `C1WM`: from the entry state
`entrySt` (the framed request on stream `0`, every other stream empty, every register `0`) to a state whose output
stream holds the selected coset's word, every head at `0` and every register at `0`. The compiled program's encoded
entry bank is the word function's entry bank padded (the result cell `[false]`, each register tape blank of capacity
`cap + 1`), so base's `ZeroPadding.run_unpad` runs the same machine from the empty tapes. Main declarations:
`entrySt`, `C1WM`, `capT`, `wenc_entry_H`, `wenc_entry_A`, **`c1Run_of_wm`**. Paper quantity: the selected coset's
word on the output tape. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Top
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.SelectionMachine.Plan

variable {ns nr : ℕ}

/-- **The entry state**: the framed word `w` on stream `0`, every other stream empty, every head and register at
`0`, the result cell `false`. -/
def entrySt (w : List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame w else [], fun _ => 0, false⟩

/-- **C1 as one register-machine run**: on every request meeting C1's base precondition, the program runs within
`cost R` steps at register capacity `capOf R` from the entry state of `selWord R` to a state whose stream `OUT` holds
`cosetWord (selArgmin R)`, every head at `0`, every register at `0`. -/
def C1WM (Pw : WM ns nr) (OUT : Fin (ns + 1)) (capOf cost : SelectionReq → ℕ) : Prop :=
  ∀ R : SelectionReq, BasePre R → ∃ τ : WState ns nr, WExec (capOf R) Pw (entrySt (selWord R)) τ (cost R) ∧
    τ.st OUT = cosetWord (selArgmin R) ∧ (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0)

/-- The padding capacities of the encoded bank: `0` on a stream, `1` on the result cell, `cap + 1` on a register. -/
def capT (cap : ℕ) (j : Fin (ns + 2 + nr)) : ℕ :=
  match role j with
  | .stream _ => 0
  | .cell => 1
  | .reg _ => cap + 1

theorem wenc_entry_H (cap : ℕ) (w : List Bool) : (wenc cap (entrySt (ns := ns) (nr := nr) w)).H = fun _ => 0 := by
  funext j
  simp only [wenc]
  cases role j <;> rfl

theorem wenc_entry_A (cap : ℕ) (w : List Bool) : (wenc cap (entrySt (ns := ns) (nr := nr) w)).A =
    fun j => ZeroPadding.pad (capT cap j) (if j.val = 0 then frame w else []) := by
  funext j
  simp only [wenc, capT]
  cases h : role j with
  | stream i =>
    have hj := role_stream h
    subst hj
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst hi'
      simp [entrySt, sTape]
    · have hi' : i ≠ 0 := fun e => hi (by rw [e]; rfl)
      simp [entrySt, sTape, hi, hi']
  | cell =>
    have hj := role_cell h
    subst hj
    simp [entrySt, cTape, ZeroPadding.pad]
  | reg r =>
    have hj := role_reg h
    subst hj
    simp [entrySt, rTape, regTape, ZeroPadding.pad, List.replicate_succ]

/-- **C1's run residual from one register-machine run.** -/
theorem c1Run_of_wm (Pw : WM ns nr) (OUT : Fin (ns + 1)) (capOf cost : SelectionReq → ℕ)
    (h : C1WM Pw OUT capOf cost) : C1Run Pw.toProg.compile (sTape OUT) cost := by
  intro R hR
  obtain ⟨τ, hx, hout, hsh, hval⟩ := h R hR
  obtain ⟨src, hsrc, hH, hA, hs⟩ := (WExec.exec (capOf R) hx).step
  have e : ZeroPadding.config (capT (capOf R))
      (⟨Pw.toProg.compile.start, fun _ => 0, fun j => if j.val = 0 then frame (selWord R) else []⟩ :
        Configuration (ns + 2 + nr) _) =
      ⟨Pw.toProg.compile.start, (wenc (capOf R) (entrySt (ns := ns) (nr := nr) (selWord R))).H,
        (wenc (capOf R) (entrySt (ns := ns) (nr := nr) (selWord R))).A⟩ := by
    rw [wenc_entry_H, wenc_entry_A]
    rfl
  have hsrc' := hsrc
  rw [← e] at hsrc'
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad Pw.toProg.compile (capT (capOf R)) _ _ src hsrc'
  refine ⟨r.final.tapes, ⟨r, hr, ?_, rfl, by omega⟩, ?_⟩
  · have e2 := congrArg Configuration.heads hcf
    change r.final.heads = src.final.heads at e2
    rw [e2, hH]
    funext j
    simp only [wenc]
    cases role j with
    | stream i => exact hsh i
    | cell => rfl
    | reg r' => exact hval r'
  · have e2 := congrFun (congrArg Configuration.tapes hcf) (sTape OUT)
    change ZeroPadding.pad (capT (capOf R) (sTape (nr := nr) OUT)) (r.final.tapes (sTape OUT)) =
      src.final.tapes (sTape OUT) at e2
    have h0 : capT (capOf R) (sTape (nr := nr) OUT) = 0 := by simp [capT, role_sTape]
    rw [h0, ZeroPadding.pad_zero, hA] at e2
    rw [e2, wenc_A_s, hout]

theorem sTape_ne_zero (OUT : Fin (ns + 1)) (h : OUT.val ≠ 0) : (sTape (nr := nr) OUT).val ≠ 0 := by
  simp [sTape, h]

end NearCubicWires.WireExponent3_5.SelectionMachine.Top
