import Proof.Wire_3_5.Primitive.SeedFix.HbCell

/-! # C4.Hb, machine part 18: the enumeration loop (`filt:soft`, P3:2253-2290)

"Expand each `A`-product into at most `2^{2t}` signed products [...] each printed term has fixed arity and at most
`poly(M,2^{O(k)})` integer size" (P3:2262-2290). The Hb machine is base's stream loop (`StreamController`, C6's
`whileRun`) over one cell (`cellM`) while the word state's bit `MORE` is set. **`hashEnum_run`**: from a bank with the
invariant before cell `0`, the loop reaches a bank with the invariant before cell `n`, whose output stream holds
`outAt n`, the printed words of all cells, within `n·(K + 2) + 1` steps.

Paper quantity of the main type: the printed words `outAt X.n` (through `HbX.Inv X.n`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The loop's condition tape: the word state's `MORE` stream. -/
def iMORE : Fin 94 := ⟨15, by omega⟩

/-- **The Hb machine**: the cell while `MORE` is set. -/
noncomputable def hashLoopM := StreamController.machine cellM iMORE

namespace HbX
variable (X : HbX)

theorem more_bit (c : ℕ) (A : Fin 94 → List Bool) (hA : X.Inv c A) : readTapeBit (A iMORE) 0 = decide (c < X.n) := by
  obtain ⟨st, R, O, W, P, g, v, rfl, _, hs, _, _⟩ := hA
  rw [show iMORE = (⟨15, by omega⟩ : Fin 94) from rfl, hbBank_lt X.cap X.capL _ _ 15 (by omega)]
  show readTapeBit ((wenc X.cap (bnd st)).A (sTape (14 : Fin 24))) 0 = _
  rw [wenc_A_s]
  simp [bnd, hs.more, readTapeBit]

theorem step_exists (hok : X.HbOk) (hcell : ∀ c < X.n, X.CellOk c) (K : ℕ) (hK : ∀ c < X.n, X.cellCost c ≤ K) :
    ∀ c < X.n, ∀ A, X.Inv c A → ∃ A', X.Inv (c + 1) A' ∧ Step cellM K (fun _ => 0) A (fun _ => 0) A' := by
  intro c hc A hA
  obtain ⟨A', h1, h2⟩ := cell_step X c hc hok (hcell c hc) A hA
  exact ⟨A', h1, h2.enlarge (hK c hc)⟩

/-- The banks between the cells, chosen along the invariant. -/
noncomputable def banks (K : ℕ)
    (hstep : ∀ c < X.n, ∀ A, X.Inv c A → ∃ A', X.Inv (c + 1) A' ∧ Step cellM K (fun _ => 0) A (fun _ => 0) A')
    (A0 : Fin 94 → List Bool) (h0 : X.Inv 0 A0) : (c : ℕ) → {A : Fin 94 → List Bool // c ≤ X.n → X.Inv c A}
  | 0 => ⟨A0, fun _ => h0⟩
  | c + 1 =>
    if h : c < X.n then
      ⟨Classical.choose (hstep c h (banks K hstep A0 h0 c).1 ((banks K hstep A0 h0 c).2 h.le)),
        fun _ => (Classical.choose_spec (hstep c h (banks K hstep A0 h0 c).1 ((banks K hstep A0 h0 c).2 h.le))).1⟩
    else ⟨(banks K hstep A0 h0 c).1, fun h' => absurd h' (by omega)⟩

/-- **The Hb machine's run**: all `n` cells, from the invariant before cell `0` to the invariant before cell `n`. -/
theorem hashEnum_run (hok : X.HbOk) (hcell : ∀ c < X.n, X.CellOk c) (K : ℕ) (hK : ∀ c < X.n, X.cellCost c ≤ K)
    (A0 : Fin 94 → List Bool) (h0 : X.Inv 0 A0) :
    ∃ A', X.Inv X.n A' ∧ Step hashLoopM (X.n * (K + 2) + 1) (fun _ => 0) A0 (fun _ => 0) A' := by
  have hstep := step_exists X hok hcell K hK
  let As : ℕ → Fin 94 → List Bool := fun c => (banks X K hstep A0 h0 c).1
  have hinv : ∀ c ≤ X.n, X.Inv c (As c) := fun c hc => (banks X K hstep A0 h0 c).2 hc
  have hb : ∀ c < X.n, Step cellM K (fun _ => 0) (As c) (fun _ => 0) (As (c + 1)) := by
    intro c hc
    show Step cellM K (fun _ => 0) (banks X K hstep A0 h0 c).1 (fun _ => 0) (banks X K hstep A0 h0 (c + 1)).1
    simp only [banks, dif_pos hc]
    exact (Classical.choose_spec (hstep c hc (banks X K hstep A0 h0 c).1 ((banks X K hstep A0 h0 c).2 hc.le))).2
  have hT : ∀ c < X.n, readTapeBit (As c iMORE) ((fun (_ : ℕ) (_ : Fin 94) => 0) c iMORE) = true := by
    intro c hc
    rw [more_bit X c (As c) (hinv c hc.le)]; simp [hc]
  have hF : readTapeBit (As X.n iMORE) ((fun (_ : ℕ) (_ : Fin 94) => 0) X.n iMORE) = false := by
    rw [more_bit X X.n (As X.n) (hinv X.n le_rfl)]; simp
  have hw := UnionMachine.whileRun cellM iMORE X.n K (fun _ _ => 0) As hT hF hb
  exact ⟨As X.n, hinv X.n le_rfl, hw⟩

end HbX

end NearCubicWires.WireExponent3_5.PrimT.HbM
