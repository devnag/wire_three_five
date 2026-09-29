import Proof.Wire_3_5.UnionMachine.EwSize

/-! # C6, e/W_j: THE `e`/`W_j` STAGE, built to `EWSpec2`

"`H_h(x) ≤ H_max := A(M + J M^{2t}) = 2^{O_D(L^2)}`" (filt:H-bounds, P3:2143) and the level windows
"`W_j = 16t + 20(⌊√(t·B_*)⌋ + 1)/2^{⌊j/2⌋} + 20`" (filt:majorant, P3:2150-2157): one register program on its own
layout `WState 8 48` (inputs `M, A, B_*, K, J, t` in registers `0 … 5`, `e` in `6`, the window records on stream `0`):
the window block (`EwRecs.winW`, the records `Joins.winRecs (thrMP M A B_* K)`), then the `e` phase (`EwE.eW`,
`e = Primitive.listE A B_* M K` in binary), compiled (`WM.toProg.compile`) and run as a `Step`.
* **`ewSpec2 : PrimThrW.EW.EWSpec2`**: need `10^13·(m+1)^12`, time `10^21·(m+1)^18`, `m = M + A + B_* + K`;
  the streams `1 … 8` keep their width-`wd` words (the bounded residue of).

Paper quantities of the main type: the aux filter's `e` and the fixed hash's windows `W_j`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch

/-- The window block's registers: `t = 5`, `B_* = 2`, `J = 4`, scratch `7 … 35`. -/
def wmap : Fin 32 ↪ Fin 48 := ⟨![5, 2, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], by decide⟩

@[simp] theorem wmap_apply (i : Fin 32) : wmap i = ![5, 2, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] i := rfl

/-- The input registers `M, A, B_*, K, J, t`. -/
def inpR : Fin 6 → Fin 48 := ![0, 1, 2, 3, 4, 5]

/-- **The stage's program**: the window block, then the `e` phase. -/
def ewProg : WM 8 48 := .seq (EwRecs.winW 0 wmap) EwE.eW

theorem wmap_hi (i : Fin 32) (hi : 3 ≤ i.val) : 7 ≤ (wmap i).val := by
  fin_cases i <;> simp_all

theorem run (cap Mv Av Bs den : ℕ) (σ : WState 8 48) (h0 : σ.val (inpR 0) = Mv) (h1 : σ.val (inpR 1) = Av)
    (h2 : σ.val (inpR 2) = Bs) (h3 : σ.val (inpR 3) = den) (h4 : σ.val (inpR 4) = Primitive.listJ Av Bs den)
    (h5 : σ.val (inpR 5) = Primitive.listT Av Bs den) (hz : ∀ r, (∀ k, inpR k ≠ r) → σ.val r = 0)
    (hs : ∀ i : Fin 9, σ.st i = [] ∧ σ.sh i = 0) (hc : σ.cell = false)
    (hneed : EwSize.ewNeed (Mv + Av + Bs + den) ≤ cap) :
    ∃ (τ : WState 8 48) (m : ℕ), Step ewProg.toProg.compile m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H
        (wenc cap τ).A ∧
      m ≤ EwSize.ewBound (Mv + Av + Bs + den) ∧ (∀ k, τ.val (inpR k) = σ.val (inpR k)) ∧
      τ.val 6 = Primitive.listE Av Bs Mv den ∧ (∀ r, (∀ k, inpR k ≠ r) → r ≠ 6 → τ.val r = 0) ∧
      τ.st 0 = PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP Mv Av Bs den) ∧ τ.sh 0 = 0 ∧
      (∀ i : Fin 9, i ≠ 0 → (τ.st i).length ≤ EwSize.ewBound (Mv + Av + Bs + den) ∧ τ.sh i = 0) ∧
      τ.cell = false := by
  have g0 : σ.val 0 = Mv := h0
  have g1 : σ.val 1 = Av := h1
  have g2 : σ.val 2 = Bs := h2
  have g3 : σ.val 3 = den := h3
  have g4 : σ.val 4 = Primitive.listJ Av Bs den := h4
  have g5 : σ.val 5 = Primitive.listT Av Bs den := h5
  have hz6 : ∀ r : Fin 48, 6 ≤ r.val → σ.val r = 0 := by
    intro r hr
    apply hz r
    intro k hk
    subst hk
    fin_cases k <;> simp [inpR] at hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwdY, -, hY1⟩ := EwSize.yb Mv Av Bs den
  have hW1 := EwSize.winNeed_le Mv Av Bs den
  have hE1 := EwSize.eNeed_le Mv Av Bs den
  have hWc := EwSize.winCost_le Mv Av Bs den
  have hEc := EwSize.eCost_le Mv Av Bs den
  have hsq := EwSize.sq_y (Mv + Av + Bs + den)
  have hcu := EwSize.cube_y (Mv + Av + Bs + den)
  generalize hJd : Primitive.listJ Av Bs den = J at *
  generalize htd : Primitive.listT Av Bs den = t at *
  obtain ⟨n1, w1, hn1⟩ := EwRecs.winW_spec cap 0 wmap σ t Bs J g5 g2 g4
    (fun i hi => hz6 _ (by have := wmap_hi i hi; omega)) (hs 0).1 (hs 0).2 (by omega)
  obtain ⟨τ, w2, hv6, hval, hst, hst0, hsh0, hcell⟩ := EwE.e_spec cap (σ.sets 0 (EwWin.winList t Bs J)) Mv Av
    den J t (by simp [g0]) (by simp [g1]) (by simp [g3]) (by simp [g4]) (by simp [g5])
    (fun r hr => by simp [hz6 r hr]) (fun i hi => by simp [Function.update_apply, hi, (hs i).1, (hs i).2])
    (by omega)
  have hx := WExec.seq w1 w2
  refine ⟨τ, _, (WExec.exec cap hx).step, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc3 : n1 + 1 + EwE.eCost Mv Av den J t ≤ 2 * (10 ^ 7 * (EwSize.yOf (Mv + Av + Bs + den) + 1) *
        (EwSize.yOf (Mv + Av + Bs + den) + 1) * (EwSize.yOf (Mv + Av + Bs + den) + 1)) + 1 := by omega
    have hY : 1 ≤ 10 ^ 7 * (EwSize.yOf (Mv + Av + Bs + den) + 1) * (EwSize.yOf (Mv + Av + Bs + den) + 1) *
        (EwSize.yOf (Mv + Av + Bs + den) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  · intro k
    rw [hval _ (by fin_cases k <;> simp [inpR])]
    fin_cases k <;> simp [inpR]
  · rw [hv6, EwE.listE_eq, hJd, htd]
  · intro r hr hr6
    rw [hval r hr6]
    simp [hz r hr]
  · rw [hst0, ← EwRecs.winList_winRecs Mv Av Bs den, htd, hJd]
    simp
  · rw [hsh0]; simp [(hs 0).2]
  · intro i hi
    refine ⟨?_, (hst i hi).2⟩
    rw [(hst i hi).1]
    have hY3 : EwSize.yOf (Mv + Av + Bs + den) ≤ 10 ^ 7 * (EwSize.yOf (Mv + Av + Bs + den) + 1) *
        (EwSize.yOf (Mv + Av + Bs + den) + 1) * (EwSize.yOf (Mv + Av + Bs + den) + 1) := by
      generalize EwSize.yOf (Mv + Av + Bs + den) = Y
      nlinarith [Nat.zero_le (Y * Y), Nat.zero_le (Y * Y * Y)]
    omega
  · rw [hcell]; simp [hc]

end NearCubicWires.WireExponent3_5.UnionMachine.EwStage
