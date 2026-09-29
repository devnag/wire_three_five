import Proof.Wire_3_5.Primitive.SeedFix.CtrWhole

/-! # X3, part 14: the center writer at any layout, and the sum over the centers (P3:1206-1216)

The final pass (the X3 seam) enumerates the cell centers of the partition `σ` by table position `(row, col)` and
writes each center with the center writer. Here:

* **`ctrW S R`** (C5's `WM.liftW` of `ctrM`): the streams `S 0 … S 3` (offset, row, column, center) and the registers
  `R 0 … R 4` (`b`, `s`, `r/2`, `hL`, `n − rb − hL`), `R 5 … R 25` scratch;
* **`ctrW_spec`**: from the offset `frameP (ofFn (offset P σ)) ++ [false]` (FLIPS's `sOFF`, `offW_eq`), the row
  `frame (binary dRow row)`, the column `frame (binary dR col)` (C6's `NumOn` format), heads `0`, scratch `0`, and any
  old center frame (at most `2n + 1` cells), the center stream holds `frameP (List.ofFn (centerAt P σ row col)) ++
  [false]` at head `0`; every other stream and every register is back at its entry value; nothing outside moves;
* `ctrCost_le`: the steps are at most `1500·(n+2)^4`;
* **`sum_centers`**: `Σ_{c center} F c = Σ_{row < 2^dRow} Σ_{col < 2^dR} F (centerAt P σ row col)` (V3's bijection).

Paper quantity of the main types: the cell centers of the partition `σ` (P3:1206-1209). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **The center writer at any layout.** -/
def ctrW {ns nr : ℕ} (S : Fin 4 → Fin (ns + 1)) (R : Fin 26 ↪ Fin nr) : WM ns nr := ctrM.liftW S R

/-- **The center writer's run** (the X3 seam). -/
theorem ctrW_spec {ns nr : ℕ} (cap : ℕ) (P : StarParams) (σT : P.Translation) (row col : ℕ)
    (S : Fin 4 → Fin (ns + 1)) (hS : Function.Injective S) (R : Fin 26 ↪ Fin nr) (ω : WState ns nr)
    (hoff : ω.st (S 0) = frameP (List.ofFn (offset P σT)) ++ [false])
    (hrow : ω.st (S 1) = frame (binary (dRow P) row)) (hcol : ω.st (S 2) = frame (binary (dR P) col))
    (hctr : (ω.st (S 3)).length ≤ 2 * P.n + 1) (hsh : ∀ i, ω.sh (S i) = 0)
    (hB : ω.val (R 0) = P.b) (hs : ω.val (R 1) = P.s) (hH : ω.val (R 2) = P.r / 2) (hHL : ω.val (R 3) = hL P)
    (hHR : ω.val (R 4) = P.n - P.r * P.b - hL P) (hz : ∀ i : Fin 26, 5 ≤ i.val → ω.val (R i) = 0)
    (hcap : 8 * (P.n + 2) ≤ cap) :
    ∃ ω', WExec cap (ctrW S R) ω ω' (ctrCost P) ∧
      ω'.st (S 3) = frameP (List.ofFn (centerAt P σT row col)) ++ [false] ∧ (∀ i, ω'.sh (S i) = 0) ∧
      (∀ i, i ≠ 3 → ω'.st (S i) = ω.st (S i)) ∧ (∀ i, ω'.val (R i) = ω.val (R i)) ∧ ω'.cell = ω.cell ∧
      OutsideW S R ω ω' := by
  let x : CS := ⟨fun i => ω.sh (S i), fun i => ω.st (S i), fun r => ω.val (R r), ω.cell⟩
  obtain ⟨τ, e, a, b, c, d, f⟩ := ctrM_spec cap P σT row col (ω.st (S 3)) x hoff
    (by show ω.st (S 1) = _; rw [hrow, frame_eq_frameP]) (by show ω.st (S 2) = _; rw [hcol, frame_eq_frameP]) rfl hctr
    (fun i => hsh i) hB hs hH hHL hHR hz hcap
  have hL : LiftW S R ω x := ⟨fun i => rfl, fun i => rfl, fun r => rfl, rfl⟩
  obtain ⟨ω', e', hL', hO'⟩ := WExec.liftW cap cap le_rfl S hS R R.injective e ω hL
  refine ⟨ω', e', ?_, fun i => ?_, fun i hi => ?_, fun i => ?_, ?_, hO'⟩
  · rw [hL'.st 3]; exact a
  · rw [hL'.sh i]; exact c i
  · rw [hL'.st i]; exact b i hi
  · rw [hL'.val i, d]
  · rw [hL'.cell]; exact f

/-- **The sum over the cell centers is the sum over the table positions** (`row < 2^dRow`, `col < 2^dR`, V3). -/
theorem sum_centers {M : Type} [AddCommMonoid M] (P : StarParams) (σ : P.Translation) (F : BitInput P.n → M) :
    ∑ c : {c // P.IsCenter σ c}, F c.1 =
      ∑ row ∈ Finset.range (2 ^ dRow P), ∑ col ∈ Finset.range (2 ^ dR P), F (centerAt P σ row col) := by
  symm
  let e : Fin (2 ^ dRow P) × Fin (2 ^ dR P) → {c // P.IsCenter σ c} :=
    fun p => ⟨centerAt P σ p.1 p.2, centerAt_isCenter P σ p.1 p.2⟩
  have hinj : Function.Injective e := by
    intro p p' h
    have h' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := centerAt_inj P σ p.1 p.2 p'.1 p'.2 p.1.isLt p'.1.isLt p.2.isLt p'.2.isLt h'
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hcard : Fintype.card (Fin (2 ^ dRow P) × Fin (2 ^ dR P)) = Fintype.card {c // P.IsCenter σ c} := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, P.card_centers σ, ← pow_add]
    congr 1
    exact P.centerBits_sum
  have hbij : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).mpr ⟨hinj, hcard⟩
  have hs := hbij.sum_comp (fun c : {c // P.IsCenter σ c} => F c.1)
  rw [← hs, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun row => ∑ col ∈ Finset.range (2 ^ dR P), F (centerAt P σ row col))]
  apply Finset.sum_congr rfl
  intro row _
  rw [← Fin.sum_univ_eq_sum_range (fun col => F (centerAt P σ row col))]

end NearCubicWires.WireExponent3_5.PrimT.Ctr
