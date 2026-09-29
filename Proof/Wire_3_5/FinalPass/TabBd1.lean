import Proof.Wire_3_5.FinalPass.TabShell
import Proof.Wire_3_5.UnionMachine.FiltPipeLe

/-! # S4 (f1), the tables writer, part 10: the writer's sizes, the pieces (P3:2036-2101, 3170-3178)

The pieces of the writer's size hypotheses at the call's sizes `≤ X`: a seed's table's length (**`tw_len`**, every
seed alike; `tw_le`), the unit request word's length (`reqT_len`, `reqT_le`), C6's FILTER setup need (`need_le`) and
bound (`bound_le`), the table stages' cost (**`tabPre_le`**, `FiltPipeLe.partAD`), the boot (`boot_le`).

Paper quantity of the main type: the unit's time and space, polynomial in the call's sizes (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem len_flatMap_const' {α : Type} (l : List α) (f : α → List Bool) (c : ℕ) (h : ∀ x ∈ l, (f x).length = c) :
    (l.flatMap f).length = l.length * c := by
  rw [List.length_flatMap, List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

/-- **A seed's table's length.** -/
theorem tw_len (P : GapParams) (e : GapSeed P) (L : ℕ) :
    (tableWord (filterTable P e L)).length = P.walkLen * (2 + 128 * (2 * L + 2)) + 1 := by
  have h128 : ∀ vs ∈ filterTable P e L, vs.length = 128 := by
    intro vs hmem
    simp only [filterTable, List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    simp
  have hvw : ∀ vs ∈ filterTable P e L, (visitWord vs).length = 2 + 128 * (2 * L + 2) := fun vs hmem => by
    simp only [visitWord, List.length_cons, List.length_append, List.length_singleton]
    rw [len_flatMap_const' vs copyWord (2 * L + 2) (fun cs hcs => by
      simp [copyWord, frame_eq_frameP, filterTable_lengths P e L vs hmem cs hcs] <;> omega), h128 vs hmem]
    simp only [List.length_nil]
    ring
  simp only [tableWord, List.length_append, List.length_singleton]
  rw [len_flatMap_const' _ visitWord _ hvw]
  simp [filterTable]

theorem tw_le (P : GapParams) (e : GapSeed P) (L X : ℕ) (hL : L ≤ X) (he : P.errExp ≤ X) (hX : 2 ≤ X) :
    (tableWord (filterTable P e L)).length ≤ 1100 * (X * X) := by
  rw [tw_len]
  have hwk := UnionMachine.FiltPipeLe.walkLen_le P
  have h1 : P.walkLen ≤ X + 1 := by omega
  have h2 : 2 + 128 * (2 * L + 2) ≤ 258 + 256 * X := by omega
  have h3 := Nat.mul_le_mul h1 h2
  nlinarith

/-- The unit request word's length. -/
theorem reqT_len (n len cp err L0 L1 nE : ℕ) :
    (reqT n len cp err L0 L1 nE).length =
      2 * natBitLength n + 1 + 7 + (len + 1) + (cp + 1) + (err + 1) + (L0 + 1) + (L1 + 1) + (nE + 1) := by
  rw [reqT_eq, List.length_append, ParseNat.natWord_length]
  simp [Data.unaryList]
  ring

theorem reqT_le (n len cp err L0 L1 nE X : ℕ) (hn : n + 2 ≤ X) (h1 : len ≤ X) (h2 : cp ≤ X) (h3 : err ≤ X)
    (h4 : L0 ≤ X) (h5 : L1 ≤ X) (h6 : nE ≤ X) : (reqT n len cp err L0 L1 nE).length ≤ 16 * X := by
  have hbl : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  rw [reqT_len]
  omega

section Pieces
variable (W : WalkBankProducer) (F5 : FiltSetupSpec5 W)

/-- C6's FILTER setup need at sizes `≤ X`. -/
theorem need_le (len cp err L nE X : ℕ) (h : len + cp + err + L + nE + 1 ≤ X) :
    F5.need len cp err L 0 0 0 nE ≤ F5.Cn * X ^ F5.Dn := by
  have hp := F5.need_poly len cp err L 0 0 0 nE
  unfold ValidatorPolynomialDomination.PolyBounded at hp
  exact hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

/-- C6's FILTER setup bound at a capacity `c ≤ X`. -/
theorem bound_le (c X : ℕ) (h : c + 1 ≤ X) : F5.bound c ≤ F5.Cb * X ^ F5.Db := by
  have hp := F5.bound_poly c
  unfold ValidatorPolynomialDomination.PolyBounded at hp
  exact hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))

end Pieces

/-- **The table stages' cost** at sizes `≤ X` (`partAD`). -/
theorem tabPre_le (P : GapParams) (L X : ℕ) (h : P.len + P.cap + P.errExp + L + 2 ≤ X) :
    tabPreCost P L (rulerW P) (rulerW P) ≤ 50000000 * (30000 * X) ^ 4 := by
  have a := UnionMachine.FiltPipeLe.atoms P L 0 0 0
  have hp := UnionMachine.FiltPipeLe.partAD P L 0 0 0 _ _ a
  unfold tabPreCost
  refine hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 4))
  omega

/-- The boot's cost at the unit request word. -/
theorem boot_le (w : List Bool) (n X : ℕ) (hw : w.length ≤ X) (hn : n + 2 ≤ X) :
    ShellD.bootCost w n 0 0 ≤ 250 * X := by
  have hbl : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have b00 := UnaryCalc.poly_cost_polyBounded 0 0 n
  unfold ValidatorPolynomialDomination.PolyBounded at b00
  have e00 : UnaryCalc.polyCoefficient 0 0 * (n + 1) ^ (0 + 1) = 13 * (n + 1) := by
    simp [UnaryCalc.polyCoefficient]
  have v00 : UnaryCalc.value 0 0 n = 0 := by simp [UnaryCalc.value]
  unfold ShellD.bootCost
  rw [v00]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.TabW
