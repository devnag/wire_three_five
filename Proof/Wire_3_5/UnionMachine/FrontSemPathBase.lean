import Proof.Wire_3_5.UnionMachine.FrontSemDecBase

/-! # C6 front, the semantic core (5): the chain after phase 2 at a decoded guess (P3:3672-3691)

At a witness whose checks pass (the entries' scan and the atom test at the description envelope), the chain after
phase 2 (`FrontRest.restM` at the guess's mode) runs to the end's bank (`FrontSemTW.endOut`): the entries' positions
and payloads form the atom stage's input (**`atomsOK_of`**), the guess's words are the chain's sources, C1's carrier
loop reads the guess's carriers and literal list, and the end is `FrontSemTW.end_sem` (**`valid_rest`**).

Paper quantity of the main type: the front's output bank at a valid witness. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter gridWord)
open NearCubicWires.RepairOrdinary

/-! ## The atom stage's input -/

section Atoms

theorem shape_len (r : List Bool) (p : ℕ) (b x : Bool) (pay rest : List Bool)
    (h : r.drop p = gridWord b x ++ (List.replicate pay.length true ++ false :: pay) ++ rest) :
    p + 2 * pay.length + 5 ≤ r.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append, List.length_replicate, List.length_cons, gridWord,
    List.length_nil] at hl
  omega

theorem pos_ge (r : List Bool) (En : ℕ) (hpos0 : posOf r En 0 = 0)
    (hpos : ∀ j, j < En → posOf r En (j + 1) = posOf r En j + 2 * (payOf r En j).length + 5) :
    ∀ j, j ≤ En → 5 * j ≤ posOf r En j
  | 0, _ => by omega
  | j + 1, hj => by
    have := pos_ge r En hpos0 hpos j (by omega)
    rw [hpos j (by omega)]; omega

/-- The atom stage's per-atom constants. -/
noncomputable def KcOf (pay : ℕ → List Bool) (En : ℕ) : ℕ := FrontSemTW.supR (fun j => 70 * ((pay j).length + 2)) En
noncomputable def KdOf (nx : ℕ) (pay : ℕ → List Bool) (En : ℕ) : ℕ :=
  FrontSemTW.supR (fun j => CloseoutRowsCircuitWholeBudget.budget (FrontAtomStageL.capP nx) (pay j).length) En

/-- **The entries' positions and payloads are the atom stage's input.** -/
theorem atomsOK_of (r v : List Bool) (En nx q : ℕ) (hr : restAfter En r = some v) (hE1 : 1 ≤ En)
    (hrx : r.length + 1 ≤ nx) (hq : q + 3 ≤ 2 * nx + 2) :
    FrontAtP.AtomsOK r nx q En nx (posOf r En) (payOf r En) (KcOf (payOf r En) En) (KdOf nx (payOf r En) En) := by
  obtain ⟨h0, hent, hk, hpos⟩ := atom_shapes En r v hr
  have hlen : ∀ j, j < En → posOf r En j + 2 * (payOf r En j).length + 5 ≤ r.length := fun j hj => by
    obtain ⟨b, x, rest, e⟩ := hent j hj; exact shape_len r _ b x _ rest e
  have hcov := fun j (hj : j < En) => FrontAtomStageL.capP_covers nx (payOf r En j) (by have := hlen j hj; omega)
  refine ⟨hE1, h0, hent, hk, hpos, fun j hj => (hcov j hj).2.2, fun j hj => (hcov j hj).2.1, fun j hj => ?_, hq, ?_,
    fun j hj => FrontSemTW.le_supR (fun j => 70 * ((payOf r En j).length + 2)) En j hj,
    fun j hj => FrontSemTW.le_supR (fun j => CloseoutRowsCircuitWholeBudget.budget (FrontAtomStageL.capP nx)
      (payOf r En j).length) En j hj⟩
  · have := hlen j hj; omega
  · have h5 := pos_ge r En h0 hpos (En - 1) (by omega)
    have := hlen (En - 1) (by omega)
    omega

end Atoms

/-! ## The end's tape positions on the valid path -/

section Pos
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontRest
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))

theorem c1R_lt : (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val < 2 + NL P + oE m Dw Dl deg De Dt c k0 := by
  unfold c1R FrontC1D.c1O
  rw [sl_none P tf _ _ _ _ (FrontCh5.insL_none_of P tf _ _ (by
    intro p hp
    simp only [FrontC1D.c1L, List.mem_cons, List.not_mem_nil, or_false] at hp
    have e : (FrontC1D.stL c (C1Stage.outT c)).val = 1436 + C1Stage.TC c + 1 := rfl
    have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega))), rg_val]
  have := (FrontC1D.stL c (C1Stage.outT c)).isLt
  unfold oE
  show 2 + NL P + (oC m Dw Dl deg De Dt k0 + 8 + _) < 2 + NL P + (oC m Dw Dl deg De Dt k0 + (8 + FrontC1D.NC c))
  omega

/-- **The end's positions, as arithmetic**: ten values and a count in the known layout. -/
theorem pos_arith (b k0 Dw Dl OA AP0 O5 NS OC CP OE po a1 a2 a3 a4 a5 a6 a7 a8 a9 aw : ℕ)
    (hpo1 : b ≤ po) (hpo2 : po < b + k0) (haw : aw = b + (k0 + 4 + (3 + 2 * Dw)))
    (ha2 : a2 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 2))
    (ha7 : a7 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 0))
    (ha8 : a8 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 7))
    (hOA : OA = k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 71 + 22) (hO5 : O5 = OA + AP0)
    (ha1 : a1 = b + (O5 + 2)) (ha4 : a4 = b + (O5 + 40 + 0)) (ha5 : a5 = b + (O5 + 50 + 5))
    (ha6 : a6 = b + (O5 + 50 + 6)) (ha9 : a9 = b + (O5 + 50 + 7)) (hOC : OC = O5 + 50 + NS) (hNS : 1225 ≤ NS)
    (hOE : OE = OC + CP) (ha3 : b + OC ≤ a3) (ha3' : a3 < b + OE) :
    Function.Injective (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) ∧
    (∀ i, b ≤ (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i ∧
      (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i < b + OE) ∧
    (b ≤ aw ∧ aw < b + OE) ∧ (∀ i, (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i ≠ aw) := by
  have c1 : po < a2 := by omega
  have c2 : a2 < a7 := by omega
  have c3 : a7 < a8 := by omega
  have c4 : a8 < a1 := by omega
  have c5 : a1 < a4 := by omega
  have c6 : a4 < a5 := by omega
  have c7 : a5 < a6 := by omega
  have c8 : a6 < a9 := by omega
  have c9 : a9 < a3 := by omega
  have w1 : po < aw := by omega
  have w2 : aw < a2 := by omega
  have e1 : b ≤ aw := by omega
  have e2 : a3 < b + OE := ha3'
  clear haw ha2 ha7 ha8 hOA hO5 ha1 ha4 ha5 ha6 ha9 hOC hOE ha3 hNS hpo2 ha3'
  refine ⟨fun i j hij => ?_, fun i => ?_, ⟨e1, by omega⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  · fin_cases i <;> simp <;> omega
  · fin_cases i <;> simp <;> omega

/-- **The end's tape positions**: the ten sources and the count lie below the end's regions, pairwise apart. -/
theorem end_pos (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) :
    Function.Injective (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT) ∧
    (∀ i, 2 + NL P ≤ (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val ∧
      (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val < 2 + NL P + oE m Dw Dl deg De Dt c k0) ∧
    (2 + NL P ≤ (wcR P tf m Dw Dl deg De Dt c k0 h qT).val ∧
      (wcR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + oE m Dw Dl deg De Dt c k0) ∧
    (∀ i, srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i ≠ wcR P tf m Dw Dl deg De Dt c k0 h qT) := by
  obtain ⟨o1, o2, o3, o4, o5e, o6, o7⟩ := offs m Dw Dl deg De Dt k0
  have hfun : (fun i => (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val) = ![poT.val, (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val, (hdR P tf m Dw Dl deg De Dt c k0 h qT).val,
      (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val, (ccR P tf m Dw Dl deg De Dt c k0 h).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val,
      (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val, (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val] := by
    funext i; fin_cases i <;> rfl
  have A := pos_arith (2 + NL P) k0 Dw Dl (oA Dw Dl k0) FrontAtP.AP (o5 Dw Dl k0) (FrontCh5.NSF m deg De Dt)
    (oC m Dw Dl deg De Dt k0) (FrontC1D.C1P c) (oE m Dw Dl deg De Dt c k0) poT.val
    (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val (hdR P tf m Dw Dl deg De Dt c k0 h qT).val
    (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val (ccR P tf m Dw Dl deg De Dt c k0 h).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val (wcR P tf m Dw Dl deg De Dt c k0 h qT).val
    hpL.1 hpL.2 (wcR_v P tf m Dw Dl deg De Dt c k0 h qT)
    (by rw [hdR_v, o1, o2])
    (by rw [nuR_v0, o1, o2, o3])
    (by rw [nuR_v6, o1, o2, o3])
    (by rw [o4, o1, o2, o3]) o5e (unR_v P tf m Dw Dl deg De Dt c k0 h qT rT) (ccR_v P tf m Dw Dl deg De Dt c k0 h)
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num) (by norm_num)])
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num) (by norm_num)])
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num) (by norm_num)]) o6 o7 rfl
    (c1R_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT) (c1R_lt P tf m Dw Dl deg De Dt c k0 h qT rT poT)
  rw [← hfun] at A
  obtain ⟨A1, A2, A3, A4⟩ := A
  exact ⟨fun i j hij => A1 (congrArg Fin.val hij), A2, A3, fun i hi => A4 i (congrArg Fin.val hi)⟩

end Pos

/-! ## The valid path -/

section Valid
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontRest NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop (bank rlR rndM wSl)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)

end Valid

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath
