import Proof.Wire_3_5.Primitive.SeedFix.S3Big8

/-! # S3, part 15: the loop over the list seeds

`Σ_{e'} R̂_{e'}(c,u,v)` over the list seeds `e'_0, e'_1, …` of base's enumeration (P3:3170-3178, `rsum_seeds`): the
loop counts the seeds down in `qIc` and runs the seed body at seed `d` after `d` seeds. **`seedLoop_spec`**: from `d`
seeds done (the accumulator holds `rsumD d`, every table offset at `d·λ_j`), the loop ends with the accumulator
`rsumD N`, the offsets at `N·λ_j`, the invariant kept, every register outside the loop's as found.

Paper quantity of the main type: the accumulated `Σ_{i<N} R̂_{e'_i}(c,u,v)` (`rsumD`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)

/-- `R̂` at the `i`-th list seed as the four slots' AND (`0` past the seeds). -/
def rAt (k : SymCall) (c eu ev : BitInput k.P.n) (i : ℕ) : ℕ :=
  if h : i < Fintype.card k.Pl.FlatSeed then
    (circAt k (seedOf k ⟨i, h⟩) c eu ev 0 && circAt k (seedOf k ⟨i, h⟩) c eu ev 1 &&
      circAt k (seedOf k ⟨i, h⟩) c eu ev 2 && circAt k (seedOf k ⟨i, h⟩) c eu ev 3).toNat
  else 0

/-- **The accumulated sum after `d` seeds.** -/
def rsumD (k : SymCall) (c eu ev : BitInput k.P.n) (d : ℕ) : ℕ := ∑ i ∈ Finset.range d, rAt k c eu ev i

theorem rsumD_le (k : SymCall) (c eu ev : BitInput k.P.n) : ∀ d, rsumD k c eu ev d ≤ d
  | 0 => by simp [rsumD]
  | d + 1 => by
    have ih := rsumD_le k c eu ev d
    have h1 : rAt k c eu ev d ≤ 1 := by
      unfold rAt
      split
      · exact Bool.toNat_le _
      · omega
    unfold rsumD at ih ⊢
    rw [Finset.sum_range_succ]
    omega

/-- **The loop over the list seeds.** -/
def seedLoop : BM := .whr qIc (.seq (.dec qIc) seedBody)

theorem seedLoop_spec (cap : ℕ) (k : SymCall) (c eu ev : BitInput k.P.n)
    (hcap : ∀ (i : Fin (Fintype.card k.Pl.FlatSeed)) (j : Fin 4), j.val < k.a →
      CircCap cap k.Pl (seedOf k i) k.P.n (gatesJ k j) (topJ k j).length)
    (c1 : ∀ j : Fin 4, (templJ k j).length ≤ cap)
    (c2 : ∀ j : Fin 4, Fintype.card k.Pl.FlatSeed * tabLen k j ≤ cap) (c4 : 4 ≤ cap)
    (c5 : Fintype.card k.Pl.FlatSeed + 1 ≤ cap) :
    ∀ (rem d : ℕ), d + rem = Fintype.card k.Pl.FlatSeed → ∀ ω : BS, BodyInv k c eu ev (fun j => d * adv k j) ω →
      ω.val qIc = rem → ω.val qRh = 0 → ω.val qAc = 0 → ω.val qAcc = rsumD k c eu ev d →
      ∃ τ, WExec cap seedLoop ω τ (rem * (bodyCost k + 4) + 1) ∧
        BodyInv k c eu ev (fun j => Fintype.card k.Pl.FlatSeed * adv k j) τ ∧ τ.val qIc = 0 ∧ τ.val qRh = 0 ∧
        τ.val qAc = 0 ∧ τ.val qAcc = rsumD k c eu ev (Fintype.card k.Pl.FlatSeed) ∧
        (∀ r, r ≠ qIc → r ≠ qRh → r ≠ qAc → r ≠ qAcc → (∀ j, r ≠ qOff j) → τ.val r = ω.val r) := by
  intro rem
  induction rem with
  | zero =>
    intro d hd ω hI hic hrh hac hacc
    rw [Nat.add_zero] at hd
    subst hd
    exact ⟨ω, WExec.mono (WExec.whrF hic) (by omega), hI, hic, hrh, hac, hacc, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    intro d hd ω hI hic hrh hac hacc
    have hdN : d < Fintype.card k.Pl.FlatSeed := by omega
    -- count the seed down
    have e0 := WExec.dec (cap := cap) qIc ω (by rw [hic]; omega)
    obtain ⟨ω1, hω1⟩ : ∃ y, y = ω.setv qIc (ω.val qIc - 1) := ⟨_, rfl⟩
    rw [← hω1] at e0
    have I1 : BodyInv k c eu ev (fun j => d * adv k j) ω1 := by
      rw [hω1]; exact hI.setv _ _ (Or.inr ⟨by decide, by decide⟩)
    have v1 : ∀ r, r ≠ qIc → ω1.val r = ω.val r := fun r hr => by
      rw [hω1, WState.setv_val, Function.update_of_ne hr]
    -- the seed body at seed `d`
    have hsd : rsumD k c eu ev d ≤ d := rsumD_le k c eu ev d
    obtain ⟨ω2, e2, I2, a2, r2, c2', o2⟩ := seedBody_spec cap k c eu ev ⟨d, hdN⟩ _ ω1 I1
      (fun j hj => by
        show d * adv k j = d * tabLen k j
        unfold adv; rw [if_pos hj])
      (by rw [v1 _ (by decide), hrh]) (by rw [v1 _ (by decide), hac]) (hcap ⟨d, hdN⟩) c1
      (fun j => le_trans (Nat.mul_le_mul_right _ (show d + 1 ≤ Fintype.card k.Pl.FlatSeed by omega)) (c2 j)) c4
      (by rw [v1 _ (by decide), hacc]; omega)
    have hoffe : (fun j => (fun j => d * adv k j) j + adv k j) = fun j => (d + 1) * adv k j := by
      funext j; simp only; ring
    rw [hoffe] at I2
    have hic2 : ω2.val qIc = rem := by
      rw [o2 _ (by decide) (by decide) (by decide) (fun j => ne_qOff j (by decide)), hω1, WState.setv_val,
        Function.update_self, hic, Nat.add_sub_cancel]
    have hacc2 : ω2.val qAcc = rsumD k c eu ev (d + 1) := by
      rw [a2, v1 _ (by decide), hacc]
      unfold rsumD
      rw [Finset.sum_range_succ]
      congr 1
      unfold rAt
      rw [dif_pos hdN]
    obtain ⟨τ, e3, I3, t1, t2, t3, t4, o3⟩ := ih (d + 1) (by omega) ω2 I2 hic2 r2 c2' hacc2
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hic]; omega) (WExec.seq e0 e2) e3) (by rw [Nat.succ_mul]; omega), I3,
      t1, t2, t3, t4, fun r h1 h2 h3 h4 h5 => ?_⟩
    rw [o3 r h1 h2 h3 h4 h5, o2 r h2 h3 h4 h5, v1 r h1]

end NearCubicWires.WireExponent3_5.PrimT.S3
