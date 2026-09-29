import Proof.Wire_3_5.Primitive.SeedFix.C4SymWD
import Proof.Wire_3_5.Primitive.SeedFix.C4WA
import Proof.Wire_3_5.UnionMachine.SampStage

/-! # C4 SYM stage, part 5: the stage on the SYM layout (the consumer dock of the wrapper and the setup)

"For each candidate child prefix [...] Choose a child with no larger sum. After `S` decisions the actual trace objective
is no larger than its random expectation" (P3:3034-3038); "The sample positions are `S_j = π(f(λ_j))`" (P3:2932-2937).
On the SYM layout (`C4Set.Lay`, the setup at capacity `2^m`, `C4Cap.setup_run2`), the decision loop of a child
family of the shape `ChShape` docked by `symExt` (`C4Wrap.LoopEntry` from `SymBank`, `entry_all`), and C6's sample
expansion (`UnionMachine.SampStage.sampM`) docked above the loop's cells by `finExt` (`C4Wrap.FinDock`): the stage ends
with the sample word of the fixed seed on port `2` (`C4Wrap.wrap_run`).

* `offF`, `finExt`, `finExt_some`, `pfx_slot`, **`sym_entry`** (`LoopEntry`), **`sym_fin`** (`FinDock`),
  **`symLay_run`**.

Paper quantity of the main type: the stage's output `sampleWord kh (seedPairs P s)` (the fixed seed's samples). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (LoopEntry FinDock postLoop wrapM wrapCost pfxL)

section Stage
variable (L : Lay)

/-- The finisher's region: above the loop's cells. -/
def offF : ℕ := L.oLP + L.T

theorem hoffF (htS : 31 ≤ L.tS) : offF L + 31 ≤ 3 + L.X := by
  have := Lay.N_eq L
  unfold offF Lay.oLP
  show _ ≤ L.N
  omega

theorem hoffL (F : C4Loop.ChildFam) (hT : F.T + 1 + 1 + 1 ≤ L.T) : L.oLP + (F.T + 1 + 1 + 1) ≤ 3 + L.X := by
  have := Lay.N_eq L
  unfold Lay.oLP
  show _ ≤ L.N
  omega

/-- **The finisher's slots**: the seed (the loop's prefix tape `gW 10`), `1^{kh}`, `1^Q`, `1^ℓ` (`gW 28, 29, 30`), the
modulus word (`gMB`), the output onto port `2`. -/
def finExt (j : Fin 31) : Option (Fin L.N) :=
  if j.val = 0 then some (L.gW 10) else if j.val = 2 then some (L.gW 28) else if j.val = 3 then some (L.gW 29)
  else if j.val = 4 then some (L.gW 30) else if j.val = 5 then some L.gMB else if j.val = 6 then some L.gP2 else none

theorem finExt_some {j : Fin 31} {g : Fin L.N} (h : finExt L j = some g) :
    (j.val = 0 ∧ g = L.gW 10) ∨ (j.val = 2 ∧ g = L.gW 28) ∨ (j.val = 3 ∧ g = L.gW 29) ∨ (j.val = 4 ∧ g = L.gW 30) ∨
      (j.val = 5 ∧ g = L.gMB) ∨ (j.val = 6 ∧ g = L.gP2) := by
  unfold finExt at h
  split_ifs at h with h0 h2 h3 h4 h5 h6 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp_all

theorem finExt_val {j : Fin 31} {g : Fin L.N} (h : finExt L j = some g) :
    (j.val = 0 ∧ g.val = 10055 + 3 * L.U) ∨ (j.val = 2 ∧ g.val = 10074 + 3 * L.U) ∨
      (j.val = 3 ∧ g.val = 10075 + 3 * L.U) ∨ (j.val = 4 ∧ g.val = 10076 + 3 * L.U) ∨
      (j.val = 5 ∧ g.val = 10630 + 3 * L.U) ∨ (j.val = 6 ∧ g.val = 2) := by
  have s10 : (symO 10).val = 130 := rfl
  have s28 : (symO 28).val = 149 := rfl
  have s29 : (symO 29).val = 150 := rfl
  have s30 : (symO 30).val = 151 := rfl
  rcases finExt_some L h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact Or.inl ⟨a, by show 9925 + 3 * L.U + (symO 10).val = _; omega⟩
  · exact Or.inr (Or.inl ⟨a, by show 9925 + 3 * L.U + (symO 28).val = _; omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, by show 9925 + 3 * L.U + (symO 29).val = _; omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by show 9925 + 3 * L.U + (symO 30).val = _; omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl⟩))))

/-- The loop's prefix slot is `gW 10`. -/
theorem pfx_slot (F : C4Loop.ChildFam) (pd : ℕ) (hP : F.PFX.val = 17) (hoff : L.oLP + (F.T + 1 + 1 + 1) ≤ L.N) :
    slx L.oLP hoff (symExt L pd) (pfxL F) = L.gW 10 := by
  have hv : (pfxL F).val = 17 := hP
  have e : pfxL F = ⟨17, by rw [← hv]; exact (pfxL F).isLt⟩ := Fin.ext hv
  rw [e, slx_some (symExt_isK L pd (show isK pd 17 by unfold isK; omega))]
  apply Fin.ext
  show tgtV L pd 17 = 9925 + 3 * L.U + (symO 10).val
  rw [tv3 L pd 17 (by norm_num) (by norm_num)]
  have : (symO 10).val = 130 := rfl
  omega

variable (M0s : ℕ) (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr))
  (TWd Cap nT : ℕ) (pre post : List Bool) (q uu : ℕ) (B : Fin L.N → List Bool) (ρ : ℕ) (v w : List Bool)
  (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)

/-- **The loop's entry on the SYM setup's bank** (`C4Wrap.LoopEntry`). -/
theorem sym_entry (hS : ChShape F pd P ents TWd Cap nT pre post q uu)
    (hB : SymBank L pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd)
    (hP0 : B L.gP0 = frame w) (hP2 : B L.gP2 = []) (hT : F.T + 1 + 1 + 1 ≤ L.T) (hR : F.cellCost + 1 ≤ 2 ^ ρ) :
    LoopEntry F (2 ^ ρ) (2 ^ ρ + 1) L.oLP (hoffL L F hT) (symExt L pd) w v B where
  hR := hR
  hL := le_refl _
  h3 := by unfold Lay.oLP; omega
  inj := symExt_inj L pd
  lt := symExt_lt L pd
  port := symExt_port L pd
  pfx := fun g hg => by
    obtain ⟨hk, hg'⟩ := symExt_some L pd hg
    have hv : (pfxL F).val = 17 := hS.pfx
    rw [hg', hv, tv3 L pd 17 (by norm_num) (by norm_num)]
    omega
  entry := entry_all L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB (hoffL L F hT) hT
  p0 := hP0
  p1 := hB.hP1
  p2 := hP2

/-- **The finisher's dock** after the loop (`C4Wrap.FinDock`). -/
theorem sym_fin (hS : ChShape F pd P ents TWd Cap nT pre post q uu)
    (hB : SymBank L pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd)
    (hP2 : B L.gP2 = []) (hMB : B L.gMB = frame (binary ell (GF.firstPrimitive ell)))
    (hbl : ∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B i = []) (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s) :
    FinDock (offF L) (hoffF L htS) (finExt L) 6 (C4Iface.sampIn (0 : Fin 31) 2 3 4 5 P s)
      (postLoop F L.oLP (hoffL L F hT) (symExt L pd) B) where
  inj := fun i j g hi hj => by
    have := finExt_val L hi
    have := finExt_val L hj
    apply Fin.ext
    omega
  lt := fun i g hi => by
    have := finExt_val L hi
    unfold offF Lay.oLP
    omega
  port := fun i g hi => by
    have := finExt_val L hi
    omega
  out := by unfold finExt; rfl
  inp := fun j g hj => by
    have hps := pfx_slot L F pd hS.pfx (hoffL L F hT)
    have hne : ∀ g' : Fin L.N, g' ≠ L.gW 10 → postLoop F L.oLP (hoffL L F hT) (symExt L pd) B g' = B g' := by
      intro g' hg'
      unfold postLoop
      rw [hps]
      exact Function.update_of_ne hg' _ _
    rcases finExt_some L hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have ej : j = 0 := Fin.ext a
      subst ej
      unfold postLoop
      rw [hps, Function.update_self, hG]
      rfl
    · have ej : j = 2 := Fin.ext a
      subst ej
      rw [hne _ (fun e => absurd (congrArg Fin.val e) (by simp [Lay.gW]; decide)), hB.hW]
      show List.replicate kh true = List.replicate P.kh true
      rw [hB.e_kh]
    · have ej : j = 3 := Fin.ext a
      subst ej
      rw [hne _ (fun e => absurd (congrArg Fin.val e) (by simp [Lay.gW]; decide)), hB.hW]
      show List.replicate Q true = List.replicate P.Q true
      rw [hB.e_Q]
    · have ej : j = 4 := Fin.ext a
      subst ej
      rw [hne _ (fun e => absurd (congrArg Fin.val e) (by simp [Lay.gW]; decide)), hB.hW]
      show List.replicate ell true = List.replicate P.ell true
      rw [hB.e_ell]
    · have ej : j = 5 := Fin.ext a
      subst ej
      rw [hne _ (fun e => absurd (congrArg Fin.val e) (by simp [Lay.gW, Lay.gMB]; omega)), hMB]
      show frame (binary ell (GF.firstPrimitive ell)) = frame (binary P.ell P.modulus)
      rw [hB.e_mod, hB.e_ell]
    · have ej : j = 6 := Fin.ext a
      subst ej
      rw [hne _ (fun e => absurd (congrArg Fin.val e) (by simp [Lay.gW, Lay.gP2]; omega)), hP2]
      rfl
  own := fun j hj => by
    unfold finExt at hj
    unfold C4Iface.sampIn
    split_ifs at hj with h0 h2 h3 h4 h5 h6
    have n0 : j ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have n2 : j ≠ 2 := fun e => h2 (by rw [e]; rfl)
    have n3 : j ≠ 3 := fun e => h3 (by rw [e]; rfl)
    have n4 : j ≠ 4 := fun e => h4 (by rw [e]; rfl)
    have n5 : j ≠ 5 := fun e => h5 (by rw [e]; rfl)
    rw [if_neg n0, if_neg n2, if_neg n3, if_neg n4, if_neg n5]
  blank := fun i hi => by
    have hps := pfx_slot L F pd hS.pfx (hoffL L F hT)
    unfold postLoop
    rw [hps, Function.update_of_ne (fun e => by rw [e] at hi; unfold offF Lay.oLP at hi; simp [Lay.gW] at hi; omega)]
    exact hbl i (by unfold offF at hi; omega)

/-- **The C4 stage on the SYM layout**: a setup run (any machine `M0`) to a `SymBank` bank, the docked loop of a child
family of the shape `ChShape`, C6's sample expansion docked by `finExt`; within any budget above `wrapCost + 1`, the
stage ends with `sampleWord P.kh (seedPairs P s)` on port `2`, `s` the loop's decisions. -/
theorem symLay_run {s0 c0 : ℕ} (M0 : Machine (3 + L.X) s0) (h0 : Step M0 c0 (fun _ => 0)
    (SeedFixTypes.stageIn L.X w v) (fun _ => 0) B)
    (hS : ChShape F pd P ents TWd Cap nT pre post q uu)
    (hB : SymBank L pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd)
    (hP0 : B L.gP0 = frame w) (hP2 : B L.gP2 = []) (hMB : B L.gMB = frame (binary ell (GF.firstPrimitive ell)))
    (hbl : ∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B i = []) (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    (hR : F.cellCost + 1 ≤ 2 ^ ρ) (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s)
    (Bd : ℕ) (hBd : wrapCost c0 F (2 ^ ρ) (C4Iface.sampCost P) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨L.X, _, wrapM M0 F L.oLP (hoffL L F hT) (symExt L pd) UnionMachine.SampStage.sampM (offF L)
      (hoffF L htS) (finExt L)⟩ Bd w v (FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s)) := by
  obtain ⟨A', hf, hout⟩ := UnionMachine.SampStage.samp_run P s
  have r := C4Wrap.wrap_run M0 w v B h0 F (2 ^ ρ) (2 ^ ρ + 1) L.oLP (hoffL L F hT) (symExt L pd)
    (sym_entry L F pd P ents TWd Cap nT pre post q uu B ρ v w Q kh ell cnt d2 fr dd hS hB hP0 hP2 hT hR)
    UnionMachine.SampStage.sampM _ A' hf (offF L) (hoffF L htS) (finExt L) 6
    (sym_fin L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hP2 hMB hbl hT htS s hG) Bd hBd
  rw [hout] at r
  exact r

end Stage

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
