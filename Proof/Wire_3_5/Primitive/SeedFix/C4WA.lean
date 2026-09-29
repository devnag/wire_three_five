import Proof.Wire_3_5.Primitive.SeedFix.C4WIface
import Proof.Wire_3_5.UnionMachine.FrontKit
import Proof.SourceAssembly.SourceFactorSelRunBound

/-! # C4 Stage3 wrapper: the run

"Choose a child with no larger sum. After `S` decisions the actual trace objective is no larger than its random
expectation" (P3:3035-3038); the processor writes the loop's inputs first (P3:3011-3016) and the fixed seed is read
back for the final pass (P3:2932-2937, 3165-3175). From any setup run ending in a `LoopEntry` bank and any finisher run
docked by a `FinDock`, the stage `wrapM` runs from `stageIn x w v` to `stageOut x w v (tout o) J` with every head at
`0` and residues within the budget:
* `stage3_of_step` (a stage's run from a `Step` with every head at `0`, residues by `RunBound.step_len_window`);
* `cfwd_step`, `cbwd_step` (the counter head), `loopH`, `loop_step` (`loop_run` at `loopM`), `loopH_val`;
* `src_other`, `loopBank_ne`, `loopBank_pfx` (the loop changes only its prefix tape), `install_post`;
* **`loopZ_step`** (the docked loop: from a bank carrying `loopBank F R L 0` at the slots to `postLoop`);
* **`wrap_run`**: `Stage3Run ⟨x, _, wrapM …⟩ Bd w v (tout o)`.

Paper quantity of the main type: the stage's output `tout o` (the finisher's word from the fixed prefix). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Wrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx slx_inj slx_some slx_none stageP)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## A stage's run from a step -/

/-- **A stage's run from a `Step`** with every head at `0`: the ports kept, the output on port `2`, the residues (from
blank scratch) at most the step bound plus one. -/
theorem stage3_of_step {x s n : ℕ} {M : Machine (3 + x) s} {w v y : List Bool} {A' : Fin (3 + x) → List Bool}
    (h : Step M n (fun _ => 0) (SeedFixTypes.stageIn x w v) (fun _ => 0) A')
    (h0 : A' ⟨0, by omega⟩ = frame w) (h1 : A' ⟨1, by omega⟩ = v) (h2 : A' ⟨2, by omega⟩ = y) (B : ℕ)
    (hB : n + 1 ≤ B) : SeedFixTypes.Stage3Run ⟨x, s, M⟩ B w v y := by
  have e : A' = SeedFixTypes.stageOut x w v y (fun j => A' (Fin.natAdd 3 j)) := by
    funext i
    refine Fin.addCases (motive := fun i => A' i = SeedFixTypes.stageOut x w v y (fun j => A' (Fin.natAdd 3 j)) i)
      (fun k => ?_) (fun j => ?_) i
    · unfold SeedFixTypes.stageOut
      rw [Fin.addCases_left]
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
    · unfold SeedFixTypes.stageOut
      rw [Fin.addCases_right]
  refine ⟨fun j => A' (Fin.natAdd 3 j), fun j => ?_, ?_⟩
  · refine SourceFactorSel.RunBound.step_len_window h B (Fin.natAdd 3 j) ?_ rfl hB
    unfold SeedFixTypes.stageIn
    rw [Fin.addCases_right]
    simp
  · rw [e] at h
    exact UnionMachine.FrontKit.ready_of_step (h.enlarge (by omega))

/-! ## The counter head -/

theorem cfwd_step {u : ℕ} (g : Fin u) (B : Fin u → List Bool) :
    Step (cfwdP g).compile 1 (fun _ => 0) B (hAt g) B := by
  have h := act_step (⟨fun _ => 0, B⟩ : Bank u) (fun _ => none) (moveAt g .right)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = g
    · simp [Bank.act, moveAt, hi, HeadMove.apply, hAt]
    · simp [Bank.act, moveAt, hi, HeadMove.apply, hAt]
  · funext i
    rfl

theorem cbwd_step {u : ℕ} (g : Fin u) (B : Fin u → List Bool) :
    Step (cbwdP g).compile 1 (hAt g) B (fun _ => 0) B := by
  have h := act_step (⟨hAt g, B⟩ : Bank u) (fun _ => none) (moveAt g .left)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = g
    · simp [Bank.act, moveAt, hi, HeadMove.apply, hAt]
    · simp [Bank.act, moveAt, hi, HeadMove.apply, hAt]
  · funext i
    rfl

/-! ## The loop -/

section Loop
variable (F : C4Loop.ChildFam)

/-- The loop's heads: every head at `0`, the counter's at `1`. -/
def loopH : Fin (F.T + 1 + 1 + 1) → ℕ := Fin.addCases (Scrub.heads (fun _ : Fin F.T => 0)) (fun _ : Fin 1 => 1)

/-- **The loop** (`loop_run` at `loopM`). -/
theorem loop_step (R L : ℕ) (hR : F.cellCost + 1 ≤ R) (hL : R + 1 ≤ L) :
    Step (loopM F) (loopCost F R) (loopH F) (loopBank F R L 0) (loopH F) (loopBank F R L F.bound) := by
  obtain ⟨c, h, hb, hbd, hc⟩ := F.loop_run R L hR hL
  rw [hb, hbd, hc] at h
  exact h

theorem loopH_val (j : Fin (F.T + 1 + 1 + 1)) : loopH F j = if j = cntL F then 1 else 0 := by
  refine Fin.addCases (motive := fun j => loopH F j = if j = cntL F then 1 else 0) (fun k => ?_) (fun k => ?_) j
  · have hne : Fin.castAdd 1 k ≠ cntL F := by
      intro e
      have := congrArg Fin.val e
      simp [cntL] at this
      omega
    rw [if_neg hne]
    unfold loopH
    rw [Fin.addCases_left]
    refine Scrub.cover (motive := fun k => Scrub.heads (fun _ : Fin F.T => 0) k = 0) (fun i => ?_) ?_ ?_ k <;> simp
  · have he : Fin.natAdd (F.T + 1 + 1) k = cntL F :=
      Fin.ext (by have := k.isLt; simp only [cntL, Fin.val_natAdd, Fin.val_last]; omega)
    rw [if_pos he]
    unfold loopH
    rw [Fin.addCases_right]

theorem src_other (R j j' : ℕ) (i : Fin F.T) (hi : i ≠ F.sl0 F.PFX) : F.src R j i = F.src R j' i := by
  unfold C4Loop.ChildFam.src Scrub.blank
  split_ifs with hS
  · rfl
  · unfold C4Loop.ChildFam.cellIn
    split_ifs with hl
    · unfold C4Loop.cin
      have hP : (⟨i.val, hl⟩ : Fin F.t) ≠ F.PFX := fun e => hi (Fin.ext (by show i.val = F.PFX.val; rw [← e]))
      simp only [if_neg hP]
    · rfl

theorem loopBank_ne (R L : ℕ) (j : Fin (F.T + 1 + 1 + 1)) (hj : j ≠ pfxL F) :
    loopBank F R L F.bound j = loopBank F R L 0 j := by
  refine Fin.addCases (motive := fun j => j ≠ pfxL F → loopBank F R L F.bound j = loopBank F R L 0 j)
    (fun k hk => ?_) (fun k _ => ?_) j hj
  · unfold loopBank
    rw [Fin.addCases_left, Fin.addCases_left]
    refine Scrub.cover (motive := fun k => Fin.castAdd 1 k ≠ pfxL F →
      Scrub.bank (F.src R F.bound) R L k = Scrub.bank (F.src R 0) R L k) (fun i hi => ?_) (fun _ => ?_) (fun _ => ?_) k hk
    · rw [Scrub.bank_inner, Scrub.bank_inner]
      exact src_other F R _ _ i (fun e => hi (by rw [e]; rfl))
    · simp
    · simp
  · unfold loopBank
    rw [Fin.addCases_right, Fin.addCases_right]

theorem loopBank_pfx (R L : ℕ) : loopBank F R L F.bound (pfxL F) = frame (SeedFix.greedyLoop F.bound F.Rv) := by
  unfold loopBank pfxL
  rw [Fin.addCases_left, Scrub.bank_inner]
  exact F.src_pfx R

/-- **After the loop**, the bank is `postLoop`: the prefix slot holds the greedy's decisions. -/
theorem install_post {u : ℕ} (off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ u)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin u)) (hinj : ∀ i j g, ext i = some g → ext j = some g → i = j)
    (hlt : ∀ i g, ext i = some g → g.val < off) (B : Fin u → List Bool) (R L : ℕ)
    (hB : ∀ j, B (slx off hoff ext j) = loopBank F R L 0 j) :
    install (slx off hoff ext) B (loopBank F R L F.bound) = postLoop F off hoff ext B := by
  have hi := slx_inj off hoff ext hinj hlt
  funext i
  unfold postLoop
  by_cases hs : ∃ j, slx off hoff ext j = i
  · obtain ⟨j, rfl⟩ := hs
    rw [install_slot _ hi]
    by_cases hj : j = pfxL F
    · subst hj
      rw [Function.update_self, loopBank_pfx]
    · rw [Function.update_of_ne (fun e => hj (hi e)), hB j, loopBank_ne F R L j hj]
  · simp only [not_exists] at hs
    rw [install_other _ _ _ _ hs, Function.update_of_ne (fun e => hs _ e.symm)]

/-- **The docked loop**: from a bank carrying the loop's entry at the slots, every head at `0`, to `postLoop`. -/
theorem loopZ_step {u : ℕ} (off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ u)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin u)) (hinj : ∀ i j g, ext i = some g → ext j = some g → i = j)
    (hlt : ∀ i g, ext i = some g → g.val < off) (R L : ℕ) (hR : F.cellCost + 1 ≤ R) (hL : R + 1 ≤ L)
    (B : Fin u → List Bool) (hB : ∀ j, B (slx off hoff ext j) = loopBank F R L 0 j) :
    Step (loopZM F off hoff ext) (loopZCost F R) (fun _ => 0) B (fun _ => 0) (postLoop F off hoff ext B) := by
  have hi := slx_inj off hoff ext hinj hlt
  have hH : ∀ j, hAt (slx off hoff ext (cntL F)) (slx off hoff ext j) = loopH F j := by
    intro j
    rw [loopH_val]
    unfold hAt
    by_cases hj : j = cntL F
    · rw [if_pos hj, if_pos (by rw [hj])]
    · rw [if_neg hj, if_neg (fun e => hj (hi e))]
  have d := (loop_step F R L hR hL).dock (slx off hoff ext) hi (hAt (slx off hoff ext (cntL F))) B hH hB
  rw [ExtDecompositionBatch.dockH_existing (slx off hoff ext) _ (loopH F) hH,
    install_post F off hoff ext hinj hlt B R L hB] at d
  exact (cfwd_step _ B).seq (d.seq (cbwd_step _ _))

end Loop

/-! ## The stage -/

/-- **The C4 stage's run** (the wrapper): a setup run to a `LoopEntry` bank, the docked loop, a finisher docked by a
`FinDock` at the bank after the loop; the stage ends with the ports kept and the finisher's output `tout o` on port
`2`, within any budget above `wrapCost + 1`. -/
theorem wrap_run {x s0 c0 : ℕ} (M0 : Machine (3 + x) s0) (w v : List Bool) (B : Fin (3 + x) → List Bool)
    (h0 : Step M0 c0 (fun _ => 0) (SeedFixTypes.stageIn x w v) (fun _ => 0) B)
    (F : C4Loop.ChildFam) (R L off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ 3 + x)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin (3 + x))) (hE : LoopEntry F R L off hoff ext w v B)
    {tf sf nf : ℕ} (Mf : Machine tf sf) (tin tout : Fin tf → List Bool)
    (hf : Step Mf nf (fun _ => 0) tin (fun _ => 0) tout) (off2 : ℕ) (hoff2 : off2 + tf ≤ 3 + x)
    (ext2 : Fin tf → Option (Fin (3 + x))) (o : Fin tf)
    (hD : FinDock off2 hoff2 ext2 o tin (postLoop F off hoff ext B)) (Bd : ℕ)
    (hBd : wrapCost c0 F R nf + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨x, _, wrapM M0 F off hoff ext Mf off2 hoff2 ext2⟩ Bd w v (tout o) := by
  have s1 := loopZ_step F off hoff ext hE.inj hE.lt R L hE.hR hE.hL B hE.entry
  obtain ⟨st, -, un, -, ex⟩ := stageP hf off2 hoff2 ext2 hD.inj hD.lt (postLoop F off hoff ext B) hD.inp hD.blank
    hD.own
  have hsl : ∀ (j : Fin (F.T + 1 + 1 + 1)) (k : ℕ), k < 3 → (slx off hoff ext j).val = k →
      (k ≠ 0 ∧ k ≠ 2) ∧ (j = pfxL F → k ≠ 1) := by
    intro j k hk e
    cases hj : ext j with
    | some g =>
      rw [slx_some hj] at e
      subst e
      exact ⟨hE.port j g hj, fun hp => by subst hp; exact hE.pfx g hj⟩
    | none =>
      rw [slx_none hj] at e
      have := hE.h3
      omega
  have hpost : ∀ k (hk : k < 3), k ≠ 2 → postLoop F off hoff ext B ⟨k, by omega⟩ = B ⟨k, by omega⟩ := by
    intro k hk h2
    unfold postLoop
    apply Function.update_of_ne
    intro e
    have := hsl (pfxL F) k hk (congrArg Fin.val e).symm
    omega
  have h2 : 2 < off2 := hD.lt o _ hD.out
  refine stage3_of_step (h0.seq (s1.seq st)) ?_ ?_ ?_ Bd hBd
  · rw [un ⟨0, by omega⟩ (by show 0 < off2; omega) (fun j e => (hD.port j _ e).1 rfl),
      hpost 0 (by omega) (by omega)]
    exact hE.p0
  · rw [un ⟨1, by omega⟩ (by show 1 < off2; omega) (fun j e => (hD.port j _ e).2 rfl), hpost 1 (by omega) (by omega)]
    exact hE.p1
  · exact ex o ⟨2, by omega⟩ hD.out

end NearCubicWires.WireExponent3_5.PrimT.C4Wrap
