import Proof.Wire_3_5.FinalPass.Core18
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ

/-! # S5Core over the writers with arbitrary residues, part J10: the writer's stage (P3:3170-3181)

`dock_stage` and `wstage` (Core6, Core10) with the writer's residues bounded in LENGTH only (`CoreWordsMJ` /
`SymWordsMJ`): **`dock_stageJ`** (one writer's stage: its registers padded against `sent c`, its cell written, its run
zero-padded to `c + 1` and focused; its outputs written, the input kept, its block within `c + 1`, every other tape
kept), **`wstageJ`** (the same on a block of the core's room, the room invariant moved on).

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c sTape_val rTape_val cTape_val)

section Dock

end Dock

/-! ## One writer's stage -/

/-- **One writer's stage on the bank.** -/
theorem dock_stageJ {u ns nr m s : ℕ} (M : Machine (ns + 2 + nr) s) (sIn : Fin (ns + 1)) (sOut : Fin m ↪ Fin (ns + 1))
    (hne : ∀ k, sOut k ≠ sIn) (i0 : Fin u) (out : Fin m → Fin u) (hout : Function.Injective out)
    (room : Fin (ns + 2 + nr) → Fin u) (hroom : Function.Injective room) (h0o : ∀ k, out k ≠ i0)
    (h0r : ∀ j, room j ≠ i0) (hor : ∀ k j, out k ≠ room j) (T : Fin u) (hTr : ∀ j, room j ≠ T)
    (c K S : ℕ) (hK : K ≤ c) (hS : S ≤ c) (x : List Bool) (ws : Fin m → List Bool)
    (hrun : ∀ σ : WState ns nr, σ.st sIn = x → (∀ i, σ.sh i = 0) → (∀ i, i ≠ sIn → σ.st i = []) →
      (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ S ∧ Step M n (wenc K σ).H (wenc K σ).A (wenc K τ).H (wenc K τ).A ∧
        (∀ k, τ.st (sOut k) = ws k) ∧ τ.st sIn = x ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) → (τ.st i).length ≤ S) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0))
    (A : Fin u → List Bool) (hA0 : A i0 = x) (hAo : ∀ k, A (out k) = []) (hAr : ∀ j, A (room j) = [])
    (hAT : A T = sent c) :
    ∃ A' : Fin u → List Bool,
      Step (Composition.machine (prepP T (room cTape) (regsOf room)).compile
        (RecoveryFocus.machine (wslots sIn sOut i0 out room) M)) (nr * (6 * c + 17) + 1 + 1 + 1 + S)
        (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k, A' (out k) = ws k) ∧ A' i0 = x ∧ (∀ j, (A' (room j)).length ≤ c + 1) ∧
      (∀ y, y ≠ i0 → (∀ k, y ≠ out k) → (∀ j, y ≠ room j) → A' y = A y) := by
  classical
  have hso : Function.Injective sOut := sOut.injective
  have hnd : (regsOf room).Nodup := (List.nodup_finRange nr).map (fun a b h => rTape_inj (hroom h))
  have hTn : T ∉ regsOf room := by rw [mem_regsOf]; rintro ⟨q, hq⟩; exact hTr _ hq
  have hcn : room cTape ∉ regsOf room := by
    rw [mem_regsOf]; rintro ⟨q, hq⟩; exact cTape_ne_r q (hroom hq).symm
  have hreg0 : ∀ j ∈ regsOf room, (A j).length ≤ c + 1 := by
    intro j hj
    rw [mem_regsOf] at hj
    obtain ⟨q, rfl⟩ := hj
    rw [hAr]; simp
  have hp := Exec.step (prepP_exec T (room cTape) c (regsOf room) ⟨fun _ => 0, A⟩ hnd hTn hcn hAT (fun _ => rfl)
    hreg0 (hAr _))
  set A1 : Fin u → List Bool := fun i => if i = room cTape then [false] else if i ∈ regsOf room then
    List.replicate (c + 1) false else A i with hA1
  have hA1o : ∀ y, y ≠ room cTape → y ∉ regsOf room → A1 y = A y := fun y h1 h2 => by
    rw [hA1]; simp only [if_neg h1, if_neg h2]
  have hrs : ∀ i : Fin (ns + 1), room (sTape i) ∉ regsOf room := fun i => by
    rw [mem_regsOf]; rintro ⟨q, hq⟩; exact sTape_ne_r i q (hroom hq).symm
  have hrc : ∀ i : Fin (ns + 1), room (sTape i) ≠ room cTape := fun i e => sTape_ne_c i (hroom e)
  have h0n : i0 ∉ regsOf room := by rw [mem_regsOf]; rintro ⟨q, hq⟩; exact h0r _ hq
  have hon : ∀ k, out k ∉ regsOf room := fun k => by rw [mem_regsOf]; rintro ⟨q, hq⟩; exact hor k _ hq.symm
  -- the entry state
  let σ : WState ns nr := ⟨fun _ => 0, fun i => if i = sIn then x else [], fun _ => 0, false⟩
  obtain ⟨τ, n, hn, hstep, hτo, hkeep, hres, hτs, hτv⟩ :=
    hrun σ (by simp [σ]) (fun _ => rfl) (fun i hi => by simp [σ, hi]) (fun _ => rfl) rfl
  have hi := wslots_inj sIn sOut i0 out room hso hne hout hroom h0o h0r hor
  have hA : ∀ j, A1 (wslots sIn sOut i0 out room j) = ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc K σ).A j) := by
    refine entry_eq _ K c hK σ (fun _ => rfl) A1 (fun i => ?_) ?_ (fun q => ?_)
    · rcases slot_cases sIn sOut (sTape (nr := nr) i) with e | ⟨k, e⟩ | ⟨a, b⟩
      · have hi' : i = sIn := sTape_inj e
        subst hi'
        rw [wslots_in, hA1o _ (fun e => h0r _ e.symm) h0n, hA0]
        simp [σ]
      · have hi' : sOut k = i := sTape_inj e
        subst hi'
        rw [wslots_out _ _ _ _ _ hso hne, hA1o _ (fun e => hor k _ e) (hon k), hAo]
        simp [σ, hne k]
      · rw [wslots_room _ _ _ _ _ _ a b, hA1o _ (hrc i) (hrs i), hAr]
        have : i ≠ sIn := fun e => a (by rw [e])
        simp [σ, this]
    · have a : (cTape (ns := ns) (nr := nr)) ≠ sTape sIn := fun e => sTape_ne_c sIn e.symm
      have b : ∀ k, sTape (nr := nr) (sOut k) ≠ cTape := fun k => sTape_ne_c _
      rw [wslots_room _ _ _ _ _ _ a b]
      simp [hA1, σ]
    · have a : (rTape (ns := ns) q) ≠ sTape sIn := fun e => sTape_ne_r sIn q e.symm
      have b : ∀ k, sTape (nr := nr) (sOut k) ≠ rTape q := fun k => sTape_ne_r _ q
      rw [wslots_room _ _ _ _ _ _ a b, hA1]
      have hm : room (rTape q) ∈ regsOf room := by rw [mem_regsOf]; exact ⟨q, rfl⟩
      have hc : room (rTape q) ≠ room cTape := fun e => cTape_ne_r q (hroom e).symm
      simp only [if_neg hc, if_pos hm]
  have hd := dock_stepM M _ hi K c σ τ n hstep (fun _ => rfl) (fun _ => rfl) hτs hτv A1 hA
  have hp' : Step (prepP T (room cTape) (regsOf room)).compile ((regsOf room).length * (6 * c + 17) + 1 + 1)
      (fun _ => 0) A (fun _ => 0) A1 := hp
  refine ⟨_, (Step.seq hp' hd).enlarge (by rw [regsOf_length]; omega), ?_, ?_, ?_, ?_⟩
  · intro k
    have h := exit_s (wslots sIn sOut i0 out room) hi K c τ A1 (sOut k)
    rw [wslots_out sIn sOut i0 out room hso hne k] at h
    exact h.trans (hτo k)
  · have h := exit_s (wslots sIn sOut i0 out room) hi K c τ A1 sIn
    rw [wslots_in sIn sOut i0 out room] at h
    exact h.trans hkeep
  · intro j
    rcases slot_cases sIn sOut j with e | ⟨k, e⟩ | ⟨a, b⟩
    · subst e
      rw [install_other _ _ _ _ (wslots_ne sIn sOut i0 out room _ (h0r _) (fun k => (hor k _).symm)
        (fun j a' _ e => a' (hroom e).symm) hso hne), hA1o _ (hrc sIn) (hrs sIn), hAr]
      simp
    · subst e
      rw [install_other _ _ _ _ (wslots_ne sIn sOut i0 out room _ (h0r _) (fun k' => (hor k' _).symm)
        (fun j _ b' e => b' k (hroom e)) hso hne), hA1o _ (hrc _) (hrs _), hAr]
      simp
    · rw [← wslots_room sIn sOut i0 out room j a b, install_slot _ hi]
      rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [pc_s, ZeroPadding.pad_zero, wenc_A_s]
        have := hres i (fun e => a (by rw [e])) (fun k e => b k (by rw [e]))
        omega
      · rw [pc_c, ZeroPadding.pad_zero, wenc_A_c]; simp
      · rw [pc_r, wenc_A_r, hτv, regTape_zero, Bridge.pad_replicate K c hK]; simp
  · intro y h0 ho hr
    rw [install_other _ _ _ _ (wslots_ne sIn sOut i0 out room y h0 ho (fun j _ _ => hr j) hso hne)]
    exact hA1o y (hr _) (by rw [mem_regsOf]; rintro ⟨q, hq⟩; exact hr _ hq.symm)

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent)

section Stage
variable {nw : ℕ} (L : S5Lay nw) {mTh mC : ℕ} (hR : Bank.HalfRoom2 L mTh mC)

/-- **A writer's stage in the core's room.** -/
theorem wstageJ {ns nr m s : ℕ} (M : Machine (ns + 2 + nr) s) (sIn : Fin (ns + 1)) (sOut : Fin m ↪ Fin (ns + 1))
    (hne : ∀ k, sOut k ≠ sIn) (out : Fin m → Fin L.t) (hout : Function.Injective out) (h0o : ∀ k, out k ≠ i0 L)
    (hoR : ∀ k i, out k ≠ hR.coreE i) (o : ℕ) (h : o + (ns + 2 + nr) ≤ mC) (iT : Fin mC) (hiT : iT.val < o)
    (c K S : ℕ) (hK : K ≤ c) (hS : S ≤ c) (x : List Bool) (ws : Fin m → List Bool)
    (hrun : ∀ σ : WState ns nr, σ.st sIn = x → (∀ i, σ.sh i = 0) → (∀ i, i ≠ sIn → σ.st i = []) →
      (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ S ∧ Step M n (wenc K σ).H (wenc K σ).A (wenc K τ).H (wenc K τ).A ∧
        (∀ k, τ.st (sOut k) = ws k) ∧ τ.st sIn = x ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) → (τ.st i).length ≤ S) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0))
    (b : Fin L.t → List Bool) (hin : b (i0 L) = x) (hbo : ∀ k, b (out k) = []) (hinv : RInv L hR c b o)
    (hT : b (hR.coreE iT) = sent c) :
    ∃ b' : Fin L.t → List Bool,
      Step (wstageM L hR M sIn sOut out o h (hR.coreE iT)) (nr * (6 * c + 17) + 1 + 1 + 1 + S) (fun _ => 0) b
        (fun _ => 0) b' ∧
      (∀ k, b' (out k) = ws k) ∧ b' (i0 L) = x ∧ RInv L hR c b' (o + (ns + 2 + nr)) ∧
      b' (hR.coreE iT) = sent c ∧ (∀ y, (∀ i, hR.coreE i ≠ y) → (∀ k, y ≠ out k) → b' y = b y) ∧
      (∀ i : Fin mC, (i.val < o ∨ o + (ns + 2 + nr) ≤ i.val) → b' (hR.coreE i) = b (hR.coreE i)) := by
  have hroomT : ∀ j, blk L hR o (ns + 2 + nr) h j ≠ hR.coreE iT := fun j e => by
    have := congrArg Fin.val (hR.coreE.injective e)
    simp only at this
    omega
  obtain ⟨b', hs, hw, hi, hr, hk⟩ := dock_stageJ M sIn sOut hne (i0 L) out hout (blk L hR o (ns + 2 + nr) h)
    (blk_inj L hR o _ h) h0o (blk_ne0 L hR o _ h) (fun k j => hoR k _) (hR.coreE iT) hroomT c K S hK hS x ws hrun b
    hin hbo (fun j => (hinv ⟨o + j.val, by omega⟩).2 (by simp)) hT
  have hkeepR : ∀ i : Fin mC, (i.val < o ∨ o + (ns + 2 + nr) ≤ i.val) → b' (hR.coreE i) = b (hR.coreE i) := by
    intro i hi'
    have hne' : ∀ j, hR.coreE i ≠ blk L hR o (ns + 2 + nr) h j := fun j e => by
      have := congrArg Fin.val (hR.coreE.injective e)
      simp only at this
      have := j.isLt
      omega
    exact hk _ (fun e => (core_off L hR i).1 (by rw [e]; rfl)) (fun k e => hoR k i e.symm) hne'
  refine ⟨b', hs, hw, hi, fun i => ?_, ?_, fun y hy hyo => ?_, hkeepR⟩
  · by_cases hb : o ≤ i.val ∧ i.val < o + (ns + 2 + nr)
    · have e : hR.coreE i = blk L hR o (ns + 2 + nr) h ⟨i.val - o, by omega⟩ := by
        unfold blk; congr 1; exact Fin.ext (by simp; omega)
      rw [e]
      exact ⟨hr _, fun h' => by omega⟩
    · have hne' : ∀ j, hR.coreE i ≠ blk L hR o (ns + 2 + nr) h j := fun j e => by
        have := congrArg Fin.val (hR.coreE.injective e)
        simp only at this
        have := j.isLt
        omega
      rw [hk _ (fun e => (core_off L hR i).1 (by rw [e]; rfl)) (fun k e => hoR k i e.symm) hne']
      exact ⟨(hinv i).1, fun h' => (hinv i).2 (by omega)⟩
  · rw [hk _ (fun e => (core_off L hR iT).1 (by rw [e]; rfl)) (fun k e => hoR k iT e.symm)
      (fun j e => hroomT j e.symm), hT]
  · by_cases hy0 : y = i0 L
    · subst hy0; rw [hi, hin]
    · exact hk y hy0 hyo (fun j e => hy _ (by unfold blk at e; exact e.symm))

end Stage

end NearCubicWires.WireExponent3_5.FinalPass.Core
