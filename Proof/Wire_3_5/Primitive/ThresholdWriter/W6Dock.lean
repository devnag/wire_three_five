import Proof.Wire_3_5.Primitive.Writers.DockW

/-! # W6 part 3: a word program of one layout run inside another (`SubL`, `dockL`)

P3:2220-2231 and P3:2150-2157 (the auxiliary filter's `e` and the fixed hash's level windows `W_j`, computed by the verified stage `EwStage.ewSpec2` on its own layout `WState 8 48`): the THR numbers machine runs that stage inside
its own layout. A layout `(ns₁, nr₁)` embeds into `(ns₂, nr₂)` by injective stream and register maps and one stream
of the big layout that stands for the small layout's cell (a cell tape is `[c]` at head `0`, exactly a stream holding
`[c]`). Generic (PA's `DockW.dockS` docks raw machines onto streams only):

* **`SubL`** (the maps), `SubL.tm` (the tape map), `SubL.tm_inj`, **`SubL.Agree`** (the big state restricts to the
  small one);
* **`dockL`**: a `Step` of the small layout's machine between encoded states is a `Step` of the docked machine in the big
  layout, whose exit agrees with the small exit and keeps every stream, register and the cell outside the image.

Paper quantity of the main type: none (machine plumbing; the docked stage's type carries `e` and `W_j`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.W6Dock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- **A small layout inside a big one.** -/
structure SubL (ns₁ nr₁ ns₂ nr₂ : ℕ) where
  sm : Fin (ns₁ + 1) → Fin (ns₂ + 1)
  rm : Fin nr₁ → Fin nr₂
  cs : Fin (ns₂ + 1)
  sm_inj : Function.Injective sm
  rm_inj : Function.Injective rm
  cs_ne : ∀ i, sm i ≠ cs

variable {ns₁ nr₁ ns₂ nr₂ : ℕ} (L : SubL ns₁ nr₁ ns₂ nr₂)

/-- The tape map: streams to streams, the cell to the cell stream, registers to registers. -/
def SubL.tm (j : Fin (ns₁ + 2 + nr₁)) : Fin (ns₂ + 2 + nr₂) :=
  match role (ns := ns₁) (nr := nr₁) j with
  | .stream i => sTape (L.sm i)
  | .cell => sTape L.cs
  | .reg r => rTape (L.rm r)

theorem SubL.tm_s (i : Fin (ns₁ + 1)) : L.tm (sTape (nr := nr₁) i) = sTape (L.sm i) := by
  simp [SubL.tm, role_sTape]

theorem SubL.tm_c : L.tm (cTape (ns := ns₁) (nr := nr₁)) = sTape L.cs := by
  simp [SubL.tm, role_cTape]

theorem SubL.tm_r (r : Fin nr₁) : L.tm (rTape (ns := ns₁) r) = rTape (L.rm r) := by
  simp [SubL.tm, role_rTape]

theorem SubL.tm_inj : Function.Injective L.tm := by
  intro a b h
  rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩ <;> rcases tape_cases b with ⟨i', rfl⟩ | rfl | ⟨r', rfl⟩
  · rw [L.tm_s, L.tm_s] at h; rw [L.sm_inj (sTape_inj h)]
  · rw [L.tm_s, L.tm_c] at h; exact absurd (sTape_inj h) (L.cs_ne i)
  · rw [L.tm_s, L.tm_r] at h; exact absurd h (sTape_ne_r _ _)
  · rw [L.tm_c, L.tm_s] at h; exact absurd (sTape_inj h).symm (L.cs_ne i')
  · rfl
  · rw [L.tm_c, L.tm_r] at h; exact absurd h (sTape_ne_r _ _)
  · rw [L.tm_r, L.tm_s] at h; exact absurd h.symm (sTape_ne_r _ _)
  · rw [L.tm_r, L.tm_c] at h; exact absurd h.symm (sTape_ne_r _ _)
  · rw [L.tm_r, L.tm_r] at h; rw [L.rm_inj (rTape_inj h)]

/-- **The big state restricts to the small one.** -/
def SubL.Agree (σ₁ : WState ns₁ nr₁) (σ₂ : WState ns₂ nr₂) : Prop :=
  (∀ i, σ₂.st (L.sm i) = σ₁.st i ∧ σ₂.sh (L.sm i) = σ₁.sh i) ∧ (∀ r, σ₂.val (L.rm r) = σ₁.val r) ∧
    σ₂.st L.cs = [σ₁.cell] ∧ σ₂.sh L.cs = 0

theorem SubL.agree_H (cap : ℕ) {σ₁ : WState ns₁ nr₁} {σ₂ : WState ns₂ nr₂} (h : L.Agree σ₁ σ₂)
    (j : Fin (ns₁ + 2 + nr₁)) : (wenc cap σ₂).H (L.tm j) = (wenc cap σ₁).H j := by
  obtain ⟨hs, hr, -, hc⟩ := h
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [L.tm_s, wenc_H_s, wenc_H_s, (hs i).2]
  · rw [L.tm_c, wenc_H_s, wenc_H_c, hc]
  · rw [L.tm_r, wenc_H_r, wenc_H_r, hr r]

theorem SubL.agree_A (cap : ℕ) {σ₁ : WState ns₁ nr₁} {σ₂ : WState ns₂ nr₂} (h : L.Agree σ₁ σ₂)
    (j : Fin (ns₁ + 2 + nr₁)) : (wenc cap σ₂).A (L.tm j) = (wenc cap σ₁).A j := by
  obtain ⟨hs, hr, hcs, -⟩ := h
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [L.tm_s, wenc_A_s, wenc_A_s, (hs i).1]
  · rw [L.tm_c, wenc_A_s, wenc_A_c, hcs]
  · rw [L.tm_r, wenc_A_r, wenc_A_r, hr r]

/-- **The docked run**: the big layout's exit agrees with the small exit and keeps everything else. -/
theorem dockL (cap : ℕ) {s m : ℕ} {M : Machine (ns₁ + 2 + nr₁) s} {σ₁ τ₁ : WState ns₁ nr₁}
    (h : Step M m (wenc cap σ₁).H (wenc cap σ₁).A (wenc cap τ₁).H (wenc cap τ₁).A) (σ₂ : WState ns₂ nr₂)
    (hag : L.Agree σ₁ σ₂) :
    ∃ τ₂ : WState ns₂ nr₂, Step (RecoveryFocus.machine L.tm M) m (wenc cap σ₂).H (wenc cap σ₂).A
        (wenc cap τ₂).H (wenc cap τ₂).A ∧ L.Agree τ₁ τ₂ ∧
      (∀ s, (∀ i, L.sm i ≠ s) → s ≠ L.cs → τ₂.st s = σ₂.st s ∧ τ₂.sh s = σ₂.sh s) ∧
      (∀ r, (∀ r₁, L.rm r₁ ≠ r) → τ₂.val r = σ₂.val r) ∧ τ₂.cell = σ₂.cell := by
  classical
  have d := h.dock L.tm L.tm_inj (wenc cap σ₂).H (wenc cap σ₂).A (L.agree_H cap hag) (L.agree_A cap hag)
  let τ₂ : WState ns₂ nr₂ :=
    ⟨fun s => if h : ∃ i, L.sm i = s then τ₁.sh (Classical.choose h) else if s = L.cs then 0 else σ₂.sh s,
     fun s => if h : ∃ i, L.sm i = s then τ₁.st (Classical.choose h) else if s = L.cs then [τ₁.cell] else σ₂.st s,
     fun r => if h : ∃ r₁, L.rm r₁ = r then τ₁.val (Classical.choose h) else σ₂.val r, σ₂.cell⟩
  have ch_s : ∀ i, (Classical.choose (⟨i, rfl⟩ : ∃ i', L.sm i' = L.sm i)) = i := fun i =>
    L.sm_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', L.sm i' = L.sm i))
  have ch_r : ∀ r, (Classical.choose (⟨r, rfl⟩ : ∃ r', L.rm r' = L.rm r)) = r := fun r =>
    L.rm_inj (Classical.choose_spec (⟨r, rfl⟩ : ∃ r', L.rm r' = L.rm r))
  have hcs : ¬ ∃ i, L.sm i = L.cs := fun ⟨i, hi⟩ => L.cs_ne i hi
  have eH : dockH L.tm (wenc cap σ₂).H (wenc cap τ₁).H = (wenc cap τ₂).H := by
    funext k
    rcases tape_cases k with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [wenc_H_s]
      by_cases hs : ∃ i, L.sm i = s
      · obtain ⟨i, rfl⟩ := hs
        rw [← L.tm_s, dockH_slot _ L.tm_inj, wenc_H_s]
        simp only [τ₂, dif_pos (⟨i, rfl⟩ : ∃ i', L.sm i' = L.sm i), ch_s]
      · by_cases hc : s = L.cs
        · subst hc
          rw [← L.tm_c, dockH_slot _ L.tm_inj, wenc_H_c]
          simp only [τ₂, dif_neg hcs, if_true]
        · rw [dockH_other _ _ _ _ (fun j hj => by
              rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
              · rw [L.tm_s] at hj; exact hs ⟨i, sTape_inj hj⟩
              · rw [L.tm_c] at hj; exact hc (sTape_inj hj).symm
              · rw [L.tm_r] at hj; exact sTape_ne_r _ _ hj.symm), wenc_H_s]
          simp only [τ₂, dif_neg hs, if_neg hc]
    · rw [dockH_other _ _ _ _ (fun j hj => by
          rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
          · rw [L.tm_s] at hj; exact sTape_ne_c _ hj
          · rw [L.tm_c] at hj; exact sTape_ne_c _ hj
          · rw [L.tm_r] at hj; exact cTape_ne_r _ hj.symm), wenc_H_c, wenc_H_c]
    · rw [wenc_H_r]
      by_cases hr : ∃ r₁, L.rm r₁ = r
      · obtain ⟨r₁, rfl⟩ := hr
        rw [← L.tm_r, dockH_slot _ L.tm_inj, wenc_H_r]
        simp only [τ₂, dif_pos (⟨r₁, rfl⟩ : ∃ r', L.rm r' = L.rm r₁), ch_r]
      · rw [dockH_other _ _ _ _ (fun j hj => by
            rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r', rfl⟩
            · rw [L.tm_s] at hj; exact sTape_ne_r _ _ hj
            · rw [L.tm_c] at hj; exact sTape_ne_r _ _ hj
            · rw [L.tm_r] at hj; exact hr ⟨r', rTape_inj hj⟩), wenc_H_r]
        simp only [τ₂, dif_neg hr]
  have eA : install L.tm (wenc cap σ₂).A (wenc cap τ₁).A = (wenc cap τ₂).A := by
    funext k
    rcases tape_cases k with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [wenc_A_s]
      by_cases hs : ∃ i, L.sm i = s
      · obtain ⟨i, rfl⟩ := hs
        rw [← L.tm_s, install_slot _ L.tm_inj, wenc_A_s]
        simp only [τ₂, dif_pos (⟨i, rfl⟩ : ∃ i', L.sm i' = L.sm i), ch_s]
      · by_cases hc : s = L.cs
        · subst hc
          rw [← L.tm_c, install_slot _ L.tm_inj, wenc_A_c]
          simp only [τ₂, dif_neg hcs, if_true]
        · rw [install_other _ _ _ _ (fun j hj => by
              rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
              · rw [L.tm_s] at hj; exact hs ⟨i, sTape_inj hj⟩
              · rw [L.tm_c] at hj; exact hc (sTape_inj hj).symm
              · rw [L.tm_r] at hj; exact sTape_ne_r _ _ hj.symm), wenc_A_s]
          simp only [τ₂, dif_neg hs, if_neg hc]
    · rw [install_other _ _ _ _ (fun j hj => by
          rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
          · rw [L.tm_s] at hj; exact sTape_ne_c _ hj
          · rw [L.tm_c] at hj; exact sTape_ne_c _ hj
          · rw [L.tm_r] at hj; exact cTape_ne_r _ hj.symm), wenc_A_c, wenc_A_c]
    · rw [wenc_A_r]
      by_cases hr : ∃ r₁, L.rm r₁ = r
      · obtain ⟨r₁, rfl⟩ := hr
        rw [← L.tm_r, install_slot _ L.tm_inj, wenc_A_r]
        simp only [τ₂, dif_pos (⟨r₁, rfl⟩ : ∃ r', L.rm r' = L.rm r₁), ch_r]
      · rw [install_other _ _ _ _ (fun j hj => by
            rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r', rfl⟩
            · rw [L.tm_s] at hj; exact sTape_ne_r _ _ hj
            · rw [L.tm_c] at hj; exact sTape_ne_r _ _ hj
            · rw [L.tm_r] at hj; exact hr ⟨r', rTape_inj hj⟩), wenc_A_r]
        simp only [τ₂, dif_neg hr]
  rw [eH, eA] at d
  refine ⟨τ₂, d, ⟨fun i => ?_, fun r => ?_, ?_, ?_⟩, fun s hs hc => ?_, fun r hr => ?_, rfl⟩
  · simp only [τ₂, dif_pos (⟨i, rfl⟩ : ∃ i', L.sm i' = L.sm i), ch_s, and_self]
  · simp only [τ₂, dif_pos (⟨r, rfl⟩ : ∃ r', L.rm r' = L.rm r), ch_r]
  · simp only [τ₂, dif_neg hcs, if_true]
  · simp only [τ₂, dif_neg hcs, if_true]
  · have hs' : ¬ ∃ i, L.sm i = s := fun ⟨i, hi⟩ => hs i hi
    simp only [τ₂, dif_neg hs', if_neg hc, and_self]
  · have hr' : ¬ ∃ r₁, L.rm r₁ = r := fun ⟨r₁, hr₁⟩ => hr r₁ hr₁
    simp only [τ₂, dif_neg hr']

end NearCubicWires.WireExponent3_5.PrimThrW.W6Dock
