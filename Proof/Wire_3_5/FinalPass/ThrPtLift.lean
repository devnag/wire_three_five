import Proof.Wire_3_5.FinalPass.LiftR

/-! # Exact lifting of word programs (P3:3170-3178; build once)

`WExec.liftW` (C5, verified) runs a word program on renamed streams and registers and describes the end state
relationally (`LiftW` inside the images, `OutsideW` outside). `updW fs fr ω τ` is that end state written out: `ω` with
the images of `fs`, `fr` replaced by `τ`'s streams, heads and registers, and `τ`'s cell (**`liftW_updW_eq`**:
the end state IS `updW`). So a component's spec transports to the exact spec **`WExec.liftW_upd`**, and `updW`
computes along the component's own updates: `updW_self`, `updW_sets`, `updW_seth`, `updW_setv`, `updW_setc`.
Paper quantity: none beyond the machine model (composing the per-point stages in one layout). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr ns' nr' : ℕ} (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr')

/-- `ω` with the images of `fs`, `fr` replaced by `τ` (and `τ`'s cell). -/
noncomputable def updW (ω : WState ns' nr') (τ : WState ns nr) : WState ns' nr' := by
  classical
  exact ⟨fun j => if h : ∃ i, fs i = j then τ.sh h.choose else ω.sh j,
    fun j => if h : ∃ i, fs i = j then τ.st h.choose else ω.st j,
    fun q => if h : ∃ r, fr r = q then τ.val h.choose else ω.val q, τ.cell⟩

variable {fs fr}

theorem choose_eq (hfs : Function.Injective fs) (i : Fin (ns + 1)) (h : ∃ i', fs i' = fs i) : h.choose = i :=
  hfs h.choose_spec

theorem chooseR_eq (hfr : Function.Injective fr) (r : Fin nr) (h : ∃ r', fr r' = fr r) : h.choose = r :=
  hfr h.choose_spec

theorem updW_sh_in (hfs : Function.Injective fs) (ω : WState ns' nr') (τ : WState ns nr) (i : Fin (ns + 1)) :
    (updW fs fr ω τ).sh (fs i) = τ.sh i := by
  classical
  have h : ∃ i', fs i' = fs i := ⟨i, rfl⟩
  simp only [updW, dif_pos h, choose_eq hfs i h]

theorem updW_st_in (hfs : Function.Injective fs) (ω : WState ns' nr') (τ : WState ns nr) (i : Fin (ns + 1)) :
    (updW fs fr ω τ).st (fs i) = τ.st i := by
  classical
  have h : ∃ i', fs i' = fs i := ⟨i, rfl⟩
  simp only [updW, dif_pos h, choose_eq hfs i h]

theorem updW_val_in (hfr : Function.Injective fr) (ω : WState ns' nr') (τ : WState ns nr) (r : Fin nr) :
    (updW fs fr ω τ).val (fr r) = τ.val r := by
  classical
  have h : ∃ r', fr r' = fr r := ⟨r, rfl⟩
  simp only [updW, dif_pos h, chooseR_eq hfr r h]

theorem updW_sh_out (ω : WState ns' nr') (τ : WState ns nr) (j : Fin (ns' + 1)) (hj : ∀ i, fs i ≠ j) :
    (updW fs fr ω τ).sh j = ω.sh j := by
  classical
  have h : ¬ ∃ i, fs i = j := fun ⟨i, e⟩ => hj i e
  simp only [updW, dif_neg h]

theorem updW_st_out (ω : WState ns' nr') (τ : WState ns nr) (j : Fin (ns' + 1)) (hj : ∀ i, fs i ≠ j) :
    (updW fs fr ω τ).st j = ω.st j := by
  classical
  have h : ¬ ∃ i, fs i = j := fun ⟨i, e⟩ => hj i e
  simp only [updW, dif_neg h]

theorem updW_val_out (ω : WState ns' nr') (τ : WState ns nr) (q : Fin nr') (hq : ∀ r, fr r ≠ q) :
    (updW fs fr ω τ).val q = ω.val q := by
  classical
  have h : ¬ ∃ r, fr r = q := fun ⟨r, e⟩ => hq r e
  simp only [updW, dif_neg h]

theorem updW_cell (ω : WState ns' nr') (τ : WState ns nr) : (updW fs fr ω τ).cell = τ.cell := rfl

/-- Two states agreeing on every stream, head, register and the cell through a case split on the images. -/
theorem wstate_ext_img {α β : WState ns' nr'}
    (hsi : ∀ i, α.sh (fs i) = β.sh (fs i)) (hso : ∀ j, (∀ i, fs i ≠ j) → α.sh j = β.sh j)
    (hti : ∀ i, α.st (fs i) = β.st (fs i)) (hto : ∀ j, (∀ i, fs i ≠ j) → α.st j = β.st j)
    (hvi : ∀ r, α.val (fr r) = β.val (fr r)) (hvo : ∀ q, (∀ r, fr r ≠ q) → α.val q = β.val q)
    (hc : α.cell = β.cell) : α = β := by
  classical
  apply WState.eq
  · funext j
    by_cases h : ∃ i, fs i = j
    · obtain ⟨i, rfl⟩ := h; exact hsi i
    · exact hso j (fun i e => h ⟨i, e⟩)
  · funext j
    by_cases h : ∃ i, fs i = j
    · obtain ⟨i, rfl⟩ := h; exact hti i
    · exact hto j (fun i e => h ⟨i, e⟩)
  · funext q
    by_cases h : ∃ r, fr r = q
    · obtain ⟨r, rfl⟩ := h; exact hvi r
    · exact hvo q (fun r e => h ⟨r, e⟩)
  · exact hc

/-- **The lifted end state is `updW`.** -/
theorem liftW_updW_eq (hfs : Function.Injective fs) (hfr : Function.Injective fr) {ω ω' : WState ns' nr'}
    {τ : WState ns nr} (hL : LiftW fs fr ω' τ) (hO : OutsideW fs fr ω ω') : ω' = updW fs fr ω τ :=
  wstate_ext_img (fs := fs) (fr := fr) (fun i => by rw [updW_sh_in hfs, hL.sh]) (fun j hj => by rw [updW_sh_out _ _ j hj,
    (hO.1 j hj).1]) (fun i => by rw [updW_st_in hfs, hL.st]) (fun j hj => by rw [updW_st_out _ _ j hj,
    (hO.1 j hj).2]) (fun r => by rw [updW_val_in hfr, hL.val]) (fun q hq => by rw [updW_val_out _ _ q hq,
    hO.2 q hq]) hL.cell

/-- **Exact lifting**: a component's run from `σ` to `τ` runs, renamed, from any `ω` carrying `σ` to `updW ω τ`. -/
theorem WExec.liftW_upd (cap : ℕ) (hfs : Function.Injective fs) (hfr : Function.Injective fr) {P : WM ns nr}
    {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (ω : WState ns' nr') (hL : LiftW fs fr ω σ) :
    WExec cap (P.liftW fs fr) ω (updW fs fr ω τ) n := by
  obtain ⟨ω', e, hL', hO⟩ := WExec.liftW cap cap le_rfl fs hfs fr hfr h ω hL
  rwa [liftW_updW_eq hfs hfr hL' hO] at e

/-! ## Computing `updW` -/

theorem updW_self (hfs : Function.Injective fs) (hfr : Function.Injective fr) {ω : WState ns' nr'}
    {σ : WState ns nr} (hL : LiftW fs fr ω σ) : updW fs fr ω σ = ω :=
  wstate_ext_img (fs := fs) (fr := fr) (fun i => by rw [updW_sh_in hfs, hL.sh]) (fun j hj => updW_sh_out _ _ j hj)
    (fun i => by rw [updW_st_in hfs, hL.st]) (fun j hj => updW_st_out _ _ j hj)
    (fun r => by rw [updW_val_in hfr, hL.val]) (fun q hq => updW_val_out _ _ q hq) hL.cell.symm

theorem updW_sets (hfs : Function.Injective fs) (hfr : Function.Injective fr) (ω : WState ns' nr')
    (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) :
    updW fs fr ω (σ.sets i l) = (updW fs fr ω σ).sets (fs i) l := by
  refine wstate_ext_img (fs := fs) (fr := fr) (fun i' => ?_) (fun j hj => ?_) (fun i' => ?_) (fun j hj => ?_) (fun r => ?_)
    (fun q hq => ?_) rfl
  · rw [updW_sh_in hfs]; simp [updW_sh_in hfs]
  · rw [updW_sh_out _ _ j hj]; simp [updW_sh_out _ _ j hj]
  · rw [updW_st_in hfs]
    by_cases h : i' = i
    · subst h; simp
    · have hne : fs i' ≠ fs i := fun e => h (hfs e)
      simp [Function.update_of_ne h, Function.update_of_ne hne, updW_st_in hfs]
  · rw [updW_st_out _ _ j hj]
    have hne : j ≠ fs i := fun e => hj i e.symm
    simp [Function.update_of_ne hne, updW_st_out _ _ j hj]
  · rw [updW_val_in hfr]; simp [updW_val_in hfr]
  · rw [updW_val_out _ _ q hq]; simp [updW_val_out _ _ q hq]

theorem updW_seth (hfs : Function.Injective fs) (hfr : Function.Injective fr) (ω : WState ns' nr')
    (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) :
    updW fs fr ω (σ.seth i x) = (updW fs fr ω σ).seth (fs i) x := by
  refine wstate_ext_img (fs := fs) (fr := fr) (fun i' => ?_) (fun j hj => ?_) (fun i' => ?_) (fun j hj => ?_) (fun r => ?_)
    (fun q hq => ?_) rfl
  · rw [updW_sh_in hfs]
    by_cases h : i' = i
    · subst h; simp
    · have hne : fs i' ≠ fs i := fun e => h (hfs e)
      simp [Function.update_of_ne h, Function.update_of_ne hne, updW_sh_in hfs]
  · rw [updW_sh_out _ _ j hj]
    have hne : j ≠ fs i := fun e => hj i e.symm
    simp [Function.update_of_ne hne, updW_sh_out _ _ j hj]
  · rw [updW_st_in hfs]; simp [updW_st_in hfs]
  · rw [updW_st_out _ _ j hj]; simp [updW_st_out _ _ j hj]
  · rw [updW_val_in hfr]; simp [updW_val_in hfr]
  · rw [updW_val_out _ _ q hq]; simp [updW_val_out _ _ q hq]

theorem updW_setv (hfs : Function.Injective fs) (hfr : Function.Injective fr) (ω : WState ns' nr')
    (σ : WState ns nr) (r : Fin nr) (v : ℕ) :
    updW fs fr ω (σ.setv r v) = (updW fs fr ω σ).setv (fr r) v := by
  refine wstate_ext_img (fs := fs) (fr := fr) (fun i' => ?_) (fun j hj => ?_) (fun i' => ?_) (fun j hj => ?_) (fun r' => ?_)
    (fun q hq => ?_) rfl
  · rw [updW_sh_in hfs]; simp [updW_sh_in hfs]
  · rw [updW_sh_out _ _ j hj]; simp [updW_sh_out _ _ j hj]
  · rw [updW_st_in hfs]; simp [updW_st_in hfs]
  · rw [updW_st_out _ _ j hj]; simp [updW_st_out _ _ j hj]
  · rw [updW_val_in hfr]
    by_cases h : r' = r
    · subst h; simp
    · have hne : fr r' ≠ fr r := fun e => h (hfr e)
      simp [Function.update_of_ne h, Function.update_of_ne hne, updW_val_in hfr]
  · rw [updW_val_out _ _ q hq]
    have hne : q ≠ fr r := fun e => hq r e.symm
    simp [Function.update_of_ne hne, updW_val_out _ _ q hq]

theorem updW_setc (ω : WState ns' nr') (σ : WState ns nr) (c : Bool) :
    updW fs fr ω (σ.setc c) = (updW fs fr ω σ).setc c := rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
