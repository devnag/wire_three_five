import Proof.Wire_3_5.FinalPass.ThrPtLift

/-! # Exact lifting of register programs (P3:3170-3178; build once)

`RExec.liftR` (C5, verified) runs a register program on renamed read-only streams and renamed registers,
relationally. `updR fs fr ω τ` is its end state written out: `ω` with the heads of the renamed streams, the renamed
registers and the cell taken from `τ`, every stream's content kept (**`liftR_updR_eq`**), so a register program's spec
transports exactly (**`RExec.liftR_upd`**). Paper quantity: none beyond the machine model. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr ns' nr' : ℕ} (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr')

/-- `ω` with the renamed heads, the renamed registers and the cell taken from `τ`. -/
noncomputable def updR (ω : WState ns' nr') (τ : RState ns nr) : WState ns' nr' := by
  classical
  exact ⟨fun j => if h : ∃ i, fs i = j then τ.sh h.choose else ω.sh j, ω.st,
    fun q => if h : ∃ r, fr r = q then τ.val h.choose else ω.val q, τ.cell⟩

variable {fs fr}

theorem updR_sh_in (hfs : Function.Injective fs) (ω : WState ns' nr') (τ : RState ns nr) (i : Fin (ns + 1)) :
    (updR fs fr ω τ).sh (fs i) = τ.sh i := by
  classical
  have h : ∃ i', fs i' = fs i := ⟨i, rfl⟩
  simp only [updR, dif_pos h, choose_eq hfs i h]

theorem updR_val_in (hfr : Function.Injective fr) (ω : WState ns' nr') (τ : RState ns nr) (r : Fin nr) :
    (updR fs fr ω τ).val (fr r) = τ.val r := by
  classical
  have h : ∃ r', fr r' = fr r := ⟨r, rfl⟩
  simp only [updR, dif_pos h, chooseR_eq hfr r h]

theorem updR_sh_out (ω : WState ns' nr') (τ : RState ns nr) (j : Fin (ns' + 1)) (hj : ∀ i, fs i ≠ j) :
    (updR fs fr ω τ).sh j = ω.sh j := by
  classical
  have h : ¬ ∃ i, fs i = j := fun ⟨i, e⟩ => hj i e
  simp only [updR, dif_neg h]

theorem updR_val_out (ω : WState ns' nr') (τ : RState ns nr) (q : Fin nr') (hq : ∀ r, fr r ≠ q) :
    (updR fs fr ω τ).val q = ω.val q := by
  classical
  have h : ¬ ∃ r, fr r = q := fun ⟨r, e⟩ => hq r e
  simp only [updR, dif_neg h]

theorem updR_st (ω : WState ns' nr') (τ : RState ns nr) : (updR fs fr ω τ).st = ω.st := rfl

/-- **The lifted end state is `updR`.** -/
theorem liftR_updR_eq (inp : Fin (ns + 1) → List Bool) (hfs : Function.Injective fs) (hfr : Function.Injective fr)
    {ω ω' : WState ns' nr'} {τ : RState ns nr} (hL : LiftRelR fs fr inp ω' τ) (hO : OutsideR fs fr ω ω') :
    ω' = updR fs fr ω τ :=
  wstate_ext_img (fs := fs) (fr := fr) (fun i => by rw [updR_sh_in hfs, hL.sh])
    (fun j hj => by rw [updR_sh_out _ _ j hj, hO.2.1 j hj]) (fun i => by rw [updR_st, hO.1])
    (fun j _ => by rw [updR_st, hO.1]) (fun r => by rw [updR_val_in hfr, hL.val])
    (fun q hq => by rw [updR_val_out _ _ q hq, hO.2.2 q hq]) hL.cell

/-- **Exact lifting of a register program.** -/
theorem RExec.liftR_upd (inp : Fin (ns + 1) → List Bool) (cap cap' : ℕ) (hcap : cap ≤ cap')
    (hfs : Function.Injective fs) (hfr : Function.Injective fr) {P : RM ns nr} {σ τ : RState ns nr} {n : ℕ}
    (h : RExec inp cap P σ τ n) (ω : WState ns' nr') (hL : LiftRelR fs fr inp ω σ) :
    WExec cap' (P.liftR fs fr) ω (updR fs fr ω τ) n := by
  obtain ⟨ω', e, hL', hO⟩ := RExec.liftR inp cap cap' hcap fs hfs fr hfr h ω hL
  rwa [liftR_updR_eq inp hfs hfr hL' hO] at e

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
