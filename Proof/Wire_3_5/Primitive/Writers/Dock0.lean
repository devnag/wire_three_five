import Proof.Wire_3_5.Primitive.Writers.DockW

/-! # A sub-layout machine docked into a bigger word layout at the same capacity (no extra tapes)

`DockW.dockW` docks a sub-layout machine with `q` extra tapes. Without extra tapes the slots are `wslot fs fr`
directly (streams by `fs`, registers by `fr`, the cell to the cell), and the exit state is `upd0`:

* `wslot_inj`, `upd0`, `upd0_A`, `upd0_H`, **`dockW0`**.

Paper quantity: none (machine plumbing: SB docks the carrier pipeline, P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.ListMachine.Rec

section Sub0
variable {ns nr ns' nr' : ℕ} (cap : ℕ)

theorem wslot_inj (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (hfs : Function.Injective fs)
    (hfr : Function.Injective fr) : Function.Injective (wslot fs fr) := by
  intro a b h
  rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩ <;> rcases tape_cases b with ⟨i', rfl⟩ | rfl | ⟨r', rfl⟩ <;>
    simp only [wslot_s, wslot_c, wslot_r] at h
  · rw [hfs (sTape_inj h)]
  · exact absurd h (sTape_ne_c _)
  · exact absurd h (sTape_ne_r _ _)
  · exact absurd h.symm (sTape_ne_c _)
  · rfl
  · exact absurd h (cTape_ne_r _)
  · exact absurd h.symm (sTape_ne_r _ _)
  · exact absurd h.symm (cTape_ne_r _)
  · rw [hfr (rTape_inj h)]

/-- The state after a sub-layout machine docked without extra tapes. -/
noncomputable def upd0 (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (σ : WState ns nr)
    (y : WState ns' nr') : WState ns nr :=
  ⟨dockH fs σ.sh y.sh, install fs σ.st y.st, dockH fr σ.val y.val, y.cell⟩

theorem wslot_out_s (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (j : Fin (ns' + 2 + nr'))
    (hj : ∀ x, sTape (nr := nr') x ≠ j) (i : Fin (ns + 1)) : wslot fs fr j ≠ sTape (nr := nr) i := by
  rcases tape_cases j with ⟨x, rfl⟩ | rfl | ⟨r, rfl⟩
  · exact absurd rfl (hj x)
  · rw [wslot_c]; exact fun h => sTape_ne_c i h.symm
  · rw [wslot_r]; exact fun h => sTape_ne_r i _ h.symm

theorem wslot_out_r (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (j : Fin (ns' + 2 + nr'))
    (hj : ∀ r, rTape (ns := ns') r ≠ j) (r : Fin nr) : wslot fs fr j ≠ rTape (ns := ns) r := by
  rcases tape_cases j with ⟨x, rfl⟩ | rfl | ⟨r', rfl⟩
  · rw [wslot_s]; exact sTape_ne_r _ r
  · rw [wslot_c]; exact cTape_ne_r r
  · exact absurd rfl (hj r')

theorem upd0_A (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (hfs : Function.Injective fs)
    (hfr : Function.Injective fr) (σ : WState ns nr) (y : WState ns' nr') :
    install (wslot fs fr) (wenc cap σ).A (wenc cap y).A = (wenc cap (upd0 fs fr σ y)).A := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [install_fac (wslot fs fr) (wslot_inj fs fr hfs hfr) sTape sTape_inj fs hfs sTape (fun x => wslot_s fs fr x)
      (fun j hj i => wslot_out_s fs fr j hj i), wenc_A_s,
      show (fun k => (wenc cap σ).A (sTape k)) = σ.st from funext fun k => wenc_A_s cap σ k,
      show (fun x => (wenc cap y).A (sTape x)) = y.st from funext fun x => wenc_A_s cap y x]
    rfl
  · have e := install_slot (wslot fs fr) (wslot_inj fs fr hfs hfr) (wenc cap σ).A (wenc cap y).A cTape
    rw [wslot_c, wenc_A_c] at e
    rw [e, wenc_A_c]
    rfl
  · rw [install_fac (wslot fs fr) (wslot_inj fs fr hfs hfr) rTape rTape_inj fr hfr rTape (fun r' => wslot_r fs fr r')
      (fun j hj r => wslot_out_r fs fr j hj r), wenc_A_r,
      show (fun k => (wenc cap σ).A (rTape k)) = fun k => regTape cap (σ.val k) from funext fun k => wenc_A_r cap σ k,
      show (fun x => (wenc cap y).A (rTape x)) = fun x => regTape cap (y.val x) from funext fun x => wenc_A_r cap y x,
      install_reg fr hfr σ.val y.val r (regTape cap)]
    rfl

theorem upd0_H (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr) (hfs : Function.Injective fs)
    (hfr : Function.Injective fr) (σ : WState ns nr) (y : WState ns' nr') :
    dockH (wslot fs fr) (wenc cap σ).H (wenc cap y).H = (wenc cap (upd0 fs fr σ y)).H := by
  funext k
  rcases tape_cases k with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [dockH_fac (wslot fs fr) (wslot_inj fs fr hfs hfr) sTape sTape_inj fs hfs sTape (fun x => wslot_s fs fr x)
      (fun j hj i => wslot_out_s fs fr j hj i), wenc_H_s,
      show (fun k => (wenc cap σ).H (sTape k)) = σ.sh from funext fun k => wenc_H_s cap σ k,
      show (fun x => (wenc cap y).H (sTape x)) = y.sh from funext fun x => wenc_H_s cap y x]
    rfl
  · have e := dockH_slot (wslot fs fr) (wslot_inj fs fr hfs hfr) (wenc cap σ).H (wenc cap y).H cTape
    rw [wslot_c, wenc_H_c] at e
    rw [e, wenc_H_c]
  · rw [dockH_fac (wslot fs fr) (wslot_inj fs fr hfs hfr) rTape rTape_inj fr hfr rTape (fun r' => wslot_r fs fr r')
      (fun j hj r => wslot_out_r fs fr j hj r), wenc_H_r,
      show (fun k => (wenc cap σ).H (rTape k)) = σ.val from funext fun k => wenc_H_r cap σ k,
      show (fun x => (wenc cap y).H (rTape x)) = y.val from funext fun x => wenc_H_r cap y x]
    rfl

/-- **A sub-layout machine docked at the same capacity**: a run on `wenc y` docked onto the streams `fs`, the
registers `fr` and the cell of a state `σ` that restricts to `y` there leaves `upd0 fs fr σ y'`. -/
theorem dockW0 {s n : ℕ} {M : Machine (ns' + 2 + nr') s} (fs : Fin (ns' + 1) → Fin (ns + 1)) (fr : Fin nr' → Fin nr)
    (hfs : Function.Injective fs) (hfr : Function.Injective fr) (σ : WState ns nr) (y y' : WState ns' nr')
    (h : Step M n (wenc cap y).H (wenc cap y).A (wenc cap y').H (wenc cap y').A)
    (hsh : ∀ i, σ.sh (fs i) = y.sh i) (hst : ∀ i, σ.st (fs i) = y.st i) (hv : ∀ r, σ.val (fr r) = y.val r)
    (hc : σ.cell = y.cell) :
    Step (RecoveryFocus.machine (wslot fs fr) M) n (wenc cap σ).H (wenc cap σ).A
      (wenc cap (upd0 fs fr σ y')).H (wenc cap (upd0 fs fr σ y')).A := by
  have hH : ∀ j, (wenc cap σ).H (wslot fs fr j) = (wenc cap y).H j := by
    intro j
    rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [wslot_s, wenc_H_s, wenc_H_s, hsh]
    · rw [wslot_c, wenc_H_c, wenc_H_c]
    · rw [wslot_r, wenc_H_r, wenc_H_r, hv]
  have hA : ∀ j, (wenc cap σ).A (wslot fs fr j) = (wenc cap y).A j := by
    intro j
    rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [wslot_s, wenc_A_s, wenc_A_s, hst]
    · rw [wslot_c, wenc_A_c, wenc_A_c, hc]
    · rw [wslot_r, wenc_A_r, wenc_A_r, hv]
  have hd := dockRun h (wslot fs fr) (wslot_inj fs fr hfs hfr) (wenc cap σ).H (wenc cap σ).A hH hA
  rw [upd0_H cap fs fr hfs hfr σ y', upd0_A cap fs fr hfs hfr σ y'] at hd
  exact hd

end Sub0

end NearCubicWires.WireExponent3_5.PrimAsm.DockW
