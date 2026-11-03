import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.Primitive.Writers.DockW
import Proof.Wire_3_5.MachineModel.BlockJoin
import Proof.Circuits.DecompositionSourceBounds

/-! # Writer combinators: one writer from several

The core half's writers are one machine per gate on their own encoded bank (`Finish.CoreWordsMJ`, P3:3170-3181).
A writer whose words come from several producers (S4's words: the offset, the sample, the carrier tables) is built
here from writers of the parts:

* the layout embedding: `tmap` (a writer's tapes into a larger bank: streams along `es`, the cell, registers along
  `er`), `restrict`, `overlay`, **`embed_run`** (a run on the restricted state is a focused run on the large one);
* **`CoreWordsMJ.join W W'`**: `W`'s words then `W'`'s (`Fin.append`), on the disjoint union of the two layouts,
  sharing the input stream (`W` keeps it, `W'` reads it after), the cell reset between them; capacity
  `(Kc + Kc')·(N+1)^{Dk + Dk'}`, steps and residues within `(Cs + Cs' + 4)·(N+1)^{Ds + Ds'}`;
* **`CoreWordsMJ.reindex`** (along `Fin m' ≃ Fin m`), **`CoreWordsMJ.congr`** (equal word families),
  **`CoreWordsMJ.sub`** (a subset of the words; the dropped words become residues, bounded by the step count).

Paper quantity of the main type: the front's words at a request (the writers' output words `ws r`, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Join
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Encodings: heads, padding, tape growth -/

theorem wencH0 {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ q, σ.val q = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [wenc_H_s, hs]
  · rw [wenc_H_c]
  · rw [wenc_H_r, hv]

theorem stepPad {t s : ℕ} {p : Machine t s} {n : ℕ} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (cap : Fin t → ℕ) :
    Step p n H (fun i => ZeroPadding.pad (cap i) (A i)) H' (fun i => ZeroPadding.pad (cap i) (A' i)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨r', hr', hf, hsteps, -⟩ := ZeroPadding.run_config p cap n _ r hr
  refine ⟨r', ?_, ?_, ?_, by omega⟩
  · have e : ZeroPadding.config cap (⟨p.start, H, A⟩ : Configuration t s) =
        ⟨p.start, H, fun i => ZeroPadding.pad (cap i) (A i)⟩ := rfl
    rw [← e]; exact hr'
  · rw [hf]; exact hh
  · rw [hf]; funext i; simp only [ZeroPadding.config, ht]

theorem stepLen {t s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (i : Fin t) (k : ℕ) (hh : hin i ≤ k) (ht : (tin i).length ≤ k) :
    (tout i).length ≤ k + n := by
  obtain ⟨r, hr, _, hT, hs⟩ := h
  have := DecompositionSource.one_tape_support p n ⟨p.start, hin, tin⟩ r i k hr hh ht
  rw [hT] at this
  omega

/-- The padding of the register tapes to capacity `c'`. -/
def padC (ns nr c' : ℕ) (j : Fin (ns + 2 + nr)) : ℕ := if ns + 2 ≤ j.val then c' + 1 else 0

theorem wenc_padC {ns nr : ℕ} (c c' : ℕ) (hc : c ≤ c') (σ : WState ns nr) (hv : ∀ r, σ.val r = 0) :
    (fun j => ZeroPadding.pad (padC ns nr c' j) ((wenc c σ).A j)) = (wenc c' σ).A := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · have h0 : padC ns nr c' (sTape (nr := nr) i) = 0 := by
      unfold padC; rw [if_neg]; rw [sTape_val]; have := i.isLt; split_ifs <;> omega
    rw [h0, ZeroPadding.pad_zero, wenc_A_s, wenc_A_s]
  · have h0 : padC ns nr c' (cTape (ns := ns) (nr := nr)) = 0 := by
      unfold padC; rw [if_neg]; rw [cTape_val]; omega
    rw [h0, ZeroPadding.pad_zero, wenc_A_c, wenc_A_c]
  · have h1 : padC ns nr c' (rTape (ns := ns) r) = c' + 1 := by
      unfold padC; rw [if_pos]; rw [rTape_val]; omega
    rw [h1, wenc_A_r, wenc_A_r, hv, regTape_zero, regTape_zero]
    unfold ZeroPadding.pad
    rw [List.length_replicate, ← List.replicate_add]
    congr 1
    omega

/-- **A run at a capacity is a run at any larger one** (registers `0` at both ends). -/
theorem stepUp {ns nr s : ℕ} (M : Machine (ns + 2 + nr) s) (n c c' : ℕ) (hc : c ≤ c') (σ τ : WState ns nr)
    (hσ : ∀ r, σ.val r = 0) (hτ : ∀ r, τ.val r = 0)
    (h : Step M n (wenc c σ).H (wenc c σ).A (wenc c τ).H (wenc c τ).A) :
    Step M n (wenc c' σ).H (wenc c' σ).A (wenc c' τ).H (wenc c' τ).A := by
  have hp := stepPad h (padC ns nr c')
  rw [wenc_padC c c' hc σ hσ, wenc_padC c c' hc τ hτ] at hp
  exact hp

/-! ## A writer's layout inside a larger one -/

section Embed
variable {ns nr NS NR : ℕ} (es : Fin (ns + 1) → Fin (NS + 1)) (er : Fin nr → Fin NR)

/-- The tape map: streams along `es`, the cell to the cell, registers along `er`. -/
def tmap (j : Fin (ns + 2 + nr)) : Fin (NS + 2 + NR) :=
  match role j with
  | .stream i => sTape (es i)
  | .cell => cTape
  | .reg q => rTape (er q)

theorem tmap_s (i : Fin (ns + 1)) : tmap es er (sTape (nr := nr) i) = sTape (nr := NR) (es i) := by
  simp only [tmap, role_sTape]

theorem tmap_c : tmap es er (cTape (ns := ns) (nr := nr)) = cTape (ns := NS) (nr := NR) := by
  simp only [tmap, role_cTape]

theorem tmap_r (q : Fin nr) : tmap es er (rTape (ns := ns) q) = rTape (ns := NS) (er q) := by
  simp only [tmap, role_rTape]

theorem tmap_inj (hs : Function.Injective es) (hr : Function.Injective er) : Function.Injective (tmap es er) := by
  intro a b h
  rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩ <;> rcases tape_cases b with ⟨i', rfl⟩ | rfl | ⟨q', rfl⟩
  · rw [tmap_s, tmap_s] at h; rw [hs (sTape_inj h)]
  · rw [tmap_s, tmap_c] at h; exact absurd h (sTape_ne_c _)
  · rw [tmap_s, tmap_r] at h; exact absurd h (sTape_ne_r _ _)
  · rw [tmap_c, tmap_s] at h; exact absurd h.symm (sTape_ne_c _)
  · rfl
  · rw [tmap_c, tmap_r] at h; exact absurd h (cTape_ne_r _)
  · rw [tmap_r, tmap_s] at h; exact absurd h.symm (sTape_ne_r _ _)
  · rw [tmap_r, tmap_c] at h; exact absurd h.symm (cTape_ne_r _)
  · rw [tmap_r, tmap_r] at h; rw [hr (rTape_inj h)]

/-- The writer's state read off the large one. -/
def restrict (σ : WState NS NR) : WState ns nr :=
  ⟨fun i => σ.sh (es i), fun i => σ.st (es i), fun q => σ.val (er q), σ.cell⟩

open Classical in
/-- The large state with the writer's part replaced by `τ`. -/
noncomputable def overlay (σ : WState NS NR) (τ : WState ns nr) : WState NS NR :=
  ⟨fun i => if h : ∃ j, es j = i then τ.sh h.choose else σ.sh i,
    fun i => if h : ∃ j, es j = i then τ.st h.choose else σ.st i,
    fun q => if h : ∃ p, er p = q then τ.val h.choose else σ.val q, τ.cell⟩

variable {es er}

theorem overlay_sh_in (hs : Function.Injective es) (σ : WState NS NR) (τ : WState ns nr) (i : Fin (ns + 1)) :
    (overlay es er σ τ).sh (es i) = τ.sh i := by
  have h : ∃ j, es j = es i := ⟨i, rfl⟩
  simp only [overlay]
  rw [dif_pos h, hs h.choose_spec]

theorem overlay_st_in (hs : Function.Injective es) (σ : WState NS NR) (τ : WState ns nr) (i : Fin (ns + 1)) :
    (overlay es er σ τ).st (es i) = τ.st i := by
  have h : ∃ j, es j = es i := ⟨i, rfl⟩
  simp only [overlay]
  rw [dif_pos h, hs h.choose_spec]

theorem overlay_val_in (hr : Function.Injective er) (σ : WState NS NR) (τ : WState ns nr) (q : Fin nr) :
    (overlay es er σ τ).val (er q) = τ.val q := by
  have h : ∃ p, er p = er q := ⟨q, rfl⟩
  simp only [overlay]
  rw [dif_pos h, hr h.choose_spec]

theorem overlay_st_off (σ : WState NS NR) (τ : WState ns nr) (i : Fin (NS + 1)) (hi : ∀ j, es j ≠ i) :
    (overlay es er σ τ).st i = σ.st i := by
  simp only [overlay]
  rw [dif_neg (fun ⟨j, hj⟩ => hi j hj)]

theorem overlay_val_off (σ : WState NS NR) (τ : WState ns nr) (q : Fin NR) (hq : ∀ p, er p ≠ q) :
    (overlay es er σ τ).val q = σ.val q := by
  simp only [overlay]
  rw [dif_neg (fun ⟨p, hp⟩ => hq p hp)]

theorem overlay_sh0 (σ : WState NS NR) (τ : WState ns nr) (hσ : ∀ i, σ.sh i = 0) (hτ : ∀ i, τ.sh i = 0) :
    ∀ i, (overlay es er σ τ).sh i = 0 := by
  intro i
  simp only [overlay]
  split_ifs
  · exact hτ _
  · exact hσ _

theorem overlay_val0 (σ : WState NS NR) (τ : WState ns nr) (hσ : ∀ q, σ.val q = 0) (hτ : ∀ q, τ.val q = 0) :
    ∀ q, (overlay es er σ τ).val q = 0 := by
  intro q
  simp only [overlay]
  split_ifs
  · exact hτ _
  · exact hσ _

theorem restrict_overlay (hs : Function.Injective es) (hr : Function.Injective er) (σ : WState NS NR)
    (τ : WState ns nr) : restrict es er (overlay es er σ τ) = τ :=
  WState.eq (funext fun i => overlay_sh_in (er := er) hs σ τ i) (funext fun i => overlay_st_in (er := er) hs σ τ i)
    (funext fun q => overlay_val_in (es := es) hr σ τ q) rfl

variable (es er)

theorem wenc_restrict (c : ℕ) (σ : WState NS NR) (j : Fin (ns + 2 + nr)) :
    (wenc c σ).A (tmap es er j) = (wenc c (restrict es er σ)).A j := by
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [tmap_s, wenc_A_s, wenc_A_s]; rfl
  · rw [tmap_c, wenc_A_c, wenc_A_c]; rfl
  · rw [tmap_r, wenc_A_r, wenc_A_r]; rfl

theorem wenc_overlay (hs : Function.Injective es) (hr : Function.Injective er) (c : ℕ) (σ : WState NS NR)
    (τ : WState ns nr) : install (tmap es er) (wenc c σ).A (wenc c τ).A = (wenc c (overlay es er σ τ)).A := by
  funext y
  by_cases hy : ∃ j, tmap es er j = y
  · obtain ⟨j, rfl⟩ := hy
    rw [install_slot _ (tmap_inj es er hs hr), wenc_restrict, restrict_overlay hs hr]
  · have hy' : ∀ j, tmap es er j ≠ y := fun j e => hy ⟨j, e⟩
    rw [install_other _ _ _ _ hy']
    rcases tape_cases y with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
    · rw [wenc_A_s, wenc_A_s, overlay_st_off σ τ i (fun j e => hy' (sTape j) (by rw [tmap_s, e]))]
    · exact absurd (tmap_c es er) (hy' _)
    · rw [wenc_A_r, wenc_A_r, overlay_val_off σ τ q (fun p e => hy' (rTape p) (by rw [tmap_r, e]))]

/-- **A writer's run inside a larger layout**: a run from the restricted state, heads and registers `0` at both
ends, is the focused machine's run on the large encoding, ending at the overlay. -/
theorem embed_run {s : ℕ} (M : Machine (ns + 2 + nr) s) (hs : Function.Injective es) (hr : Function.Injective er)
    (c n : ℕ) (σ : WState NS NR) (τ : WState ns nr) (hσs : ∀ i, σ.sh i = 0) (hσv : ∀ q, σ.val q = 0)
    (hτs : ∀ i, τ.sh i = 0) (hτv : ∀ q, τ.val q = 0)
    (h : Step M n (wenc c (restrict es er σ)).H (wenc c (restrict es er σ)).A (wenc c τ).H (wenc c τ).A) :
    Step (RecoveryFocus.machine (tmap es er) M) n (wenc c σ).H (wenc c σ).A (wenc c (overlay es er σ τ)).H
      (wenc c (overlay es er σ τ)).A := by
  rw [wencH0 c (restrict es er σ) (fun i => hσs _) (fun q => hσv _), wencH0 c τ hτs hτv] at h
  have hd := Block.dockKeep h (tmap es er) (tmap_inj es er hs hr) (wenc c σ).H (wenc c σ).A
    (fun j => by rw [wencH0 c σ hσs hσv]) (wenc_restrict es er c σ)
  rw [wenc_overlay es er hs hr c σ τ] at hd
  have e : (wenc c (overlay es er σ τ)).H = (wenc c σ).H := by
    rw [wencH0 c σ hσs hσv, wencH0 c _ (overlay_sh0 σ τ hσs hτs) (overlay_val0 σ τ hσv hτv)]
  rw [e]
  exact hd

end Embed

end NearCubicWires.WireExponent3_5.FinalPass.Out.Join
