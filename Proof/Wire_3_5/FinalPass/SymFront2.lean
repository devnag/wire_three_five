import Proof.Wire_3_5.FinalPass.SymFront1

/-! # The SYM front, part 2: stream `113` rewound by a bound

The SYM numbers program leaves the counts stream `113`'s head within its step count `h ≤ K₁·(|fpIn|+1)^{D₃}`
(`numsBankG`, `NumsA11.K1a`, `D3a`). **`rewW K₁ D₃`** (the finish pattern, `NumsA10.finW`, without the
denominator's multiply): the scratch `480 … 486` cleared, `|fpIn|` measured (`frameLenW`), `K₁·(|fpIn|+1)^{D₃}`
computed (`incK`, `powN`), stream `113` rewound by it, the scratch cleared. **`rew_run`**: every head `0`, the streams
and the cell kept, the registers kept but the scratch (`0`).

Paper quantity: none (plumbing of the SYM front). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (clearL zeroL clearL_spec powN powN_spec)

/-- The rewind's scratch registers `480 + k`. -/
def pr (k : Fin 7) : Fin LNR := ⟨480 + k.val, by have := k.isLt; show 480 + k.val < 512; omega⟩

/-- The power's registers `(value, base, scratch …)`. -/
def PR : Fin 6 ↪ Fin LNR := ⟨![pr 0, pr 1, pr 2, pr 3, pr 4, pr 5], by decide⟩

/-- The scratch list. -/
def scrR : List (Fin LNR) := List.ofFn pr

theorem mem_scrR (q : Fin LNR) : q ∈ scrR ↔ 480 ≤ q.val ∧ q.val ≤ 486 := by
  unfold scrR
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨k, rfl⟩
    have := k.isLt
    show 480 ≤ 480 + k.val ∧ 480 + k.val ≤ 486
    omega
  · intro ⟨h1, h2⟩
    exact ⟨⟨q.val - 480, by omega⟩, Fin.ext (by show 480 + (q.val - 480) = q.val; omega)⟩

variable (x : ℕ)

/-- **The rewind of stream `113`** by `K₁·(|fpIn|+1)^{D₃}`. -/
def rewW (K1 D3 : ℕ) : WM (LNS x) LNR :=
  .seq (clearL scrR) (.seq (frameLenW (sIn x) (pr 1) (pr 6)) (.seq (.inc (pr 1)) (.seq (incK (pr 0) K1)
    (.seq (powN PR D3) (.seq (WM.rewind (sk x 113) (pr 0)) (WM.clear (pr 1)))))))

/-- The rewind's step bound. -/
def rewCost (B Bh F K1 D3 : ℕ) : ℕ := 1000 * (B + Bh + F + K1 + D3 + 2) ^ 3

theorem rew_run (cap K1 D3 h B : ℕ) (w : List Bool) (ω : WState (LNS x) LNR) (hin : ω.st (sIn x) = frame w)
    (hsh : ∀ i, i ≠ sk x 113 → ω.sh i = 0) (h113 : ω.sh (sk x 113) = h) (hh : h ≤ K1 * (w.length + 1) ^ D3)
    (hval : ∀ q, ω.val q ≤ B) (hc : B + K1 * (w.length + 1) ^ D3 + 2 * w.length + 2 ≤ cap) :
    ∃ c, WExec cap (rewW x K1 D3) ω ⟨fun _ => 0, ω.st, fun q => if q ∈ scrR then 0 else ω.val q, ω.cell⟩ c ∧
      c ≤ rewCost B (K1 * (w.length + 1) ^ D3) w.length K1 D3 := by
  obtain ⟨X, hXd⟩ : ∃ v, v = w.length + 1 := ⟨_, rfl⟩
  obtain ⟨Bh, hBhd⟩ : ∃ v, v = K1 * X ^ D3 := ⟨_, rfl⟩
  rw [← hXd, ← hBhd] at hh hc ⊢
  have hX1 : 1 ≤ X := by omega
  have pv : ∀ k : Fin 7, (pr k).val = 480 + k.val := fun k => rfl
  have pne : ∀ a b : Fin 7, a ≠ b → pr a ≠ pr b := fun a b h e => h (Fin.ext (by
    have := congrArg Fin.val e; rw [pv, pv] at this; omega))
  -- the scratch cleared
  obtain ⟨c0, e0, hc0⟩ := clearL_spec cap B (by omega) scrR ω (fun r _ => hval r)
  set ω0 := zeroL ω scrR with hω0
  have z0 : ∀ k : Fin 7, ω0.val (pr k) = 0 := fun k => by
    show (if pr k ∈ scrR then 0 else ω.val (pr k)) = 0
    rw [if_pos ((mem_scrR _).2 (by rw [pv]; have := k.isLt; omega))]
  -- `|fpIn|`
  have e1 := frameLen_spec cap (sIn x) (pr 1) (pr 6) (pne 1 6 (by decide)) w ω0 hin (hsh _ (fne (by show (150 : ℕ) ≠ 113; omega)))
    (z0 1) (z0 6) (by omega)
  set ω1 := ω0.setv (pr 1) w.length with hω1
  -- `X = |fpIn| + 1`
  have e2 := WExec.inc (cap := cap) (pr 1) ω1 (by rw [hω1, wsetv_val_self]; omega)
  set ω2 := ω1.setv (pr 1) (ω1.val (pr 1) + 1) with hω2
  have v21 : ω2.val (pr 1) = X := by rw [hω2, wsetv_val_self, hω1, wsetv_val_self]; omega
  -- `K₁`
  have e3 := incK_spec cap (pr 0) K1 ω2 (by
    rw [hω2, wsetv_val_ne _ _ (pne 0 1 (by decide)), hω1, wsetv_val_ne _ _ (pne 0 1 (by decide)), z0]
    have : K1 ≤ Bh := by rw [hBhd]; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hX1)
    omega)
  set ω3 := ω2.setv (pr 0) (ω2.val (pr 0) + K1) with hω3
  have v30 : ω3.val (pr 0) = K1 := by
    rw [hω3, wsetv_val_self, hω2, wsetv_val_ne _ _ (pne 0 1 (by decide)), hω1,
      wsetv_val_ne _ _ (pne 0 1 (by decide)), z0, Nat.zero_add]
  have v31 : ω3.val (pr 1) = X := by rw [hω3, wsetv_val_ne _ _ (pne 1 0 (by decide)), v21]
  have v3k : ∀ k : Fin 7, 2 ≤ k.val → ω3.val (pr k) = 0 := fun k hk => by
    have n0 : pr k ≠ pr 0 := pne k 0 (fun e => by rw [e] at hk; simp at hk)
    have n1 : pr k ≠ pr 1 := pne k 1 (fun e => by rw [e] at hk; simp at hk)
    rw [hω3, wsetv_val_ne _ _ n0, hω2, wsetv_val_ne _ _ n1, hω1, wsetv_val_ne _ _ n1, z0]
  -- `K₁·X^{D₃}`
  have hpw : ∀ j, j ≤ D3 → K1 * X ^ j ≤ Bh := fun j hj => by
    rw [hBhd]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 hj)
  obtain ⟨c4, e4, hc4⟩ := powN_spec cap PR Bh (by omega) D3 ω3 (v3k 2 (by decide)) (v3k 3 (by decide))
    (v3k 4 (by decide)) (v3k 5 (by decide)) (by show ω3.val (pr 1) ≤ cap; rw [v31]; omega)
    (fun j hj => by show ω3.val (pr 0) * ω3.val (pr 1) ^ j ≤ Bh; rw [v30, v31]; exact hpw j hj)
  set ω4 := ω3.setv (PR 0) (ω3.val (PR 0) * ω3.val (PR 1) ^ D3) with hω4
  have v40 : ω4.val (pr 0) = Bh := by
    rw [hω4]; show (ω3.setv (pr 0) (ω3.val (pr 0) * ω3.val (pr 1) ^ D3)).val (pr 0) = Bh
    rw [wsetv_val_self, v30, v31, hBhd]
  -- the rewind
  have e5 := wrewind_spec cap (sk x 113) (pr 0) Bh ω4 v40 (by rw [v40]; omega)
  set ω5 := (ω4.setv (pr 0) 0).seth (sk x 113) (ω4.sh (sk x 113) - Bh) with hω5
  have v51 : ω5.val (pr 1) = X := by
    rw [hω5]; simp only [WState.seth_val]
    rw [wsetv_val_ne _ _ (pne 1 0 (by decide)), hω4]
    show (ω3.setv (pr 0) _).val (pr 1) = X
    rw [wsetv_val_ne _ _ (pne 1 0 (by decide)), v31]
  have e6 := wclear_spec cap (pr 1) X ω5 v51 (by omega)
  refine ⟨_, WExec.cast cap (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4
    (WExec.seq e5 e6)))))) ?_ (le_refl _), ?_⟩
  · -- the exit state
    have sh4 : ω4.sh = ω.sh := by rw [hω4, hω3, hω2, hω1, hω0]; rfl
    have st4 : ω4.st = ω.st := by rw [hω4, hω3, hω2, hω1, hω0]; rfl
    have cl4 : ω4.cell = ω.cell := by rw [hω4, hω3, hω2, hω1, hω0]; rfl
    refine WState.eq ?_ ?_ ?_ ?_
    · funext i
      simp only [WState.setv_sh, WState.seth_sh, hω5]
      by_cases hi : i = sk x 113
      · subst hi; rw [Function.update_self, sh4, h113]; omega
      · rw [Function.update_of_ne hi, sh4, hsh i hi]
    · simp only [WState.setv_st, WState.seth_st, hω5, st4]
    · funext q
      simp only [WState.setv_val, WState.seth_val, hω5]
      by_cases hq : q ∈ scrR
      · rw [if_pos hq]
        by_cases e1q : q = pr 1
        · subst e1q; rw [Function.update_self]
        · rw [Function.update_of_ne e1q]
          by_cases e0q : q = pr 0
          · subst e0q; rw [Function.update_self]
          · rw [Function.update_of_ne e0q, hω4]
            show (ω3.setv (pr 0) _).val q = 0
            rw [wsetv_val_ne _ _ e0q]
            obtain ⟨k, hk⟩ : ∃ k : Fin 7, pr k = q := by
              rw [mem_scrR] at hq
              exact ⟨⟨q.val - 480, by omega⟩, Fin.ext (by show 480 + (q.val - 480) = q.val; omega)⟩
            subst hk
            refine v3k k ?_
            have k0 : k.val ≠ 0 := fun hk0 => e0q (by congr 1; exact Fin.ext hk0)
            have k1 : k.val ≠ 1 := fun hk1 => e1q (by congr 1; exact Fin.ext hk1)
            omega
      · rw [if_neg hq]
        have n1 : q ≠ pr 1 := fun e => hq (by rw [e]; exact (mem_scrR _).2 (by rw [pv]; simp))
        have n0 : q ≠ pr 0 := fun e => hq (by rw [e]; exact (mem_scrR _).2 (by rw [pv]; simp))
        rw [Function.update_of_ne n1, Function.update_of_ne n0, hω4]
        show (ω3.setv (pr 0) _).val q = _
        rw [wsetv_val_ne _ _ n0, hω3, wsetv_val_ne _ _ n0, hω2, wsetv_val_ne _ _ n1, hω1, wsetv_val_ne _ _ n1]
        show (if q ∈ scrR then 0 else ω.val q) = _
        rw [if_neg hq]
    · simp only [WState.setv_cell, WState.seth_cell, hω5, cl4]
  · -- the steps
    have hB1 : 1 ≤ B + Bh + w.length + K1 + D3 + 2 := by omega
    set S := B + Bh + w.length + K1 + D3 + 2 with hS
    have hsc : scrR.length = 7 := by simp [scrR]
    rw [hsc] at hc0
    have hXS : X ≤ S := by omega
    have hBS : Bh ≤ S := by omega
    have hc4' : c4 ≤ D3 * (60 * (Bh + 1) * (X + 1) + 1) := by
      have e : ω3.val (PR 1) = X := v31
      rw [e] at hc4; exact hc4
    have t1 : D3 * (60 * (Bh + 1) * (X + 1) + 1) ≤ S * (60 * (S + 1) * (S + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by
        have := Nat.mul_le_mul (Nat.mul_le_mul_left 60 (show Bh + 1 ≤ S + 1 by omega)) (show X + 1 ≤ S + 1 by omega)
        omega)
    have t2 : S * (60 * (S + 1) * (S + 1) + 1) ≤ 250 * S ^ 3 := by
      have : S + 1 ≤ 2 * S := by omega
      have h2 : (S + 1) * (S + 1) ≤ 4 * (S * S) := by nlinarith
      have e : S ^ 3 = S * (S * S) := by ring
      rw [e]
      nlinarith
    have t3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) S
    unfold rewCost
    rw [← hS]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
