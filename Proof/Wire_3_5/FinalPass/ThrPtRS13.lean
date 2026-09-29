import Proof.Wire_3_5.FinalPass.ThrPtRS12

/-! # S2 (THR per point), part 27: the loop over `g` (P3:2587-2630)

`gLoop`: while `GREM ≠ 0` — `GREM` down, the primes loop at `g`'s index `gi`, stream `8` rewound, `gi` up.
**`gLoop_spec`**: from `gi = i` with `GREM = m`, the accumulator gains `Σ_{j < m} Σ_{p ∈ L} F (i + j) p` and the state
stays `RowReady`. Paper quantity: `Σ_{g,p} R̂_{g,p}(c, u, v)` (the per-point sum `rsumThr`, in `g`'s index order). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem sum_le_len (f : ℕ → ℕ) (hf : ∀ p, f p ≤ 1) : ∀ L : List ℕ, (L.map f).sum ≤ L.length
  | [] => le_rfl
  | q :: L => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hf q
    have h2 := sum_le_len f hf L
    omega

theorem sum_shift (G : ℕ → ℕ) (i m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), G (i + j) = ∑ j ∈ Finset.range m, G (i + 1 + j) + G i := by
  rw [Finset.sum_range_succ', Nat.add_zero]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by congr 1; omega)

variable (cap : ℕ) (σB : WState 16 118)

theorem rewPr_spec (t : TSt) (h : t.prH = t.hPr) (hc : t.prH ≤ cap) :
    WExec cap (WM.rewind 8 110) (t.w σB) ({ t with prH := 0, hPr := 0 }.w σB) (5 * t.prH + 1) := by
  have e := wrewind_spec cap (8 : Fin 17) (110 : Fin 118) t.prH (t.w σB) (by rw [tw_val_prH])
    (by rw [tw_val_prH]; exact hc)
  rw [tw_setv_prH, tw_sh_hPr, tw_seth_hPr] at e
  refine WExec.cast cap e (tw_eq ?_) le_rfl
  simp only [h, Nat.sub_self]

theorem incGi_spec (t : TSt) (hc : t.gi < cap) :
    WExec cap (.inc 6) (t.w σB) ({ t with gi := t.gi + 1 }.w σB) 3 := by
  have e := WExec.inc (cap := cap) (6 : Fin 118) (t.w σB) (by rw [tw_val_gi]; exact hc)
  rwa [tw_val_gi, tw_setv_gi] at e

theorem decGRem_spec (t : TSt) (hc : t.gRem ≤ cap) :
    WExec cap (.dec 109) (t.w σB) ({ t with gRem := t.gRem - 1 }.w σB) 1 := by
  have e := WExec.dec (cap := cap) (109 : Fin 118) (t.w σB) (by rw [tw_val_gRem]; exact hc)
  rwa [tw_val_gRem, tw_setv_gRem] at e

/-- **The loop over `g`.** -/
noncomputable def gLoop : TProg := .whr 109 (.seq (.dec 109) (.seq primeLoop (.seq (WM.rewind 8 110) (.inc 6))))

/-- The loop's step bound. -/
def gLoopCost (Lp : List ℕ) (C : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | i, m + 1 => 1 + 1 + (primeLoopCost (C i) Lp + 1 + ((5 * (PrimAsm.Data.unaryList Lp).length + 1) + 1 + 3)) + 2 +
      gLoopCost Lp C (i + 1) m

theorem gLoop_spec (M τ : ℕ) (X : List Bool) (Lp : List ℕ) (F C : ℕ → ℕ → ℕ) (hF : ∀ j p, F j p ≤ 1)
    (hst : σB.st 8 = PrimAsm.Data.unaryList Lp) (hpos : ∀ p ∈ Lp, 0 < p)
    (hUc : (PrimAsm.Data.unaryList Lp).length ≤ cap) :
    ∀ (m i : ℕ) (t : TSt), (∀ j, i ≤ j → j < i + m → ∀ p ∈ Lp, RowStepOK cap σB M τ X j (F j p) (C j p) p) →
      RowReady t M τ X → t.gRem = m → t.gi = i → t.p = 0 → t.hPr = 0 → t.prH = 0 →
      t.acc + m * Lp.length ≤ cap → i + m ≤ cap →
      ∃ R1 Z1 S1 P1 : List Bool,
        RowReady { t with
          rw := R1, z := Z1, ss := S1, rep := P1,
          acc := t.acc + ∑ j ∈ Finset.range m, (Lp.map (F (i + j))).sum, gi := i + m, gRem := 0 } M τ X ∧
        WExec cap gLoop (t.w σB) ({ t with
          rw := R1, z := Z1, ss := S1, rep := P1,
          acc := t.acc + ∑ j ∈ Finset.range m, (Lp.map (F (i + j))).sum, gi := i + m, gRem := 0 }.w σB)
          (gLoopCost Lp C i m)
  | 0, i, t, _, hR, hm, hi, _, _, _, _, _ => by
    refine ⟨t.rw, t.z, t.ss, t.rep, RowReady.cast hR rfl, ?_⟩
    refine WExec.cast cap (WExec.whrF (show (t.w σB).val 109 = 0 by rw [tw_val_gRem, hm])) (tw_eq ?_) le_rfl
    obtain ⟨⟩ := t
    simp only at hm hi ⊢
    simp [hm, hi]
  | m + 1, i, t, hstep, hR, hm, hi, hp, hh, hH, hacc, hic => by
    rw [Nat.add_mul, Nat.one_mul] at hacc
    have hs1 := sum_le_len (F i) (hF i) Lp
    have e0 := decGRem_spec cap σB t (by omega)
    obtain ⟨t0, ht0⟩ : ∃ s : TSt, s = { t with gRem := t.gRem - 1 } := ⟨_, rfl⟩
    rw [← ht0] at e0
    obtain ⟨R1, Z1, S1, P1, hR1, e1⟩ := primeLoop_spec cap σB M τ X i (F i) (C i) (hF i) Lp [] t0
      (by rw [hst, List.nil_append]) hpos (hstep i le_rfl (by omega)) (by subst ht0; exact RowReady.cast hR rfl)
      (by subst ht0; exact hi) (by subst ht0; exact hp) (by subst ht0; exact hh) (by subst ht0; exact hH)
      (by subst ht0; show t.acc + Lp.length ≤ cap; omega) (by simpa using hUc)
    obtain ⟨t1, ht1⟩ : ∃ s : TSt, s = { t0 with
        rw := R1, z := Z1, ss := S1, rep := P1, acc := t0.acc + (Lp.map (F i)).sum,
        hPr := ([] : List Bool).length + (PrimAsm.Data.unaryList Lp).length,
        prH := ([] : List Bool).length + (PrimAsm.Data.unaryList Lp).length } := ⟨_, rfl⟩
    rw [← ht1] at e1 hR1
    have h1p : t1.prH = (PrimAsm.Data.unaryList Lp).length := by subst ht1; simp
    have e2 := rewPr_spec cap σB t1 (by subst ht1; rfl) (by rw [h1p]; exact hUc)
    obtain ⟨t2, ht2⟩ : ∃ s : TSt, s = { t1 with prH := 0, hPr := 0 } := ⟨_, rfl⟩
    rw [← ht2] at e2
    have e3 := incGi_spec cap σB t2 (by subst ht2 ht1 ht0; show t.gi < cap; omega)
    obtain ⟨t3, ht3⟩ : ∃ s : TSt, s = { t2 with gi := t2.gi + 1 } := ⟨_, rfl⟩
    rw [← ht3] at e3
    obtain ⟨R1', Z1', S1', P1', hR3, e4⟩ := gLoop_spec M τ X Lp F C hF hst hpos hUc m (i + 1) t3
      (fun j h1 h2 => hstep j (by omega) (by omega)) (by subst ht3 ht2; exact RowReady.cast hR1 rfl)
      (by subst ht3 ht2 ht1 ht0; show t.gRem - 1 = m; omega) (by subst ht3 ht2 ht1 ht0; show t.gi + 1 = i + 1; omega)
      (by subst ht3 ht2 ht1 ht0; exact hp) (by subst ht3 ht2; rfl) (by subst ht3 ht2; rfl)
      (by subst ht3 ht2 ht1 ht0; show t.acc + (Lp.map (F i)).sum + m * Lp.length ≤ cap; omega) (by omega)
    refine ⟨R1', Z1', S1', P1', by subst ht3 ht2 ht1 ht0; exact RowReady.cast hR3 rfl, ?_⟩
    refine WExec.cast cap (WExec.whrT (by rw [tw_val_gRem, hm]; omega) (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)))
      e4) (tw_eq ?_) (by rw [h1p]; simp only [gLoopCost]; omega)
    clear e0 e1 e2 e3 e4 hR1 hR3
    have hs := sum_shift (fun j => (Lp.map (F j)).sum) i m
    subst ht3 ht2 ht1 ht0
    obtain ⟨⟩ := t
    simp only at hm hi hh hH ⊢
    simp only [TSt.mk.injEq, true_and, and_true, List.length_nil, Nat.zero_add, hs]
    repeat' constructor
    all_goals omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
