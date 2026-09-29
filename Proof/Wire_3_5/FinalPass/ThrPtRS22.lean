import Proof.Wire_3_5.FinalPass.ThrPtRS21

/-! # S2 (THR per point), part 36: the evaluator's internal run (P3:2587-2630, 3170-3178)

`thrInt`: the setup, the loop over `g` (each `g` the primes loop, each prime the row), the cleanup.
**`thrInt_spec`**: from the internal entry `Init0`, given each row's contract `RowStepOK` (gain `F j p`), the run
ends with the accumulator `Σ_{j < |𝒢|} Σ_{p ∈ L} F j p`, every other register, every head and the cell as at
entry, the call's streams unchanged and the scratch blank. Paper quantity: `Σ_{g,p} R̂_{g,p}(c, u, v)` (with
`F j p = R̂` from `rowStep_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem cw_len {n : ℕ} (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    (Pop.cornerWord Ts c u v).length = 4 * Ts.length := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih => simp [Pop.cornerWord, List.length_flatMap] at ih ⊢; omega

/-- **The evaluator's internal program.** -/
noncomputable def thrInt : TProg := .seq setup (.seq gLoop cleanup)

variable (cap : ℕ)

theorem thrInt_spec (σ0 : WState 16 118) (a G τ M H : ℕ) (I : Init0 σ0 a G τ M) {n : ℕ}
    (Gs : List (NormalizedThresholdGate n)) (c u v : BitInput n)
    (hmeas : ∀ i < H, readTapeBit (σ0.st 3) (1 + 2 * i) = true) (hmz : readTapeBit (σ0.st 3) (1 + 2 * H) = false)
    (hGs : a ≠ 0 → σ0.st 3 = Corner.gatesW H Gs) (ha0 : a = 0 → Gs = []) (hGM : Gs.length = M)
    (hC : σ0.st 0 = frame (List.ofFn c)) (hU : σ0.st 1 = frame (List.ofFn u)) (hV : σ0.st 2 = frame (List.ofFn v))
    (hov : ∀ g ∈ Gs, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ H)
    (Lp : List ℕ) (hst8 : σ0.st 8 = PrimAsm.Data.unaryList Lp) (hpos : ∀ p ∈ Lp, 0 < p)
    (F C : ℕ → ℕ → ℕ) (hF : ∀ j p, F j p ≤ 1)
    (hrow : ∀ j < G, ∀ p ∈ Lp, RowStepOK cap (σ0.setv 117 H) M τ
      (Pop.cornerWord (Gs.map NormalizedThresholdGate.eval) c u v) j (F j p) (C j p) p)
    (hc1 : 2 * τ + 10 * M + 2 * H + 2 ≤ cap) (hcn : 2 * n ≤ cap)
    (hcK : M * (1 + (n + 1) * (2 * (2 * H + 1))) ≤ cap) (hcL : (PrimAsm.Data.unaryList Lp).length ≤ cap)
    (hcG : G * Lp.length ≤ cap) (hcG2 : G + 2 * H + 8 * M + τ + 1 ≤ cap) :
    ∃ τf : WState 16 118,
      WExec cap thrInt σ0 τf
        (setupCost τ M H (Corner.cwCost H n M) + 1 + (gLoopCost Lp C 0 G + 1 + cleanCost G τ M H)) ∧
      τf.val = Function.update σ0.val 0 (∑ j ∈ Finset.range G, (Lp.map (F j)).sum) ∧ τf.sh = σ0.sh ∧
      τf.cell = σ0.cell ∧ (∀ i : Fin 17, i.val < 10 → τf.st i = σ0.st i) ∧
      (∀ i : Fin 17, 10 ≤ i.val → ∀ b ∈ τf.st i, b = false) := by
  have z := I.zero
  have h117 : σ0.val 117 = 0 := z 117 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨X, hX⟩ : ∃ l, l = Pop.cornerWord (Gs.map NormalizedThresholdGate.eval) c u v := ⟨_, rfl⟩
  rw [← hX] at hrow
  have hXl : X.length = 4 * M := by rw [hX, cw_len, List.length_map, hGM]
  obtain ⟨P, N, hP, hN, e1⟩ := setup_spec cap σ0 a G τ M H Gs c u v I.sh I.v5 I.v8 I.v63 h117
    (fun q h1 h2 => z q (by omega) (by omega) (by omega) (by omega) (by omega)) hmeas hmz hGs ha0 hGM hC hU hV hov
    hc1 hcn hcK
  rw [← hX, init_w σ0 a G τ M I] at e1
  obtain ⟨ts, hts⟩ : ∃ s : TSt, s = { tInit G with
      dRem := τ, kS := M, pos := P, neg := N, x := frameP X ++ [false],
      z := List.replicate (2 * M + 1) false } := ⟨_, rfl⟩
  rw [← hts] at e1
  have hRs : RowReady ts M τ X := by rw [hts]; exact rowReady_setup G τ M P N X
  obtain ⟨R1, Z1, S1, P1, hRe, e2⟩ := gLoop_spec cap (σ0.setv 117 H) M τ X Lp F C hF hst8 hpos hcL G 0 ts
    (fun j _ hj p hp => hrow j (by omega) p hp) hRs (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
    (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; show 0 + G * Lp.length ≤ cap; omega) (by omega)
  obtain ⟨te, hte⟩ : ∃ s : TSt, s = { ts with
      rw := R1, z := Z1, ss := S1, rep := P1,
      acc := ts.acc + ∑ j ∈ Finset.range G, (Lp.map (F (0 + j))).sum, gi := 0 + G, gRem := 0 } := ⟨_, rfl⟩
  rw [← hte] at e2 hRe
  have e3 := cleanup_spec cap (σ0.setv 117 H) te M τ G H X hRe hXl (by rw [hte, hts]; exact hP)
    (by rw [hte, hts]; exact hN) (by rw [hte]; show 0 + G = G; omega) (by rw [hte]) (fun j => I.sh j) (by simp) hcG2
  have hb : (σ0.setv 117 H).setv 117 0 = σ0 := by
    rw [wsetv_setv]
    have h := wsetv_same σ0 117
    rwa [h117] at h
  rw [hb] at e3
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_⟩
  · clear e1 e2 e3
    subst hte hts
    have hv : ∀ x : ℕ, (({ tInit G with acc := x } : TSt).w σ0).val = Function.update σ0.val 0 x := by
      intro x
      rw [← tw_setv_acc, init_w σ0 a G τ M I]
      rfl
    simp only [Nat.zero_add]
    have hacc : (tInit G).acc + ∑ j ∈ Finset.range G, (Lp.map (F j)).sum = ∑ j ∈ Finset.range G, (Lp.map (F j)).sum :=
      Nat.zero_add _
    refine Eq.trans (?_ : _ = (({ tInit G with
      acc := (tInit G).acc + ∑ j ∈ Finset.range G, (Lp.map (F j)).sum } : TSt).w σ0).val) ?_
    · rfl
    · rw [hv, hacc]
  · clear e1 e2 e3
    subst hte hts
    have hs : (tInit G).w σ0 = σ0 := init_w σ0 a G τ M I
    rw [← congrArg WState.sh hs]
    rfl
  · exact I.cell.symm
  · intro i hi
    exact tw_st_other σ0 _ i hi
  · intro i hi b hb
    clear e1 e2 e3
    by_cases h10 : i.val = 10
    · obtain rfl : i = 10 := Fin.ext h10
      rw [tw_st_pos] at hb; exact (List.mem_replicate.mp hb).2
    by_cases h11 : i.val = 11
    · obtain rfl : i = 11 := Fin.ext h11
      rw [tw_st_neg] at hb; exact (List.mem_replicate.mp hb).2
    by_cases h12 : i.val = 12
    · obtain rfl : i = 12 := Fin.ext h12
      rw [tw_st_x] at hb; exact (List.mem_replicate.mp hb).2
    by_cases h13 : i.val = 13
    · obtain rfl : i = 13 := Fin.ext h13
      rw [tw_st_rw] at hb; exact hRe.rw b hb
    by_cases h14 : i.val = 14
    · obtain rfl : i = 14 := Fin.ext h14
      rw [tw_st_z] at hb; exact (List.mem_replicate.mp hb).2
    by_cases h15 : i.val = 15
    · obtain rfl : i = 15 := Fin.ext h15
      rw [tw_st_ss] at hb; exact hRe.ss b hb
    by_cases h16 : i.val = 16
    · obtain rfl : i = 16 := Fin.ext h16
      rw [tw_st_rep] at hb; exact hRe.rep b hb
    have := i.isLt
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
