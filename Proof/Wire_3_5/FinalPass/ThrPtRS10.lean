import Proof.Wire_3_5.FinalPass.ThrPtRS9

/-! # S2 (THR per point), part 24: one row `(g, p)`, the run (P3:2587-2630)

**`rowStep_spec`**: from a `RowReady` state at `g`'s index and the prime `p`, `rowStep` adds
`[thrTermOk p r₀ X as ws tp tm]` to the accumulator (`r₀`, `as`, `ws`: row `(g, p)`'s residue, reduced coefficients,
digit weights; `tp`, `tm`: the digits' reports) and ends `RowReady` again. Paper quantity: `R̂_{g,p}(c, u, v)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Pop

theorem rowStep_spec (cap : ℕ) (P : Shared.StarParams) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (alg : RepairRepresentation.DecompositionAlgorithm)
    (den : ℕ) (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
    (σB : WState 16 118) (τ M : ℕ) (hB : BaseOK σB a' τ M)
    (hpay : ∀ i : Fin 4, σB.st (payS i) = if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else [])
    (hτ : Primitive.thrDigits P Cs alg den = τ)
    (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (hT5 : σB.st 9 = ListEval.levelWord DM DJ DW row)
    (hrows : ∀ j ≤ DJ, (row j).length = M)
    (r0 : ℕ) (as ws : List ℕ) (er0 : Term.thrR0 P Cs alg g pr.val = r0) (eas : Term.thrCoeffs P Cs alg g pr.val = as)
    (ews : Term.thrWeights P Cs alg den pr.val = ws) (hMl : as.length = M) (hr0 : r0 < pr.val)
    (A0 : ℕ) (hA : ∀ x ∈ as, x ≤ A0) (hW : ∀ x ∈ ws, x ≤ A0) (X : List Bool) (hXl : X.length = 4 * M)
    (t : TSt) (hR : RowReady t M τ X) (hgi : t.gi = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)) (hp : t.p = pr.val)
    (hcW : DigsBody.rowWImpl.need (Digs.digsN P Cs [] alg den pr.val) ≤ cap)
    (hc1 : popCap pr.val r0 M A0 τ ≤ cap) (hc2 : ListEval.capOf DM DJ DW row M ≤ cap)
    (hc3 : 2 * τ * (DM + 1) + 2 * (DM + 1) + τ ≤ cap)
    (hc4 : Term.capT pr.val r0 M as ws (tRepL DM DJ DW row as X true τ) (tRepL DM DJ DW row as X false τ) ≤ cap)
    (hc5 : t.acc + 1 ≤ cap) (hc6 : (Term.rowWord pr.val r0 as ws).length + M + τ ≤ cap) :
    ∃ (R1 Z1 S1 P1 : List Bool),
      RowReady { t with
        rw := R1, z := Z1, ss := S1, rep := P1,
        acc := t.acc + (Term.thrTermOk pr.val r0 X as ws (tRepL DM DJ DW row as X true τ)
          (tRepL DM DJ DW row as X false τ)).toNat } M τ X ∧
      WExec cap rowStep (t.w σB) ({ t with
        rw := R1, z := Z1, ss := S1, rep := P1,
        acc := t.acc + (Term.thrTermOk pr.val r0 X as ws (tRepL DM DJ DW row as X true τ)
          (tRepL DM DJ DW row as X false τ)).toNat }.w σB)
        (rowCost (DigsBody.rowWImpl.bound (Digs.digsN P Cs [] alg den pr.val)) pr.val r0 M A0 τ DM
          (ListEval.capOf DM DJ DW row M) as ws (tRepL DM DJ DW row as X true τ) (tRepL DM DJ DW row as X false τ)) := by
  obtain ⟨hrw0, hhRw, hrwH, ⟨zr0, hz, hzr⟩, hss, hrep, hhRep, hrH, hd, hdRem, hkS, hrS, hr82, hw92, hx⟩ := hR
  have hWl : ws.length = τ := by rw [← ews, ← hτ, Term.thrWeights, List.length_ofFn]
  obtain ⟨tp, etp⟩ : ∃ l, l = tRepL DM DJ DW row as X true τ := ⟨_, rfl⟩
  obtain ⟨tm, etm⟩ : ∃ l, l = tRepL DM DJ DW row as X false τ := ⟨_, rfl⟩
  rw [← etp, ← etm] at hc4 ⊢
  obtain ⟨v, ev⟩ : ∃ b : Bool, b = Term.thrTermOk pr.val r0 X as ws tp tm := ⟨_, rfl⟩
  rw [← ev]
  have hv : v.toNat ≤ 1 := Bool.toNat_le v
  obtain ⟨W, eW⟩ : ∃ l, l = Term.rowWord pr.val r0 as ws := ⟨_, rfl⟩
  have htpl : tp.length = τ := by rw [etp, tRepL_length]
  have html : tm.length = τ := by rw [etm, tRepL_length]
  have hRWl : (Term.repWord tp tm).length ≤ 2 * τ * (DM + 1) := by
    rw [etp, etm]; exact repWordL_length DM DJ DW row as X τ
  have hpadW : pad W t.rw.length = Term.rowWord pr.val r0 as ws ++ List.replicate (t.rw.length - W.length) false := by
    subst eW; rfl
  -- 1: the row's word
  have e1 := rowWL_spec cap P ha' Cs alg den g pr t.rw.length (t.w σB)
    (fun i => by rw [tw_st_other σB t (payS i) (payS_lt i)]; exact hpay i)
    (fun i => by rw [tw_sh_other σB t (payS i) (payS_sh8 i) (payS_sh13 i) (payS_sh16 i)]; exact hB.sh _)
    (by rw [tw_st_rw]; exact eq_rep_false _ hrw0) (by rw [tw_sh_hRw, hhRw])
    (by rw [tw_val_low σB t 5 (by decide) (by decide) (by decide) (by decide)]; exact hB.vA)
    (by rw [tw_val_gi, hgi]) (by rw [tw_val_p, hp])
    (by rw [tw_val_low σB t 8 (by decide) (by decide) (by decide) (by decide), hB.vT, hτ])
    (by rw [tw_val_low σB t 9 (by decide) (by decide) (by decide) (by decide)]; exact hB.vO)
    (fun j hj => by
      have hj48 : j.val < 48 := j.isLt
      rw [tw_val_low σB t (rowR j) (by rw [rowR_val]; omega) (by rw [rowR_val]; omega) (by rw [rowR_val]; omega)
        (by rw [rowR_val]; omega)]
      exact hB.rowZ _ (by rw [rowR_val]; omega) (by rw [rowR_val]; omega)) hcW
  rw [tw_sets_rw, er0, eas, ews, ← eW] at e1
  -- 2: the digits' reports
  have hnil : Term.repWord (tRepL DM DJ DW row as X true 0) (tRepL DM DJ DW row as X false 0) = [] := by
    simp [tRepL, Term.repWord]
  obtain ⟨zr1, kS', Bf', hzr1, hBf', e2⟩ := digLoop_spec cap σB a' τ M hB DM DJ DW row hT5 pr.val r0 A0 as X
    (Term.digWord ws ++ [false] ++ List.replicate (t.rw.length - W.length) false) [false] hA hMl (by rw [hXl, hMl])
    hrows (by rw [hMl]; exact hc1) hc2 (by omega) (by omega) τ 0 { t with rw := pad W t.rw.length } zr0 t.rep
    t.ss.length (Nat.zero_add τ) hdRem hd
    (by show pad W t.rw.length = _; rw [hpadW, eW]; simp [Term.rowWord, List.append_assoc])
    hx hz (by rw [hzr, hMl]) (eq_rep_false _ hss) (by simp only [hnil, List.nil_append]) hrep hhRw
    (by rw [hnil]; exact hhRep) (by rw [hnil]; exact hrH) hr82
  rw [← etp, ← etm] at e2
  obtain ⟨t2, ht2⟩ : ∃ s : TSt, s = { { t with rw := pad W t.rw.length } with
      z := zr1 ++ [false], ss := List.replicate kS' false, rep := Term.repWord tp tm ++ Bf',
      hRep := (Term.repWord tp tm).length, rH := (Term.repWord tp tm).length, d := τ, dRem := 0 } := ⟨_, rfl⟩
  rw [← ht2] at e2
  -- 3: the digit counter restored
  have e3 := dRestore_spec cap σB t2 τ (by subst ht2; rfl) (by subst ht2; rfl) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ s : TSt, s = { t2 with d := 0, dRem := τ } := ⟨_, rfl⟩
  rw [← ht3] at e3
  -- 4: the reports rewound
  have h3r : t3.rH = (Term.repWord tp tm).length := by subst ht3 ht2; rfl
  have e4 := rewRep_spec cap σB t3 (by subst ht3 ht2; rfl) (by rw [h3r]; omega)
  obtain ⟨t4, ht4⟩ : ∃ s : TSt, s = { t3 with rH := 0, hRep := 0 } := ⟨_, rfl⟩
  rw [← ht4] at e4
  -- 5: stage 8
  have e5 := thr8T_spec cap σB a' τ M hB X as ws tp tm M pr.val r0 [] (List.replicate (t.rw.length - W.length) false)
    Bf' hXl hMl (by rw [hWl, htpl]) (by rw [hWl, html]) hr0 t4 (by subst ht4 ht3 ht2; exact hx)
    (by subst ht4 ht3 ht2; exact hpadW) (by subst ht4 ht3 ht2; rfl) (by subst ht4 ht3 ht2; exact hhRw)
    (by subst ht4; rfl) (by subst ht4 ht3 ht2; exact hw92) hc4
  rw [← ev] at e5
  obtain ⟨t5, ht5⟩ : ∃ s : TSt, s = { t4 with w92 := v.toNat } := ⟨_, rfl⟩
  rw [← ht5] at e5
  -- 6: the factor into the accumulator
  have h5w : t5.w92 = v.toNat := by subst ht5; rfl
  have h5a : t5.acc = t.acc := by subst ht5 ht4 ht3 ht2; rfl
  have e6 := accAdd_spec cap σB t5 (by rw [h5w]; omega) (by rw [h5w, h5a]; omega)
  obtain ⟨t6, ht6⟩ : ∃ s : TSt, s = { t5 with w92 := 0, acc := t5.acc + t5.w92 } := ⟨_, rfl⟩
  rw [← ht6] at e6
  -- 7: the reports erased
  have e7 := erRepAll_spec cap σB DM tp tm Bf' t6 (by rw [htpl, html])
    (by rw [etp]; exact tRepL_le DM DJ DW row as X true τ) (by rw [etm]; exact tRepL_le DM DJ DW row as X false τ)
    (by subst ht6 ht5 ht4 ht3 ht2; rfl) (by subst ht6 ht5 ht4; rfl) (by subst ht6 ht5 ht4; rfl)
    (by subst ht6 ht5 ht4 ht3; exact htpl.symm) (by subst ht6 ht5 ht4 ht3; rfl) (by omega)
  obtain ⟨t7, ht7⟩ : ∃ s : TSt, s = { t6 with rep := List.replicate (Term.repWord tp tm).length false ++ Bf' } :=
    ⟨_, rfl⟩
  rw [← ht7] at e7
  -- 8: the row's word erased
  have e8 := eraseRow_spec cap σB A0 pr.val r0 as ws (List.replicate (t.rw.length - W.length) false) t7 hA hW
    (by subst ht7 ht6 ht5 ht4 ht3 ht2; exact hpadW) (by subst ht7 ht6 ht5 ht4 ht3 ht2; exact hhRw)
    (by subst ht7 ht6 ht5 ht4 ht3 ht2; exact hrwH) (by subst ht7 ht6 ht5 ht4 ht3 ht2; exact hkS.trans hMl.symm)
    (by subst ht7 ht6 ht5 ht4 ht3 ht2; exact hrS) (by subst ht7 ht6 ht5 ht4 ht3; exact hWl.symm)
    (by subst ht7 ht6 ht5 ht4 ht3; rfl) (by rw [hMl, hWl]; omega)
  obtain ⟨t8, ht8⟩ : ∃ s : TSt, s = { t7 with
      rw := List.replicate (Term.rowWord pr.val r0 as ws).length false ++
        List.replicate (t.rw.length - W.length) false } := ⟨_, rfl⟩
  rw [← ht8] at e8
  refine ⟨List.replicate (Term.rowWord pr.val r0 as ws).length false ++ List.replicate (t.rw.length - W.length) false,
    zr1 ++ [false], List.replicate kS' false, List.replicate (Term.repWord tp tm).length false ++ Bf',
    ⟨fun b hb => ?_, hhRw, hrwH, ⟨zr1, rfl, by rw [hzr1, hMl]⟩, fun b hb => (List.mem_replicate.mp hb).2,
      fun b hb => ?_, hhRep, hrH, hd, hdRem, hkS, hrS, hr82, hw92, hx⟩, ?_⟩
  · rcases List.mem_append.mp hb with h | h
    · exact (List.mem_replicate.mp h).2
    · exact (List.mem_replicate.mp h).2
  · rcases List.mem_append.mp hb with h | h
    · exact (List.mem_replicate.mp h).2
    · exact hBf' b h
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) (tw_eq ?_) ?_
  · clear e1 e2 e3 e4 e5 e6 e7 e8
    subst ht8 ht7 ht6 ht5 ht4 ht3 ht2
    obtain ⟨⟩ := t
    simp only at hhRep hrH hd hdRem hw92 ⊢
    simp only [TSt.mk.injEq, true_and, and_true]
    repeat' constructor
    all_goals omega
  · rw [h3r, h5w, htpl]
    unfold rowCost
    rw [hMl, hWl]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
