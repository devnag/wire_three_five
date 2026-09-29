import Proof.Wire_3_5.FinalPass.SampPad
import Proof.Wire_3_5.FinalPass.SymBF
import Proof.Wire_3_5.FinalPass.SymCost5
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7

/-! # The SYM free numbers' builder (v7): `SymFreeOk7` at every gate, fixed before `F`

The C4.K contract v7 (`C4SymKB7.SymFreeOk7 l F wa K3 D3 Kp Dp`): the deliverable. For each endpoint exponent
`f_e`, the constants `SymC` (`symCof`: `d_T = 2e_N`, `d_Q = c_S + 401`, `d_H = coef·4^{deg} + 2`, `e_H = 26deg + 1`,
`d_D = symDD` (the linear degree bound, `SymDeg`), `d_P`, `e_P`, `d_C = symDC`, `d_A = symDAc`, `d_R = 0`), the load
floor `C_{D,s}` (`symCDs`: the printer floor `occCD`, the capacity floor `16·symC1` and the child's-steps floor
`symHC`, all fixed before `F`, P3:3094-3107), the C3 load constants `K3 = c3K2`, `D3 = e_H + e_P` and the pad
constants `Kp = 4^{d_A} + 1`, `Dp = d_A + d_R` are fixed; at every gate `F` with `F.filterErrDeg = f_e`,
`C_{D,s} ≤ C_D` and `1 ≤ c_ψ` the free program `freeProg2 (symK2 c)` with `dF = symDF c`, `K = symKn c` (the
capacity) and `K_ch = symKch` (`2^{n−k+d_A L−4}`) meets every field: the program's bounds (FreeGen9), the pad
(`pad2`), the C3 load (`c3_sym2`), `side` at every SYM call with rows (the SYM batch) and `side_pad` at every
degenerate call (the padded batch).

The floors recorded: `occCD ≤ C_D` (the printer's budget), `16·symC1(e_N, e_Q, Z) ≤ C_D` (the
enumeration's capacity), `symHC ≤ C_D` (one child's steps under the pad); `symDC ≤ d_C`, `symDAc ≤ d_A`,
`symDD ≤ d_D` are the constants' own choices. All depend on `l` and `f_e` only (and on `wa` for `d_A`).

* `algL`, `symCof`, `symCDs`, `small_of`, **`symFreeOk`**.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the SYM stage and their bounds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairRepresentation

/-- The gate's decomposition algorithm (the literals' `DecompositionSource`, fixed before `F`). -/
noncomputable def algL (l : Literals) : DecompositionAlgorithm := Classical.choice l.eightSources.decomposition

/-- **The SYM constants** at the endpoint exponent `fe` (fixed before `F`). -/
noncomputable def symCof (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) : SymC where
  dT := 2 * eN l fe
  dC := symDC (2 * eN l fe) fe
  dQ := cS l fe + 401
  dH := (algL l).coefficient * 4 ^ (algL l).degree + 2
  eH := 26 * (algL l).degree + 1
  dP := ((algL l).coefficient * 4 ^ (algL l).degree + 2) * (cS l fe + 401) * symDD l fe *
      2 ^ (50 + CallIndexR.capZR l) + 2 * (24 + 8 * eQ l fe + (cS l fe + 401))
  eP := 26 * (algL l).degree + 1 + 49 + CallIndexR.capZR l
  dA := symDAc (26 * (algL l).degree + 1) (26 * (algL l).degree + 1 + 49 + CallIndexR.capZR l)
    ((algL l).coefficient * 4 ^ (algL l).degree + 2)
    (((algL l).coefficient * 4 ^ (algL l).degree + 2) * (cS l fe + 401) * symDD l fe *
      2 ^ (50 + CallIndexR.capZR l) + 2 * (24 + 8 * eQ l fe + (cS l fe + 401)))
    (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa)
  dR := 0
  dD := symDD l fe

/-- **The load floor** `C_{D,s}` (fixed before `F`). -/
noncomputable def symCDs (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) : ℕ :=
  occCD (algL l) (symCof l wa fe) (A1 l fe 63) + 16 * symC1 (eN l fe) (eQ l fe) (CallIndexR.capZR l) +
    symHC (symCof l wa fe).dC (cDa (algL l)) (symCof l wa fe).dQ (symCof l wa fe).dD
      (coOf (A1 l fe 63) (symCof l wa fe).dQ (cDa (algL l)) (symCof l wa fe).dD) (eN l fe) (eQ l fe)

/-- The small inputs are small for the free program (the four fields it reads). -/
theorem small_of {Ds : ℕ} {x : FreeIn} (h : PrimT.C4SymW.FreeSmall Ds x) : FreeSmall Ds x :=
  ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- **The SYM free numbers at every gate** (v7). -/
noncomputable def symFreeOk (l : Literals) (wa : WilliamsAlgorithm) : ∀ fe : ℕ, Σ CDs K3 D3 Kp Dp : ℕ,
    ∀ F : GateFree l, F.filterErrDeg = fe → CDs ≤ F.CD → 1 ≤ F.E.cpsi → PrimT.C4SymW.SymFreeOk7 l F wa K3 D3 Kp Dp :=
  fun fe => ⟨symCDs l wa fe, c3K2 (symCof l wa fe), (symCof l wa fe).eH + (symCof l wa fe).eP,
    4 ^ (symCof l wa fe).dA + 1, (symCof l wa fe).dA + (symCof l wa fe).dR, fun F hfe hCD hcpsi =>
    { Fp := freeProg2 (symK2 (symCof l wa fe))
      dF := symDF (symCof l wa fe)
      K := symKn (symCof l wa fe)
      Kch := symKch l F (symCof l wa fe)
      E3 := F.E
      ok_le := fun Ds => by
        obtain ⟨Ko, hKo⟩ := ok2_le (symK2 (symCof l wa fe)) Ds
        exact ⟨Ko, fun cap x hx hc => hKo cap x (small_of hx) hc⟩
      cost_le := cost2_le _
      val_le := fun Ds => by
        obtain ⟨Kv, hKv⟩ := val2_le (symK2 (symCof l wa fe)) Ds
        exact ⟨Kv, fun x j hx hj => hKv x j (small_of hx) hj⟩
      rho_le := rho2_le _
      pad_le := by
        intro kclk coef A a ha n a' ha' Cs carriers translation _ hs
        have h := pad2 (symK2 (symCof l wa fe)) (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)
        have hk : (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs).kh +
            (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs).kh =
              ((gate0 l F).budget kclk coef A a ha).kOf n := by
          rw [← kh_two l F kclk coef A a ha hs]
          show SeedFix.callKh _ + SeedFix.callKh _ = _
          ring
        rw [hk] at h
        exact h
      c3_le := c3_sym2 l F (symCof l wa fe)
      side := by
        subst hfe
        intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs h1
        have hc : HpreC l F.filterErrDeg (gate0 l F).alg (symCof l wa F.filterErrDeg) :=
          ⟨by show 1 ≤ cS l F.filterErrDeg + 401; omega, le_refl _, le_refl _,
            by show _ ≤ _ + _; exact Nat.le_add_right _ _, le_refl _,
            by show _ ≤ _ + _; exact Nat.le_add_left _ _, by show 1 ≤ _ + 1 + 49 + _; omega⟩
        have hdT : 2 * eN l F.filterErrDeg ≤ (symCof l wa F.filterErrDeg).dT := le_refl _
        have hdC : symDC (symCof l wa F.filterErrDeg).dT F.filterErrDeg ≤ (symCof l wa F.filterErrDeg).dC := le_refl _
        have hdA : symDAc (symCof l wa F.filterErrDeg).eH (symCof l wa F.filterErrDeg).eP (symCof l wa F.filterErrDeg).dH
            (symCof l wa F.filterErrDeg).dP (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤
            (symCof l wa F.filterErrDeg).dA := le_refl _
        have hdQr : cS l F.filterErrDeg + 401 ≤ (symCof l wa F.filterErrDeg).dQ := le_refl _
        have hdH1 : 1 ≤ (symCof l wa F.filterErrDeg).dH := by show 1 ≤ _ + 2; omega
        have eCD : symCDs l wa F.filterErrDeg = occCD (gate0 l F).alg (symCof l wa F.filterErrDeg) (A1 l F.filterErrDeg 63) +
            16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) +
            symHC (symCof l wa F.filterErrDeg).dC (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dQ
              (symCof l wa F.filterErrDeg).dD (coOf (A1 l F.filterErrDeg 63) (symCof l wa F.filterErrDeg).dQ
                (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dD) (eN l F.filterErrDeg) (eQ l F.filterErrDeg) := rfl
        rw [eCD] at hCD
        have hCDo : occCD (gate0 l F).alg (symCof l wa F.filterErrDeg) (A1 l F.filterErrDeg 63) ≤ F.CD := by omega
        have hCDq : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD := by omega
        have hCDh : symHC (symCof l wa F.filterErrDeg).dC (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dQ
            (symCof l wa F.filterErrDeg).dD (coOf (A1 l F.filterErrDeg 63) (symCof l wa F.filterErrDeg).dQ
              (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dD) (eN l F.filterErrDeg) (eQ l F.filterErrDeg) ≤ F.CD := by
          omega
        have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
        have hDgF : symDg l F kclk coef A a ha Cs carriers ≤
            symDF (symCof l wa F.filterErrDeg) (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) :=
          symDg_lin l F kclk coef A a ha ha' Cs carriers translation hcall hs
        refine ⟨symHok l F (symCof l wa F.filterErrDeg) hdT hCDq hcpsi hdC kclk coef A a ha ha' Cs carriers translation
            hcall hs,
          fun p b _ => hpre_sym l F (symCof l wa F.filterErrDeg) hc 63 _ _ hCDo hcpsi kclk coef A a ha ha' Cs carriers
            translation hcall hs _ (by omega) _ _ (symBatchFacts l F kclk coef A a ha Cs carriers translation hs)
            (symT_le l F kclk coef A a ha ha' Cs carriers translation hcall)
            (sym_hmf l F (symCof l wa F.filterErrDeg) kclk coef A a ha Cs carriers hs h1) hDgF (p ++ [b]),
          hQp_sym l F (symCof l wa F.filterErrDeg) (by have := hc.dP2; omega) hc.eP2 kclk coef A a ha ha' Cs carriers
            translation hcall hs,
          symHcost_of l F (symCof l wa F.filterErrDeg) wa 63 hc hCDo hCDq hCDh hcpsi hdC hdA kclk coef A a ha ha' Cs
            carriers translation hcall hs _ _ _ _ _ _ (by omega) (BShape.sym_coef_pm1 _ hs Cs carriers)
            (symBsz_le l F kclk coef A a ha ha' Cs carriers translation hcall hs)
            (symDg_le l F kclk coef A a ha ha' Cs carriers translation hcall hs)
            (symBatchFacts l F kclk coef A a ha Cs carriers translation hs)
            (symT_le l F kclk coef A a ha ha' Cs carriers translation hcall)
            (sym_hmf l F (symCof l wa F.filterErrDeg) kclk coef A a ha Cs carriers hs h1) hDgF,
          hrange_sym l F (symCof l wa F.filterErrDeg) hdQr kclk coef A a ha ha' Cs carriers translation hcall hs,
          ?_,
          (fits_sym l F (symCof l wa F.filterErrDeg) hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs
            ((freeProg2 (symK2 (symCof l wa F.filterErrDeg))).val
              (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0).1,
          one_le_h_sym (symCof l wa F.filterErrDeg) hdH1 _⟩
        exact symHR l F (symCof l wa F.filterErrDeg) wa 63 hCDh hcpsi hdA kclk coef A a ha ha' Cs carriers translation
          hcall hs
      side_pad := by
        subst hfe
        intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs h0
        have hc : HpreC l F.filterErrDeg (gate0 l F).alg (symCof l wa F.filterErrDeg) :=
          ⟨by show 1 ≤ cS l F.filterErrDeg + 401; omega, le_refl _, le_refl _,
            by show _ ≤ _ + _; exact Nat.le_add_right _ _, le_refl _,
            by show _ ≤ _ + _; exact Nat.le_add_left _ _, by show 1 ≤ _ + 1 + 49 + _; omega⟩
        have hdT : 2 * eN l F.filterErrDeg ≤ (symCof l wa F.filterErrDeg).dT := le_refl _
        have hdC : symDC (symCof l wa F.filterErrDeg).dT F.filterErrDeg ≤ (symCof l wa F.filterErrDeg).dC := le_refl _
        have hdA : symDAc (symCof l wa F.filterErrDeg).eH (symCof l wa F.filterErrDeg).eP (symCof l wa F.filterErrDeg).dH
            (symCof l wa F.filterErrDeg).dP (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤
            (symCof l wa F.filterErrDeg).dA := le_refl _
        have hdQr : cS l F.filterErrDeg + 401 ≤ (symCof l wa F.filterErrDeg).dQ := le_refl _
        have hdH1 : 1 ≤ (symCof l wa F.filterErrDeg).dH := by show 1 ≤ _ + 2; omega
        have eCD : symCDs l wa F.filterErrDeg = occCD (gate0 l F).alg (symCof l wa F.filterErrDeg) (A1 l F.filterErrDeg 63) +
            16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) +
            symHC (symCof l wa F.filterErrDeg).dC (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dQ
              (symCof l wa F.filterErrDeg).dD (coOf (A1 l F.filterErrDeg 63) (symCof l wa F.filterErrDeg).dQ
                (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dD) (eN l F.filterErrDeg) (eQ l F.filterErrDeg) := rfl
        rw [eCD] at hCD
        have hCDo : occCD (gate0 l F).alg (symCof l wa F.filterErrDeg) (A1 l F.filterErrDeg 63) ≤ F.CD := by omega
        have hCDq : 16 * symC1 (eN l F.filterErrDeg) (eQ l F.filterErrDeg) (CallIndexR.capZR l) ≤ F.CD := by omega
        have hCDh : symHC (symCof l wa F.filterErrDeg).dC (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dQ
            (symCof l wa F.filterErrDeg).dD (coOf (A1 l F.filterErrDeg 63) (symCof l wa F.filterErrDeg).dQ
              (cDa (gate0 l F).alg) (symCof l wa F.filterErrDeg).dD) (eN l F.filterErrDeg) (eQ l F.filterErrDeg) ≤ F.CD := by
          omega
        have h24 : PrimT.C4Grp.bsz (PrimT.C4Pad.padBatch (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
            (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers)) ≤ 2 ^ ((26 * Nat.clog 2 (n + 2) + 7) * 0 +
              ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24) := by
          refine EnumCap.bsz_le _ _ Nat.one_le_two_pow (fun V hV => ?_)
          rw [List.eq_of_mem_replicate hV]
          exact constRow_word.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hpm : ∀ V ∈ PrimT.C4Pad.padBatch (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
            (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers), ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1 := by
          intro V hV t ht
          rw [List.eq_of_mem_replicate hV] at ht
          simp only [PrimT.C4Pad.constRow, List.mem_singleton] at ht
          subst ht
          left; rfl
        have hT1 : 1 ≤ 2 ^ (63 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) :=
          Nat.one_le_two_pow
        refine ⟨padHok l F (symCof l wa F.filterErrDeg) hdT hCDq hcpsi hdC kclk coef A a ha ha' Cs carriers translation
            hcall hs,
          fun p b _ => hpre_sym l F (symCof l wa F.filterErrDeg) hc 63 0 1 hCDo hcpsi kclk coef A a ha ha' Cs carriers
            translation hcall hs 1 (by norm_num) _ (fun _ => 1) (SampShape.padFacts _ _ _) hT1
            (pad_hmf l F (symCof l wa F.filterErrDeg) kclk coef A a ha Cs carriers hs h0) (Nat.zero_le _) (p ++ [b]),
          hQp_sym l F (symCof l wa F.filterErrDeg) (by have := hc.dP2; omega) hc.eP2 kclk coef A a ha ha' Cs carriers
            translation hcall hs,
          symHcost_of l F (symCof l wa F.filterErrDeg) wa 63 hc hCDo hCDq hCDh hcpsi hdC hdA kclk coef A a ha ha' Cs
            carriers translation hcall hs 1 0 0 1 (fun _ => 1) _ (by norm_num) hpm h24 (Nat.zero_le _)
            (SampShape.padFacts _ _ _) hT1
            (pad_hmf l F (symCof l wa F.filterErrDeg) kclk coef A a ha Cs carriers hs h0) (Nat.zero_le _),
          hrange_sym l F (symCof l wa F.filterErrDeg) hdQr kclk coef A a ha ha' Cs carriers translation hcall hs,
          ?_,
          (fits_sym l F (symCof l wa F.filterErrDeg) hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs
            ((freeProg2 (symK2 (symCof l wa F.filterErrDeg))).val
              (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0).1,
          one_le_h_sym (symCof l wa F.filterErrDeg) hdH1 _⟩
        exact symHR l F (symCof l wa F.filterErrDeg) wa 63 hCDh hcpsi hdA kclk coef A a ha ha' Cs carriers translation
          hcall hs }⟩

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
