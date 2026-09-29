import Proof.Wire_3_5.FinalPass.S5TRun2

/-! # S5-THR, part 42: the THR half, generic in S4's bank (P3:3170-3181)

The THR half on S4's bank at every request (**`half_run`**: the prelude, the scrubbed stage, the erasers, focused onto
the bank's THR slots and THR room), and the deliverables:

* **`thrHalf`** : `S5ThrB2 l F kclk coef A a ha Sw L` at any bank `L` with the THR room `mThrL l`
  (`HalfRoom2 L (mThrL l) mC`), register length `K ≤ L.Kc`, `D ≤ L.Dc`: cost `(43·D + 6000)·y^{D+1}`, scratch
  `2·y^{D+1} + 3` (`y = |fpIn| + 1 + c₀`), cost within `s5Bound Ct Dt`;
* **`thrHalfGen`** : `ThrHalfGen2 Sw mThrL mC` for every `mC`;
* the uniformity (`S6Uni`): `thrHalfGen_D`, `thrHalf_Dt` (functions of `l` alone), `thrHalfGen_K`,
  `thrHalf_Ct` (functions of `(l, F)`), all by `rfl`.

Paper quantity of the main type: THR slots `8 … 15` of the front's words, written within the preprocessing class
(P3:3105-3115, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam NearCubicWires.WireExponent3_5.FinalPass.Bank
open NearCubicWires.SupplierPipeline

/-- **The THR half's room** at `l`. -/
noncomputable abbrev mThrL (l : Literals) : ℕ := mThr (Dl l) (x6L l) (xtL l)

section Inst
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The THR half's machine on the scrub layout. -/
noncomputable abbrev thrML :=
  thrM (Dl l) (PrimT.W6.litAlg l) 1 l F.cr (Hd l - 1) (Hd l - 1) (Hd l) (c0T l F)

/-- **The THR half on S4's bank at every request.** -/
theorem half_run (Sw : SymWords) (L : S5Lay Sw.nw) {mC : ℕ} (hR : HalfRoom2 L (mThrL l) mC)
    (r : PlanFP.FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool)
    (hAb0 : Ab ⟨0, L.ht⟩ = frame (PlanFP.fpIn l F kclk coef A a ha r)) (hAbS : ∀ k, thrSlot k → Ab (L.wd k) = [])
    (hAbT : ∀ j, L.thrSc j = true → Ab j = []) :
    ∃ Ab' : Fin L.t → List Bool,
      Step (RecoveryFocus.machine (slotMap (Dl l) (x6L l) (xtL l) L hR) (thrML l F))
        ((43 * Dl l + 6000) * yOf l F kclk coef A a ha r ^ (Dl l + 1)) (fun _ => 0) Ab (fun _ => 0) Ab' ∧
      (∀ k, thrSlot k → Ab' (L.wd k) = frontWordsW l F kclk coef A a ha Sw r k) ∧
      (∀ j, L.thrSc j = true → ∃ ℓ ≤ 2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 3,
        Ab' j = List.replicate ℓ false) ∧
      (∀ j, L.thrSc j = false → (∀ k, thrSlot k → j ≠ L.wd k) → Ab' j = Ab j) := by
  obtain ⟨σE, c, hst, hc1, hsl, hin, hxD, hreg⟩ := stage_at l F kclk coef A a ha Sw r
  have hH30 := one_le_Hd l
  have hZD := Zx_le_Dl l
  have hZx : Zx l = 3 * Hd l + 1 := rfl
  have k0 : 100000 ≤ c0T l F := by unfold c0T; omega
  have hsp := thrM_step (Dl l) (PrimT.W6.litAlg l) 1 l F.cr (Hd l - 1) (Hd l - 1) (Hd l) (c0T l F)
    (PlanFP.fpIn l F kclk coef A a ha r) (yOf l F kclk coef A a ha r ^ (Dl l + 1)) rfl (by omega) (by omega) σE c hst
    hc1 hreg
  obtain ⟨Ab', hstep, hslot, hsc, hrest⟩ := focus_run (Dl l) (x6L l) (xtL l) L hR (thrML l F)
    (PlanFP.fpIn l F kclk coef A a ha r) (thrAf (Dl l) (PrimT.W6.litAlg l) 1 (yOf l F kclk coef A a ha r ^ (Dl l + 1)) σE)
    (fun m => σE.st (sSlot (Dl l) (x6L l) (xtL l) m)) (2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 3) hsp
    ((thrAf_in (Dl l) (PrimT.W6.litAlg l) 1 _ σE).trans hin)
    (fun m => thrAf_slot (Dl l) (PrimT.W6.litAlg l) 1 _ σE m)
    (fun j hj hm => thrAf_blank (Dl l) (PrimT.W6.litAlg l) 1 _ σE hreg hxD j hj hm) Ab hAb0 hAbS hAbT
  have htot := total_le ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) (c0T l F) (Dl l) c (by omega)
    (Nat.le_of_succ_le hc1)
  refine ⟨Ab', hstep.enlarge htot, fun k hk => ?_, hsc, hrest⟩
  rw [hslot k hk, hsl]
  congr 1
  exact Fin.ext (by have := hk.1; simp; omega)

/-- **The THR half at a bank** (`S5ThrB2`): register length `2·(c₀+1)^{D+1} + 2`, degree `D + 1`. -/
noncomputable def thrHalf (Sw : SymWords) (L : S5Lay Sw.nw) {mC : ℕ} (hR : HalfRoom2 L (mThrL l) mC)
    (hK : 2 * (c0T l F + 1) ^ (Dl l + 1) + 2 ≤ L.Kc) (hD : Dl l + 1 ≤ L.Dc) :
    S5ThrB2 l F kclk coef A a ha Sw L where
  s := _
  M := RecoveryFocus.machine (slotMap (Dl l) (x6L l) (xtL l) L hR) (thrML l F)
  cost := fun r => (43 * Dl l + 6000) * yOf l F kclk coef A a ha r ^ (Dl l + 1)
  len := fun r => 2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 3
  len_le := fun r => by
    have hN : 1 ≤ (PlanFP.fpIn l F kclk coef A a ha r).length + 1 := by omega
    have hs := pow_split ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) (c0T l F) (Dl l + 1) hN
    have h2 : ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) ≤
        ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc := Nat.pow_le_pow_right hN hD
    have h3 := Nat.mul_le_mul hK h2
    have e : (2 * (c0T l F + 1) ^ (Dl l + 1) + 2) * ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) =
        2 * ((c0T l F + 1) ^ (Dl l + 1) * ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1)) +
          2 * ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) := by ring
    have h1 : 1 ≤ ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) := Nat.one_le_pow _ _ hN
    show 2 * yOf l F kclk coef A a ha r ^ (Dl l + 1) + 3 ≤ _
    unfold yOf
    omega
  run := fun r Ab h0 hS hT => half_run l F kclk coef A a ha Sw L hR r Ab h0 hS hT
  Ct := (43 * Dl l + 6000) * (c0T l F + 1) ^ (Dl l + 1)
  Dt := Dl l + 1
  cost_le := fun r => by
    have hN : 1 ≤ (PlanFP.fpIn l F kclk coef A a ha r).length + 1 := by omega
    have hs := pow_split ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) (c0T l F) (Dl l + 1) hN
    have h2 : 1 ≤ 2 ^ ((Dl l + 1) * s5Psi l F kclk coef A a ha r) := Nat.one_le_two_pow
    show (43 * Dl l + 6000) * yOf l F kclk coef A a ha r ^ (Dl l + 1) ≤ _
    unfold s5Bound yOf
    calc (43 * Dl l + 6000) * ((PlanFP.fpIn l F kclk coef A a ha r).length + 1 + c0T l F) ^ (Dl l + 1)
        ≤ (43 * Dl l + 6000) * ((c0T l F + 1) ^ (Dl l + 1) *
          ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1)) := Nat.mul_le_mul_left _ hs
      _ = (43 * Dl l + 6000) * (c0T l F + 1) ^ (Dl l + 1) * 1 *
          ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) := by ring
      _ ≤ (43 * Dl l + 6000) * (c0T l F + 1) ^ (Dl l + 1) * 2 ^ ((Dl l + 1) * s5Psi l F kclk coef A a ha r) *
          ((PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ (Dl l + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)

end Inst

/-- **The THR half's target** (`ThrHalfGen2`) at the THR room `mThrL`, for every core room `mC`. -/
noncomputable def thrHalfGen (Sw : SymWords) (mC : Literals → ℕ) : ThrHalfGen2 Sw mThrL mC :=
  fun l F kclk coef A a ha => ⟨2 * (c0T l F + 1) ^ (Dl l + 1) + 2, Dl l + 1,
    fun L hR hK hD => thrHalf l F kclk coef A a ha Sw L hR hK hD⟩

section Uni

end Uni

end NearCubicWires.WireExponent3_5.FinalPass.S5T
