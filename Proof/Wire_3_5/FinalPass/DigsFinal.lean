import Proof.Wire_3_5.FinalPass.DigsSize

/-! # **`DigsW`**, built: the RADIX row's digit populations as a word program (P3:2585-2599, W17)

`digsWImpl : Digs.DigsW`: the program `topW` (base pass, `τ₀` digit passes, output rewound), capacity
`need N = 2 · 16 (N + 1)^4 + 2`, bound `topB (16 (N + 1)^4)`, both polynomial. `run`: from every `DigsIn` entry it
writes exactly `digsWord (List.ofFn fun d => Records.thrDigGis P Cs carriers alg den g pr d)` on `Dg` and changes
nothing else (`top_spec`, with the data `cDd`/`zsd`/`wsd`/`td`/`restd` at the child indices `Gs G md i mod md i`,
`Bf_base`, `Wd_digs`, and the sizes of `size`). Main declaration: **`digsWImpl`**. Paper quantity: the digit
populations `v_{i,d}` of row `(g, p)` of `row:radix` (P3:2598-2599). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem allL_ge : ∀ k ∈ allL, 5 ≤ k.val := by decide

theorem prime_two (c : ℕ) (pr : SupplierPrime.PrimeIndex c) : 2 ≤ pr.val :=
  (SupplierPrime.mem_primesUpTo.mp pr.2).1.two_le

/-- **The digit program.** -/
noncomputable def digsWImpl : Digs.DigsW where
  prog := fun Pay Dg R => topW R Pay Dg
  need := fun N => 2 * (16 * (N + 1) ^ 4) + 2
  bound := fun N => topB (16 * (N + 1) ^ 4)
  C := max (Classical.choose (PolyB.subst topB_poly 16 4)) 34
  D := max (Classical.choose (Classical.choose_spec (PolyB.subst topB_poly 16 4))) 4
  need_le := fun N => by
    have h0 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h1 : 2 * (16 * (N + 1) ^ 4) + 2 ≤ 34 * (N + 1) ^ 4 := by omega
    exact le_trans h1 (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
  bound_le := fun N => by
    have h := Classical.choose_spec (Classical.choose_spec (PolyB.subst topB_poly 16 4)) N
    exact le_trans h (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (by omega) (le_max_left _ _)))
  run := by
    intro ns nr Pay Dg R _ hPD P a' ha Cs carriers alg den g pr cap σ hin hneed
    have hp2 := prime_two _ pr
    have hkk : ∀ i, i < a' → Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) i % md Cs alg i < md Cs alg i :=
      fun i hi => Nat.mod_lt _ (by have := md_pos P Cs alg g i hi; omega)
    have hN : (∑ j : Fin a', (PrimThrW.TopFront.payOf alg (Cs j)).length) + pr.val + Primitive.thrDigits P Cs alg den +
        PrimAsm.Records.thrOff P Cs carriers = Digs.digsN P Cs carriers alg den pr.val := rfl
    have hcN : ∀ i, i < a' → (cDd Cs alg i).length ≤ Digs.digsN P Cs carriers alg den pr.val := fun i hi => by
      have := cDd_le P Cs alg i hi; omega
    have hmN : ∀ i, i < a' → md Cs alg i ≤ Digs.digsN P Cs carriers alg den pr.val := fun i hi =>
      le_trans (md_le_cDd P Cs alg i hi) (hcN i hi)
    have hGN := G_le P Cs alg g _ hmN ha
    have hON : Os (Sd Cs) a' ≤ Digs.digsN P Cs carriers alg den pr.val := by
      have := Os_le P Cs alg _ hkk; omega
    have h0 : 1 ≤ (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hNU : Digs.digsN P Cs carriers alg den pr.val ≤ 16 * (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4 := by
      have := Nat.le_self_pow (show 4 ≠ 0 by norm_num) (Digs.digsN P Cs carriers alg den pr.val + 1); omega
    have hlU := U_bound (Digs.digsN P Cs carriers alg den pr.val) (Primitive.thrDigits P Cs alg den) (Os (Sd Cs) a')
      (PrimAsm.Records.thrOff P Cs carriers) _ (by omega) hON (by omega)
      (Wd_len a' (PrimAsm.Records.thrOff P Cs carriers)
        (Bf pr.val (fun i => wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
          md Cs alg j) i ++ [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
          md Cs alg j) i]) a') pr.val (Sd Cs)
        (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
        (wsd_len_all P Cs alg g) (Primitive.thrDigits P Cs alg den))
    have key := top_spec cap R Pay Dg hPD a' ha (cDd Cs alg) (Sd Cs) (md Cs alg)
      (zsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (restd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) pr.val (Primitive.thrDigits P Cs alg den)
      (PrimAsm.Records.thrOff P Cs carriers) (16 * (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4) σ
      (fun i hi => by rw [hin.pay i, dif_pos hi, payOf_cDd Cs alg i.val hi]) (fun i _ => hin.payH i)
      (fun i hi => cDd_eq Cs alg _ i hi (hkk i hi)) (fun i hi => zsd_len Cs alg _ i hi (hkk i hi).le)
      (fun i hi => wsd_len Cs alg _ i hi (hkk i hi)) (fun i hi => md_pos P Cs alg g i hi) (Gs_top P Cs alg g) hp2
      hin.dg hin.dgH hin.vA hin.vG hin.vP hin.vTau hin.vOff (fun k hk => hin.zero k (allL_ge k hk))
      (fun i hi => le_trans (hcN i hi) hNU) (fun i hi => le_trans (hmN i hi) hNU) (by omega) (by omega) (by omega)
      hlU (by omega) hneed
    rw [Bf_base P Cs alg g pr.val hp2, Wd_digs P Cs alg carriers den g pr hp2] at key
    exact key

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
