import Proof.Wire_3_5.FinalPass.RowIface
import Proof.Wire_3_5.FinalPass.RowJ

/-! # **`RowW`**, built: stage 8's row word as a word program (P3:2585-2630)

`rowWImpl : Digs.RowW`: the program `rowTopW` (base pass, target pass, `1^p 0`, `1^{r₀} 0`, coefficient pass, digit
weights, final `0`, output rewound), capacity `need N = 2 · 16 (N + 1)^4 + 2`, bound `rowTB (16 (N + 1)^4)`, both
polynomial. `run`: from every `DigsIn` entry it writes exactly `Term.rowWord p (Term.thrR0 g p) (Term.thrCoeffs g p)
(Term.thrWeights p)` on `Dg` and changes nothing else (`rowTop_spec`, `r0_eq`, `La_coeffs`, `weights_eq`,
`Bf_base`). Main declarations: `La_len`, `rowTB_poly`, **`rowWImpl`**. Paper quantity: row `(g, p)`'s word that
stage 8 evaluates (`row:thr-reported`, `Term.thrRhat_eq_termOk`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ThrCore NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires.WireExponent3_5.FinalPass.ThrArith

theorem aWord_len (B p : ℕ) (hp : 1 ≤ p) : ∀ ws : List ℤ, (aWord B p ws).length ≤ ws.length * p
  | [] => by simp [aWord]
  | w :: ws => by
    have ih := aWord_len B p hp ws
    have hm : B * (w % (p : ℤ)).toNat % p < p := Nat.mod_lt _ (by omega)
    unfold aWord at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, List.length_append, ListEval.unary, List.length_replicate,
      List.length_singleton, List.length_cons, List.length_nil] at ih ⊢
    nlinarith

theorem La_len (bm p : ℕ) (hp : 1 ≤ p) (ws : ℕ → List ℤ) (S : ℕ → ℕ) (hS : ∀ i, (ws i).length = S i) :
    ∀ n, (La bm p ws [] n).length ≤ Os S n * p
  | 0 => by simp [La]
  | n + 1 => by
    have ih := La_len bm p hp ws S hS n
    have h1 := aWord_len (Bs bm p n) p hp (ws n)
    rw [hS] at h1
    rw [La, List.length_append, Os]
    nlinarith

/-- The row program's bound is polynomial. -/
theorem rowTB_poly : PolyB rowTB := by
  unfold rowTB rowAB rowBB bB tPB aPB tB cAB cBB navB modCost2 coreCost bitCost2 bitCost ThrArith.mulStep aCost
    bUpdCost dwCost
  repeat (first | apply PolyB.add | apply PolyB.mul | exact PolyB.id | exact PolyB.const _)

/-- **The row program.** -/
noncomputable def rowWImpl : Digs.RowW where
  prog := fun Pay Dg R => rowTopW R Pay Dg
  need := fun N => 2 * (16 * (N + 1) ^ 4) + 2
  bound := fun N => rowTB (16 * (N + 1) ^ 4)
  C := max (Classical.choose (PolyB.subst rowTB_poly 16 4)) 34
  D := max (Classical.choose (Classical.choose_spec (PolyB.subst rowTB_poly 16 4))) 4
  need_le := fun N => by
    have h0 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h1 : 2 * (16 * (N + 1) ^ 4) + 2 ≤ 34 * (N + 1) ^ 4 := by omega
    exact le_trans h1 (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
  bound_le := fun N => by
    have h := Classical.choose_spec (Classical.choose_spec (PolyB.subst rowTB_poly 16 4)) N
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
    have hLa := La_len (Bf pr.val (fun i => wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
      (md Cs alg) j % md Cs alg j) i ++ [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
      md Cs alg j) i]) a') pr.val (by omega) (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
      (md Cs alg) j % md Cs alg j)) (Sd Cs) (wsd_len_all P Cs alg g) a'
    have hlU : (La (Bf pr.val (fun i => wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
        (md Cs alg) j % md Cs alg j) i ++ [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
        (md Cs alg) j % md Cs alg j) i]) a') pr.val (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
        (md Cs alg) j % md Cs alg j)) [] a').length + 2 * (pr.val + 1) + Primitive.thrDigits P Cs alg den * (pr.val + 1) +
        pr.val + 2 ≤ 16 * (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4 := by
      have hpN : pr.val ≤ Digs.digsN P Cs carriers alg den pr.val := by omega
      have hτN : Primitive.thrDigits P Cs alg den ≤ Digs.digsN P Cs carriers alg den pr.val := by omega
      have e1 : Os (Sd Cs) a' * pr.val ≤ Digs.digsN P Cs carriers alg den pr.val *
          Digs.digsN P Cs carriers alg den pr.val := Nat.mul_le_mul hON hpN
      have e2 : Primitive.thrDigits P Cs alg den * (pr.val + 1) ≤ Digs.digsN P Cs carriers alg den pr.val *
          (Digs.digsN P Cs carriers alg den pr.val + 1) := Nat.mul_le_mul hτN (by omega)
      have e3 : (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4 = (Digs.digsN P Cs carriers alg den pr.val + 1) *
          (Digs.digsN P Cs carriers alg den pr.val + 1) * (Digs.digsN P Cs carriers alg den pr.val + 1) *
          (Digs.digsN P Cs carriers alg den pr.val + 1) := by ring
      nlinarith
    have key := rowTop_spec cap R Pay Dg hPD a' ha (cDd Cs alg) (Sd Cs) (md Cs alg)
      (zsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (restd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) pr.val (Primitive.thrDigits P Cs alg den)
      (16 * (Digs.digsN P Cs carriers alg den pr.val + 1) ^ 4) σ
      (fun i hi => by rw [hin.pay i, dif_pos hi, payOf_cDd Cs alg i.val hi]) (fun i _ => hin.payH i)
      (fun i hi => cDd_eq Cs alg _ i hi (hkk i hi)) (fun i hi => zsd_len Cs alg _ i hi (hkk i hi).le)
      (fun i hi => wsd_len Cs alg _ i hi (hkk i hi)) (fun i hi => md_pos P Cs alg g i hi) (Gs_top P Cs alg g) hp2
      hin.dg hin.dgH hin.vA hin.vG hin.vP hin.vTau (fun k hk => hin.zero k (allL_ge k hk))
      (fun i hi => le_trans (hcN i hi) hNU) (fun i hi => le_trans (hmN i hi) hNU) (by omega) (by omega) (by omega)
      hlU (by omega) hneed
    rw [Bf_base P Cs alg g pr.val hp2, r0_eq P Cs alg g pr.val hp2, La_coeffs P Cs alg g pr.val hp2,
      weights_eq P Cs alg den pr.val] at key
    have e : ListEval.unary pr.val ++ ListEval.unary (Term.thrR0 P Cs alg g pr.val) ++
        (Term.thrCoeffs P Cs alg g pr.val).flatMap ListEval.unary ++ Term.digWord (Term.thrWeights P Cs alg den pr.val) ++
        [false] = Term.rowWord pr.val (Term.thrR0 P Cs alg g pr.val) (Term.thrCoeffs P Cs alg g pr.val)
          (Term.thrWeights P Cs alg den pr.val) := rfl
    rw [e] at key
    exact key

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
