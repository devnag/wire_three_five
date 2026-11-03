import Proof.Wire_3_5.FinalPass.RowI
import Proof.Wire_3_5.FinalPass.DigsLink4

/-! # `RowW`, part 10: the row program writes `Term.rowWord` of row `(g, p)` (P3:2585-2599)

The coefficients: `La (base mod p) p wsd [] a' = (Term.thrCoeffs g p).flatMap unary` (`La_coeffs`, via
`EqRef.weights_blocks` and `resid_mul`). The digit weights: `(range τ₀).map (2^d mod p) = Term.thrWeights`
(`weights_eq`). The residue: `(p − Tf …) mod p = Term.thrR0 g p` (`r0_eq`: in `ZMod p` both are `−target`, by
`EqRef.target_eq`). Main declarations: `coeffs_eq`, `La_coeffs`, `weights_eq`, `Tf_zmod`, **`r0_eq`**. Paper
quantities: `r₀ = (−target) mod p`, the reduced coefficients `a_i` and the digit weights `2^d mod p` of row
`(g, p)` (`row:radix`, `thrRhat_eq_termOk`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5

theorem La_eq (bm p : ℕ) (ws : ℕ → List ℤ) : ∀ n,
    La bm p ws [] n = ((List.range n).flatMap fun i => (ws i).map fun w => Bs bm p i * (w % (p : ℤ)).toNat % p).flatMap
      ListEval.unary
  | 0 => by simp [La]
  | n + 1 => by
    rw [La, La_eq bm p ws n, List.range_succ, List.flatMap_append, List.flatMap_append]
    simp [aWord]

section Sel
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : DecompositionAlgorithm)

/-- **The row's reduced coefficients, circuit by circuit.** -/
theorem coeffs_eq (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 2 ≤ p) :
    Term.thrCoeffs P Cs alg g p = (List.range a').flatMap (fun i => (wsd Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i).map fun w =>
      Bs (PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % p) p i * (w % (p : ℤ)).toNat % p) := by
  have hpos : 0 < p := by omega
  obtain ⟨base, hbase⟩ : ∃ b, b = PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g := ⟨_, rfl⟩
  rw [← hbase]
  have e1 : Term.thrCoeffs P Cs alg g p =
      (List.ofFn (Primitive.thrRealize P Cs alg g).weights).map (fun w => (w % (p : ℤ)).toNat) := by
    unfold Term.thrCoeffs; rw [List.map_ofFn]; rfl
  rw [e1]
  unfold Primitive.thrRealize
  rw [PrimThrW.EqRef.weights_blocks, List.map_flatMap, ← hbase]
  obtain ⟨B, hB⟩ : ∃ B : ℕ → List ℕ, B = fun j => (wsd Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) j).map fun w =>
      Bs (base % p) p j * (w % (p : ℤ)).toNat % p := ⟨_, rfl⟩
  rw [show (List.finRange (Primitive.thrRequest P Cs).circuits.length).flatMap (fun i =>
      (List.ofFn fun k => ((base : ℕ) : ℤ) ^ i.val *
        (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i).weight k).map
        (fun w => (w % (p : ℤ)).toNat)) =
      (List.finRange (List.ofFn Cs).length).flatMap (fun i => B i.val) from
    List.flatMap_congr (fun i _ => by
      rw [hB]
      beta_reduce
      rw [← ws_child P Cs alg g i, List.map_ofFn, List.map_ofFn]
      congr 1
      funext k
      simp only [Function.comp_apply]
      rw [resid_mul base i.val _ p hpos, Bs_eq _ _ hp, ← Nat.pow_mod])]
  rw [finRange_flatMap (List.ofFn Cs).length B, hB]
  simp only [List.length_ofFn]

theorem La_coeffs (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 2 ≤ p) :
    La (PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % p) p (wsd Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j)) [] a' =
      (Term.thrCoeffs P Cs alg g p).flatMap ListEval.unary := by
  rw [La_eq, coeffs_eq P Cs alg g p hp]

theorem weights_eq (den p : ℕ) :
    (List.range (Primitive.thrDigits P Cs alg den)).map (fun d => 2 ^ d % p) = Term.thrWeights P Cs alg den p := by
  unfold Term.thrWeights
  rw [ofFn_range (fun d => 2 ^ d % p)]

theorem td_child (g : Primitive.ThrEq P Cs alg) (i : Fin (List.ofFn Cs).length) :
    (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i).target =
      td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i.val := by
  have h := ys_child P Cs alg g i
  unfold ysOf at h
  have := (List.append_inj' h rfl).2
  simpa using this

theorem Tf_sum (bm p : ℕ) (hp : 0 < p) (t : ℕ → ℤ) : ∀ n,
    Tf bm p t n = (∑ i ∈ Finset.range n, Bs bm p i * (t i % (p : ℤ)).toNat % p) % p
  | 0 => by simp [Tf]
  | n + 1 => by
    rw [Tf, Tf_sum bm p hp t n, Finset.sum_range_succ]
    exact Nat.ModEq.add_right _ (Nat.mod_modEq _ _)

/-- **The residue of row `(g, p)`**: `(p − T) mod p = r₀ = (−target) mod p`. -/
theorem r0_eq (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 2 ≤ p) :
    (p - Tf (PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % p) p (td Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j)) a') % p =
      Term.thrR0 P Cs alg g p := by
  haveI : NeZero p := ⟨by omega⟩
  have hpos : 0 < p := by omega
  obtain ⟨base, hbase⟩ : ∃ b, b = PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g := ⟨_, rfl⟩
  rw [← hbase]
  obtain ⟨T, hT⟩ : ∃ T, T = Tf (base % p) p (td Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j)) a' := ⟨_, rfl⟩
  rw [← hT]
  have hTp : T < p := by rw [hT]; exact Tf_lt _ p (by omega) _ a'
  -- both sides are `−target` in `ZMod p`
  have htarget : ((Primitive.thrRealize P Cs alg g).target : ZMod p) = (T : ZMod p) := by
    unfold Primitive.thrRealize
    rw [PrimThrW.EqRef.target_eq, ← hbase, hT, Tf_sum _ p hpos, ZMod.natCast_mod]
    push_cast
    rw [show (∑ i : Fin (Primitive.thrRequest P Cs).circuits.length, ((base : ZMod p) ^ i.val *
        ((PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i).target : ZMod p))) =
        ∑ i : Fin (List.ofFn Cs).length, (fun j : ℕ => (base : ZMod p) ^ j * ((td Cs alg (fun j =>
          Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) j : ℤ) : ZMod p)) i.val from
      Finset.sum_congr rfl (fun i _ => by rw [td_child P Cs alg g i])]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (base : ZMod p) ^ j * ((td Cs alg (fun j =>
      Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) j : ℤ) : ZMod p))]
    simp only [List.length_ofFn]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Term.natCast_toNat_emod p hpos, Bs_eq _ _ hp]
  have hL : (((p - T) % p : ℕ) : ZMod p) = -(T : ZMod p) := by
    rw [ZMod.natCast_mod, Nat.cast_sub hTp.le, ZMod.natCast_self, zero_sub]
  have hR : ((Term.thrR0 P Cs alg g p : ℕ) : ZMod p) = -(T : ZMod p) := by
    unfold Term.thrR0
    rw [Term.natCast_toNat_emod p hpos]
    push_cast
    rw [htarget]
  have heq : (((p - T) % p : ℕ) : ZMod p) = ((Term.thrR0 P Cs alg g p : ℕ) : ZMod p) := by rw [hL, hR]
  rw [ZMod.natCast_eq_natCast_iff'] at heq
  have h1 : (p - T) % p < p := Nat.mod_lt _ hpos
  have h2 : Term.thrR0 P Cs alg g p < p := by
    unfold Term.thrR0
    have h3 := Int.emod_lt_of_pos (-(Primitive.thrRealize P Cs alg g).target) (by exact_mod_cast hpos : (0 : ℤ) < p)
    have h4 := Int.emod_nonneg (-(Primitive.thrRealize P Cs alg g).target) (by exact_mod_cast hpos.ne' : (p : ℤ) ≠ 0)
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at heq
  exact heq

end Sel

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
