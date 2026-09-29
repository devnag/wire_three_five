import Proof.Wire_3_5.FinalPass.DigsLink4
import Proof.Wire_3_5.FinalPass.DigsPoly

/-! # `DigsW`'s body, part 20: the sizes behind the capacity (`DigsW.need`)

Every quantity the program holds in a register is at most `U = 16 (N + 1)^4`, `N = digsN` (payload lengths, `p`,
`τ₀`, `oOff`): a payload's content and child count are at most its length (`cDd_le`, `md_le_cDd`), the selection
index is below `Π_i |children_i| ≤ N^4` (`G_le`), the occurrence count is at most `N` (`Os_le`), and the output word
has length at most `τ₀ · (Os (oOff + Os + 2) + 1)` (`Wd_len`). Main declarations: `emitList_len`, `Ls_len`,
`Wd_len`, `cDd_le`, `md_le_cDd`, `Sd_le_cDd`, `Os_le`, `G_le`, **`U_bound`**. Paper quantity: none (the input size
bounding the digit program's registers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.ThrArith

theorem emitW_len (off o d a : ℕ) : (emitW off o d a).length ≤ off + o + 2 := by
  unfold emitW; split_ifs <;> simp [enc]

theorem emitList_len (off d B p : ℕ) : ∀ (o : ℕ) (ws : List ℤ),
    (emitList off d B p o ws).length ≤ ws.length * (off + o + ws.length + 2)
  | o, [] => by simp [emitList]
  | o, w :: ws => by
    have ih := emitList_len off d B p (o + 1) ws
    have h1 := emitW_len off o d (B * (w % (p : ℤ)).toNat % p)
    rw [emitList, List.length_append, List.length_cons]
    nlinarith

theorem Os_sum (S : ℕ → ℕ) : ∀ n, Os S n = ∑ i ∈ Finset.range n, S i
  | 0 => by simp [Os]
  | n + 1 => by rw [Os, Os_sum S n, Finset.sum_range_succ]

theorem Ls_len (off d bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (hS : ∀ i, (ws i).length = S i) :
    ∀ n, (Ls off d bm p S ws [] n).length ≤ Os S n * (off + Os S n + 2)
  | 0 => by simp [Ls, Os]
  | n + 1 => by
    have ih := Ls_len off d bm p S ws hS n
    have h1 := emitList_len off d (Bs bm p n) p (Os S n) (ws n)
    rw [hS] at h1
    rw [Ls, List.length_append, Os]
    nlinarith

theorem Wd_len (a' off bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (hS : ∀ i, (ws i).length = S i) :
    ∀ τ, (Wd a' off bm p S ws [] τ).length ≤ τ * (Os S a' * (off + Os S a' + 2) + 1)
  | 0 => by simp [Wd]
  | τ + 1 => by
    have ih := Wd_len a' off bm p S ws hS τ
    have h1 := Ls_len off τ bm p S ws hS a'
    rw [Wd_succ, List.length_append, dWord, List.length_append, List.length_singleton]
    nlinarith

theorem exactWord_len_pos {k : ℕ} (ch : ExactThresholdGate k) : 1 ≤ (exactWord ch).length := by
  rw [PrimThrW.EqRead.exactWord_eq, List.length_append, ThrCore.intWord_length']; omega

theorem len_le_flat {k : ℕ} : ∀ l : List (ExactThresholdGate k), l.length ≤ (l.flatMap exactWord).length
  | [] => by simp
  | ch :: l => by
    have := len_le_flat l
    have := exactWord_len_pos ch
    rw [List.flatMap_cons, List.length_append, List.length_cons]; omega

section Sel
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : DecompositionAlgorithm)

theorem cDd_le (i : ℕ) (h : i < a') :
    (cDd Cs alg i).length ≤ ∑ j : Fin a', (PrimThrW.TopFront.payOf alg (Cs j)).length := by
  have e := payOf_cDd Cs alg i h
  have h1 : (PrimThrW.TopFront.payOf alg (Cs ⟨i, h⟩)).length ≤ ∑ j : Fin a', (PrimThrW.TopFront.payOf alg (Cs j)).length :=
    Finset.single_le_sum (f := fun j => (PrimThrW.TopFront.payOf alg (Cs j)).length) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ _)
  rw [e, HashSeed.frame_length'] at h1
  omega

theorem md_le_cDd (i : ℕ) (h : i < a') : md Cs alg i ≤ (cDd Cs alg i).length := by
  unfold md cDd
  rw [dif_pos h, dif_pos h]
  have := len_le_flat (ThresholdRows.children alg (Cs ⟨i, h⟩))
  simp only [List.length_append]; omega

theorem Sd_le_cDd (kk : ℕ → ℕ) (i : ℕ) (h : i < a') (hk : kk i < md Cs alg i) : Sd Cs i ≤ (cDd Cs alg i).length := by
  have e := cDd_eq Cs alg kk i h hk
  have h1 := fm_len_ge (wsd Cs alg kk i ++ [td Cs alg kk i])
  have h2 := wsd_len Cs alg kk i h hk
  rw [e]; simp only [List.length_append, List.length_singleton] at h1 ⊢; omega

theorem Os_le (kk : ℕ → ℕ) (hk : ∀ i, i < a' → kk i < md Cs alg i) :
    Os (Sd Cs) a' ≤ ∑ j : Fin a', (PrimThrW.TopFront.payOf alg (Cs j)).length := by
  rw [Os_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro j _
  have e1 := Sd_le_cDd P Cs alg kk j.val j.isLt (hk j.val j.isLt)
  have e2 : (cDd Cs alg j.val).length ≤ (PrimThrW.TopFront.payOf alg (Cs j)).length := by
    rw [payOf_cDd Cs alg j.val j.isLt, HashSeed.frame_length']; omega
  omega

theorem G_le (g : Primitive.ThrEq P Cs alg) (N : ℕ) (hN : ∀ i, i < a' → md Cs alg i ≤ N) (ha : a' ≤ 4) :
    (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) ≤ (N + 1) ^ 4 := by
  have h := lt_of_lt_of_eq (PrimAsm.Enum.thrEqEquiv P Cs alg g).isLt (prod_all P Cs alg)
  have h2 : ∏ j ∈ Finset.range a', md Cs alg j ≤ N ^ a' := by
    have := Finset.prod_le_pow_card (Finset.range a') (md Cs alg) N (fun j hj => hN j (Finset.mem_range.mp hj))
    simpa using this
  have h3 : N ^ a' ≤ (N + 1) ^ 4 := le_trans (Nat.pow_le_pow_left (by omega) a') (Nat.pow_le_pow_right (by omega) ha)
  omega

end Sel

/-- The final size arithmetic. -/
theorem U_bound (N τ O off W : ℕ) (hτ : τ ≤ N) (hO : O ≤ N) (hoff : off ≤ N) (hW : W ≤ τ * (O * (off + O + 2) + 1)) :
    W + off + O + 2 ≤ 16 * (N + 1) ^ 4 := by
  have h1 : τ * (O * (off + O + 2) + 1) ≤ N * (N * (N + N + 2) + 1) := by gcongr
  have h2 : (N + 1) ^ 4 = N ^ 4 + 4 * N ^ 3 + 6 * N ^ 2 + 4 * N + 1 := by ring
  nlinarith [Nat.zero_le (N ^ 4), Nat.zero_le (N ^ 3), Nat.zero_le (N ^ 2)]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
