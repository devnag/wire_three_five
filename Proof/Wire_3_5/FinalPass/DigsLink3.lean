import Proof.Wire_3_5.FinalPass.DigsLink2

/-! # `DigsW`'s body, part 17: the selection's child indices and the stack base (P3:2543-2551)

With `G = thrEqEquiv g` (the selection's mixed-radix index): circuit `i`'s child index is `g i = Gs G md i mod md i`
(`sel_kk`, from `EqRead.sel_digit`), every circuit has a child (`md_pos`), `Gs G md a' = 0` (`Gs_top`), and the base
pass's residue is `baseOf mod p` (`Bf_base`, from `EqRead.baseOf_eq`, `childMagnitude_eq`). Main declarations:
`get_ofFn_eq`, `md_get`, **`sel_kk`**, `md_pos`, `Gs_top`, `ys_child`, **`Bf_base`**. Paper quantities: the child
indices `g_i` of selection `g` and the stack base `1 + Σ_i ‖child_i‖` modulo `p`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5

theorem sum_range_list (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f n, Finset.sum_range_succ]; simp

theorem Gs_eq' (G : ℕ) (m : ℕ → ℕ) : ∀ i, Gs G m i = G / ∏ j ∈ Finset.range i, m j
  | 0 => by simp [Gs]
  | i + 1 => by rw [Gs, Gs_eq' G m i, Finset.prod_range_succ, Nat.div_div_eq_div_mul]

theorem cm_ys {k : ℕ} (ch : ExactThresholdGate k) :
    ThresholdAlignedEnvelope.childMagnitude ch = ((ysOf ch).map Int.natAbs).sum := by
  rw [PrimThrW.EqRead.childMagnitude_eq, ysOf, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn]
  simp

section Sel
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : DecompositionAlgorithm)

theorem get_ofFn_eq (i : Fin (List.ofFn Cs).length) (h : i.val < a') : (List.ofFn Cs).get i = Cs ⟨i.val, h⟩ := by
  rw [List.get_ofFn]; rfl

theorem lt_of_fin (i : Fin (List.ofFn Cs).length) : i.val < a' := by have := i.isLt; simpa using this

theorem md_get (i : Fin (List.ofFn Cs).length) :
    (ThresholdRows.children alg ((List.ofFn Cs).get i)).length = md Cs alg i.val := by
  rw [md, dif_pos (lt_of_fin P Cs i), get_ofFn_eq P Cs i (lt_of_fin P Cs i)]

theorem prod_md (n : ℕ) (hn : n ≤ (List.ofFn Cs).length) :
    ∏ j : Fin n, (ThresholdRows.children alg ((List.ofFn Cs).get (Fin.castLE hn j))).length =
      ∏ j ∈ Finset.range n, md Cs alg j := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [md_get]; rfl

/-- **Circuit `i`'s child index** from the selection's index. -/
theorem sel_kk (g : Primitive.ThrEq P Cs alg) (i : Fin (List.ofFn Cs).length) :
    ((g i : ℕ)) = Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) i.val % md Cs alg i.val := by
  have hsd := PrimThrW.EqRead.sel_digit P Cs alg _ (PrimAsm.Enum.thrEqEquiv P Cs alg g).isLt i
  rw [Fin.eta, Equiv.symm_apply_apply] at hsd
  rw [hsd, prod_md P Cs alg i.val i.is_lt.le, md_get, Gs_eq']

theorem md_pos (g : Primitive.ThrEq P Cs alg) (i : ℕ) (h : i < a') : 1 ≤ md Cs alg i := by
  have hi : i < (List.ofFn Cs).length := by simpa using h
  have h1 := (g ⟨i, hi⟩).isLt
  have e : (ThresholdRows.children alg ((Primitive.thrRequest P Cs).circuits.get ⟨i, hi⟩)).length = md Cs alg i :=
    md_get P Cs alg ⟨i, hi⟩
  omega

theorem prod_all : ∏ i : Fin (List.ofFn Cs).length, (ThresholdRows.children alg ((List.ofFn Cs).get i)).length =
    ∏ j ∈ Finset.range a', md Cs alg j := by
  rw [show ∏ i : Fin (List.ofFn Cs).length, (ThresholdRows.children alg ((List.ofFn Cs).get i)).length =
    ∏ i : Fin (List.ofFn Cs).length, md Cs alg i.val from Finset.prod_congr rfl (fun i _ => md_get P Cs alg i),
    Fin.prod_univ_eq_prod_range, List.length_ofFn]

theorem Gs_top (g : Primitive.ThrEq P Cs alg) : Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) a' = 0 := by
  rw [Gs_eq']
  apply Nat.div_eq_of_lt
  exact lt_of_lt_of_eq (PrimAsm.Enum.thrEqEquiv P Cs alg g).isLt (prod_all P Cs alg)

/-- A circuit's integers at child index `k`. -/
def Yc {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) (k : ℕ) : List ℤ :=
  (((ThresholdRows.children alg c)[k]?).map ysOf).getD []

theorem ys_child (g : Primitive.ThrEq P Cs alg) (i : Fin (List.ofFn Cs).length) :
    ysOf (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i) =
      wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i.val ++
        [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i.val] := by
  have h := lt_of_fin P Cs i
  have e1 : ysOf (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i) = Yc alg ((List.ofFn Cs).get i) (g i) := by
    unfold Yc PacketsMeta.CutoffMath.child
    rw [List.getElem?_eq_getElem (g i).isLt]; rfl
  have hsel := sel_kk P Cs alg g i
  rw [e1]
  generalize ((g i : ℕ)) = k at hsel ⊢
  rw [get_ofFn_eq P Cs i h, hsel]
  have hk : Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) i.val % md Cs alg i.val <
      (ThresholdRows.children alg (Cs ⟨i.val, h⟩)).length := by
    have := md_pos P Cs alg g i.val h
    have e : md Cs alg i.val = (ThresholdRows.children alg (Cs ⟨i.val, h⟩)).length := by rw [md, dif_pos h]
    rw [← e]; exact Nat.mod_lt _ (by omega)
  unfold Yc wsd td
  rw [dif_pos h, dif_pos h, List.getElem?_eq_getElem hk]
  rfl

/-- **The base pass's residue is the stack base modulo `p`.** -/
theorem Bf_base (g : Primitive.ThrEq P Cs alg) (p : ℕ) (hp : 2 ≤ p) :
    Bf p (fun i => wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i ++
      [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i]) a' =
      PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % p := by
  rw [Bf_eq p hp, PrimThrW.EqRead.baseOf_eq, sum_range_list]
  congr 1
  rw [Nat.add_comm]
  congr 1
  rw [show (∑ i : Fin (Primitive.thrRequest P Cs).circuits.length,
      ThresholdAlignedEnvelope.childMagnitude ((ThresholdRows.children alg ((Primitive.thrRequest P Cs).circuits.get i)).get (g i))) =
      ∑ i : Fin (List.ofFn Cs).length, ((wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
        md Cs alg j) i.val ++ [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
        md Cs alg j) i.val]).map Int.natAbs).sum from Finset.sum_congr rfl (fun i _ => by
      rw [cm_ys, ← ys_child P Cs alg g i])]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
    (md Cs alg) j % md Cs alg j) j ++ [td Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j %
    md Cs alg j) j]).map Int.natAbs).sum)]
  simp only [List.length_ofFn]

end Sel

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
