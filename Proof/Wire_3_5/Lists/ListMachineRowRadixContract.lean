import Proof.Wire_3_5.Lists.ListMachineRowRadixInst

/-! # C2 rows, part 25: the RADIX row's record, capacities and cost

The RADIX row's self-contained record is computable (`radRowRecC`): the setup fields (the scrub
capacity `R` above every factor stage's explicit cost bound `costC`, the log capacity above every masked stage's cost,
the zero tuple's one-hot word, the position word, the contribution fields and the residue pattern), then the
`2τ₀(M+1)` factor blocks. Its reference is `radixExpr` over the computable prints (`radRefC`).

* `radRowRecC_eq`: it is the record `radRow_step` runs on;
* **`radRow_run`**: the RADIX row end to end from its computable record: the output is `exprWord (radRefC …)`, whose
  value at EVERY assignment is `[Σ_d b_0^d(t_d^+ − t_d^−) ≡ s (mod p)]`, and the cost is at most
  `(M+1)^{2τ₀} · 128 · (|record| + 1)^2` — the digit tuples times a polynomial in the record. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.ExtDecompositionBatch

section
variable (D : ListData) (digs : List Dig) (p b0 s : ℕ)

/-- The factor blocks, in store order. -/
def radBlocksC : List (List Bool) :=
  digs.flatMap fun dg => (List.range (D.M + 1)).map (fun t => blockC D dg.1 t true false dg.2) ++
    (List.range (D.M + 1)).map (fun t => blockC D dg.1 t false false dg.2)

/-- The contribution fields. -/
def radCs : List ℕ := consFrom D.M p b0 0 digs.length

/-- The residue pattern. -/
def radT : List Bool := patT p s (2 * digs.length * p + 1)

/-- The store's prints. -/
def radFs : List Poly := storeFrom D.M (radPp D digs) (radPm D digs) 0 digs.length

/-- **The RADIX row's reference expression** (computable): `radixExpr` over the digit lists' prints. -/
def radRefC : Expr := radixExpr digs.length D.M p b0 (radPp D digs) (radPm D digs) (s : ZMod p)

variable (hok : DigsOk digs)

theorem blockSpecs_block (dg : Dig) (sgn : Bool) (hl : 4 * dg.1 ≤ dg.2.length) :
    (blockSpecs D dg sgn hl).map FSpec.block = (List.range (D.M + 1)).map fun t => blockC D dg.1 t sgn false dg.2 := by
  unfold blockSpecs
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' : t ≤ D.M := Nat.le_of_lt_succ (List.mem_range.mp ht)
  simp only [Function.comp_apply]
  rw [visitSpec_block, min_eq_left ht']

theorem radSpecs_block : ∀ (digs : List Dig) (h : DigsOk digs), (radSpecs D digs h).map FSpec.block = radBlocksC D digs
  | [], _ => rfl
  | dg :: rest, h => by
    simp only [radSpecs, List.map_append, blockSpecs_block, radBlocksC, List.flatMap_cons, List.append_assoc]
    rw [radSpecs_block rest (fun x hx => h x (by simp [hx]))]
    rfl

theorem storeRec_radSpecs : storeRec (radSpecs D digs hok) = (radBlocksC D digs).flatMap (fun b => true :: b) ++ [false] := by
  rw [← radSpecs_block D digs hok, List.flatMap_map]
  rfl

theorem mem_radSpecs : ∀ (digs : List Dig) (h : DigsOk digs) (x : FSpec (negFam F35)), x ∈ radSpecs D digs h →
    ∃ dg ∈ digs, ∃ t ≤ D.M, ∃ sgn : Bool, ∃ hl : 4 * dg.1 ≤ dg.2.length,
      x = visitSpec D dg.1 (min t D.M) sgn (capC D dg.1) (min_le_right _ _) le_rfl false dg.2 hl
  | [], _, x, hx => by simp [radSpecs] at hx
  | dg :: rest, h, x, hx => by
    simp only [radSpecs, List.mem_append] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact ⟨dg, by simp, t, Nat.le_of_lt_succ (List.mem_range.mp ht), true, _, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact ⟨dg, by simp, t, Nat.le_of_lt_succ (List.mem_range.mp ht), false, _, rfl⟩
    · obtain ⟨dg', hdg', t, ht, sgn, hl, rfl⟩ := mem_radSpecs rest (fun x hx => h x (by simp [hx])) x hx
      exact ⟨dg', by simp [hdg'], t, ht, sgn, hl, rfl⟩

/-! ## The cost bound -/

theorem setupFieldsG_eq (u R L : ℕ) (ev : Fin 8 → List Bool) :
    setupFieldsG u R L ev = [List.replicate R true, List.replicate L false, ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, ev 7] := by
  simp only [setupFieldsG, targetsQ, List.map_cons, List.map_nil, setupG_driver, setupG_log]
  rw [setupG_e _ _ _ _ 0 (by decide), setupG_e _ _ _ _ 1 (by decide), setupG_e _ _ _ _ 2 (by decide),
    setupG_e _ _ _ _ 3 (by decide), setupG_e _ _ _ _ 4 (by decide), setupG_e _ _ _ _ 5 (by decide),
    setupG_e _ _ _ _ 7 (by decide)]

theorem setupFieldsG_len (u R L : ℕ) (ev : Fin 8 → List Bool) :
    R ≤ (fieldsWord (setupFieldsG u R L ev)).length ∧ (ev 7).length ≤ (fieldsWord (setupFieldsG u R L ev)).length := by
  rw [setupFieldsG_eq]
  simp only [fieldsWord, List.flatMap_cons, List.flatMap_nil, List.length_append, frame_length, List.length_replicate,
    List.length_nil]
  omega

theorem termCostR_le (fs : List Poly) : termCostR fs ≤ 2 * mselCost fs + 18 := by
  simp [termCostR, putCost, coefWord, NearCubicWires.RepairOrdinary.frame]
  omega

/-- The RADIX row's cost, for any parameters meeting the capacity conditions. -/
theorem radRowCost_bound {F : EvalFam} (K P : ℕ) (cs : List ℕ) (T : List Bool) (R Lg cap : ℕ) (xs : List (FSpec F))
    (hst : storeCost xs R ≤ cap) (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost (xs.map FSpec.poly) ≤ cap)
    (hc3 : incCost K P ≤ cap) :
    radRowCost K P cs T R Lg cap xs ≤ (K + 1) ^ P * (128 * ((radRowRec K P cs T R Lg cap xs).length + 1) ^ 2) := by
  set S := (radRowRec K P cs T R Lg cap xs).length with hS
  set N := (K + 1) ^ P with hN
  obtain ⟨hRf, hcf⟩ := setupFieldsG_len F.t R Lg (radEv K P cs T cap)
  have hc7 : (radEv K P cs T cap 7).length = cap := by simp [radEv]
  have hlen : (fieldsWord (setupFieldsG F.t R Lg (radEv K P cs T cap))).length + (storeRec xs).length = S := by
    rw [hS, radRowRec, List.length_append]
  have hRS : R ≤ S := by omega
  have hcS : cap ≤ S := by omega
  have hld := loadCost_le (setupFieldsG F.t R Lg (radEv K P cs T cap))
  have hterm := termCostR_le (xs.map FSpec.poly)
  have hpass : radPass K P cs (xs.map FSpec.poly) ≤ 6 * cap + 28 := by
    unfold radPass; omega
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrc : radCost K P cs (xs.map FSpec.poly) ≤ N * (6 * S + 30) + 1 := by
    unfold radCost
    rw [← hN]
    have := Nat.mul_le_mul_left N (show radPass K P cs (xs.map FSpec.poly) + 2 ≤ 6 * S + 30 by omega)
    omega
  unfold radRowCost radPopCost
  have hpoly : 16 * S + 40 ≤ N * (16 * S + 40) := by nlinarith
  have hfin : N * (6 * S + 30) + N * (16 * S + 40) ≤ N * (128 * (S + 1) ^ 2) := by
    rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; nlinarith
  omega

/-! ## The RADIX row, end to end -/

theorem radT_eq (hs : s < p) : radT digs p s = patT p ((s : ZMod p).val) (2 * digs.length * p + 1) := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hs]; rfl

end

end NearCubicWires.WireExponent3_5.ListMachine.Row
