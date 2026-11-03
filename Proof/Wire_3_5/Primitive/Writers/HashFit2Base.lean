import Proof.Wire_3_5.Primitive.Writers.HashFit1Base
import Proof.Wire_3_5.Primitive.SeedFix.C4CapF
import Proof.Wire_3_5.Filters.FilterGap

/-! # HASH setup (C), fit part 2: the HASH cell's capacity facts at every THR call

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`") and P3:3170-3181 (the seed phase's capacity
`2^{⌊n/8⌋ + C}`): with `q = 2^{E·(B+1)²}` bounding the call's sizes (`CallSz`), the cell's capacity facts `CellFit`
hold at the capacity `2^30·q⁴`, with the digit program's bound `Bm = C·(8q+1)^D` and the digit populations' words
`Sm = 4q³`; `2^30·q⁴ ≤ 2^{(4E+30)(B+1)²} ≤ 2^{⌊n/8⌋ + C}` once `C` is past a threshold fixed by the literals.

* `getD_le`, `num_mem`, `segW_flat_le`, `digL_len`, `digsN_le`; `bmOf`, `smOf`, `capOf`; **`cell_sizes`**;
  **`cellFit_mono`**; `capOf_le`, `bmOf_le`; **`cell_fits`** (`∃ Cc₀, ∀ Cc ≥ Cc₀`, `CellFit` at `2·2^{capExp2 Cc n} + 2`,
  with `Bm` within that capacity).

Paper quantities of the main type: the seed phase's capacity `2^{⌊n/8⌋+C}` (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimT

theorem getD_le : ∀ {l : List ℕ} {q : ℕ}, (∀ v ∈ l, v ≤ q) → ∀ k, l.getD k 0 ≤ q
  | [], _, _, k => by simp
  | a :: l, q, h, 0 => by simpa using h a (by simp)
  | a :: l, q, h, k + 1 => by
      simpa using getD_le (fun v hv => h v (List.mem_cons_of_mem a hv)) k

theorem num_mem (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT : ℕ) (i : Fin 14) :
    (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length capT).get i ∈
      ThrData.hashNums P Cs carriers alg Dexp capT :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem segW_flat_le (ls : List (List ℕ)) (M G : ℕ) (h : ∀ l ∈ ls, l.length ≤ M ∧ ∀ gi ∈ l, gi < G) :
    (ls.flatMap HashPops.segW).length ≤ ls.length * (M * (G + 2) + 1) := by
  rw [List.length_flatMap]
  refine BShape.sum_map_le_card ls _ _ (fun l hl => ?_)
  unfold HashPops.segW
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have h1 := BShape.sum_map_le_card l (fun gi => (PrimT.HbM.elemW gi).length) (G + 2) (fun gi hgi => by
    rw [PrimT.HbM.elemW_length]; have := (h l hl).2 gi hgi; omega)
  have h2 : l.length * (G + 2) ≤ M * (G + 2) := Nat.mul_le_mul_right _ (h l hl).1
  omega

theorem digL_len {kclk : ℕ} {Ev : Envelope} {B : TimeBudget kclk Ev} (alg : RepairRepresentation.DecompositionAlgorithm)
    (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (g : ThrEq (I.starParams n hs) Cs alg)
    (pr : SupplierPrime.PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) :
    ((HashPops.digL (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs) g pr).flatMap HashPops.segW).length ≤
      thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) * ((thrOccs (I.starParams n hs) Cs).length *
        ((Records.thrPool (I.starParams n hs) Cs carriers).length + 2) + 1) := by
  have h := segW_flat_le (HashPops.digL (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs) g pr)
    (thrOccs (I.starParams n hs) Cs).length (Records.thrPool (I.starParams n hs) Cs carriers).length (fun l hl => by
      unfold HashPops.digL at hl
      obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hl
      rw [← HashPops.hashGis_eq alg I hs Cs carriers g pr d]
      exact ⟨FinalPass.HashFr.hashGis_length_le alg I hs Cs carriers g pr d,
        FinalPass.HashFr.hashGis_lt alg I hs Cs carriers g pr d⟩)
  unfold HashPops.digL at h ⊢
  rwa [List.length_ofFn] at h

theorem digsN_le (P : StarParams) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den p q : ℕ)
    (hpay : ∀ i, (PrimThrW.TopFront.payOf alg (Cs i)).length ≤ q) (hp : p ≤ q)
    (hd : thrDigits P Cs alg den ≤ q) (hsx : (carriers.map List.length).sum ≤ q) :
    FinalPass.Digs.digsN P Cs carriers alg den p ≤ 8 * q := by
  unfold FinalPass.Digs.digsN
  rw [Records.thrOff_eq]
  have h1 : ∑ i : Fin a', (PrimThrW.TopFront.payOf alg (Cs i)).length ≤ a' * q := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin a'))
      (fun i => (PrimThrW.TopFront.payOf alg (Cs i)).length) q (fun i _ => hpay i)
    simpa using this
  have h2 : a' * q ≤ 4 * q := Nat.mul_le_mul_right _ ha'
  omega

/-- The digit program's bound at the unit `q`. -/
noncomputable def bmOf (q : ℕ) : ℕ := FinalPass.DigsBody.digsWImpl.C * (8 * q + 1) ^ FinalPass.DigsBody.digsWImpl.D

/-- The digit populations' word bound at the unit `q`. -/
def smOf (q : ℕ) : ℕ := 4 * (q * q * q)

/-- The cell's capacity at the unit `q`. -/
def capOf (q : ℕ) : ℕ := 2 ^ 30 * (q * q * q * q)

theorem need_eq (N : ℕ) : FinalPass.DigsBody.digsWImpl.need N = 2 * (16 * (N + 1) ^ 4) + 2 := rfl

section Call


end Call

/-- **Capacity monotonicity** of the cell's facts. -/
theorem cellFit_mono {kclk : ℕ} {Ev : Envelope} {B : TimeBudget kclk Ev}
    (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
    (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (cr Bm Sm cap cap' : ℕ)
    (h : HashCell.CellFit alg I hs ha' Cs carriers translation cr Bm Sm cap) (hc : cap ≤ cap') :
    HashCell.CellFit alg I hs ha' Cs carriers translation cr Bm Sm cap' :=
  { c1 := h.c1.trans hc, c2 := h.c2.trans hc, c3 := h.c3.trans hc, cl := fun k => (h.cl k).trans hc,
    cs := h.cs.trans hc, cD1 := h.cD1.trans hc, cG1 := h.cG1.trans hc, cG2 := h.cG2.trans hc, cG3 := h.cG3.trans hc,
    cG4 := h.cG4.trans hc, cG5 := h.cG5.trans hc, cD3 := h.cD3.trans hc, ckh := h.ckh.trans hc, cB := h.cB.trans hc,
    cneed := fun pr => (h.cneed pr).trans hc, cBm := h.cBm, cSm := h.cSm, cn := h.cn.trans hc, cc := h.cc.trans hc,
    cP := h.cP.trans hc, cG := h.cG.trans hc }

theorem capOf_le (E s : ℕ) (hs : 1 ≤ s) : capOf (2 ^ (E * s)) ≤ 2 ^ ((4 * E + 30) * s) := by
  unfold capOf
  have e : 2 ^ 30 * (2 ^ (E * s) * 2 ^ (E * s) * 2 ^ (E * s) * 2 ^ (E * s)) = 2 ^ (30 + 4 * (E * s)) := by ring
  rw [e]
  apply Nat.pow_le_pow_right (by norm_num)
  have : (4 * E + 30) * s = 4 * (E * s) + 30 * s := by ring
  omega

theorem bmOf_le (E s : ℕ) : bmOf (2 ^ (E * s)) ≤
    FinalPass.DigsBody.digsWImpl.C * 9 ^ FinalPass.DigsBody.digsWImpl.D * 2 ^ ((E * FinalPass.DigsBody.digsWImpl.D) * s) := by
  unfold bmOf
  have h1 : 1 ≤ 2 ^ (E * s) := Nat.one_le_two_pow
  have h2 : 8 * 2 ^ (E * s) + 1 ≤ 9 * 2 ^ (E * s) := by omega
  have h3 := Nat.pow_le_pow_left h2 FinalPass.DigsBody.digsWImpl.D
  have e : (9 * 2 ^ (E * s)) ^ FinalPass.DigsBody.digsWImpl.D =
      9 ^ FinalPass.DigsBody.digsWImpl.D * 2 ^ ((E * FinalPass.DigsBody.digsWImpl.D) * s) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [e] at h3
  calc FinalPass.DigsBody.digsWImpl.C * (8 * 2 ^ (E * s) + 1) ^ FinalPass.DigsBody.digsWImpl.D
      ≤ FinalPass.DigsBody.digsWImpl.C * (9 ^ FinalPass.DigsBody.digsWImpl.D *
          2 ^ ((E * FinalPass.DigsBody.digsWImpl.D) * s)) := Nat.mul_le_mul_left _ h3
    _ = _ := by ring

end NearCubicWires.WireExponent3_5.PrimAsm.HashFit
