import Proof.Wire_3_5.FinalPass.SdSeed1

/-! # S4 (the seeds phase), part 18: the seeds' tables word and the seed loop's state (P3:2036-2101, 3044-3048)

The tables word `twW es L₀ L₁`: per filter seed `e` its two tables (`tb e k = tableWord (filterTable FP e Lₖ)`)
framed, then `0` (`twW_cons`, `twW_head`: its first bit says whether a seed follows); every seed's table of carrier
`k` has the same length (**`tab_len`**). `CarNT`: a carrier's streams but its table. **`SdInv`**: the seed loop's
state at accumulator `x`, relative to the loop's entry state `ωQ` (every kept stream, head, register but the saved
position and the flag, the numerator `frame (binary W x)`, the point's halves formatted, the tables' lengths, the
carriers, the scratch blank, both counters at `0`). **`cStat_tr`**: the center loop's static facts move to any state
agreeing on the kept streams, the heads and the registers below `200`.

Paper quantity of the main type: the filter seeds' tables `tableWord (filterTable FP e Lₖ)` (P3:2036-2101) as the
seed loop reads them. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)

/-! ## The tables -/

theorem len_flatMap_const {α : Type} (l : List α) (f : α → List Bool) (c : ℕ) (h : ∀ x ∈ l, (f x).length = c) :
    (l.flatMap f).length = l.length * c := by
  rw [List.length_flatMap, List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

/-- **Every seed's table has the same length.** -/
theorem tab_len (P : GapParams) (e : GapSeed P) (L : ℕ) :
    (tableWord (filterTable P e L)).length = P.walkLen * (2 + 128 * (2 * L + 2)) + 1 := by
  have h128 : ∀ vs ∈ filterTable P e L, vs.length = 128 := by
    intro vs hmem
    simp only [filterTable, List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    simp
  have hvw : ∀ vs ∈ filterTable P e L, (visitWord vs).length = 2 + 128 * (2 * L + 2) := fun vs hmem => by
    simp only [visitWord, List.length_cons, List.length_append, List.length_singleton]
    rw [len_flatMap_const vs copyWord (2 * L + 2) (fun cs hcs => by
      simp [copyWord, frame_eq_frameP, filterTable_lengths P e L vs hmem cs hcs] <;> omega), h128 vs hmem]
    simp only [List.length_nil]
    ring
  simp only [tableWord, List.length_append, List.length_singleton]
  rw [len_flatMap_const _ visitWord _ hvw]
  simp [filterTable]

/-- A seed's table of carrier `k` (length `Lₖ`). -/
def tb (FP : GapParams) (e : GapSeed FP) (L : ℕ) : List Bool := tableWord (filterTable FP e L)

/-- **The tables word**: per seed its two tables framed, then `0`. -/
def twW (FP : GapParams) (es : List (GapSeed FP)) (L0 L1 : ℕ) : List Bool :=
  es.flatMap (fun e => frame (tb FP e L0) ++ frame (tb FP e L1)) ++ [false]

theorem twW_cons (FP : GapParams) (e : GapSeed FP) (es : List (GapSeed FP)) (L0 L1 : ℕ) :
    twW FP (e :: es) L0 L1 = frameP (tb FP e L0) ++ false :: (frameP (tb FP e L1) ++ false :: twW FP es L0 L1) := by
  simp [twW, frame_eq_frameP]

theorem twW_head (FP : GapParams) (es : List (GapSeed FP)) (L0 L1 : ℕ) :
    (twW FP es L0 L1).getD 0 false = decide (es ≠ []) := by
  cases es with
  | nil => rfl
  | cons e es =>
    rw [twW_cons]
    have hne : tb FP e L0 ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [tb, tab_len] at this
      simp at this
    obtain ⟨b, t, hbt⟩ : ∃ b t, tb FP e L0 = b :: t := List.exists_cons_of_ne_nil hne
    rw [hbt]
    simp

/-! ## The seed loop's state -/

section Lay
variable {nw nn nsc nrs : ℕ}

/-- **A carrier's streams but its table.** -/
structure CarNT {n : ℕ} (X : Stars.Carrier n) (k : Fin 2) (ω : BS nw nn nsc nrs) : Prop where
  G : ω.st (tG k) = gatesW (PrimT.tabH X) (maskGates X)
  acc : ∃ A B : ℕ, ∃ ys : List Bool, ω.st (tPos k) = frameP (binary (PrimT.tabH X) A) ++ [false] ∧
    ω.st (tNeg k) = frameP (binary (PrimT.tabH X) B) ++ [false] ∧ ω.st (tX k) = ys ++ [false] ∧
    ys.length = 8 * (maskGates X).length
  Z : ω.st (tZ k) = List.replicate (2 * (maskGates X).length + 1) false

/-- **The seed loop's state** at accumulator `x`, relative to the loop's entry state `ωQ`. -/
structure SdInv (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (W x : ℕ)
    (ωQ ω : BS nw nn nsc nrs) : Prop where
  st : ∀ i, KeptC i → i ≠ tT 0 → i ≠ tT 1 → ω.st i = ωQ.st i
  sh : ω.sh = ωQ.sh
  val : ∀ q, q ≠ rgP → q ≠ fS → ω.val q = ωQ.val q
  cell : ω.cell = ωQ.cell
  Nw : ω.st tN = frame (binary W x)
  U : ∃ Y : List Bool, ω.st tU = frameP Y ++ [false] ∧ Y.length = P.n
  V : ∃ Y : List Bool, ω.st tV = frameP Y ++ [false] ∧ Y.length = P.n
  C : ∃ Y : List Bool, ω.st tC = frameP Y ++ [false] ∧ Y.length = P.n
  T : ∀ k : Fin 2, (ω.st (tT k)).length = FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers k.val + 2)) + 1
  car : ∀ (k : Fin 2) (h : k.val < carriers.length), CarNT (carriers.get ⟨k.val, h⟩) k ω
  sc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false
  cc : CntAt false (dR P) 0 0 ω
  cr : CntAt true (dRow P) 0 0 ω

theorem cStat_tr (cap : ℕ) (FP : GapParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (P : StarParams)
    (σT : P.Translation) {N : ℕ} (ps : List (Fin N × Fin N)) (s bb h tl : ℕ) (ωQ ω : BS nw nn nsc nrs)
    (hR : CStat cap FP carriers P σT ps s bb h tl ωQ)
    (hst : ∀ i, KeptC i → i ≠ tT 0 → i ≠ tT 1 → ω.st i = ωQ.st i) (hsh : ω.sh = ωQ.sh)
    (hv : ∀ (j : ℕ) (hj : j < 220), j < 200 → ω.val (brg j hj) = ωQ.val (brg j hj)) :
    CStat cap FP carriers P σT ps s bb h tl ω := by
  have kT : ∀ (j : ℕ) (hj : j < 47), j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 8 → j ≠ 9 → j ≠ 25 → j ≠ 26 →
      (j < 10 ∨ 18 ≤ j) → (j < 18 ∨ 25 ≤ j) → ω.st (bst j hj) = ωQ.st (bst j hj) :=
    fun j hj h0 h1 h2 h3 h8 h9 h25 h26 hm hs => hst _
      ⟨kept_bst j hj h0 h2 h3 hm hs, by simp only [tC]; apply bst_ne; omega, by simp only [tRow]; apply bst_ne; omega,
        by simp only [tCol]; apply bst_ne; omega⟩
      (by simp only [tT]; apply bst_ne; simp; omega) (by simp only [tT]; apply bst_ne; simp; omega)
  have k10 : ∀ j (hj : j < 47), 26 < j → j ≠ 32 → j ≠ 33 → ω.st (bst j hj) = ωQ.st (bst j hj) := fun j hj h1 h2 h3 =>
    kT j hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  refine
    { Sp := ?_, Thr := ?_, sh := ?_, ms := ?_, cap2 := hR.cap2, M := ?_, Pf := ?_, acc := ?_, ac := ?_,
      dec := ?_, off := ?_, cB := ?_, cS := ?_, cH := ?_, cL := ?_, cR := ?_, cZ := ?_, I := ?_, cnt := ?_ }
  · rw [show (tSp : Fin (bns nw nsc + 1)) = bst 4 (by omega) from rfl,
      kT 4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
    exact hR.Sp
  · rw [show (tThr : Fin (bns nw nsc + 1)) = bst 36 (by omega) from rfl, k10 36 _ (by omega) (by omega) (by omega)]
    exact hR.Thr
  · intro i; rw [hsh]; exact hR.sh i
  · intro j hj; rw [hv (122 + j) (by omega) (by omega)]; exact hR.ms j hj
  · intro k
    have := k.isLt
    rw [show (rM k : Fin (bnr nn nrs)) = brg (118 + k.val) (by omega) from rfl, hv (118 + k.val) (by omega) (by omega)]
    exact hR.M k
  · intro k
    have := k.isLt
    rw [show (rP k : Fin (bnr nn nrs)) = brg (120 + k.val) (by omega) from rfl, hv (120 + k.val) (by omega) (by omega)]
    exact hR.Pf k
  · rw [show (rAcc : Fin (bnr nn nrs)) = brg 0 (by omega) from rfl, hv 0 (by omega) (by omega)]; exact hR.acc
  · rw [show (rAc : Fin (bnr nn nrs)) = brg 154 (by omega) from rfl, hv 154 (by omega) (by omega)]; exact hR.ac
  · intro q
    have := q.isLt
    rw [show (frD q : Fin (bnr nn nrs)) = brg (156 + q.val) (by omega) from rfl, hv (156 + q.val) (by omega) (by omega)]
    exact hR.dec q
  · rw [show (ctrS 0 : Fin (bns nw nsc + 1)) = bst 30 (by omega) from rfl, k10 30 _ (by omega) (by omega) (by omega)]
    exact hR.off
  · rw [show (ctrR 0 : Fin (bnr nn nrs)) = brg 168 (by omega) from rfl, hv 168 (by omega) (by omega)]; exact hR.cB
  · rw [show (ctrR 1 : Fin (bnr nn nrs)) = brg 169 (by omega) from rfl, hv 169 (by omega) (by omega)]; exact hR.cS
  · rw [show (ctrR 2 : Fin (bnr nn nrs)) = brg 170 (by omega) from rfl, hv 170 (by omega) (by omega)]; exact hR.cH
  · rw [show (ctrR 3 : Fin (bnr nn nrs)) = brg 171 (by omega) from rfl, hv 171 (by omega) (by omega)]; exact hR.cL
  · rw [show (ctrR 4 : Fin (bnr nn nrs)) = brg 172 (by omega) from rfl, hv 172 (by omega) (by omega)]; exact hR.cR
  · intro i hi
    have := i.isLt
    rw [show (ctrR i : Fin (bnr nn nrs)) = brg (168 + i.val) (by omega) from rfl, hv (168 + i.val) (by omega) (by omega)]
    exact hR.cZ i hi
  · rw [show (tI : Fin (bns nw nsc + 1)) = bst 31 (by omega) from rfl, k10 31 _ (by omega) (by omega) (by omega)]
    exact hR.I
  · intro b
    constructor
    · rw [show (cC b : Fin (bnr nn nrs)) = brg (if b then 197 else 194) (by split <;> omega) from rfl,
        hv (if b then 197 else 194) (by split <;> omega) (by split <;> omega)]
      exact (hR.cnt b).1
    · rw [show (cK b : Fin (bnr nn nrs)) = brg (if b then 199 else 196) (by split <;> omega) from rfl,
        hv (if b then 199 else 196) (by split <;> omega) (by split <;> omega)]
      exact (hR.cnt b).2

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
