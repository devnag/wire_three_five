import Proof.Wire_3_5.FinalPass.SymCap2

/-! # The SYM batch's facts at a call (for `hpre_sym`, `symHcost_of`)

P3:2477-2496 (row:sym) and P3:3011-3016 at a SYM call: the SYM batch (`symExprs`, `R = |carriers| + 2a′` rows
per entry) meets `SampShape.BatchFacts` with the factor counts `f r = 1` (filter rows) or the walk `w` (population
rows) (`sym_rows_factors`), the degree bound `symDg` and the atoms `< |flips|·|pool|` (`sym_factors_ok`), `±1`
coefficients (`sym_coef_pm1`) and at most `T = (M+1)²2^w ≤ 2^{63(k+L)}` terms per row (`sym_row_terms_le`); the
child's factor count `8·Σ_r f r` is the free number `m` whenever the call has rows (`sym_hmf`), and `8` (= `m`, the
padded batch's single constant row) at a degenerate call (`pad_hmf`).

* `symF`, `sum_split`, **`symBatchFacts`**, **`symT_le`**, **`sym_hmf`**, **`pad_hmf`**.

Paper quantity of the main type: the SYM rows' shape at a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

theorem sum_split (N M w : ℕ) : ((List.range (N + M)).map fun r => if r < N then 1 else w).sum = N + M * w := by
  rw [List.range_add, List.map_append, List.sum_append]
  have h1 : ((List.range N).map fun r => if r < N then 1 else w).sum = N := by
    rw [List.map_congr_left (g := fun _ => 1) (fun r hr => if_pos (List.mem_range.mp hr))]
    simp
  have h2 : (((List.range M).map (N + ·)).map fun r => if r < N then 1 else w).sum = M * w := by
    rw [List.map_map, List.map_congr_left (g := fun _ => w) (fun r _ => by simp)]
    simp
  rw [h1, h2]

section Gate
variable (l : Literals) (F : GateFree l)

/-- The SYM rows' factor counts by row position (`sym_rows_factors`). -/
noncomputable def symF (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) : ℕ → ℕ :=
  fun r => if r < carriers.length then 1 else (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen

/-- **The SYM batch's facts.** -/
theorem symBatchFacts (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    SampShape.BatchFacts (symExprs (callInputs l F kclk coef A a ha) hs Cs carriers) (carriers.length + 2 * a')
      (symF l F kclk coef A a ha Cs carriers) (symDg l F kclk coef A a ha Cs carriers)
      ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
        (Records.symPool Cs carriers).length)
      (((symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).M + 1) ^ 2 *
        2 ^ (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen) := by
  have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length =
      4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
        2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := by
    simp [PrimT.C4Geo.flips]
  refine ⟨BShape.sym_rows_factors _ hs Cs carriers, fun V hV t ht p hp => ?_, BShape.sym_coef_pm1 _ hs Cs carriers,
    BShape.sym_row_terms_le _ hs Cs carriers⟩
  rw [hfl]
  exact BShape.sym_factors_ok _ hs Cs carriers V hV t ht p hp

/-- **The rows' term bound below `2^{63(k+L)}`.** -/
theorem symT_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation)) :
    ((symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).M + 1) ^ 2 *
        2 ^ (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen ≤
      2 ^ (63 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hN := n26_le n
  have hL1 := one_le_L n
  have hM : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).M + 1 ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 3) := by
    show (∑ i, (Cs i).bottomCount) + 1 ≤ _
    have h1 : ∑ i, (Cs i).bottomCount ≤ a' * (n + 1) ^ 26 := by
      calc _ ≤ ∑ _i : Fin a', (n + 1) ^ 26 := Finset.sum_le_sum fun i _ => CallIndex.bottomCount_le (Cs i) (hd i)
        _ = _ := by simp
    have h2 := Nat.mul_le_mul_right ((n + 1) ^ 26) ha'
    rw [pow_add]
    have h3 : 1 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.one_le_two_pow
    norm_num
    omega
  have hw : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen ≤ Nat.clog 2 (n + 2) + 4 := by
    show 2 * ((1 * Nat.clog 2 (n + 2) + 5) / 4) + 1 ≤ _
    omega
  have h1 := pow_mono_mul 2 hM
  have h2 : 2 ^ (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen ≤
      2 ^ (Nat.clog 2 (n + 2) + 4) := Nat.pow_le_pow_right (by norm_num) hw
  calc _ ≤ 2 ^ (2 * (26 * Nat.clog 2 (n + 2) + 3)) * 2 ^ (Nat.clog 2 (n + 2) + 4) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (2 * (26 * Nat.clog 2 (n + 2) + 3) + (Nat.clog 2 (n + 2) + 4)) := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The child's factor count is `m`** at a call with rows. -/
theorem sym_hmf (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (h1 : 1 ≤ carriers.length + 2 * a') :
    8 * ((List.range (carriers.length + 2 * a')).map (symF l F kclk coef A a ha Cs carriers)).sum =
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 := by
  unfold symF
  rw [sum_split]
  have hw : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen =
      W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) := by
    show 2 * ((1 * Nat.clog 2 (n + 2) + 5) / 4) + 1 = 2 * ((Nat.clog 2 (n + 2) + 5) / 4) + 1
    rw [Nat.one_mul]
  rw [hw]
  show _ = max (mOf (symK2 c).k (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) 8
  unfold mOf
  show _ = max (8 * carriers.length + 16 * (a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) +
    0 * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) + 0 * a' +
    0 * (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs).M + 0) 8
  have hW1 : 1 ≤ W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) := by unfold W; omega
  have e : 2 * a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) =
      2 * (a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) := by ring
  have hpos : a' ≤ a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) :=
    Nat.le_mul_of_pos_right _ hW1
  omega

/-- **The padded batch's factor count is `m = 8`** at a degenerate call. -/
theorem pad_hmf (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (h0 : carriers.length + 2 * a' = 0) :
    8 * ((List.range 1).map fun _ => 1).sum =
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 := by
  show _ = max (mOf (symK2 c).k (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) 8
  unfold mOf
  show _ = max (8 * carriers.length + 16 * (a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) +
    0 * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) + 0 * a' +
    0 * (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs).M + 0) 8
  have hc0 : carriers.length = 0 := by omega
  have hW0 : a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) ≤ 0 :=
    (Nat.mul_le_mul_right _ (show a' ≤ 0 by omega)).trans (by rw [Nat.zero_mul])
  have hs1 : ((List.range 1).map fun (_ : ℕ) => (1 : ℕ)).sum = 1 := rfl
  rw [hs1]
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
