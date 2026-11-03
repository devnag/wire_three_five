import Lean
import Proof.Wire_3_5.FinalPass.ThrSz5
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.BudgetIface
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.ThrSz6Base


noncomputable section
set_option maxRecDepth 4096


/-! # The THR word-size lemma, part 2: the primes, stage 4's table, the numbers; the theorem

From the call's THR numbers (`valsOf`, each `≤ K_t·(n+1)^{D_t}`): **`w5_le`** (the primes' word), **`w6_le`** (stage
4's table: the majorant's `M, J, t, B_*` are the numbers' `M, J, t, B_*`, `thrNumVals_A`), **`nums_le`** (`a`, `|𝒢|`,
`τ₀`, `|occs|`), and **`thrSize_poly`**: `ThrNumsPoly l → ∃ D, ∀ F, ∃ C, ∀ …, thrSize (thrCallOf …) ≤ C·(n+1)^D`.
Paper quantity: the call's size, polynomial in `n` with the degree fixed before the gate (P3:3069-3072, 3176-3178,
P3:3114-3115: "All powers of `n` are fixed before a fixed `r`"). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrSz
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

section Pieces2
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
  (hs : (Plan.callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

theorem w5_le (Kt Dt : ℕ) (hcut : (valsOf l F kclk coef A a ha n hs Cs carriers).cut ≤ Kt * (n + 1) ^ Dt) :
    (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 5).length ≤
      (Kt + 1) ^ 2 * (n + 1) ^ (2 * Dt) := by
  rw [ThrPt.thrWords_primes]
  refine (primesWord_le _).trans ?_
  have h1 : 1 ≤ (n + 1) ^ Dt := Nat.one_le_pow _ _ (by omega)
  have hc : (valsOf l F kclk coef A a ha n hs Cs carriers).cut + 1 ≤ (Kt + 1) * (n + 1) ^ Dt := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  calc _ ≤ ((Kt + 1) * (n + 1) ^ Dt) * ((Kt + 1) * (n + 1) ^ Dt) := Nat.mul_le_mul hc hc
    _ = (Kt + 1) ^ 2 * (n + 1) ^ (2 * Dt) := by rw [two_mul, pow_add]; ring

theorem J_eq : Primitive.thrCallJ (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers =
    (valsOf l F kclk coef A a ha n hs Cs carriers).J := by
  unfold Primitive.thrCallJ
  rw [← PrimThrW.Joins.thrNumVals_A (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers.length
    (capOfT l F kclk coef A a ha n)]
  rfl

theorem t_eq : Primitive.thrCallT (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers =
    (valsOf l F kclk coef A a ha n hs Cs carriers).tt := by
  unfold Primitive.thrCallT
  rw [← PrimThrW.Joins.thrNumVals_A (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers.length
    (capOfT l F kclk coef A a ha n)]
  rfl

/-- The call's majorant parameters. -/
noncomputable abbrev MPof : Filters.MajorantParams :=
  Primitive.thrMajorant ((Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    ((Plan.callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (Primitive.thrCallDen (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs)
    (Primitive.thrCallE (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallT (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallJ (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers)

theorem DM_eq : (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).D.M =
    (MPof l F kclk coef A a ha n hs Cs carriers).M := rfl

theorem DJ_eq : (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).D.J =
    (MPof l F kclk coef A a ha n hs Cs carriers).J := rfl

theorem DW_eq : (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).D.W =
    (MPof l F kclk coef A a ha n hs Cs carriers).W := rfl

theorem w6_le (Kt Dt : ℕ) (hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt) :
    (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 6).length ≤
      levK Kt * (n + 1) ^ (3 * Dt) := by
  rw [ThrPt.thrWords_level, DM_eq, DJ_eq, DW_eq]
  have hM : (MPof l F kclk coef A a ha n hs Cs carriers).M ≤ Kt * (n + 1) ^ Dt := hv 6
  have hJ : (MPof l F kclk coef A a ha n hs Cs carriers).J ≤ Kt * (n + 1) ^ Dt := by
    show Primitive.thrCallJ (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers ≤ _
    rw [J_eq]; exact hv 9
  have ht : (MPof l F kclk coef A a ha n hs Cs carriers).t ≤ Kt * (n + 1) ^ Dt := by
    show Primitive.thrCallT (gate0 l F).alg (Plan.callInputs l F kclk coef A a ha) hs Cs carriers ≤ _
    rw [t_eq]; exact hv 10
  have hB : (MPof l F kclk coef A a ha n hs Cs carriers).Bstar ≤ Kt * (n + 1) ^ Dt := hv 8
  have hL : (Primitive.thrOccs (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).P
      (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).Cs).length ≤ Kt * (n + 1) ^ Dt := hv 6
  exact level_kn (MPof l F kclk coef A a ha n hs Cs carriers) _
    (ListEval.rowsOf (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).D _)
    (fun j => ThrPt.rowsOf_len _ _ j) (by omega) hM hJ ht hB hL

theorem nums1 (Kt Dt : ℕ) (hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt) :
    Seams.thrNums (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 1 ≤ Kt * (n + 1) ^ Dt := by
  convert hv 0 using 1
  simp [Seams.thrNums, valsOf, kOf, Seams.thrCallOf, PrimThrW.Joins.thrNumVals, PrimThrW.Joins.ThrNumVals.get]
  exact (Fintype.card_congr (Equiv.refl _)).trans ((ThrPt.card_thrEq
    ((Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg).trans (by simp [ThrPt.gN]))

theorem nums2 (Kt Dt : ℕ) (hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt) :
    Seams.thrNums (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 2 ≤ Kt * (n + 1) ^ Dt := by
  convert hv 5 using 1
  simp [Seams.thrNums, valsOf, kOf, Seams.thrCallOf, Primitive.thrCallDen, PrimThrW.Joins.thrNumVals,
    PrimThrW.Joins.ThrNumVals.get]
  rfl

theorem nums3 (Kt Dt : ℕ) (hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt) :
    Seams.thrNums (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 3 ≤ Kt * (n + 1) ^ Dt := hv 6

theorem nums_le (Kt Dt : ℕ) (hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt) :
    ∑ i, Seams.thrNums (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) i ≤
      (4 + 3 * Kt) * (n + 1) ^ Dt := by
  rw [Fin.sum_univ_four]
  have h0 : Seams.thrNums (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 0 ≤ 4 := ha'
  have h1 := nums1 l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt hv
  have h2 := nums2 l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt hv
  have h3 := nums3 l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt hv
  have hp : 1 ≤ (n + 1) ^ Dt := Nat.one_le_pow _ _ (by omega)
  have e : (4 + 3 * Kt) * (n + 1) ^ Dt = 4 * (n + 1) ^ Dt + 3 * (Kt * (n + 1) ^ Dt) := by ring
  rw [e]
  omega

end Pieces2

/-- The exponent. -/
noncomputable def sizeD (l : Literals) (Dt : ℕ) : ℕ := 106 + CallIndex.algX l + 3 * Dt

/-- The coefficient. -/
noncomputable def sizeC (l : Literals) (Kt : ℕ) : ℕ :=
  1 + 2253 + (11 + 2 * 2 ^ CallIndex.algX l) + (11 + 2 * 2 ^ CallIndex.algX l) + (11 + 2 * 2 ^ CallIndex.algX l) +
    (11 + 2 * 2 ^ CallIndex.algX l) + (Kt + 1) ^ 2 + levK Kt + (4 + 3 * Kt)

/-- **The THR word-size lemma.** -/
theorem thrSize_poly (l : Literals) (hT : BudgetIface.ThrNumsPoly l) :
    ∃ D : ℕ, ∀ F : GateFree l, ∃ C : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
      (hs : (Plan.callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ),
      carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
      ThrPt.thrSize (Seams.thrCallOf (Plan.callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers
        translation) ≤ C * (n + 1) ^ D := by
  obtain ⟨Dt, hDt⟩ := hT (CallIndexR.capZR l)
  refine ⟨sizeD l Dt, fun F => ?_⟩
  obtain ⟨Kt, hKt⟩ := hDt (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F
  refine ⟨sizeC l Kt, fun kclk coef A a ha n hs a' ha' Cs carriers translation hcar hd => ?_⟩
  have hv : ∀ i : Fin 14, (valsOf l F kclk coef A a ha n hs Cs carriers).get i ≤ Kt * (n + 1) ^ Dt := fun i =>
    hKt kclk coef A a ha n hs Cs carriers _ ha' hcar hd (cap_kn l F kclk coef A a ha n) _
      (mem_nums l F kclk coef A a ha n hs Cs carriers i)
  have hN : 1 ≤ n + 1 := by omega
  have p0 : n ≤ 1 * (n + 1) ^ sizeD l Dt := kn_mono hN (kn_one n 1 (by rw [pow_one]; omega)) (by unfold sizeD; omega)
  have p1 := kn_mono hN (w0_le l F kclk coef A a ha n hs ha' Cs carriers translation hd)
    (show 79 ≤ sizeD l Dt by unfold sizeD; omega)
  have pp : ∀ j : Fin 4, (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation)
      ⟨j.val + 1, by omega⟩).length ≤ (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ sizeD l Dt := fun j =>
    kn_mono hN (pay_le' l F kclk coef A a ha n hs ha' Cs carriers translation hd j) (by unfold sizeD; omega)
  have p6 := kn_mono hN (w5_le l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt (hv 2))
    (show 2 * Dt ≤ sizeD l Dt by unfold sizeD; omega)
  have p7 := kn_mono hN (w6_le l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt hv)
    (show 3 * Dt ≤ sizeD l Dt by unfold sizeD; omega)
  have p8 := kn_mono hN (nums_le l F kclk coef A a ha n hs ha' Cs carriers translation Kt Dt hv)
    (show Dt ≤ sizeD l Dt by unfold sizeD; omega)
  have p2 := pp 0
  have p3 := pp 1
  have p4 := pp 2
  have p5 := pp 3
  have q2 : (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 1).length ≤
      (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ sizeD l Dt := p2
  have q3 : (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 2).length ≤
      (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ sizeD l Dt := p3
  have q4 : (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 3).length ≤
      (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ sizeD l Dt := p4
  have q5 : (Seams.thrWords (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) 4).length ≤
      (11 + 2 * 2 ^ CallIndex.algX l) * (n + 1) ^ sizeD l Dt := p5
  show ThrPt.thrSize (kOf l F kclk coef A a ha n hs ha' Cs carriers translation) ≤ _
  have hPn : (kOf l F kclk coef A a ha n hs ha' Cs carriers translation).P.n = n := rfl
  unfold ThrPt.thrSize
  rw [Fin.sum_univ_seven, hPn]
  unfold sizeC
  simp only [Nat.add_mul] at q2 q3 q4 q5 p8 ⊢
  omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrSz

end
