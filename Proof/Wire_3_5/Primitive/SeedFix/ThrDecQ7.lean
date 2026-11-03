import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ6
import Proof.Wire_3_5.Primitive.Writers.SymDecCall
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ7Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 THR decode front, packaging part 7: the call's index links

At a THR call, the front's arithmetic on the unit index `j` (`t = j / EU / N²`, then `t / Σp / |𝒢|`, `t / Σp mod |𝒢|`,
`t mod Σp`) is `Enum.thrIndexEquiv`'s mixed radix (seed major, then the selection, then the prime row): the seed's
index, the selection's index and the prime row `(p, s)` of `ThrDecOut` (`seed_val`, `sel_val`, `prime_val`). The
unit count `thrTOT` is the front's `2^{seedBits}·|𝒢|·Σp·2^{2k_h}·EU` (`tot_eq`).

Paper quantity of the main type: the THR state `(e, g, p, s)` of a request unit (P3:2543-2558, 2573-2580). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine

section Nums2

end Nums2

section Idx
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)

/-- The seed's part of the mixed radix. -/
theorem seed_fin (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    (Enum.gapSeedEquiv ((callInputs l F kclk coef A a ha).filterParams .thr n)
      ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).1).val =
      t / ((∏ i : Fin (List.ofFn Cs).length,
        (RepairOrdinary.ThresholdRows.children (gate0 l F).alg ((List.ofFn Cs).get i)).length) *
        ∑ i : Fin (SupplierPrime.primesUpTo (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)).card,
          ((Enum.primeEquiv (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) i) : ℕ)) := by
  unfold Enum.thrIndexEquiv
  simp only [Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply,
    Prod.map_fst, Equiv.apply_symm_apply]
  rfl

/-- The selection's part of the mixed radix. -/
theorem sel_fin (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    (Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).2.1).val =
      t % ((∏ i : Fin (List.ofFn Cs).length,
        (RepairOrdinary.ThresholdRows.children (gate0 l F).alg ((List.ofFn Cs).get i)).length) *
        ∑ i : Fin (SupplierPrime.primesUpTo (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)).card,
          ((Enum.primeEquiv (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) i) : ℕ)) /
        ∑ i : Fin (SupplierPrime.primesUpTo (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)).card,
          ((Enum.primeEquiv (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) i) : ℕ) := by
  unfold Enum.thrIndexEquiv
  simp only [Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply,
    Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
  rfl

/-- The prime row's part of the mixed radix. -/
theorem prow_fin (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).2.2 =
      (Enum.primeRowEquiv (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)).symm
        (Fin.modNat (Fin.modNat ⟨t, ht⟩)) := by
  unfold Enum.thrIndexEquiv
  simp only [Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply,
    Prod.map_fst, Prod.map_snd]
  rfl

section Vals
variable (carriers : List (Stars.Carrier n))

theorem prod_eq : (∏ i : Fin (List.ofFn Cs).length,
    (RepairOrdinary.ThresholdRows.children (gate0 l F).alg ((List.ofFn Cs).get i)).length) =
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 2 0 := by
  rw [hashNums_get2, ThrQ.card_thrEq]
  rfl

theorem sum_eq : (∑ i : Fin (SupplierPrime.primesUpTo (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)).card,
    ((Enum.primeEquiv (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) i) : ℕ)) =
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 := by
  rw [hashNums_get6, Enum.primeRows_sum]
  rfl

/-- **The seed's index** is the front's `t / Σp / |𝒢|`. -/
theorem seed_val (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    (Enum.gapSeedEquiv ((callInputs l F kclk coef A a ha).filterParams .thr n)
      ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).1).val =
    t / (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 /
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 2 0 := by
  rw [seed_fin, prod_eq l F kclk coef A a ha hs Cs carriers, sum_eq l F kclk coef A a ha hs Cs carriers,
    Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- **The selection's index** is the front's `t / Σp mod |𝒢|`. -/
theorem sel_val (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) :
    (Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      ((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).2.1).val =
    t / (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 %
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 2 0 := by
  rw [sel_fin, prod_eq l F kclk coef A a ha hs Cs carriers, sum_eq l F kclk coef A a ha hs Cs carriers,
    Nat.mul_comm, Nat.mod_mul_right_div_self]

/-- **The prime row** is the front's scan item `p_t'` and residue `t mod Σp − Σ_{j<t'} p_j`. -/
theorem prime_val (t : ℕ) (ht : t < Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (t' : ℕ)
    (h1 : ((PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 carriers.length
      ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)).cut).take t').sum ≤
      t % (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0)
    (h2 : t % (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 <
      ((PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 carriers.length
      ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)).cut).take (t' + 1)).sum) :
    ((((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).2.2.1 : ℕ) =
      (PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 carriers.length
        ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)).cut).getD t' 0) ∧
    (((Enum.thrIndexEquiv (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).symm ⟨t, ht⟩).2.2.2).val =
      t % (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 -
      ((PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 carriers.length
        ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 1 0)).cut).take t').sum := by
  rw [prow_fin]
  have hv : (Fin.modNat (Fin.modNat (⟨t, ht⟩ : Fin (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)))).val =
      t % (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 := by
    rw [← sum_eq l F kclk coef A a ha hs Cs carriers]
    show t % _ % _ = _
    rw [Nat.mod_mul_left_mod]
  rw [← hv] at h1 h2 ⊢
  exact primeRow_symm _ _ t' h1 h2

/-- The star rows per state `N² = 2^{2k_h}`. -/
theorem n2_eq : ThrDec.thrN2 l F kclk coef A a ha hs =
    2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
      (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) := by
  unfold ThrDec.thrN2 SeedFix.callKh
  rw [← pow_mul, Nat.mul_comm]

/-- **The call's units** are the front's `2^{seedBits}·|𝒢|·Σp·2^{2k_h}·EU`. -/
theorem tot_eq : ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers =
    2 ^ ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits *
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 2 0 *
      (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0 *
      2 ^ (2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
        (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))) *
      ((carriers.length + 1) * 3 + 2) := by
  unfold ThrDec.thrTOT Enum.thrNT
  rw [n2_eq, card_gapSeed, prod_eq l F kclk coef A a ha hs Cs carriers, sum_eq l F kclk coef A a ha hs Cs carriers]
  unfold ThrDec.thrEU
  ring

/-- **The RADIX setup's twenty values** are the front's registers. -/
theorem rad_vec (hk : carriers.length ≤ 2) (gi p s row : ℕ) :
    PrimThrW.RadSetup.radVals l F kclk coef A a ha hs Cs carriers gi p s row =
      ![gi, p, s, row,
        2 * ((carriers.map List.length).getD 0 0 + (carriers.map List.length).getD 1 0) +
          (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
            (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 8 0,
        2 * ((carriers.map List.length).getD 0 0 + (carriers.map List.length).getD 1 0),
        ((callInputs l F kclk coef A a ha).starParams n hs).n,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 2 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 3 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 4 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 5 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 6 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 7 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 8 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 9 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 10 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 11 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 12 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 14 0,
        (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD 15 0] := by
  unfold PrimThrW.RadSetup.radVals
  rw [thr_pool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap hk,
    thr_off ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers hk]
  simp only [ThrData.hashNums, ThrData.thrNumList, PrimThrW.Joins.ThrNumVals.get, List.getD_cons_succ,
    List.getD_cons_zero, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rfl

end Vals

end Idx

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF

end
