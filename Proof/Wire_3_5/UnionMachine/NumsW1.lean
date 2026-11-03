import Lean
import Proof.Wire_3_5.UnionMachine.NumsA4
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsW1Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW assembly, part 1: `V` is polynomial in the input, and the denominator split

P3:3044-3048 ("Fixed polynomially many states, filter seeds, row lookups, and requested means are absorbed by
`poly(n)`"), P3:3170-3181: phase (d) writes `max(2^e·V, 1)` in `T_f`-bit binary and needs `T + e + V + 2` below its
capacity, a polynomial in `X = |fpIn| + 1`. At every request of the family (every call is on-star):

* `V ≤ K_V·X^{D_V}`: SYM `V = |E|·|FlatSeed|·Q` (`gapSeed_leR`, `vsym_le`), THR `V = |PrimeIndex(cut)|·|E|·Q`
  (`cut_le`, `card_prime_le`), `Q ≤ |fpIn|` (the printed sample; `q_le_fpIn`, `q_le_fpIn_thr`);
* **`denSplit`**: `fpDen r = max (2^{eOf r}·vOf r) 1` (`|centers| = 2^{n−k}`, `card_centers`).

* `EV`, `DV`, `KV`, `q_le_fpIn_thr`, **`vOf_le`**, **`denSplit`**.

Paper quantities of the main type: `V`, the final pass's denominator `Den = 2^{n−k}·V` (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- `V`'s exponent in `n + 2` and its degree and coefficient in `X`. -/
noncomputable def EV (fe : ℕ) : ℕ := FinalPass.Sd.R.ZV l + CallIndexR.gapZR l fe
noncomputable def DV (fe : ℕ) : ℕ := EV l fe + 1
noncomputable def KV : ℕ := 2 * CallIndexR.gapK F.cr * (CallIndexR.flatK F.cr + 1) * 2 ^ EV l F.filterErrDeg

/-- **`Q ≤ |fpIn|`** at a THR request (the printed sample). -/
theorem q_le_fpIn_thr {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤
      (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length := by
  show _ ≤ (PrimRequest.word ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ++
    seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩).length
  simp only [seedWord, dif_pos hs]
  rw [List.length_append, List.length_append, S6Sizes.sampleWord_len, List.length_ofFn]
  have e : (SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).Q =
      SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs := rfl
  rw [e]
  have := Nat.le_mul_of_pos_right (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (by omega : 0 < 4 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 2)
  omega

/-- **`V` is polynomial in the input**: `vOf r ≤ K_V·(|fpIn|+1)^{D_V}`. -/
theorem vOf_le (r : FReq l F kclk coef A a ha) :
    NumsPh2.vOf l F kclk coef A a ha r ≤ KV l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DV l F.filterErrDeg := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hnX := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a) (ha := ha)
    ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1 :=
    ⟨_, rfl⟩
  rw [← hXd]
  have hG := CallIndexR.gapSeed_leR l F kclk coef A a ha mode n
  have hKV : KV l F * X ^ DV l F.filterErrDeg = 2 * CallIndexR.gapK F.cr * (CallIndexR.flatK F.cr + 1) *
      2 ^ (FinalPass.Sd.R.ZV l + CallIndexR.gapZR l F.filterErrDeg) *
      X ^ (FinalPass.Sd.R.ZV l + CallIndexR.gapZR l F.filterErrDeg + 1) := rfl
  rw [hKV]
  cases mode with
  | sym =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
    have hV := FinalPass.Sd.R.vsym_le l F kclk coef A a ha n ha' Cs carriers hd hcar
    have hQ := q_le_fpIn l F kclk coef A a ha ha' Cs carriers translation hcall hs
    have hnX' : n + 1 ≤ X := by rw [hXd]; exact Nat.succ_le_succ hnX
    have hQX : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤ X := by
      rw [hXd]; exact Nat.le_succ_of_le hQ
    rw [vOf_sym l F kclk coef A a ha ha' Cs carriers translation hcall hs]
    exact v_arith n X _ _ _ _ _ _ _ hnX' hG
      (le_trans hV (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))) hQX
  | thr =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
    have hcut := CallIndex.cut_le l F kclk coef A a ha n hs ha' Cs hd
    have hpr := FinalPass.Sd.card_prime_le (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
    have hpz : (n + 2) ^ (10 * CallIndex.algX l + 32) ≤ (n + 2) ^ FinalPass.Sd.R.ZV l :=
      Nat.pow_le_pow_right (by omega) (by unfold FinalPass.Sd.R.ZV; omega)
    have hp1 : 1 ≤ (n + 2) ^ FinalPass.Sd.R.ZV l := Nat.one_le_pow _ _ (by omega)
    have hQ := q_le_fpIn_thr l F kclk coef A a ha ha' Cs carriers translation hcall hs
    have hnX' : n + 1 ≤ X := by rw [hXd]; exact Nat.succ_le_succ hnX
    have hQX : SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤ X := by
      rw [hXd]; exact Nat.le_succ_of_le hQ
    simp only [NumsPh2.vOf, NumsPh2.vOfReq, dif_pos hs]
    have hQ' : ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation
        hs).Q ≤ X := by
      exact hQX
    have hP : Fintype.card (PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤
        2 * (CallIndexR.flatK F.cr + 1) * (n + 2) ^ FinalPass.Sd.R.ZV l := by
      have h2 : 2 * (n + 2) ^ FinalPass.Sd.R.ZV l ≤ 2 * (CallIndexR.flatK F.cr + 1) * (n + 2) ^ FinalPass.Sd.R.ZV l :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rw [show ∀ p g q : ℕ, p * g * q = g * p * q from fun p g q => by ring]
    exact v_arith n X _ _ _ _ _ _ _ hnX' hG hP hQ'

/-- **The denominator split** at every request of the family. -/
theorem denSplit : NumsPh2.DenSplit l F kclk coef A a ha := by
  intro r
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hcen : Fintype.card {c // ((callInputs l F kclk coef A a ha).starParams n hs).IsCenter
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) c} =
      2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) :=
    Shared.StarParams.card_centers _ _
  show max (FinalPass.NumDen.denRaw (callInputs l F kclk coef A a ha) (gate0 l F).alg
    ⟨n, mode, a', ha', Cs, carriers, translation⟩) 1 = _
  congr 1
  cases mode with
  | sym =>
    simp only [FinalPass.NumDen.denRaw, dif_pos hs, FinalPass.NumDen.symDen, Fintype.card_prod, NumsPh2.vOf,
      NumsPh2.vOfReq, NumsPh2.eOf]
    rw [hcen]
    ring
  | thr =>
    simp only [FinalPass.NumDen.denRaw, dif_pos hs, FinalPass.NumDen.thrDen, NumsPh2.vOf, NumsPh2.vOfReq,
      NumsPh2.eOf]
    rw [hcen]
    ring

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
