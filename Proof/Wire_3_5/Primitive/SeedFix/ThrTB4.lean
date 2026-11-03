import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB3Base
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrBBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB4Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 THRTAIL T-B, part 4: the data side of the THR shell at a call

The v4 shell's data width `V = C₂(n+1)^{D₂}` (the v4 data stage `S`, the fill of its input word): at
`D₂ = D₀ + d_T + D_{vS} + 26`, `C₂ = C₀ + C_{vS} + 19(K_t(F) + 5)` it meets `ThrDataOK2` (`C4GateSym.thr_data_hyps` at
`needW n ≤ V`), the numbers' unary word (`|unaryList (hashNums ++ thrCounts)| ≤ V`), the stage's need (`S.need n ≤ V`
from `S.Kn ≤ C₀`, `S.Dn ≤ D₀`) and the stage's cost `cost3 ≤ C₀(3C₂+1)^{D₀}·(n+1)^{D₂·D₀}` (`cost3_le`).

* `dT2`, `cT2`; **`data_ok`**, **`data_cu`**, **`data_need`**, **`data_cost`**.

Paper quantity of the main type: the THR call's data word (P3:2543-2558, 3083-3086) within the writer's fill. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine

/-- The data width's exponent (from `(l, D₀)`). -/
noncomputable def dT2 (l : Literals) (D0 : ℕ) : ℕ := D0 + ThrDecF.dT l + C4GateSym.DvS + 26

/-- The data width's coefficient (from `(F, C₀)`). -/
noncomputable def cT2 (l : Literals) (F : GateFree l) (C0 : ℕ) : ℕ :=
  C0 + C4GateSym.CvS + 19 * (ThrDecF.kT l F + 5)

section Data
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

omit hcall hs in
theorem needW_le_V (D0 C0 : ℕ) : C4GateSym.needW n ≤ UnaryCalc.value (dT2 l D0) (cT2 l F C0) n := by
  have h := C4GateSym.needW_le n
  unfold UnaryCalc.value at h ⊢
  refine h.trans (Nat.mul_le_mul (by unfold cT2; omega) (pow_mono_exp (by unfold dT2; omega)))

omit hs in
/-- **`ThrDataOK2` at the data width.** -/
theorem data_ok (D0 C0 : ℕ) : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value (dT2 l D0) (cT2 l F C0) n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := C4GateSym.thr_data_hyps Cs carriers ha' hcall.2.2.2.1
    hcall.2.2.1 hcall.2.1 _ (needW_le_V l F (n := n) D0 C0)
  exact ⟨ha', hcall.2.2.2.1, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The numbers' unary word within the data width.** -/
theorem data_cu (D0 C0 : ℕ) :
    2 * (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
      ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * UnaryCalc.value (dT2 l D0) (cT2 l F C0) n + 2 := by
  have hmem : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
      v ≤ ThrDecF.kT l F * (n + 1) ^ ThrDecF.dT l :=
    Classical.choose_spec (Classical.choose_spec (PrimT.W6.thrNumsPoly l (ThrDecF.capD l)) (ThrDecF.capC l) F) kclk coef A
      a ha n hs Cs carriers _ ha' hcall.2.2.2.1 hcall.2.2.1
      (ThrDecF.capT_poly l F kclk coef A a ha ha' Cs carriers translation hcall hs)
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have htg := C4GateSym.tupleG_len_le Cs ((n + 1) ^ 26) hcall.2.2.1
  have htg4 : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * (n + 1) ^ 26 := htg.trans (Nat.mul_le_mul_right _ ha')
  have hB : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
      ThrData.thrCounts Cs carriers, v ≤ ThrDecF.kT l F * (n + 1) ^ ThrDecF.dT l + 4 * (n + 1) ^ 26 := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have := hmem v hv; omega
    · unfold ThrData.thrCounts at hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hv
        have hX26 : X.length ≤ (n + 1) ^ 26 := (hcall.2.1 X hX).1
        omega
      · rw [List.mem_singleton] at hv
        omega
  have hu := C4GateSym.unaryList_len_le _ _ hB
  have hlen : (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
      ThrData.thrCounts Cs carriers).length ≤ 19 := by
    rw [List.length_append, ThrData.hashNums_length]
    simp [ThrData.thrCounts]
    omega
  have p1 : (n + 1) ^ ThrDecF.dT l ≤ (n + 1) ^ dT2 l D0 := pow_mono_exp (by unfold dT2; omega)
  have p2 : (n + 1) ^ 26 ≤ (n + 1) ^ dT2 l D0 := pow_mono_exp (by unfold dT2; omega)
  have p3 : 1 ≤ (n + 1) ^ dT2 l D0 := Nat.one_le_pow _ _ (by omega)
  have q1 : ThrDecF.kT l F * (n + 1) ^ ThrDecF.dT l ≤ ThrDecF.kT l F * (n + 1) ^ dT2 l D0 := Nat.mul_le_mul_left _ p1
  have q2 := Nat.mul_le_mul hlen (le_refl (ThrDecF.kT l F * (n + 1) ^ ThrDecF.dT l + 4 * (n + 1) ^ 26 + 1))
  have hV : 19 * (ThrDecF.kT l F * (n + 1) ^ dT2 l D0 + 4 * (n + 1) ^ dT2 l D0 + (n + 1) ^ dT2 l D0) ≤
      UnaryCalc.value (dT2 l D0) (cT2 l F C0) n := by
    unfold UnaryCalc.value cT2
    have e : 19 * (ThrDecF.kT l F * (n + 1) ^ dT2 l D0 + 4 * (n + 1) ^ dT2 l D0 + (n + 1) ^ dT2 l D0) =
        19 * (ThrDecF.kT l F + 5) * (n + 1) ^ dT2 l D0 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by omega)
  have q3 : 19 * (ThrDecF.kT l F * (n + 1) ^ ThrDecF.dT l + 4 * (n + 1) ^ 26 + 1) ≤
      19 * (ThrDecF.kT l F * (n + 1) ^ dT2 l D0 + 4 * (n + 1) ^ dT2 l D0 + (n + 1) ^ dT2 l D0) := by omega
  omega

end Data

section Stage
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
  (S : ThrData.ThrDataStage4 alg Dexp capT)

/-- **The data stage's need within the data width.** -/
theorem data_need (l : Literals) (F : GateFree l) (D0 C0 n : ℕ) (hD : S.Dn ≤ D0) (hC : S.Kn ≤ C0) :
    S.need n ≤ 2 * UnaryCalc.value (dT2 l D0) (cT2 l F C0) n + 2 := by
  have h := S.need_le n
  have h2 : S.Kn * (n + 1) ^ S.Dn ≤ UnaryCalc.value (dT2 l D0) (cT2 l F C0) n := by
    unfold UnaryCalc.value
    exact Nat.mul_le_mul (by unfold cT2; omega) (pow_mono_exp (by unfold dT2; omega))
  omega

end Stage

end NearCubicWires.WireExponent3_5.PrimT.ThrTB

end
