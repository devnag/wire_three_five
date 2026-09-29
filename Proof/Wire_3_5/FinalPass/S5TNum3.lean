import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.S5TNum2
import Proof.Wire_3_5.FinalPass.ThrSz6

/-! # S5-THR, part 37: the THR half's constants and a request's facts (P3:3114-3115, 3170-3181)

The THR half's parameters in the paper's order of choice: the degrees on `l` alone (**`DtT`**, `thrNumsPoly`
degree at the cap's degree; **`Hd`**, at least every piece's degree; **`Zx`**, **`Dl`**, the half's exponent), the
coefficient on `F` (**`KtT`**, **`c0T`**, at least every piece's coefficient). At a THR request: **`call_facts`**
(the call's precondition: carriers `≤ 2`, descriptions `≤ (n+1)^{26}`, the carriers' envelope, the star
hypotheses), **`one_le_n`**, **`vals_le`** (every W6 number `≤ K_t·(n+1)^{D_t}`), **`natWord_le_reqW`** (the codes
inside the request word).

Paper quantity of the main types: the call's numbers polynomial in `n` with the degree fixed before the gate
(P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

section Par
variable (l : Literals)

/-- The THR numbers' degree (`thrNumsPoly` at the cap's degree `capZR`). -/
noncomputable def DtT : ℕ := Classical.choose (PrimT.W6.thrNumsPoly l (PrimAsm.CallIndexR.capZR l))

/-- The THR numbers' coefficient at `F`. -/
noncomputable def KtT (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (PrimT.W6.thrNumsPoly l (PrimAsm.CallIndexR.capZR l))
    (PrimAsm.CallIndexR.capK F.cr * 2 ^ PrimAsm.CallIndexR.capZR l) F)

/-- **The base degree** (on `l` alone): at least the need and prep degrees, W6's, the top front's and the data
stage's cost degrees, the numbers' degree and the cap's. -/
noncomputable def Hd : ℕ :=
  PrimT.TS4.NDeg l + PrimT.TS4.Dp l + (PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1).Dc +
    (PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)).Dc + PrimAsm.ThrData.thrDataStage2.Dc + DtT l +
    PrimAsm.CallIndexR.capZR l + 30

/-- The exponent of the sizes' bound `Z = y^{Zx}`. -/
noncomputable def Zx : ℕ := 3 * Hd l + 1

/-- **The THR half's exponent** `D` (on `l` alone): the stage costs at most `Z^{2H+3} = y^{D}`. -/
noncomputable def Dl : ℕ := Zx l * (2 * Hd l + 3)

/-- **The THR half's coefficient** (on `F`): at least every piece's coefficient. -/
noncomputable def c0T (F : GateFree l) : ℕ :=
  KtT l F + PrimT.TS4.capKc l F.cr + PrimT.TS4.NCoef l F.cr + PrimT.TS4.Kp l F.cr +
    (PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1).Cc + (PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)).Cc +
    PrimAsm.ThrData.thrDataStage2.Cc + 100000

theorem one_le_Hd : 30 ≤ Hd l := by unfold Hd; omega

theorem Zx_le_Dl : Zx l ≤ Dl l := by
  unfold Dl; exact Nat.le_mul_of_pos_right _ (by omega)

end Par

section Req
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem alg_eq : (gate0 l F).alg = PrimT.W6.litAlg l := rfl

/-- **The call's precondition** at a THR request. -/
theorem call_facts {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (h : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩) :
    carriers.length ≤ 2 ∧ (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) ∧
      (∀ X ∈ carriers, X.WithinEnvelope 26) ∧ (callInputs l F kclk coef A a ha).StarAt n := by
  obtain ⟨_, hcar, hdesc, hcount, _, hs, _⟩ := h
  exact ⟨hcount, fun i => hdesc i, hcar, hs⟩

theorem one_le_n {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) : 1 ≤ n := by
  have h1 := hs.2.1
  have h2 := hs.2.2.1
  omega

/-- **Every W6 number of the call** is at most `K_t·(n+1)^{D_t}`. -/
theorem vals_le {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (hcar : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (i : Fin 14) :
    (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1 carriers).get i ≤
      KtT l F * (n + 1) ^ DtT l :=
  Classical.choose_spec (Classical.choose_spec (PrimT.W6.thrNumsPoly l (PrimAsm.CallIndexR.capZR l))
    (PrimAsm.CallIndexR.capK F.cr * 2 ^ PrimAsm.CallIndexR.capZR l) F) kclk coef A a ha n hs Cs carriers
    (PrimT.TS4.capTL l F.cr n) ha' hcar hd (ThrSz.cap_kn l F kclk coef A a ha n) _
    (ThrSz.mem_nums l F kclk coef A a ha n hs Cs carriers i)

end Req

/-- **The codes lie inside the request word.** -/
theorem natWord_le_reqW (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    (∀ x ∈ codes, (RepairRepresentation.natWord x).length ≤ (PrimAsm.Data.reqW n mb codes cc tl).length) ∧
    (∀ y ∈ cc, (RepairRepresentation.natWord y).length ≤ (PrimAsm.Data.reqW n mb codes cc tl).length) := by
  unfold PrimAsm.Data.reqW RepairRepresentation.natListWord
  simp only [List.length_append, List.length_flatMap]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have := List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩ :
      (RepairRepresentation.natWord x).length ∈ codes.map (fun c => (RepairRepresentation.natWord c).length))
    omega
  · have := List.le_sum_of_mem (List.mem_map.2 ⟨y, hy, rfl⟩ :
      (RepairRepresentation.natWord y).length ∈ cc.map (fun c => (RepairRepresentation.natWord c).length))
    omega

theorem nbl_le_natWord (x : ℕ) : natBitLength x ≤ (RepairRepresentation.natWord x).length := by
  rw [PrimAsm.ParseNat.natWord_length]; omega

end NearCubicWires.WireExponent3_5.FinalPass.S5T
