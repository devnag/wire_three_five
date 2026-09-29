import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.Writers.ThrFam2

/-! # The HASH free numbers' contract (the for the review): `HashFreeOk`

`filt:soft`, P3:2221-2336 at a THR call's HASH stage, with the free numbers of the SYM precedent (C4SymKB7): the free program `Fp` on the HASH input `hashX` (THR's `thrX` with the moment count `t` in the arity slot, so that
`m = 1 + 2t` is a free number: every printed term has `1 + 2t` factors, `hashTermsM_uniform`), the degree bound `dF`
(no machine reads it), the Hb printer's uniform capacities `capsOf (Cap)` (every `HbCaps` field the capacity slot's
value), the Hb cell bound `Kc` and the child bound `Kch`, the pad and the C3 load at constants fixed before `F`, and
`C4H.HashEAt` at every THR call at the call's compiler request `thrR0 … h Q' 0 m d pr 0` (the reference one, the THR pool),
the call's data `hashDataOf` and the seed length `s_h = 2t·ℓ₀`.

* `hashX`, `capsOf`, **`HashFreeOk`**.

Paper quantities of the main type: the HASH stage's free numbers `Q', h, m, pr, ρ`, the Hb capacities and bounds. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The HASH input**: THR's `thrX` with the moment count `t` in the arity slot. -/
noncomputable def hashX {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (hs : I.StarAt n) : FreeIn :=
  { ThrFam.thrX I alg Cs carriers hs with a := thrCallT alg I hs Cs carriers }

/-- The Hb printer's uniform capacities. -/
def capsOf (v : ℕ) : PrimT.C4H.HbCaps := ⟨v, v, v, v, v, v, v, v, v, v, v, v⟩

/-- **The free numbers of the HASH stage** (the deliverable, the twin of `SymFreeOk7`): the program `Fp` on
`hashX`, the degree bound `dF`, the Hb cell bound `Kc`, the child bound `Kch`, the program's bounds, the pad and the
C3 load at the constants `K3 D3 Kp Dp` fixed before `F`, and `HashEAt` at every THR call. -/
structure HashFreeOk (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ) :
    Type where
  Fp : PrimT.C4Set.FreeProg
  dF : FreeIn → ℕ
  Kc : ℕ → ℕ
  Kch : ℕ → ℕ
  ok_le : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), PrimT.C4SymW.FreeSmall Ds x →
    Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x
  cost_le : ∃ Kc : ℕ, ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2
  val_le : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), PrimT.C4SymW.FreeSmall Ds x → j.val ≠ 6 →
    Fp.val x j ≤ Kv * 2 ^ (x.n / 8)
  rho_le : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr
  pad_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      2 ^ Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6 ≤
        Kp * (2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) * (n + 1) ^ Dp +
          2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2))
  c3_le : 1 ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 +
        Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 +
        Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 +
        Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤
        K3 * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ D3
  /-- **The side conditions at every THR call's HASH stage.** -/
  side : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      PrimT.C4H.HashEAt wa (gate0 l F).alg
        (ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
          (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3)
          (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0
          (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)
          (dF (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
          (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) 0)
        (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (capsOf (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1))
        (Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (Kc n) (Kch n)
        (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t *
          (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0)

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
