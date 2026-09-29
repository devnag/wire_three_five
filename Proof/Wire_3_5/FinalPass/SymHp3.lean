import Proof.Wire_3_5.FinalPass.SymHp2

/-! # The SYM child request's precondition, part 3: `hpre`

**`hpre_sym`**: at a SYM call of the gate, under the floors and the SYM constants' constraints, the child request
of every prefix (`C4Child.chR (symR0 … h Q' 0 m dg pr 0) …`, the free numbers `freeVal2 (symK2 c)` and the degree
`symDF c`) meets `C3Req.Pre` (alg:compiler, P3:1882-1900), for every batch of the given shape (`BatchFacts`: the SYM
batch at `R = |carriers| + 2a`, or the degenerate call's padded batch at `R = 1`) whose rows' factor counts
give `8·Σ f = m`.
Paper quantity of the main type: alg:compiler's precondition at a SYM call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- The SYM constants' constraints read by `hpre` (the literals' algorithm, `fe` and the pool's `Z` alone). -/
structure HpreC (l : Literals) (fe : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (c : SymC) : Prop where
  dQ1 : 1 ≤ c.dQ
  dH : alg.coefficient * 4 ^ alg.degree + 2 ≤ c.dH
  eH : 26 * alg.degree + 1 ≤ c.eH
  dP1 : c.dH * c.dQ * c.dD * 2 ^ (50 + CallIndexR.capZR l) ≤ c.dP
  eP1 : c.eH + 49 + CallIndexR.capZR l ≤ c.eP
  dP2 : 2 * (24 + 8 * eQ l fe + c.dQ) ≤ c.dP
  eP2 : 1 ≤ c.eP

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`C3Req.Pre` at the SYM child request of every prefix.** -/
theorem hpre_sym (c : SymC) (hc : HpreC l F.filterErrDeg (gate0 l F).alg c) (eT D T : ℕ)
    (hCD : occCD (gate0 l F).alg c (A1 l F.filterErrDeg eT) ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Rn : ℕ) (hRn : Rn ≤ 10) (batch : List SeedFix.SExpr)
    (f : ℕ → ℕ)
    (hB : SampShape.BatchFacts batch Rn f D
      ((PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
        (Records.symPool Cs carriers).length) T)
    (hT : T ≤ 2 ^ (eT * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))))
    (hmf : 8 * ((List.range Rn).map f).sum =
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
    (hDg : D ≤ symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) (p' : List Bool) :
    (PrimT.C4Child.chR (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
      (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0)
      (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
      (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch p').Pre (gate0 l F).alg := by
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hfits := fits_sym l F c hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
  have hV := lenV_sym l F eT T kclk coef A a ha ha' Cs carriers translation hcall hs Rn hRn batch hB.len hT
    p'.length (SeedFix.listNum p')
  have hocc := occ_sym l F c (A1 l F.filterErrDeg eT) hCD hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs
    (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch p' hV
  have hL1 := one_le_L n
  refine SampShape.pre_of (gate0 l F).alg _ _ _ Rn batch p' f D _ T hB
    (C3Geo.poolReq_pre _ _ _ _ _ _) ?_ ?_ hmf hDg ?_ hfits.2.1 hfits.2.2
    (hqd_sym l F c hc.dP1 hc.eP1 kclk coef A a ha ha' Cs carriers translation hcall hs)
    (coef_sym l F c hc.dP2 hc.eP2 kclk coef A a ha ha' Cs carriers translation hcall hs)
    (C3Geo.width_le_dRow _) (PrimT.C4Geo.cols_length _) (C3Geo.cols_lt _) hocc
  · show 1 ≤ max (mOf (symK2 c).k (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) 8
    exact le_trans (by norm_num) (le_max_right _ _)
  · show 1 ≤ (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2
    rw [hQ]
    exact Nat.mul_le_mul hc.dQ1 (show 1 ≤ ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) by omega)
  · show _ ≤ (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length *
      ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG).length
    rw [List.length_map]

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

