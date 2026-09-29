import Proof.Wire_3_5.FinalPass.SymCost1

/-! # The SYM child's cost, part 2: the SYM request's numbers at a call

P3:1886-1906, 3094-3107 at a SYM call, with the v2 free numbers (`Q' = d_Q(k+L)`, `h = d_H(n+1)^{e_H}`,
`m ≤ 400(k+L)`, `p = d_P(n+1)^{e_P}`, `d = d_D(⌊√B_S⌋+L)`): **`symFix_le`**, the compiler input's fixed fields and the
displayed parameters below `2^{e_F}` (`fix_num`; `|D| = |flips|·|gates| ≤ 2^{k+26L+5}`, `P_ex + 1 ≤ 2^{k + cDa·L}`,
`width ≤ 2·dRow ≤ n − k + 1`); **`symOcc_le`**, the charged occurrence count at every prefix below `2^{c_O U}`
(`occ_numU`, with the child expression's term count `A ≤ 2^{A₁(k+L)}`, generic in the batch). Also `L2_mul_le`
(`C_D L² ≤ ψ`, through `Ψ_aux`) and `bnOf` (the displayed parameters' sum).

Paper quantities of the main types: the compiler input's size and `𝒮` at a SYM child request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- `C_D·L² ≤ ψ` (through `Ψ_aux`). -/
theorem L2_mul_le (CD k L BT BS : ℕ) : CD * (L * L) ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine le_trans ?_ h1
  unfold loadAux
  apply Nat.mul_le_mul_left
  rw [← sq]
  omega

/-- The displayed parameters' sum (the polynomial factor of `c3Cost_le_B`). -/
def bnOf (a : RepairRepresentation.DecompositionAlgorithm) (R : Req.C3Req) : ℕ :=
  R.p + R.P.width + (Pool.poolChildren a R.P.gates R.P.flips).length + R.P.h + R.P.Q + R.d + 1

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The SYM request's numbers below `2^{e_F}`**: the fixed fields' base and the displayed parameters. -/
theorem symFix_le (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    EnumCap.fixB (gate0 l F).alg (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
        (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0) +
      bnOf (gate0 l F).alg (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
        (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0) ≤
      2 ^ efOf (cDa (gate0 l F).alg) c.dQ c.dD c.dH c.eH c.dP c.eP
        ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) *
          (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) *
          (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2)))
        (Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hP := symPool_length_le ha' Cs carriers hcar hnc hd
  have hD := symD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
  have hm := m_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  have hn2 := n2_le_L n
  have hN := n26_le n
  have hcD : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  have hdr := two_dRow_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hwd := C3Geo.width_le_dRow ((callInputs l F kclk coef A a ha).starParams n hs)
  -- the pool's atoms
  have hDl : (Pool.densePool (gate0 l F).alg ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤
      2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + 26 * Nat.clog 2 (n + 2) + 5) := by
    rw [dense_length, List.length_map]
    have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length =
        4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
          2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := by
      simp [PrimT.C4Geo.flips]
    rw [hfl, ← pow_add, ← two_mul, hkh, pow_add, pow_add]
    have h1 : 4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (Records.symPool Cs carriers).length ≤
        4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (8 * 2 ^ (26 * Nat.clog 2 (n + 2))) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : 4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (8 * 2 ^ (26 * Nat.clog 2 (n + 2))) =
        2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * 2 ^ (26 * Nat.clog 2 (n + 2)) * 2 ^ 5 := by ring
    omega
  -- the pool children are the dense pool's labels
  have hPex : (Pool.poolChildren (gate0 l F).alg ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).length ≤
      (Pool.densePool (gate0 l F).alg ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG)
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length :=
    ((Emit.shapeOf_flatten_length _ _ _ _ _).symm.trans (Top.shapeOf_flatten_len _)).le
  have hcols : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length =
      PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := by
    simp [PrimT.C4Geo.cols]
  have hrn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have hK : ((gate0 l F).budget kclk coef A a ha).kOf n =
      ((callInputs l F kclk coef A a ha).starParams n hs).r * ((callInputs l F kclk coef A a ha).starParams n hs).s := rfl
  rw [hrn] at hdr
  have hw1 : PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs) ≤ n + 1 := by omega
  have hd1 : PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ n + 1 := by omega
  have hc1 : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams n hs)).length ≤ n + 1 := by
    rw [hcols]; exact hd1
  have key := fix_num (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n)) n (cDa (gate0 l F).alg) c.dQ c.dD c.dH c.eH
    c.dP c.eP (m := (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
    (h := (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
    (pr := (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5)
    (dg := symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
    _ _ _ _ _ _ _ hL1 hn2 hcD hQ hD hDl hm rfl rfl hw1 hd1 hc1 rfl hPex
  unfold EnumCap.fixB bnOf
  exact key

/-- **The charged occurrence count at every prefix** of a SYM call, generic in the batch (`R ≤ 10`, rows of at most
`T ≤ 2^{e_T(k+L)}` terms). -/
theorem symOcc_le (c : SymC) (eT T : ℕ) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Rn : ℕ) (hRn : Rn ≤ 10) (batch : List SeedFix.SExpr)
    (hb : ∀ V ∈ batch, V.length ≤ T) (hT : T ≤ 2 ^ (eT * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))))
    (p' : List Bool) :
    (PrimT.C4Child.chR (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
      (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0)
      (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
      (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch p').occBoundP (gate0 l F).alg ≤
      2 ^ (coOf (A1 l F.filterErrDeg eT) c.dQ (cDa (gate0 l F).alg) c.dD *
        ((((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) *
          (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) *
          (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2)))) := by
  have hV := lenV_sym l F eT T kclk coef A a ha ha' Cs carriers translation hcall hs Rn hRn batch hb hT
    p'.length (SeedFix.listNum p')
  have hD := symD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
  have hm := m_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hcD : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  unfold Req.C3Req.occBoundP
  exact occ_numU _ _ _ _ _ _ _ _ _ _ _ _ (one_le_L n) hcD hV hm hQ hD rfl

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
