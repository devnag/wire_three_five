import Proof.Wire_3_5.FinalPass.HashCost4
import Proof.Wire_3_5.FinalPass.HashFree2
import Proof.Wire_3_5.Primitive.SeedFix.C4HBh

/-! # The HASH free numbers' builder: `HashFreeOk2` at every gate, fixed before `F`

The HASH contract (`HashFreeOk2 l F wa K3 D3 Kp Dp` = `HashFreeOk` + `caps_ge`): the deliverable. The HASH constants `hashCof` (`d_Q = 8e_R + 1` for the recovery range, `d_H = coef·4^{deg} + 2`,
`e_H = 26deg + 1`, `d_D = 4(192c_E + 385)` for the aux rows' degree, `d_P`, `e_P = e_H + 5`, `d_C = 1`,
`d_A = dAH + e_P + 5 + ⌈log₂ c_Pad⌉`, `d_R = 0`), the load floor `C_{D,h} = occCDH + costCDH` (the printer's
budget against `Ψ_aux` and the child's steps, P3:3094-3107), the C3 load constants `K3 = d_H + 3d_Q + 4c_T + 1 + d_P`,
`D3 = e_H + e_P + 3` and the pad constants `Kp = 4^{d_A} + 1`, `Dp = d_A + d_R` depend on the literals and `wa` only.
At every gate `F` with `C_{D,h} ≤ C_D` and `1 ≤ c_ψ`, the free program `freeProgH (hashK2 c)` with `dF = hashDF c`,
`K_c = Cap = 2^{⌊n/16⌋ + d_C L²}` and `K_ch = symKch` meets every field: the program's bounds (FreeGenH2), the pad
(`padH`), the C3 load (`c3_hash`), `side` (`HashEAt` at every THR call: `hb_cells` under `capS_hash`,
`hpre_hash`, `hQp_hash`, `hcost_hash` with `hb_prep`, `hrange_hash`, `padHR_hash`, `fits_hash`, `one_le_h_hash`)
and `caps_ge` (`2tℓ₀ ≤ hbS ≤ Cap`).

* `c3_hash`, `capsge_hash`, `hbcells_hash`, `hashCof0`, `hashCof`, `hashCDs`, **`hashFreeOk2`**.

Paper quantities of the main type: the HASH stage's free numbers `Q', h, m, pr, ρ`, the Hb capacities and bounds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.RepairRepresentation

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The C3 load at the HASH request** (`h + Q' + m + pr ≤ K3(ψ+1)(n+1)^{D3}`). -/
theorem c3_hash (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤
      (c.dH + 3 * c.dQ + 4 * cT l + 1 + c.dP) * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) *
        (n + 1) ^ (c.eH + c.eP + 3) := by
  have hk : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := hcall.2.2.2.2.2.2.kq
  have hkh := kh_two l F kclk coef A a ha hs
  have hLn := L_le_n n
  have htl := t_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hm := m_hash l F c kclk coef A a ha Cs carriers hs
  rw [hm]
  have hN1 : 1 ≤ (n + 1) := by omega
  obtain ⟨D, hD⟩ : ∃ D, D = c.eH + c.eP + 3 := ⟨_, rfl⟩
  rw [← hD]
  have hND : ∀ e, e ≤ D → (n + 1) ^ e ≤ (n + 1) ^ D := fun e he => Nat.pow_le_pow_right hN1 he
  have t3 : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 ≤ c.dH * (n + 1) ^ D := by
    show c.dH * (n + 1) ^ c.eH ≤ _
    exact Nat.mul_le_mul_left _ (hND _ (by omega))
  have t2 : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 ≤ 3 * c.dQ * (n + 1) ^ D := by
    show c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ _
    have h1 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) ^ 3 := by
      calc (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) ≤ (n + 1) * ((n + 1) * (n + 1)) := Nat.mul_le_mul hLn (Nat.mul_le_mul hLn hLn)
        _ = (n + 1) ^ 3 := by ring
    have h2 : (n + 1) ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 := hND 3 (by omega)
    have h4 : (Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2)) ≤ 3 * (n + 1) ^ D := by omega
    calc c.dQ * ((Nat.clog 2 (n + 2)) * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) + (Nat.clog 2 (n + 2))) ≤ c.dQ * (3 * (n + 1) ^ D) := Nat.mul_le_mul_left _ h4
      _ = 3 * c.dQ * (n + 1) ^ D := by ring
  have t4 : 2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤ (4 * cT l + 1) * (n + 1) ^ D := by
    have h1 : (n + 1) ≤ (n + 1) ^ D := by
      have := hND 1 (by omega); rw [pow_one] at this; exact this
    have h2 : (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ cT l * (2 * (n + 1)) := htl.trans (Nat.mul_le_mul_left _ (by omega))
    have h3 : cT l * (2 * (n + 1)) ≤ cT l * (2 * (n + 1) ^ D) := Nat.mul_le_mul_left _ (by omega)
    have e : (4 * cT l + 1) * (n + 1) ^ D = 2 * (cT l * (2 * (n + 1) ^ D)) + (n + 1) ^ D := by ring
    have h4 : 1 ≤ (n + 1) ^ D := Nat.one_le_pow _ _ hN1
    omega
  have t5 : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤ c.dP * (n + 1) ^ D := by
    show c.dP * (n + 1) ^ c.eP ≤ _
    exact Nat.mul_le_mul_left _ (hND _ (by omega))
  have hsum : (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 + (2 * (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) + (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤
      (c.dH + 3 * c.dQ + 4 * cT l + 1 + c.dP) * (n + 1) ^ D := by
    have e : (c.dH + 3 * c.dQ + 4 * cT l + 1 + c.dP) * (n + 1) ^ D = c.dH * (n + 1) ^ D + 3 * c.dQ * (n + 1) ^ D +
        (4 * cT l + 1) * (n + 1) ^ D + c.dP * (n + 1) ^ D := by ring
    omega
  refine hsum.trans ?_
  calc (c.dH + 3 * c.dQ + 4 * cT l + 1 + c.dP) * (n + 1) ^ D
      = (c.dH + 3 * c.dQ + 4 * cT l + 1 + c.dP) * 1 * (n + 1) ^ D := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

/-- **The ruler's capacity** `2tℓ₀ ≤ Cap` (`caps_ge`). -/
theorem capsge_hash (c : SymC) (wa : WilliamsAlgorithm) (hCDc : costCDH l (gate0 l F).alg c ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi)
    (hdA : dAH c (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤ (FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1 := by
  have hcap := capS_hash l F c wa hCDc hcpsi hdA kclk coef A a ha ha' Cs carriers translation hcall hs
  have h1 : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 < 2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) :=
    lt_of_le_of_lt (Nat.le_add_left _ _) Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t + 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) ≤ PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) := by
    have key : ∀ a b c d e f g h i : ℕ, b ≤ a + b + c + d + e + f + g + h + i := by intros; omega
    unfold PrimT.C4H.hbS
    exact key _ _ _ _ _ _ _ _ _
  have h3 : PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ 2 ^ 32 * (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8 := by
    have h4 : PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) ≤ (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8 := (Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _)
    exact h4.trans (Nat.le_mul_of_pos_left _ (by positivity))
  omega

/-- **The Hb printer's conditions at every child** (`HashEAt`'s first clause, `hb_cells`). -/
theorem hbcells_hash (c : SymC) (wa : WilliamsAlgorithm) (hCDc : costCDH l (gate0 l F).alg c ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi)
    (hdA : dAH c (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ (p : List Bool) (b : Bool), p.length < (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) →
      (PrimT.C4H.hbX (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).HbOk ∧
      (∀ cc < (PrimT.C4H.hbX (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
        (PrimT.C4H.hbX (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).CellOk cc ∧
        (PrimT.C4H.hbX (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).cellCost cc ≤
          2 ^ (n / 16 + c.dC * ((Nat.clog 2 (n + 2)) * (Nat.clog 2 (n + 2))))) := by
  intro p b hp
  have hplen : (p ++ [b]).length ≤ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) := by rw [List.length_append, List.length_singleton]; omega
  have hcap := capS_hash l F c wa hCDc hcpsi hdA kclk coef A a ha ha' Cs carriers translation hcall hs
  have hge : PrimT.C4H.CapsGe (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (2 ^ 32 * (PrimT.C4H.hbS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) + 1) ^ 8) :=
    ⟨hcap, hcap, hcap, hcap, hcap, hcap, hcap, hcap, hcap, hcap, hcap, hcap⟩
  obtain ⟨h1, h2⟩ := PrimT.C4HB.hb_cells (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (PrimT.C4HB.hashData_ok (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (capsOf ((FreeGen.freeProgH (hashK2 c)).val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1)) (p ++ [b]).length (SeedFix.listNum (p ++ [b])) hplen hge
  exact ⟨h1, fun cc hcc => ⟨(h2 cc hcc).1, (h2 cc hcc).2.trans hcap⟩⟩

end Gate

/-- The HASH constants before `d_A`. -/
noncomputable def hashCof0 (l : Literals) : SymC where
  dT := 0
  dC := 1
  dQ := 8 * eR l + 1
  dH := (algL l).coefficient * 4 ^ (algL l).degree + 2
  eH := 26 * (algL l).degree + 1
  dP := 3 * ((algL l).coefficient * 4 ^ (algL l).degree + 2) * (8 * eR l + 1) * (4 * (192 * cE l + 385)) +
    (8 * cPW l + 8 * cT l * cL0 l + 3 * (8 * eR l + 1))
  eP := 26 * (algL l).degree + 1 + 5
  dA := 0
  dR := 0
  dD := 4 * (192 * cE l + 385)

/-- **The HASH constants** (fixed before `F`). -/
noncomputable def hashCof (l : Literals) (wa : WilliamsAlgorithm) : SymC :=
  { hashCof0 l with dA := dAH (hashCof0 l) (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) +
      ((hashCof0 l).eP + 5 + Nat.clog 2 (cPad l (hashCof0 l))) }

/-- **The HASH load floor** `C_{D,h}` (fixed before `F`). -/
noncomputable def hashCDs (l : Literals) (wa : WilliamsAlgorithm) : ℕ :=
  occCDH l (algL l) (hashCof l wa) + costCDH l (algL l) (hashCof l wa)

/-- **The HASH free numbers at every gate** (`HashFreeOk2`). -/
noncomputable def hashFreeOk2 (l : Literals) (wa : WilliamsAlgorithm) : ∀ _fe : ℕ, Σ CDs K3 D3 Kp Dp : ℕ,
    ∀ F : GateFree l, F.filterErrDeg = _fe → CDs ≤ F.CD → 1 ≤ F.E.cpsi → HashFreeOk2 l F wa K3 D3 Kp Dp :=
  fun _ => ⟨hashCDs l wa, (hashCof l wa).dH + 3 * (hashCof l wa).dQ + 4 * cT l + 1 + (hashCof l wa).dP,
    (hashCof l wa).eH + (hashCof l wa).eP + 3, 4 ^ (hashCof l wa).dA + 1, (hashCof l wa).dA + (hashCof l wa).dR,
    fun F _ hCD hcpsi =>
    have hc : HpreH l (gate0 l F).alg (hashCof l wa) :=
      ⟨le_refl _, le_refl _, le_refl _, le_refl _, Nat.le_add_right _ _, le_refl _, Nat.le_add_left _ _⟩
    have hCDo : occCDH l (gate0 l F).alg (hashCof l wa) ≤ F.CD := le_trans (Nat.le_add_right _ _) hCD
    have hCDc : costCDH l (gate0 l F).alg (hashCof l wa) ≤ F.CD := le_trans (Nat.le_add_left _ _) hCD
    have hdA : dAH (hashCof l wa) (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤
        (hashCof l wa).dA := Nat.le_add_right _ _
    have hdA2 : (hashCof l wa).eP + 5 + Nat.clog 2 (cPad l (hashCof l wa)) ≤ (hashCof l wa).dA := Nat.le_add_left _ _
    { Fp := freeProgH (hashK2 (hashCof l wa))
      dF := hashDF (hashCof l wa)
      Kc := fun n => 2 ^ (n / 16 + (hashCof l wa).dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))
      Kch := symKch l F (hashCof l wa)
      ok_le := fun Ds => by
        obtain ⟨Ko, hKo⟩ := okH_le (hashK2 (hashCof l wa)) Ds
        exact ⟨Ko, fun cap x hx hc => hKo cap x (small_of hx) hc⟩
      cost_le := costH_le _
      val_le := fun Ds => by
        obtain ⟨Kv, hKv⟩ := valH_le (hashK2 (hashCof l wa)) Ds
        exact ⟨Kv, fun x j hx hj => hKv x j (small_of hx) hj⟩
      rho_le := rhoH_le _
      pad_le := by
        intro kclk coef A a ha n a' ha' Cs carriers translation _ hs
        have h := padH (hashK2 (hashCof l wa)) (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)
        have hk : (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs).kh +
            (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs).kh =
              ((gate0 l F).budget kclk coef A a ha).kOf n := by
          rw [← kh_two l F kclk coef A a ha hs]
          show SeedFix.callKh _ + SeedFix.callKh _ = _
          ring
        rw [hk] at h
        exact h
      c3_le := fun _ kclk coef A a ha n a' ha' Cs carriers translation hcall hs =>
        c3_hash l F (hashCof l wa) kclk coef A a ha ha' Cs carriers translation hcall hs
      side := by
        intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs
        exact ⟨hbcells_hash l F (hashCof l wa) wa hCDc hcpsi hdA kclk coef A a ha ha' Cs carriers translation hcall hs,
          hpre_hash l F (hashCof l wa) hc hCDo hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs,
          hQp_hash l F (hashCof l wa) (by show 1 ≤ _ + 2; omega) (by show 1 ≤ 4 * _; omega) hc.dP1 hc.eP1 kclk coef A a
            ha ha' Cs carriers translation hcall hs,
          hcost_hash l F (hashCof l wa) wa hc hCDo hCDc hcpsi hdA PrimT.C4HB.hb_prep kclk coef A a ha ha' Cs carriers
            translation hcall hs,
          hrange_hash l F (hashCof l wa) hc.dQ kclk coef A a ha ha' Cs carriers translation hcall hs _ _ _,
          padHR_hash l F (hashCof l wa) hdA2 kclk coef A a ha ha' Cs carriers translation hcall hs _,
          (fits_hash l F (hashCof l wa) hc.dH hc.eH kclk coef A a ha ha' Cs carriers translation hcall hs
            ((freeProgH (hashK2 (hashCof l wa))).val
              (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) 0).1,
          one_le_h_hash (hashCof l wa) (by show 1 ≤ _ + 2; omega) _⟩
      caps_ge := fun kclk coef A a ha n a' ha' Cs carriers translation hcall hs =>
        capsge_hash l F (hashCof l wa) wa hCDc hcpsi hdA kclk coef A a ha ha' Cs carriers translation hcall hs }⟩

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
