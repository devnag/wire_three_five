import Proof.Wire_3_5.FinalPass.SymOcc2

/-! # The printer's gate budget at a SYM call, part 3: `occ_sym`

At a SYM call of the gate, with the floors (`occCD ≤ C_D`, `1 ≤ c_ψ`; P3:3094-3107, "C_D sufficiently large"),
the child request of every prefix meets alg:eq-budget's clause of `C3Req.Pre` (P3:1897-1900) at the free numbers
`freeVal2 (symK2 c)` and the degree `symDF c`: the dense pool is below `2^{k + cDa·L}` (**`symD_le`**), the expression
below `2^{A₁(k+L)}` (a premise, from the batch's shape), `m ≤ 400(k+L)`, `Q' = dQ(k+L)`, `d = dD(⌊√B_S⌋+L)`; the
linear part is within `C_D(k+L) ≤ ψ` and the quadratic part within `C_D²(k+L)²(⌊√B_S⌋+L) ≤ ψ`.
* `occCD`, **`symD_le`**, **`occ_sym`**.
Paper quantities of the main types: alg:eq-budget at a SYM call against the load `ψ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- **The load-constant floor of the printer's budget** (chosen before `F`: the algorithm is the literals'). -/
def occCD (a : RepairRepresentation.DecompositionAlgorithm) (c : SymC) (A1 : ℕ) : ℕ :=
  160 * (A1 + 400 + c.dQ + 1) + 160 * (c.dQ * c.dD * cDa a) + 2

theorem symBud_le' (a : RepairRepresentation.DecompositionAlgorithm) (n : ℕ) :
    symBud a n ≤ a.coefficient * 4 ^ a.degree * (n + 1) ^ (26 * a.degree) := by
  unfold symBud
  have h1 : n + ((n + 1) ^ 26 + 2) + 1 ≤ 4 * (n + 1) ^ 26 := by
    have : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    omega
  calc a.coefficient * (n + ((n + 1) ^ 26 + 2) + 1) ^ a.degree
      ≤ a.coefficient * (4 * (n + 1) ^ 26) ^ a.degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The dense pool is below `2^{k + cDa·L}`** at a SYM call. -/
theorem symD_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (h Q psi : ℕ) :
    (Pool.densePool (gate0 l F).alg
      (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (Records.symPool Cs carriers) h Q psi).gates
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length + 1 ≤
      2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + cDa (gate0 l F).alg * Nat.clog 2 (n + 2)) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hB := sym_budget_le (gate0 l F).alg Cs carriers hcar hd
  have hP := symPool_length_le ha' Cs carriers hcar hnc hd
  have hDl := densePool_length_le (gate0 l F).alg
    ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG)
    (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
    (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
    (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))
    (symBud (gate0 l F).alg n)
    (fun g hg => (ExtDecompositionBatch.children_le_budget _ g).trans (hB g hg))
  have hfl : (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)).length =
      4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
        2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) := by
    simp [PrimT.C4Geo.flips]
  have hkh := kh_two l F kclk coef A a ha hs
  have hbud := symBud_le' (gate0 l F).alg n
  have hn2 := n2_le_L n
  have hL1 := one_le_L n
  show (Pool.densePool (gate0 l F).alg ((Records.symPool Cs carriers).map PrimT.C4Geo.suppG) _ _ _).flatten.length + 1 ≤ _
  rw [hfl, List.length_map] at hDl
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd] at hkh
  rw [← hLd] at hn2 hL1
  rw [← hKd, ← hLd]
  obtain ⟨Ca, hCa⟩ : ∃ C, C = (gate0 l F).alg.coefficient * 4 ^ (gate0 l F).alg.degree := ⟨_, rfl⟩
  obtain ⟨dg, hdg⟩ : ∃ d, d = (gate0 l F).alg.degree := ⟨_, rfl⟩
  have hCa' : Ca ≤ 2 ^ Nat.clog 2 Ca := Nat.le_pow_clog (by norm_num) _
  have hN : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    calc (n + 1) ^ 26 ≤ (2 ^ L) ^ 26 := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (26 * L) := by rw [← pow_mul, Nat.mul_comm]
  have hNd : (n + 1) ^ (26 * dg) ≤ 2 ^ (26 * dg * L) := by
    calc (n + 1) ^ (26 * dg) ≤ (2 ^ L) ^ (26 * dg) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (26 * dg * L) := by rw [← pow_mul, Nat.mul_comm]
  have hkk : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
      2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) = 2 ^ K := by
    rw [← pow_add]; congr 1; omega
  rw [hkk] at hDl
  rw [← hCa, ← hdg] at hbud
  have hbig : 4 * 2 ^ K * (8 * (n + 1) ^ 26 * symBud (gate0 l F).alg n) ≤
      2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L) := by
    have e : 2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L) =
        32 * 2 ^ K * (2 ^ (26 * L) * (2 ^ Nat.clog 2 Ca * 2 ^ (26 * dg * L))) := by
      rw [pow_add, pow_add, pow_add, pow_add]; ring
    rw [e]
    have h1 : symBud (gate0 l F).alg n ≤ 2 ^ Nat.clog 2 Ca * 2 ^ (26 * dg * L) :=
      hbud.trans (Nat.mul_le_mul hCa' hNd)
    calc 4 * 2 ^ K * (8 * (n + 1) ^ 26 * symBud (gate0 l F).alg n)
        = 32 * 2 ^ K * ((n + 1) ^ 26 * symBud (gate0 l F).alg n) := by ring
      _ ≤ 32 * 2 ^ K * (2 ^ (26 * L) * (2 ^ Nat.clog 2 Ca * 2 ^ (26 * dg * L))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hN h1)
  have hmid : ((Records.symPool Cs carriers).length * symBud (gate0 l F).alg n) ≤
      8 * (n + 1) ^ 26 * symBud (gate0 l F).alg n := Nat.mul_le_mul_right _ hP
  have hexp : K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L + 1 ≤ K + cDa (gate0 l F).alg * L := by
    unfold cDa
    rw [← hCa, ← hdg]
    have : (6 + Nat.clog 2 Ca) * 1 ≤ (6 + Nat.clog 2 Ca) * L := Nat.mul_le_mul_left _ hL1
    nlinarith
  have hfin : 4 * 2 ^ K * ((Records.symPool Cs carriers).length * symBud (gate0 l F).alg n) + 1 ≤
      2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L + 1) := by
    rw [pow_succ]
    have := Nat.mul_le_mul_left (4 * 2 ^ K) hmid
    have h0 : 1 ≤ 2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L) := Nat.one_le_two_pow
    omega
  calc _ ≤ 4 * 2 ^ K * ((Records.symPool Cs carriers).length * symBud (gate0 l F).alg n) + 1 := by omega
    _ ≤ _ := hfin
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

