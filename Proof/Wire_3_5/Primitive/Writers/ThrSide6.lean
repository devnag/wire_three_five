import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrSide5Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide3
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 6 part 6: the THR pool's coefficient width and dense pool (twin of the SymPool)

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094) and alg:disjoint's child bits (P3:1596-1615): at a THR call every pool gate (a carrier atom,
its complement `negGate`, or an occurrence of a circuit's bottom gate) has at most `(n+1)^{26} + 1` encoding bits, so
the decomposition algorithm's budget at every pool gate is at most the `symBud a n`; hence the pool fits any `h`
with `symBud a n + n + 2 ≤ h` (the `PoolFit.poolFits_of`, generic in `h`: THR's and HASH's `h` alike), and the
dense pool has at most `2^{k + cDa·L}` children.

* **`thrPool_bits`**, **`thr_budget_le`**, **`thr_fits_of`**, **`thrD_le`**.

Paper quantities of the main types: the THR pool's coefficient bits against `h`, the THR dense pool's size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (symBud symBud_le' cDa enc_negGate enc_nonStrict n2_le_L one_le_L
  kh_two densePool_length_le)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The THR dense pool is below `2^{k + cDa·L}`** at a THR call. -/
theorem thrD_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (h Q psi : ℕ) :
    (Pool.densePool (gate0 l F).alg
      (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) h Q psi).gates
      (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
      (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))).flatten.length + 1 ≤
      2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + cDa (gate0 l F).alg * Nat.clog 2 (n + 2)) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hB := thr_budget_le (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers hcar hd
  have hP := thrPool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hDl := densePool_length_le (gate0 l F).alg
    ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG)
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
  show (Pool.densePool (gate0 l F).alg
    ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).map PrimT.C4Geo.suppG)
    _ _ _).flatten.length + 1 ≤ _
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
  have hmid : ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length *
      symBud (gate0 l F).alg n) ≤ 8 * (n + 1) ^ 26 * symBud (gate0 l F).alg n := Nat.mul_le_mul_right _ hP
  have hexp : K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L + 1 ≤ K + cDa (gate0 l F).alg * L := by
    unfold cDa
    rw [← hCa, ← hdg]
    have : (6 + Nat.clog 2 Ca) * 1 ≤ (6 + Nat.clog 2 Ca) * L := Nat.mul_le_mul_left _ hL1
    nlinarith
  have hfin : 4 * 2 ^ K * ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length *
      symBud (gate0 l F).alg n) + 1 ≤ 2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L + 1) := by
    rw [pow_succ]
    have := Nat.mul_le_mul_left (4 * 2 ^ K) hmid
    have h0 : 1 ≤ 2 ^ (K + 5 + 26 * L + Nat.clog 2 Ca + 26 * dg * L) := Nat.one_le_two_pow
    omega
  calc _ ≤ 4 * 2 ^ K * ((Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length *
        symBud (gate0 l F).alg n) + 1 := by omega
    _ ≤ _ := hfin
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide

end
