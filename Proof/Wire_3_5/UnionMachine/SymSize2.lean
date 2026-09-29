import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.Primitive.Writers.SymSizes
import Proof.Wire_3_5.UnionMachine.SymSize1

/-! # hS, part 2: **the SYM size polynomial** `symSize_poly`

At a SYM call of the family (`Sd.SymSizeOK`'s hypotheses: carriers `≤ 2`, descriptions `≤ (n+1)^26`), the atoms of
part 1 are below `Y = c_S(c_r)·N^{Z_S}`, `N = n + 2`, `Z_S = flatZR l + capZR l + 52` (the literals only):
the bottom gates `≤ (n+1)^26`, their table width `≤ 35N^52` (`Sd.hof35`), the top tables, the walk length
`t ≤ L + 6` (`errExp = L + 5` at `D = 1`), the levels and windows from the list bound `B = |carriers|·4096·B_S ≤
8192·capK·N^{capZR}` (`CallIndexR.cap_leR`), the population `M ≤ 4(n+1)^26`, and `|FlatSeed| ≤ flatK·N^{flatZR}`
(`CallIndexR.flatSeed_leR`). So `symSize ≤ 600Y⁴ ≤ C_sz·(n+1)^{4Z_S}`:

* `gate_enc_le`, **`tabH_sym`**, `ZS`, `cS`, `YS`, **`atoms_call`**, **`symSize_poly`** ('s statement:
  `∀ l, ∃ D_sz, ∀ F, ∃ C_sz, ∀ kclk coef A a ha, Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval C_sz D_sz`).

Paper quantity of the main type: the SYM per-point evaluator's input size, polynomial in `n` (P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SymSize
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.S3 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall symCallOf)

theorem gate_enc_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (i : Fin C.bottomCount) :
    (C.bottom i).gate.encodingBits ≤ C.descriptionBits := by
  have h := PrimT.SymTab.gate_desc_le C i
  unfold SupportedNormalizedGate.descriptionBits at h
  omega

/-- **The SYM bottom gates' table width** at descriptions `≤ L`. -/
theorem tabH_sym {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L) :
    PrimT.tabH (Stars.symGates C) ≤ L * (8 * n + 8 * L + 19) := by
  have hlen : (Stars.symGates C).length ≤ L := by
    unfold Stars.symGates
    rw [List.length_map, List.length_finRange]
    have := PrimT.TabCost.symDesc_pos C
    omega
  unfold PrimT.tabH PrimT.tabSeg
  rw [List.length_flatMap]
  have hsum := List.sum_le_card_nsmul ((Stars.symGates C).map fun g => (frame (PrimT.tabGW g)).length)
    (8 * n + 8 * L + 19) (fun x hx => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      unfold Stars.symGates at hg
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      have h1 := ThrSz.tabGW_len (C.bottom i).gate
      have h2 := (gate_enc_le C i).trans hL
      rw [frame_len]
      omega)
  rw [smul_eq_mul, List.length_map] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ hlen)

/-- The size exponent (the literals only). -/
noncomputable def ZS (l : Literals) : ℕ := CallIndexR.flatZR l + CallIndexR.capZR l + 52

/-- The size coefficient (`c_r` only). -/
def cS (cr : ℕ) : ℕ := 2 ^ 26 * (CallIndexR.capK cr + 1) + CallIndexR.flatK cr + 100

/-- **The atoms' bound** at length `n`. -/
noncomputable def YS (l : Literals) (cr n : ℕ) : ℕ := cS cr * (n + 2) ^ ZS l

theorem clog_self (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The call's atoms below `Y`.** -/
theorem atoms_call {n a' : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (hcar : carriers.length ≤ 2)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    AtomsY (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) (YS l F.cr n) := by
  obtain ⟨M, hM⟩ : ∃ M, M = (n + 2) ^ ZS l := ⟨_, rfl⟩
  have hY : YS l F.cr n = cS F.cr * M := by rw [hM]; rfl
  have pZ : ∀ e, e ≤ ZS l → (n + 2) ^ e ≤ M := fun e he => by
    rw [hM]; exact Nat.pow_le_pow_right (by omega) he
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.one_le_pow _ _ (by omega)
  have toY : ∀ {x c : ℕ}, x ≤ c * M → c ≤ cS F.cr → x ≤ YS l F.cr n := fun hx hc => by
    rw [hY]; exact hx.trans (Nat.mul_le_mul_right _ hc)
  have hN1 : n + 2 ≤ M := by have := pZ 1 (by unfold ZS; omega); rwa [pow_one] at this
  have h26 : (n + 1) ^ 26 ≤ M := (Nat.pow_le_pow_left (by omega) 26).trans (pZ 26 (by unfold ZS; omega))
  have hcK := CallIndexR.capK_pos F.cr
  -- the list bound
  have hcap := CallIndexR.cap_leR l F.cr .sym n
  have hB : (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B ≤
      8192 * CallIndexR.capK F.cr * M := by
    have eB : (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B =
        carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n) := rfl
    have hZ : CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l ≤ CallIndexR.capK F.cr * M :=
      Nat.mul_le_mul_left _ (pZ _ (by unfold ZS; omega))
    rw [eB]
    calc carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n)
        ≤ 2 * (4096 * (CallIndexR.capK F.cr * M)) :=
          Nat.mul_le_mul hcar (Nat.mul_le_mul_left _ (hcap.trans hZ))
      _ = 8192 * CallIndexR.capK F.cr * M := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact toY (c := 1) (by rw [one_mul]; exact hM1) (by unfold cS; omega)
  · show n + 1 ≤ _
    exact toY (c := 1) (by rw [one_mul]; omega) (by unfold cS; omega)
  · intro j
    refine toY (c := 1) ?_ (by unfold cS; omega)
    rw [one_mul]
    unfold gatesJ
    split_ifs with hj
    · show (Stars.symGates (Cs ⟨j.val, hj⟩)).length ≤ M
      unfold Stars.symGates
      rw [List.length_map, List.length_finRange]
      exact (CallIndex.bottomCount_le _ (hd _)).trans h26
    · simp
  · intro j
    refine toY (c := 35) ?_ (by unfold cS; omega)
    unfold gatesJ
    split_ifs with hj
    · show PrimT.tabH (Stars.symGates (Cs ⟨j.val, hj⟩)) ≤ 35 * M
      have h1 := tabH_sym (Cs ⟨j.val, hj⟩) ((n + 1) ^ 26) (hd _)
      have h2 := Sd.hof35 n
      have h3 : (n + 2) ^ 52 ≤ M := pZ 52 (by unfold ZS; omega)
      have e : (n + 1) ^ 26 * (8 * n + 8 * (n + 1) ^ 26 + 19) = (n + 1) ^ 26 * (8 * n + 19 + 8 * (n + 1) ^ 26) := by
        ring
      rw [e] at h1
      omega
    · show PrimT.tabH ([] : List (NormalizedThresholdGate n)) ≤ 35 * M
      unfold PrimT.tabH PrimT.tabSeg
      simp
  · intro j
    refine toY (c := 1) ?_ (by unfold cS; omega)
    rw [one_mul]
    unfold topJ
    split_ifs with hj
    · show (List.ofFn (Cs ⟨j.val, hj⟩).top).length ≤ M
      rw [List.length_ofFn]
      exact ((PrimT.TabCost.symDesc_pos _).trans (hd _)).trans h26
    · simp
  · refine toY (c := 5) ?_ (by unfold cS; omega)
    have ew : (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen =
        2 * ((1 * Nat.clog 2 (n + 2) + 5) / 4) + 1 := rfl
    show (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen ≤ _
    rw [ew]
    have := clog_self (n + 2)
    omega
  · refine toY (c := 8192 * CallIndexR.capK F.cr + 10) ?_ (by unfold cS; omega)
    have eJ : (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.J =
        Nat.clog 2 (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B + 9 := rfl
    show (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.J + 1 ≤ _
    rw [eJ]
    have := clog_self (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B
    have e : (8192 * CallIndexR.capK F.cr + 10) * M = 8192 * CallIndexR.capK F.cr * M + 10 * M := by ring
    rw [e]
    omega
  · intro i
    refine toY (c := 4096 * (8192 * CallIndexR.capK F.cr) + 65) ?_ (by unfold cS; omega)
    have eW : (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.W i =
        64 + (CanonicalFourfoldRowProgram.natCeilSqrt
          (64 ^ 2 * (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B) ⌈/⌉
            2 ^ (i / 3)) := rfl
    show (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.W i ≤ _
    rw [eW]
    have h1 := SymSizes.ceilDiv_le_self (CanonicalFourfoldRowProgram.natCeilSqrt
      (64 ^ 2 * (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B)) (2 ^ (i / 3))
      Nat.one_le_two_pow
    have h2 := LevelW.natCeilSqrt_le
      (64 ^ 2 * (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B)
    have h3 : 64 ^ 2 * (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B ≤
        4096 * (8192 * CallIndexR.capK F.cr * M) := by
      rw [show (64 : ℕ) ^ 2 = 4096 by norm_num]; exact Nat.mul_le_mul_left _ hB
    have e : (4096 * (8192 * CallIndexR.capK F.cr) + 65) * M =
        4096 * (8192 * CallIndexR.capK F.cr * M) + 65 * M := by ring
    rw [e]
    omega
  · refine toY (c := 4) ?_ (by unfold cS; omega)
    show ∑ i, (Cs i).bottomCount ≤ 4 * M
    calc ∑ i, (Cs i).bottomCount ≤ ∑ _i : Fin a', M :=
          Finset.sum_le_sum (fun i _ => (CallIndex.bottomCount_le _ (hd i)).trans h26)
      _ = a' * M := by simp
      _ ≤ 4 * M := Nat.mul_le_mul_right _ ha'
  · refine toY (c := CallIndexR.flatK F.cr) ?_ (by unfold cS; omega)
    exact (CallIndexR.flatSeed_leR l F kclk coef A a ha n ha' Cs carriers hd hcar).trans
      (Nat.mul_le_mul_left _ (pZ _ (by unfold ZS; omega)))

end Call

/-- **: the SYM size polynomial** — `D_sz = 4Z_S` from the literals, `C_sz` after `F`. -/
theorem symSize_poly (l : Literals) : ∃ Dsz : ℕ, ∀ F : GateFree l, ∃ Csz : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval Csz Dsz := by
  refine ⟨4 * ZS l, fun F => ⟨600 * cS F.cr ^ 4 * 2 ^ (4 * ZS l), fun kclk coef A a ha => ?_⟩⟩
  intro n hs a' ha' Cs carriers hcar hd
  have h := symSize_le (atoms_call l F kclk coef A a ha hs ha' Cs carriers hcar hd)
  have e : Sd.symSize PrimT.S3.symPtEval (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) =
      PrimT.S3.symSize (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) := rfl
  rw [e]
  refine h.trans ?_
  have hN : (n + 2) ^ (4 * ZS l) ≤ 2 ^ (4 * ZS l) * (n + 1) ^ (4 * ZS l) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc 600 * YS l F.cr n ^ 4 = 600 * cS F.cr ^ 4 * (n + 2) ^ (4 * ZS l) := by
        unfold YS; rw [mul_pow, ← pow_mul, Nat.mul_comm (ZS l) 4]; ring
    _ ≤ 600 * cS F.cr ^ 4 * (2 ^ (4 * ZS l) * (n + 1) ^ (4 * ZS l)) := Nat.mul_le_mul_left _ hN
    _ = 600 * cS F.cr ^ 4 * 2 ^ (4 * ZS l) * (n + 1) ^ (4 * ZS l) := by ring

end NearCubicWires.WireExponent3_5.UnionMachine.SymSize
