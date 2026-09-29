import Proof.Wire_3_5.FinalPass.SymCap1
import Proof.Wire_3_5.FinalPass.SymOcc2
import Proof.Wire_3_5.Primitive.Writers.BShape6
import Proof.Wire_3_5.Primitive.Writers.SymSizes
import Proof.Wire_3_5.UnionMachine.FiltPipeLe

/-! # The SYM enumeration's capacity, part 2: the SYM rows' words and the degree bound

P3:3011-3016 at a SYM call: every printed SYM row's word (`sym_word_le`, BShape6) is below
`2^{(26L+7)D + k + 80L + 24}` (`M ≤ 4(n+1)^{26}`, the walk `w ≤ L + 4`, `|pool| ≤ 8(n+1)^{26}`, `2k_h = k`), so the batch's
`bsz` is; and the degree bound `D = max(384·w_f + 1, 3·lbP)` of `sym_factor_count` is at most
`384(f_e L + 1) + 1 + 3(71 + 12k + ZL)(23296⌊√B_S⌋ + 23553)` (the filter walk `w_f ≤ f_e L + 1`; `lbP_le` at
`B' = 8192·B_S`, `B_S ≤ capK(c_r)(n+2)^Z`, `4c_r ≤ k`).

* `symDg`, `nb_le`, **`symBsz_le`**, **`symDg_le`**.

Paper quantities of the main types: the SYM batch's row words and the list bound `Σ_j W_j` (list:base P3:1376-1398). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- A bit length below an exponent. -/
theorem nb_le (x m : ℕ) (h : x ≤ 2 ^ m) : natBitLength x ≤ m + 1 := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log_pow (by norm_num)] at this
  omega

/-- `(n+1)^{26} ≤ 2^{26L}`. -/
theorem n26_le (n : ℕ) : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) :=
  pow_mono_mul 26 (le_trans (by omega) (n2_le_L n))

section Gate
variable (l : Literals) (F : GateFree l)

/-- The degree bound of the SYM rows' factors (`sym_factor_count`). -/
noncomputable def symDg (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) : ℕ :=
  max (384 * ((callInputs l F kclk coef A a ha).filterParams .sym n).walkLen + 1)
    (3 * PopLink.lbP (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers))

/-- **The SYM batch's row words** below `2^{(26L+7)D + k + 80L + 24}`. -/
theorem symBsz_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimT.C4Grp.bsz (symExprs (callInputs l F kclk coef A a ha) hs Cs carriers) ≤
      2 ^ ((26 * Nat.clog 2 (n + 2) + 7) * symDg l F kclk coef A a ha Cs carriers +
        ((gate0 l F).budget kclk coef A a ha).kOf n + 80 * Nat.clog 2 (n + 2) + 24) := by
  have hW := BShape.sym_word_le (callInputs l F kclk coef A a ha) hs Cs carriers
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hN := n26_le n
  have hkh := kh_two l F kclk coef A a ha hs
  -- the list's population count
  have hM : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).M + 1 ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 3) := by
    show (∑ i, (Cs i).bottomCount) + 1 ≤ _
    have h1 : ∑ i, (Cs i).bottomCount ≤ a' * (n + 1) ^ 26 := by
      calc _ ≤ ∑ _i : Fin a', (n + 1) ^ 26 := Finset.sum_le_sum fun i _ => CallIndex.bottomCount_le (Cs i) (hd i)
        _ = _ := by simp
    have h2 := Nat.mul_le_mul_right ((n + 1) ^ 26) ha'
    rw [pow_add]
    have h3 : 1 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.one_le_two_pow
    norm_num
    omega
  -- the list's walk
  have hw : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen ≤ Nat.clog 2 (n + 2) + 4 := by
    show 2 * ((1 * Nat.clog 2 (n + 2) + 5) / 4) + 1 ≤ _
    omega
  -- the pool
  have hP := symPool_length_le ha' Cs carriers hcar hnc hd
  have hG : 4 * (Records.symPool Cs carriers).length + 1 ≤ 2 ^ (26 * Nat.clog 2 (n + 2) + 6) := by
    rw [pow_add]
    have h3 : 1 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.one_le_two_pow
    norm_num
    omega
  have hA : 4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
      2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) * (Records.symPool Cs carriers).length + 1 ≤
      2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + 26 * Nat.clog 2 (n + 2) + 6) := by
    rw [← pow_add, ← two_mul, hkh, pow_add, pow_add]
    have h3 : 1 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.one_le_two_pow
    have h4 : 1 ≤ 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n := Nat.one_le_two_pow
    have h5 := Nat.mul_le_mul_left (2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n)
      (show (Records.symPool Cs carriers).length ≤ 8 * 2 ^ (26 * Nat.clog 2 (n + 2)) by omega)
    have e : 4 * 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (Records.symPool Cs carriers).length =
        4 * (2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (Records.symPool Cs carriers).length) := by ring
    have e2 : 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * (8 * 2 ^ (26 * Nat.clog 2 (n + 2))) =
        8 * (2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * 2 ^ (26 * Nat.clog 2 (n + 2))) := by ring
    have h6 : 1 ≤ 2 ^ ((gate0 l F).budget kclk coef A a ha).kOf n * 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.mul_pos h4 h3
    norm_num
    omega
  unfold symDg
  generalize max (384 * ((callInputs l F kclk coef A a ha).filterParams .sym n).walkLen + 1)
    (3 * PopLink.lbP (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)) = Dg at hW ⊢
  generalize (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).M = M at hM hW
  generalize (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).walkLen = w at hw hW
  generalize (Records.symPool Cs carriers).length = G at hG hA hW
  generalize 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) = N2 at hA hW
  generalize ((gate0 l F).budget kclk coef A a ha).kOf n = K at hA ⊢
  generalize Nat.clog 2 (n + 2) = L at hM hw hG hA ⊢
  refine EnumCap.bsz_le _ _ Nat.one_le_two_pow (fun V hV => (hW V hV).trans ?_)
  have hT : (M + 1) ^ 2 * 2 ^ w ≤ 2 ^ (53 * L + 10) := by
    have h1 := pow_mono_mul 2 hM
    have h2 : 2 ^ w ≤ 2 ^ (L + 4) := Nat.pow_le_pow_right (by norm_num) hw
    calc (M + 1) ^ 2 * 2 ^ w ≤ 2 ^ (2 * (26 * L + 3)) * 2 ^ (L + 4) := Nat.mul_le_mul h1 h2
      _ = 2 ^ (53 * L + 10) := by rw [← pow_add]; congr 1; ring
  have hw' : w ≤ 2 ^ (L + 4) := le_trans hw (Nat.lt_two_pow_self).le
  have hK : (4 * G + 1) ^ Dg ≤ 2 ^ ((26 * L + 6) * Dg) := by
    have := pow_mono_mul Dg hG
    rwa [Nat.mul_comm Dg] at this
  have hD : Dg ≤ 2 ^ Dg := (Nat.lt_two_pow_self).le
  have key := EnumCap.wordB_le ((M + 1) ^ 2 * 2 ^ w) w ((4 * G + 1) ^ Dg) Dg (4 * (N2 * N2) * G) (53 * L + 10)
    (L + 4) ((26 * L + 6) * Dg) Dg (K + 26 * L + 6) hT hw' hK hD hA
  refine key.trans (le_of_eq ?_)
  congr 1
  ring

/-- **The SYM degree bound** `D ≤ 384(f_e L + 1) + 1 + 3(71 + 12k + ZL)(23296⌊√B_S⌋ + 23553)`. -/
theorem symDg_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    symDg l F kclk coef A a ha Cs carriers ≤ 384 * (F.filterErrDeg * Nat.clog 2 (n + 2) + 1) + 1 +
      3 * ((71 + 12 * ((gate0 l F).budget kclk coef A a ha).kOf n + CallIndexR.capZR l * Nat.clog 2 (n + 2)) *
        (23296 * Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + 23553)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have h1 : ((callInputs l F kclk coef A a ha).filterParams .sym n).walkLen ≤
      F.filterErrDeg * Nat.clog 2 (n + 2) + 1 :=
    UnionMachine.FiltPipeLe.walkLen_le ((callInputs l F kclk coef A a ha).filterParams .sym n)
  obtain ⟨C, hCd⟩ : ∃ C, C = ((gate0 l F).budget kclk coef A a ha).capOf .sym n := ⟨_, rfl⟩
  have hB : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).B ≤ 8192 * C := by
    show carriers.length * (4096 * ((gate0 l F).budget kclk coef A a ha).capOf .sym n) ≤ _
    rw [← hCd]
    have := Nat.mul_le_mul_right (4096 * C) hnc
    omega
  have h2 := SymSizes.lbP_le _ (8192 * C) hB
  -- the bit length
  have hc : C ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := by
    rw [hCd]; exact CallIndexR.cap_leR l F.cr .sym n
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hK1 := capK_le F.cr
  have hZ := pow_N_le n (CallIndexR.capZR l)
  have h3 : 8192 * C ≤ 2 ^ (13 + 48 * (F.cr + 1) + CallIndexR.capZR l * Nat.clog 2 (n + 2)) := by
    rw [pow_add, pow_add]
    calc 8192 * C ≤ 8192 * (CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l) := Nat.mul_le_mul_left _ hc
      _ ≤ 8192 * (2 ^ (48 * (F.cr + 1)) * 2 ^ (CallIndexR.capZR l * Nat.clog 2 (n + 2))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hK1 hZ)
      _ = 2 ^ 13 * 2 ^ (48 * (F.cr + 1)) * 2 ^ (CallIndexR.capZR l * Nat.clog 2 (n + 2)) := by ring
  have h4 := nb_le _ _ h3
  -- the ceiling square root
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.sqrt C := ⟨_, rfl⟩
  have h5 : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * (8192 * C)) ≤ 5824 * (S + 1) := by
    apply SymSizes.natCeilSqrt_le_of
    have hs' : C < (S + 1) * (S + 1) := by rw [hSd]; exact Nat.lt_succ_sqrt C
    have e : 5824 * (S + 1) * (5824 * (S + 1)) = 33918976 * ((S + 1) * (S + 1)) := by ring
    rw [e]
    norm_num
    omega
  have h6 : PopLink.lbP (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers) ≤
      (71 + 12 * ((gate0 l F).budget kclk coef A a ha).kOf n + CallIndexR.capZR l * Nat.clog 2 (n + 2)) *
        (23296 * S + 23553) :=
    h2.trans (Nat.mul_le_mul (by omega) (by omega))
  unfold symDg
  rw [← hCd, ← hSd]
  exact max_le (by omega) (by omega)

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
