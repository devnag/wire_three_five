import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrCap1
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ThrCap2Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 3 part 2: the THR call's sizes below `2^{e(B+1)²}`

P3:3105-3115 (every size at an on-star call is `2^{O(k)}·poly(n)`), P3:1189 (`k = O((B+1)²)`), P3:2987-2988 (`Q`),
P3:2543-2558 (the THR numbers, W6's `ThrNumsPoly`): at a THR call of the gate, the star width, the THR filter's cap,
the data word's entries, the THR count, the THR filter's seed space, the request's word and the `needW` are below
`2^{e·(B+1)²}` for constants `e` of the gate (`l`, `F`) and the words' polynomial bounds.

* `eCap`, `eTn`, `eQt`, `eSb`; **`thr_sizes`**; `thrX_small`.

Paper quantities of the main type: the THR call's sizes against `2^{(B+1)²}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires.WireExponent3_5.PrimT

/-- The exponent of the THR filter's cap. -/
noncomputable def eCap (l : Literals) (cr : ℕ) : ℕ := Nat.clog 2 (CallIndexR.capK cr) + CallIndexR.capZR l

/-- The exponent of the THR data word's entries (W6's `ThrNumsPoly` at the cap's coefficient). -/
noncomputable def eTn (l : Literals) (F : GateFree l) : ℕ :=
  Nat.clog 2 (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F) +
    HashLeaf.tnD (PrimT.W6.thrNumsPoly l)

/-- The exponent of the THR count. -/
noncomputable def eQt (l : Literals) (cr fe : ℕ) : ℕ :=
  Nat.clog 2 (16384 * CallIndexR.gapK cr) + (2 * cr + 2 + (CallIndexR.thrZI l fe + 2))

/-- The exponent of the THR filter's seed space. -/
noncomputable def eSb (l : Literals) (cr fe : ℕ) : ℕ := Nat.clog 2 (CallIndexR.gapK cr) + CallIndexR.gapZR l fe

/-- **The THR call's sizes** below `2^{e·(B+1)²}`. -/
theorem thr_sizes (l : Literals) (F : GateFree l) (Cw Dw Cnw Dnw : ℕ)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ Cw * (n + 1) ^ Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw)
    (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
        SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ (2 * F.cr + 2) * C4Cap.bsq n ∧
      ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ 2 ^ (eCap l F.cr * C4Cap.bsq n) ∧
      (∀ v ∈ hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs, v ≤ 2 ^ (eTn l F * C4Cap.bsq n)) ∧
      SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs ≤
        2 ^ (eQt l F.cr F.filterErrDeg * C4Cap.bsq n) ∧
      2 ^ ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).seedBits ≤
        2 ^ (eSb l F.cr F.filterErrDeg * C4Cap.bsq n) ∧
      (thrReq n a ha Cs carriers translation).word.length ≤ 2 ^ ((Nat.clog 2 Cw + Dw) * C4Cap.bsq n) ∧
      PrimT.C4GateSym.needW n ≤ 2 ^ ((Nat.clog 2 Cnw + Dnw) * C4Cap.bsq n) := by
  have hs1 := C4Cap.bsq_pos n
  obtain ⟨hk2, hdesc, -⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have p12 : ∀ d, (n + 1) ^ d ≤ 2 ^ (d * C4Cap.bsq n) := fun d =>
    le_trans (Nat.pow_le_pow_left (Nat.le_succ _) d) (C4Cap.pow_pw d n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2kh := HashFam.fam_two_kh l F kclk coef A a0 ha0 hs
    have hk := PrimT.C4SymN.kOf_le_bsq l F kclk coef A a0 ha0 n
    unfold SeedFix.callKh
    omega
  · have h := CallIndexR.cap_leR l F.cr .thr n
    have e2 : ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap =
        Ledger.rowBCap (gateCap l) .thr (Ledger.rowBr F.cr n) (gateSp l n) n := rfl
    rw [e2]
    exact C4Cap.pw_K hs1 (le_trans h (Nat.mul_le_mul_left _ (C4Cap.pow_pw _ n)))
  · intro v hv
    have h := HashLeaf.tn_spec (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F
      kclk coef A a0 ha0 n hs Cs carriers _ ha hk2 hdesc (HashFam.fam_capT l F kclk coef A a0 ha0 n) v hv
    exact C4Cap.pw_K hs1 (le_trans h (Nat.mul_le_mul_left _ (p12 _)))
  · have hQ := CallIndexR.thrCount_leK l F kclk coef A a0 ha0 n hs ha Cs hdesc
    have hk := PrimT.C4SymN.kOf_le_bsq l F kclk coef A a0 ha0 n
    have h1 : 2 ^ (5 * ((gate0 l F).budget kclk coef A a0 ha0).kOf n / 8) ≤ 2 ^ ((2 * F.cr + 2) * C4Cap.bsq n) :=
      C4Cap.pw_exp (by omega)
    have h3 := C4Cap.pw_mul h1 (C4Cap.pow_pw (CallIndexR.thrZI l F.filterErrDeg + 2) n)
    exact C4Cap.pw_K hs1 (le_trans hQ (le_of_eq_of_le (Nat.mul_assoc _ _ _) (Nat.mul_le_mul_left _ h3)))
  · rw [← Filters.card_gapSeed]
    exact C4Cap.pw_K hs1 (le_trans (CallIndexR.gapSeed_leR l F kclk coef A a0 ha0 .thr n)
      (Nat.mul_le_mul_left _ (C4Cap.pow_pw _ n)))
  · have h := CallSize.gate_word_length_le l F kclk coef A a0 ha0 _ hcall
    exact C4Cap.pw_K hs1 (le_trans h (le_trans (hwb n) (Nat.mul_le_mul_left _ (p12 _))))
  · exact C4Cap.pw_K hs1 (le_trans (hnw n) (Nat.mul_le_mul_left _ (p12 _)))

section Small

end Small

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap

end
