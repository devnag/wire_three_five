import Proof.Wire_3_5.Primitive.Writers.ThrHc3
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNE
import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly

/-! # c4 THR block, piece 3 part 1: the THR numbers machine's values are the call's

P3:2987-2988, 3154-3162 (`samp:q` at a THR call: `Q = thrCount`), P3:2543-2558 (`n_T = |GapSeed|·|𝒢|·Σp`), P3:1200
(`dRow`), P3:2238-2251 (the fixed hash's `2t·ℓ₀` bits): the numbers `bigT_spec` reads from the THR data word
(`hashNums`, W6's fourteen THR numbers after `|carriers|`, `capT`) and leaves in its registers are the call's own, so its
`FreeIn` is `thrX`; the hash bits' length is `2t·ℓ₀` at the data word's `t`, `ℓ₀`.

* `hnC` (the call's data word numbers), `hn0` … `hn7` (its entries), `filterParams_thr`, **`thrQ_link`**,
  **`thrNT_link`**, **`thrX_eq`**, `thrCallT_eq`, `thrCallJ_eq`, **`hbF_length`**.

Paper quantities of the main types: the THR call's `Q`, `n_T`, `dRow` and the fixed hash's bit count. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- **The THR call's data word numbers** (`hashNums` at the call's THR filter cap). -/
noncomputable abbrev hnC : List ℕ :=
  ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (I.filterParams .thr n).cap

/-- The data word's entry `k + 2` is W6's THR number `k`. -/
theorem hn_get (k : ℕ) (hk : k < 14) :
    (hnC I alg Cs carriers hs).getD (k + 2) 0 =
      (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).get
        ⟨k, hk⟩ := by
  unfold hnC ThrData.hashNums ThrData.thrNumList
  rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; exact hk), List.getElem_ofFn]
  rfl

theorem hn0 : (hnC I alg Cs carriers hs).getD 0 0 = carriers.length := by
  unfold hnC ThrData.hashNums; rw [List.getD_cons_zero]; rfl
theorem hn1 : (hnC I alg Cs carriers hs).getD 1 0 = (I.filterParams .thr n).cap := by
  unfold hnC ThrData.hashNums; rw [List.getD_cons_succ, List.getD_cons_zero]
theorem hn2 : (hnC I alg Cs carriers hs).getD 2 0 = Fintype.card (ThrEq (I.starParams n hs) Cs alg) := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, hn_get I alg Cs carriers hs 0 (by norm_num)]; rfl
theorem hn4 : (hnC I alg Cs carriers hs).getD 4 0 =
    thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, hn_get I alg Cs carriers hs 2 (by norm_num)]; rfl
theorem hn6 : (hnC I alg Cs carriers hs).getD 6 0 =
    ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, hn_get I alg Cs carriers hs 4 (by norm_num)]; rfl
theorem hn7 : (hnC I alg Cs carriers hs).getD 7 0 =
    thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) := by
  rw [show (7 : ℕ) = 5 + 2 from rfl, hn_get I alg Cs carriers hs 5 (by norm_num)]; rfl

/-- The THR filter is the decode's `gP` at the call's cap. -/
theorem filterParams_thr (hcd : I.carrierDeg = 26) :
    I.filterParams .thr n = SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n) := by
  unfold PrimitiveInputs.filterParams SymDec.gP Ledger.Lq; rw [hcd]

/-- **`Q` link**: the THR count is the numbers machine's `2^{(5kh+3)/4}·(I·8192·n·n)`. -/
theorem thrQ_link (hD : I.D = 1) (hcd : I.carrierDeg = 26) :
    SeedFix.thrCount alg I hs Cs =
      2 ^ ((SeedFix.callKh (I.starParams n hs) * 5 + 3) / 2 / 2) *
        ((Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
            ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) *
            2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
            (2 * (Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
              thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) + 1) *
            (2 * (Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
              thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) + 1) + 1) * 8192 * n * n) := by
  rw [ThrQ.thrCount_eq, ← filterParams_thr I hcd]
  unfold ThrQ.thrQval Sampler.sampleCount
  rw [hD]
  have e1 : (5 * SeedFix.callKh (I.starParams n hs) + 3) / 4 =
      (SeedFix.callKh (I.starParams n hs) * 5 + 3) / 2 / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (SeedFix.callKh _) 5]
  rw [e1]
  congr 1
  ring

/-- **`n_T` link**: the THR state count is the seed block's `2^{seedBits}·|𝒢|·Σp`. -/
theorem thrNT_link (hcd : I.carrierDeg = 26) :
    Enum.thrNT alg I hs Cs =
      2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
        Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
        ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) := by
  rw [Enum.thrNT_eq, filterParams_thr I hcd, Nat.mul_assoc]

/-- **The numbers machine's `FreeIn` is the call's `thrX`** (at the data word's entries). -/
theorem thrX_eq (hcd : I.carrierDeg = 26) :
    thrX I alg Cs carriers hs =
      ⟨(I.starParams n hs).n, (I.starParams n hs).s * ((I.starParams n hs).r / 2),
        Nat.clog 2 ((I.starParams n hs).n + 2), (hnC I alg Cs carriers hs).getD 1 0, (ReqBridge.thrCodes Cs).length,
        (carriers.map Carrier.code).length, (hnC I alg Cs carriers hs).getD 7 0, SeedFix.thrCount alg I hs Cs,
        max ((I.starParams n hs).s * ((I.starParams n hs).r / 2) + (I.starParams n hs).s * ((I.starParams n hs).r / 2))
          (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)),
        2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
          Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
          ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)),
        wOf ((I.starParams n hs).s * ((I.starParams n hs).r / 2)) (SeedFix.thrCount alg I hs Cs),
        ((I.starParams n hs).n - (I.starParams n hs).r * (I.starParams n hs).b + 1) / 2 +
          ((I.starParams n hs).b - (I.starParams n hs).s) * ((I.starParams n hs).r / 2)⟩ := by
  rw [hn1 I alg Cs carriers hs, hn7 I alg Cs carriers hs, ← thrNT_link I alg Cs hs hcd, PrimT.C4SymL.dRow_link,
    List.length_map,
    show (ReqBridge.thrCodes Cs).length = a by unfold ReqBridge.thrCodes; simp]
  rfl

/-- The call's `t` is W6's. -/
theorem thrCallT_tt : thrCallT alg I hs Cs carriers =
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).tt := by
  show listT (thrCallA alg I hs Cs) _ _ = listT _ _ _
  rw [← PrimThrW.Joins.thrNumVals_A alg I hs Cs carriers.length (I.filterParams .thr n).cap]
  rfl

/-- The call's `J` is W6's. -/
theorem thrCallJ_J : thrCallJ alg I hs Cs carriers =
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).J := by
  show listJ (thrCallA alg I hs Cs) _ _ = listJ _ _ _
  rw [← PrimThrW.Joins.thrNumVals_A alg I hs Cs carriers.length (I.filterParams .thr n).cap]
  rfl

/-- **The hash bits' length**: `frame hb` has `2·(2t·ℓ₀) + 1` bits at the data word's `t`, `ℓ₀`. -/
theorem hbF_length (translation : List ℕ) :
    (frame (List.ofFn (FinalPass.thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
      Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers)
      (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers)))).length =
      2 * (2 * (hnC I alg Cs carriers hs).getD 12 0 * (hnC I alg Cs carriers hs).getD 14 0) + 1 := by
  rw [SymDec.frame_length, List.length_ofFn, thrCallT_tt I alg Cs carriers hs, thrCallJ_J I alg Cs carriers hs,
    show (12 : ℕ) = 10 + 2 from rfl, show (14 : ℕ) = 12 + 2 from rfl, hn_get I alg Cs carriers hs 10 (by norm_num),
    hn_get I alg Cs carriers hs 12 (by norm_num)]
  have hM := PrimThrW.Joins.thrNumVals_MP (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg I.D
    (thrCallE alg I hs Cs carriers)
  show 2 * (2 * (thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).den
    (thrCallE alg I hs Cs carriers)
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).tt
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).J).t *
    (thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).den
    (thrCallE alg I hs Cs carriers)
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).tt
    (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).J).ell0) + 1 = _
  exact (congrArg (fun MP : Filters.MajorantParams => 2 * (2 * MP.t * MP.ell0) + 1) hM).trans rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
