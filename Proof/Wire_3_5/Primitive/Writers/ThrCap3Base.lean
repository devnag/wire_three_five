import Proof.Wire_3_5.Primitive.Writers.ThrCap2Base

/-! # PA2 c4 THR block, piece 3 part 3: the THR call's sizes fit the capacity v2

P3:2929-2941, 2994-3000, 3011-3016 (the THR stage's words at the call's `Q`, `ℓ`, `n_T`, `dRow`), P3:3105-3115 (every
size at an on-star call is `2^{O(k)}·poly(n)`, `k = O((B+1)²)`), (the capacity `2^{⌊n/8⌋ + C}`): at every THR call
of the gate, every capacity condition of the THR numbers machine (`bigT_spec`), of the hash bits' program
(`hbX_spec`) and of the numbers' seed and derived blocks (`SeedCap`, `DerCap`) holds at `M = 2^{capExp2 C n}` once
`C ≥ C₀`, for every free program whose program runs above `K·2^{⌊n/8⌋}` and whose values stay below it (the twin of
`sym_fits2`).

* `hbC` (the call's framed hash bits), **`ThrFitAt`**; `caps_ofT` (`caps_of` without positivity: `|𝒢|` may be
  `0`); **`thr_fits2`**.

Paper quantities of the main type: the THR call's sizes against the capacity `2^{⌊n/8⌋ + C}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires.WireExponent3_5.PrimT

/-- **The THR call's framed hash bits** (the tail of the THR stage's input). -/
noncomputable abbrev hbC {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ) (hs : I.StarAt n) : List Bool :=
  frame (List.ofFn (FinalPass.thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
    Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers)
    (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers)))

/-- **The THR call's sizes fit `M`** (`2·M + 2` the numbers machine's capacity): the free program's run and values,
the seed and derived blocks' fits, the request and hash bits, the numbers front's conditions. -/
structure ThrFitAt (Fp : FreeProg) (cr fe M : ℕ) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    (I : PrimitiveInputs B) (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) : Prop where
  ok : Fp.ok (2 * M + 2) (thrX I alg Cs carriers hs)
  fv : ∀ j, Fp.val (thrX I alg Cs carriers hs) j + 1 ≤ M
  fQ : SeedFix.thrCount alg I hs Cs + 1 ≤ M
  fkk : SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs) + 1 ≤ M
  fgs : 2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits + 1 ≤ M
  fG : Fintype.card (ThrEq (I.starParams n hs) Cs alg) + 1 ≤ M
  fpS : ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) + 1 ≤ M
  fgG : 2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
    Fintype.card (ThrEq (I.starParams n hs) Cs alg) + 1 ≤ M
  fNT : 2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
    Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
    ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) + 1 ≤ M
  fW : 2 ^ (wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) + 1) + 1 ≤ M
  fcnt : 2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
    Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
    ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) *
    2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) + 1 ≤ M
  fSm : 4 * (n + 2) + 1 ≤ M
  fd0 : SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs) +
    Fp.val (thrX I alg Cs carriers hs) 0 + 1 ≤ M
  fd1 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) * 8 *
    (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) +
      max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) + 1) + Fp.val (thrX I alg Cs carriers hs) 1 + 1 ≤ M
  fd3 : wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) + 1 +
    Fp.val (thrX I alg Cs carriers hs) 0 + 1 ≤ M
  fd4 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
    (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) * 8 + 1 ≤ M
  fl : 3 * max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
    (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) + SeedFix.thrCount alg I hs Cs + 1 ≤ M
  fwd : ((thrReq n a ha Cs carriers translation).word ++ hbC I alg Cs carriers translation hs).length + 1 ≤ M
  ftr : 8 * translation.length + 2 * (RepairRepresentation.natListWord translation).length + 16 ≤ 2 * M + 2
  fcP : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) +
    2 ^ (natBitLength (carriers.map Carrier.code).length + 1) + C4GateSym.needW n + n +
    (ReqBridge.thrCodes Cs).length + 1 ≤ 2 * M + 2
  fhn : ∀ v ∈ hnC I alg Cs carriers hs ++ ThrData.thrCounts Cs carriers, v + 1 ≤ M
  fcs : (carriers.map (·.length)).sum + (ThrTab.tupleG Cs).length + 4 ≤ 2 * M + 2
  fS : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ 2 * M + 2
  fT : (I.filterParams .thr n).cap * 32 + 2 ≤ 2 * M + 2
  fL : 2 * (n + 1) ^ 26 + 8 ≤ 2 * M + 2
  fE : I.filterErrDeg * Ledger.Lq n + 4 ≤ 2 * M + 2
  fSB : 2 ^ ((SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits + 1) ≤ 2 * M + 2
  fLB : (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).labelBits +
    (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).fieldBits +
    (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).walkLen + 512 ≤ 2 * M + 2
  fB : 2 * (Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
    thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) + 2 ≤ 2 * M + 2

/-- **The capacity conditions of the THR numbers machine** from the fits `X + 1 ≤ M` (pure arithmetic; the `caps_of`
with the factors' fits in place of their positivity). -/
theorem caps_ofT (M Q kh gs fs pi b s r n tw cp : ℕ) (fQ : Q + 1 ≤ M) (fkk : kh + kh + 1 ≤ M)
    (fgs : gs + 1 ≤ M) (ffs : fs + 1 ≤ M) (fpi : pi + 1 ≤ M) (fgf : gs * fs + 1 ≤ M)
    (fG : gs * fs * pi + 1 ≤ M) (fW : 2 ^ (wOf kh Q + 1) + 1 ≤ M) (fcnt : gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ M)
    (fSm : 4 * (n + 2) + 1 ≤ M) (sb1 : b ≤ n) (sb2 : s ≤ n) (sb3 : r ≤ n) (sb5 : (b - s) * (r / 2) ≤ n)
    (sb6 : r * b ≤ n) (sb8 : (n - r * b + 1) / 2 + (b - s) * (r / 2) ≤ 2 * n) (ftw : tw + 1 ≤ M) (_fcp : cp + 1 ≤ M)
    (fd0 : kh + kh + tw + 1 ≤ M)
    (fd1 : max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp +
      1 ≤ M)
    (fd3 : wOf kh Q + 1 + tw + 1 ≤ M) (fd4 : max (kh + kh) (Nat.clog 2 Q) * 8 + 1 ≤ M)
    (fl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 1 ≤ M) :
    SeedCap (2 * M + 2) Q kh gs fs pi b s (r / 2) r n ∧ DerCap (2 * M + 2) Q kh tw cp ∧
      (∀ i, derVals Q kh tw cp i + derVals Q kh tw cp i + 3 ≤ 2 * M + 2) ∧
      Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q) ∧ Q + 1 ≤ 2 * M + 2 ∧
      3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ 2 * M + 2 ∧ kh + kh + 1 ≤ 2 * M + 2 ∧
      gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ 2 * M + 2 ∧
      (0 + ((n - r * b + 1) / 2 + (b - s) * (r / 2)) + ((n - r * b + 1) / 2 + (b - s) * (r / 2))) +
        (0 + ((n - r * b + 1) / 2 + (b - s) * (r / 2)) + ((n - r * b + 1) / 2 + (b - s) * (r / 2))) + 3 ≤ 2 * M + 2 ∧
      17 ≤ 2 * M + 2 := by
  have hw2 : wOf kh Q + 1 < 2 ^ (wOf kh Q + 1) := Nat.lt_two_pow_self
  have hr2 : r / 2 ≤ r := Nat.div_le_self _ _
  have cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q) := by
    have h1 : Q ≤ 2 ^ Nat.clog 2 Q := Nat.le_pow_clog (by norm_num) Q
    have h2 : 2 ^ Nat.clog 2 Q ≤ 2 ^ max (kh + kh) (Nat.clog 2 Q) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have h3 : 1 ≤ 2 ^ max (kh + kh) (Nat.clog 2 Q) := Nat.one_le_two_pow
    omega
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, fun i => ?_, cQl, by omega, by omega,
    by omega, by omega, by omega, by omega⟩
  fin_cases i
  · show kh + kh + tw + (kh + kh + tw) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp +
      (max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp) + 3 ≤
      2 * M + 2
    omega
  · show wOf kh Q + 1 + (wOf kh Q + 1) + 3 ≤ 2 * M + 2; omega
  · show wOf kh Q + 1 + tw + (wOf kh Q + 1 + tw) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) * 8 + max (kh + kh) (Nat.clog 2 Q) * 8 + 3 ≤ 2 * M + 2; omega
  · show Q - 1 + (Q - 1) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) - 1 + (max (kh + kh) (Nat.clog 2 Q) - 1) + 3 ≤ 2 * M + 2; omega

theorem clog_le_self' (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem len_le_flat (tr : List ℕ) : tr.length ≤ (tr.flatMap RepairRepresentation.natWord).length := by
  induction tr with
  | nil => simp
  | cons t tr ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, ParseNat.natWord_length]
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
