import Proof.Wire_3_5.Primitive.Writers.ThrCap2

/-! # c4 THR block, piece 3 part 3: the THR call's sizes fit the capacity v2

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

/-- **The capacity conditions of the THR numbers machine** from the fits `X + 1 ≤ M` (pure arithmetic; `caps_of`
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

/-- **The THR call's sizes fit the capacity v2** `2^{⌊n/8⌋ + C}` once `C ≥ C₀`. -/
theorem thr_fits2 (l : Literals) (F : GateFree l) (Fp : FreeProg)
    (hok : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), C4SymW.FreeSmall Ds x → Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x)
    (hval : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), C4SymW.FreeSmall Ds x → j.val ≠ 6 →
      Fp.val x j ≤ Kv * 2 ^ (x.n / 8))
    (hrho : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr)
    (Cw Dw Cnw Dnw : ℕ) (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ Cw * (n + 1) ^ Dw)
    (hnw : ∀ n, C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) :
    ∃ Cc0 : ℕ, ∀ Cc : ℕ, Cc0 ≤ Cc → ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
      ThrFitAt Fp F.cr F.filterErrDeg (2 ^ C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs
        carriers translation hs := by
  obtain ⟨Kr, Dr, hr⟩ := hrho
  -- the exponents
  obtain ⟨ek, hek⟩ : ∃ x, x = 2 * F.cr + 2 := ⟨_, rfl⟩
  obtain ⟨eC, heC⟩ : ∃ x, x = eCap l F.cr := ⟨_, rfl⟩
  obtain ⟨eT, heT⟩ : ∃ x, x = eTn l F := ⟨_, rfl⟩
  obtain ⟨eq, heq⟩ : ∃ x, x = eQt l F.cr F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨eS, heS⟩ : ∃ x, x = eSb l F.cr F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨eWd, heWd⟩ : ∃ x, x = Nat.clog 2 Cw + Dw := ⟨_, rfl⟩
  obtain ⟨eN, heN⟩ : ∃ x, x = Nat.clog 2 Cnw + Dnw := ⟨_, rfl⟩
  obtain ⟨eW, heW⟩ : ∃ x, x = 9 + 8 * (ek + eq) + 8 * ek := ⟨_, rfl⟩
  obtain ⟨eH, heH⟩ : ∃ x, x = 2 * eT + 10 := ⟨_, rfl⟩
  obtain ⟨eR, heR⟩ : ∃ x, x = Nat.clog 2 Kr + Dr := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ x, x = eT + eq + ek + eC + eS + eW + eT + eT + 40 := ⟨_, rfl⟩
  obtain ⟨Ko, hok'⟩ := hok Ds
  obtain ⟨Kv, hval'⟩ := hval Ds
  obtain ⟨U, hU⟩ : ∃ x, x = 4 * (ek + eC + eT + eq + eS + eWd + eN + eW + eH + eR + Ds + F.cr + F.filterErrDeg) + 100 :=
    ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := C4Cap.mul_sq_le_div16 U
  obtain ⟨K1, hK1⟩ : ∃ x, x = K0 + Nat.clog 2 Kv := ⟨_, rfl⟩
  refine ⟨K1 + Nat.clog 2 Ko + 12,
    fun Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs => ?_⟩
  -- the size unit `s = (B+1)²`, `e = ⌊n/8⌋`, `M = 2^{e + Cc}` and `E₀ = 2^{e + K₁}`
  obtain ⟨s, hsd⟩ : ∃ x, x = C4Cap.bsq n := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hsd ▸ C4Cap.bsq_pos n
  obtain ⟨e, hed⟩ : ∃ x, x = n / 8 := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ x, x = 2 ^ C4Cap.capExp2 Cc n := ⟨_, rfl⟩
  have hMe : M = 2 ^ (e + Cc) := by rw [hMd, hed]; rfl
  rw [← hMd]
  obtain ⟨E0, hE0⟩ : ∃ x, x = 2 ^ (e + K1) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E0 := hE0 ▸ Nat.one_le_two_pow
  have hME : 2048 * E0 ≤ M := by
    rw [hMe, hE0, show (2048 : ℕ) = 2 ^ 11 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUs : U * s ≤ e + K0 := by
    have h1 := hK0 n
    have h2 : U * s = U * (natBitLength n + 1) ^ 2 := by rw [hsd]; rfl
    omega
  have toE : ∀ {X a : ℕ}, X ≤ 2 ^ (a * s) → a ≤ U → X ≤ E0 := fun hX ha => by
    rw [hE0]
    exact le_trans hX (Nat.pow_le_pow_right (by norm_num)
      (le_trans (Nat.mul_le_mul_right s ha) (le_trans hUs (by omega))))
  have pwl : ∀ {x e : ℕ}, x ≤ e * s → x ≤ 2 ^ (e * s) := fun hx => C4Cap.pw_lin hx
  have pwc : ∀ {X c : ℕ}, X ≤ c → X ≤ 2 ^ (c * s) := fun hX => C4Cap.pw_const hs1 hX
  have pwp : ∀ {X Y a b : ℕ}, X ≤ 2 ^ (a * s) → Y ≤ 2 ^ (b * s) → X * Y ≤ 2 ^ ((a + b) * s) :=
    fun hX hY => C4Cap.pw_mul hX hY
  have hsz : ∀ {X e' : ℕ}, X ≤ 2 ^ (e' * s) → e' ≤ Ds → X ≤ 2 ^ (Ds * C4Cap.bsq n) := fun hX he => by
    rw [← hsd]; exact C4Cap.pw_mono he hX
  -- the call's facts and sizes
  obtain ⟨hk2, hdesc, henv⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  obtain ⟨hkk, hcapT, hhn, hQ, hsb, hwl, hnW⟩ :=
    thr_sizes l F Cw Dw Cnw Dnw hwb hnw kclk coef A a0 ha0 ha Cs carriers translation hcall hs
  rw [← hsd, ← hek] at hkk
  rw [← hsd, ← heC] at hcapT
  rw [← hsd, ← heT] at hhn
  rw [← hsd, ← heq] at hQ
  rw [← hsd, ← heS, filterParams_thr _ rfl] at hsb
  rw [← hsd, ← heWd] at hwl
  rw [← hsd, ← heN] at hnW
  have hN2 : n + 2 ≤ 2 ^ (1 * s) := by rw [hsd]; exact C4Cap.n2_pw n
  have hmem : ∀ k, k < 16 → (hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD k 0 ≤
      2 ^ (eT * s) := fun k hk => hhn _ (HashSizes.hashNums_getD_mem _ _ _ _ _ _ k hk)
  have hG : Fintype.card (ThrEq ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg) ≤
      2 ^ (eT * s) := by
    rw [← hn2 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs]; exact hmem 2 (by norm_num)
  have hc : thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) ≤ 2 ^ (eT * s) := by
    rw [← hn4 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs]; exact hmem 4 (by norm_num)
  have hpS : ThrQ.primeSum (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)) ≤ 2 ^ (eT * s) := by
    rw [← hn6 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs]; exact hmem 6 (by norm_num)
  have hdig : thrDigits ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) ≤ 2 ^ (eT * s) := by
    rw [← hn7 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs]; exact hmem 7 (by norm_num)
  have hgG := pwp hsb hG
  have hNT := pwp hgG hpS
  have hell : max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)) ≤ (ek + eq) * s :=
    max_le (le_trans hkk (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      (le_trans (C4Cap.clog_pw hQ) (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
  have hw1 : wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) + 1 ≤ eW * s := by
    rw [heW]; exact C4SymN.w_le hell hkk hs1
  have hl3 := C4SymN.l3_le hell hs1
  have hbl : (hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length ≤
      2 ^ (eH * s) := by
    rw [hbF_length]
    have h1 := pwp (pwp (pwp (pwc (le_refl 2)) (pwc (le_refl 2))) (hmem 12 (by norm_num))) (hmem 14 (by norm_num))
    have h2 := C4Cap.pw_add hs1 h1 (pwc (le_refl 1))
    refine C4Cap.pw_mono ?_ (le_of_eq_of_le ?_ h2)
    · rw [heH]; omega
    · ring
  have hwd : ((thrReq n a ha Cs carriers translation).word ++
      hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length ≤
      2 ^ ((eWd + eH + 1) * s) := by
    rw [List.length_append]; exact C4Cap.pw_add hs1 hwl hbl
  have hSm : 4 * (n + 2) ≤ 2 ^ ((4 + 1) * s) := pwp (pwc (le_refl 4)) hN2
  have hdR : C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ 2 ^ ((4 + 1) * s) :=
    le_trans (C4SymN.dRow_le _) hSm
  -- the call's numbers are small
  have hFS : C4SymW.FreeSmall Ds (thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) :=
    thrX_small (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs Ds
      (hsz (le_trans (Nat.le_add_right n 2) hN2) (by omega))
      (hsz (pwl (le_trans (Nat.le_add_left _ _) hkk)) (by omega))
      (hsz (pwl (by rw [one_mul, hsd]; exact C4Cap.lq_le_bsq n)) (by omega)) (hsz hcapT (by omega))
      (hsz (pwc ha) (by omega)) (hsz (pwc hk2) (by omega)) (hsz hdig (by omega)) (hsz hQ (by omega))
      (hsz (pwl hell) (by omega))
      (hsz (le_of_eq_of_le (thrNT_link _ _ Cs hs rfl) hNT) (by omega))
      (hsz (pwl (le_trans (Nat.le_succ _) hw1)) (by omega)) (hsz hdR (by omega))
  -- the free numbers
  have hfv : ∀ j : Fin 7, Fp.val (thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) j ≤ E0 := by
    intro j
    by_cases hj : j.val = 6
    · have hj' : j = 6 := Fin.ext hj
      subst hj'
      have h2 : (n + 1) ^ Dr ≤ 2 ^ (Dr * s) :=
        le_trans (Nat.pow_le_pow_left (Nat.le_succ _) Dr) (by rw [hsd]; exact C4Cap.pow_pw Dr n)
      have h3 : Fp.val (thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6 ≤ Kr * 2 ^ (Dr * s) :=
        le_trans (hr _) (Nat.mul_le_mul_left _ h2)
      exact toE (C4Cap.pw_K hs1 h3) (by rw [← heR]; omega)
    · have h3 : Fp.val (thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) j ≤ Kv * 2 ^ e := by
        rw [hed]; exact hval' _ j hFS hj
      rw [hE0]
      exact C4SymN.mono8 (by omega) (C4SymN.of_K h3)
  have hF : Fp.ok (2 * M + 2) (thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) := by
    apply hok' _ _ hFS
    have h1 : Ko * 2 ^ e ≤ 2 ^ (e + Nat.clog 2 Ko) := C4SymN.of_K le_rfl
    have h2 : 2 ^ (e + Nat.clog 2 Ko) ≤ M := by rw [hMe]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : Ko * 2 ^ e ≤ 2 * M + 2 := by omega
    rw [hed] at h3
    exact h3
  -- the atoms below `E₀`
  have aQ := toE hQ (by omega)
  have akk := toE (pwl hkk) (by omega)
  have asb := toE hsb (by omega)
  have aG := toE hG (by omega)
  have apS := toE hpS (by omega)
  have agG := toE hgG (by omega)
  have aNT := toE hNT (by omega)
  have aW := toE (C4Cap.pw_exp hw1) (by omega)
  have acnt := toE (pwp hNT (C4Cap.pw_exp (le_trans (Nat.le_succ _) hw1))) (by omega)
  have an := toE hN2 (by omega)
  have ad1 := toE (pwp (pwp (pwl hell) (pwc (le_refl 8))) (pwl hl3)) (by omega)
  have aw1 := toE (pwl hw1) (by omega)
  have a8 := toE (pwp (pwl hell) (pwc (le_refl 8))) (by omega)
  have a3 := toE (pwp (pwc (le_refl 3)) (pwl hell)) (by omega)
  have awd := toE hwd (by omega)
  have anW := toE hnW (by omega)
  have a26 : (n + 1) ^ 26 ≤ E0 :=
    toE (le_trans (Nat.pow_le_pow_left (Nat.le_succ _) 26) (by rw [hsd]; exact C4Cap.pow_pw 26 n)) (by omega)
  have acap := toE hcapT (by omega)
  have aerr : F.filterErrDeg * Ledger.Lq n ≤ E0 :=
    toE (pwl (Nat.mul_le_mul_left _ (by rw [hsd]; exact C4Cap.lq_le_bsq n))) (by omega)
  have hn3 : n + 3 ≤ 2 ^ ((1 + 1 + 1) * s) := C4Cap.pw_add (X := n + 2) (Y := 1) hs1 hN2 (pwc (le_refl 1))
  have afe4 := toE (pwp (pwc (le_refl (F.filterErrDeg + 4))) hn3) (by omega)
  have acr := toE (pwc (le_refl (2 * F.cr + 20))) (by omega)
  have aGc := toE (pwp hG hc) (by omega)
  have ahn : ∀ v ∈ hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs, v ≤ E0 :=
    fun v hv => toE (hhn v hv) (by omega)
  -- the counts
  have hcx : ∀ c ∈ carriers.map (·.length), c ≤ (n + 1) ^ 26 := by
    intro c hc'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc'
    exact (henv X hX).1
  have hxs : (carriers.map (·.length)).sum ≤ 2 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (carriers.map (·.length)) ((n + 1) ^ 26) hcx
    rw [List.length_map, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ hk2)
  have htg : (ThrTab.tupleG Cs).length ≤ 4 * (n + 1) ^ 26 :=
    le_trans (C4GateSym.tupleG_len_le Cs _ hdesc) (Nat.mul_le_mul_right _ ha)
  -- the request's parts
  have hwsplit : (thrReq n a ha Cs carriers translation).word = Data.reqW n true (ReqBridge.thrCodes Cs)
      (carriers.map Carrier.code) (RepairRepresentation.natListWord translation) := by
    have h := ReqBridge.reqW_thrReq ha Cs carriers translation []
    rw [List.append_nil, List.append_nil] at h
    exact h.symm
  have htr1 : (RepairRepresentation.natListWord translation).length ≤ (thrReq n a ha Cs carriers translation).word.length := by
    rw [hwsplit]; unfold Data.reqW; simp only [List.length_append]; omega
  have htr2 : translation.length ≤ (RepairRepresentation.natListWord translation).length := by
    unfold RepairRepresentation.natListWord
    rw [List.length_append]
    have := len_le_flat translation
    omega
  have hcodes : (ReqBridge.thrCodes Cs).length = a := by unfold ReqBridge.thrCodes; simp
  have hwlen : (thrReq n a ha Cs carriers translation).word.length ≤
      ((thrReq n a ha Cs carriers translation).word ++
        hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length := by
    rw [List.length_append]; omega
  have b1 : 2 ^ (natBitLength n + 1) ≤ 4 * n + 4 := by
    have := CopyNat.two_pow_natBitLength_le n; rw [pow_succ]; omega
  have b2 := C4GateSym.nbl_small (ReqBridge.thrCodes Cs).length (by rw [hcodes]; exact ha)
  have b3 := C4GateSym.nbl_small (carriers.map Carrier.code).length (by rw [List.length_map]; omega)
  -- the filter's bit counts
  have l3 : (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).labelBits ≤
      32 * ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap + 2 * (n + 1) ^ 26 := by
    unfold Filters.GapParams.labelBits Filters.GapParams.prefixBits
    exact max_le (le_trans (clog_le_self' _) (Nat.le_add_right _ _)) (le_trans (clog_le_self' _) (Nat.le_add_left _ _))
  have l4 : (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).fieldBits ≤ 2 * (n + 1) ^ 26 + 4 := by
    unfold Filters.GapParams.fieldBits; exact Nat.add_le_add_right (clog_le_self' _) 4
  have l5 : (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).walkLen ≤
      F.filterErrDeg * Ledger.Lq n + 1 := by
    unfold Filters.GapParams.walkLen; show 2 * (F.filterErrDeg * Ledger.Lq n / 4) + 1 ≤ _; omega
  have hsb2 : 2 ^ ((SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).seedBits + 1) =
      2 * 2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).seedBits := by rw [pow_succ]; ring
  have fv := fun j => hfv j
  exact {
    ok := hF
    fv := fun j => by have := fv j; omega
    fQ := by omega
    fkk := by omega
    fgs := by omega
    fG := by omega
    fpS := by omega
    fgG := by omega
    fNT := by omega
    fW := by omega
    fcnt := by omega
    fSm := by have := toE hSm (by omega); omega
    fd0 := by have := fv 0; omega
    fd1 := by have := fv 1; omega
    fd3 := by have := fv 0; omega
    fd4 := by omega
    fl := by omega
    fwd := by omega
    ftr := by omega
    fcP := by rw [hcodes] at b2 ⊢; omega
    fhn := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · have := ahn v hv; omega
      · unfold ThrData.thrCounts at hv
        rcases List.mem_append.mp hv with hv | hv
        · have := hcx v hv; omega
        · rw [List.mem_singleton] at hv; rw [hv]; omega
    fcs := by omega
    fS := by omega
    fT := by omega
    fL := by omega
    fE := by show F.filterErrDeg * Ledger.Lq n + 4 ≤ _; omega
    fSB := by rw [hsb2]; omega
    fLB := by omega
    fB := by omega }

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
