import Proof.Wire_3_5.FinalPass.HashS
import Proof.Wire_3_5.Primitive.Writers.HashCellK
import Proof.Wire_3_5.Primitive.Writers.ThrCap2

/-! # HASH setup (C), fit part 1: the THR call's sizes in the unit `2^{(B+1)²}`

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`") and P3:3170-3181 (the seed phase's capacity
`2^{⌊n/8⌋ + C}`): every size the HASH cell's capacity facts (`CellFit`) read at a THR call is at most `2^{E·(B+1)²}`
(`B` the bit length of `n`), with `E` fixed by the literals and the gate: the request word and the capacity numbers
(`ThrCap.thr_sizes`), the call's sixteen numbers (the THR numbers' polynomial bound), the carriers' sizes, the pool and
the occurrences, the cutoff, the aux seeds `nE = 2^{seedBits}`, the populations' stream (`HashFr` sizes in the
unit `⌈log₂(n+2)⌉ + 1`, whose square is at most `4(B+1)²`), and each circuit's payload (`ThrSz.payOf_le`).

* `clog_le_b`, `clogsq_le`, `pwX`, `pwXsq`; **`CallSz`**, **`call_sizes`**.

Paper quantities of the main type: the THR call's sizes (P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimT

theorem clog_le_b (n : ℕ) : Nat.clog 2 (n + 2) ≤ natBitLength n + 1 := Nat.clog_le_of_le_pow (C4Cap.n2_le n)

theorem clogsq_le (n : ℕ) : (Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1) ≤ 4 * C4Cap.bsq n := by
  have h := clog_le_b n
  have h2 : Nat.clog 2 (n + 2) + 1 ≤ 2 * (natBitLength n + 1) := by omega
  have e : C4Cap.bsq n = (natBitLength n + 1) * (natBitLength n + 1) := by unfold C4Cap.bsq; ring
  calc (Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1) ≤ (2 * (natBitLength n + 1)) * (2 * (natBitLength n + 1)) :=
        Nat.mul_le_mul h2 h2
    _ = 4 * C4Cap.bsq n := by rw [e]; ring

theorem pwX {X c n : ℕ} (h : X ≤ 2 ^ (c * Nat.clog 2 (n + 2))) : X ≤ 2 ^ (c * C4Cap.bsq n) :=
  le_trans h (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (le_trans (clog_le_b n) (C4Cap.b1_le_bsq n))))

theorem pwX1 {X c n : ℕ} (h : X ≤ 2 ^ (c * (Nat.clog 2 (n + 2) + 1))) : X ≤ 2 ^ ((2 * c) * C4Cap.bsq n) := by
  refine le_trans h (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 := clog_le_b n
  have h2 := C4Cap.b1_le_bsq n
  have : Nat.clog 2 (n + 2) + 1 ≤ 2 * C4Cap.bsq n := by omega
  calc c * (Nat.clog 2 (n + 2) + 1) ≤ c * (2 * C4Cap.bsq n) := Nat.mul_le_mul_left _ this
    _ = 2 * c * C4Cap.bsq n := by ring

theorem pwXsq {X c n : ℕ} (h : X ≤ 2 ^ (c * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)))) :
    X ≤ 2 ^ ((4 * c) * C4Cap.bsq n) := by
  refine le_trans h (Nat.pow_le_pow_right (by norm_num) ?_)
  calc c * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)) ≤ c * (4 * C4Cap.bsq n) :=
        Nat.mul_le_mul_left _ (clogsq_le n)
    _ = 4 * c * C4Cap.bsq n := by ring

theorem pwP (d n : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * C4Cap.bsq n) :=
  le_trans (Nat.pow_le_pow_left (Nat.le_succ _) d) (C4Cap.pow_pw d n)

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)

/-- **The THR call's sizes** below `2^{E·(B+1)²}`. -/
structure CallSz (E : ℕ) : Prop where
  w : (thrReq n a ha Cs carriers translation).word.length ≤ 2 ^ (E * C4Cap.bsq n)
  n3 : n + 3 ≤ 2 ^ (E * C4Cap.bsq n)
  hn : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg
    (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap,
    v ≤ 2 ^ (E * C4Cap.bsq n)
  sx : (carriers.map List.length).sum ≤ 2 ^ (E * C4Cap.bsq n)
  tg : (PrimT.ThrTab.tupleG Cs).length ≤ 2 ^ (E * C4Cap.bsq n)
  cp : ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ 2 ^ (E * C4Cap.bsq n)
  kh : SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
    SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ E * C4Cap.bsq n
  nE : WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers ≤ 2 ^ (E * C4Cap.bsq n)
  M : (thrOccs ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs).length ≤ 2 ^ (E * C4Cap.bsq n)
  G : (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers).length ≤
    2 ^ (E * C4Cap.bsq n)
  cut : thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
    (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) ≤ 2 ^ (E * C4Cap.bsq n)
  pops : (PrimT.HbM.popsWord (PrimT.C4H.hashPopsOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs
    carriers)).length ≤ 2 ^ (E * C4Cap.bsq n)
  pay : ∀ i, (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length ≤ 2 ^ (E * C4Cap.bsq n)
  cr : F.cr + 20 ≤ E

end Call

/-- **The THR call's sizes**: one exponent `E` for every THR call of the gate. -/
theorem call_sizes (l : Literals) (F : GateFree l) : ∃ E : ℕ, ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ)
    (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ), (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
      CallSz l F kclk coef A a0 ha0 ha Cs carriers translation hs E := by
  obtain ⟨cA, hcA⟩ : ∃ x, x = (gate0 l F).alg.coefficient := ⟨_, rfl⟩
  obtain ⟨dA, hdA⟩ : ∃ x, x = (gate0 l F).alg.degree := ⟨_, rfl⟩
  obtain ⟨eP, heP⟩ : ∃ x, x = Nat.clog 2 (11 + 2 * cA * 3 ^ dA) + (26 + 26 * dA) := ⟨_, rfl⟩
  obtain ⟨eW, heW⟩ : ∃ x, x = Nat.clog 2 HashLeaf.wbC + HashLeaf.wbD := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ x, x = eW + 3 + ThrCap.eTn l F + 27 + 30 + ThrCap.eCap l F.cr + (2 * F.cr + 2) +
      4 * FinalPass.HashFr.cN l + 56 + 60 + (10 * CallIndex.algX l + 32) + 2 * (24 * CallIndex.algX l + 127) + eP +
      F.cr + 20 := ⟨_, rfl⟩
  refine ⟨E, fun kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs => ?_⟩
  have hs1 := C4Cap.bsq_pos n
  have mono : ∀ {X e : ℕ}, X ≤ 2 ^ (e * C4Cap.bsq n) → e ≤ E → X ≤ 2 ^ (E * C4Cap.bsq n) :=
    fun hX he => C4Cap.pw_mono he hX
  obtain ⟨hk2, hdesc, henv⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hkk, hcapT, hhn, -, -, hwl, -⟩ := ThrCap.thr_sizes l F HashLeaf.wbC HashLeaf.wbD HashLeaf.nwC HashLeaf.nwD
    HashLeaf.wb_spec HashLeaf.nw_spec kclk coef A a0 ha0 ha Cs carriers translation hcall hs
  have hn3 : n + 3 ≤ 2 ^ (2 * C4Cap.bsq n) := by
    have h1 := C4Cap.n2_pw n
    have h2 : 2 ^ (1 * C4Cap.bsq n) * 2 ≤ 2 ^ (2 * C4Cap.bsq n) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ 2 ^ (1 * C4Cap.bsq n) := Nat.one_le_two_pow
    omega
  refine ⟨mono hwl (by omega), mono hn3 (by omega), fun v hv => mono (hhn v hv) (by omega), ?_, ?_,
    mono hcapT (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · have h := FinalPass.HashFr.sumX_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall
    have h2 : (carriers.map List.length).sum ≤ 2 ^ ((1 + 26) * Nat.clog 2 (n + 2)) := by
      rw [add_mul, one_mul, pow_add]
      have : 2 ≤ 2 ^ Nat.clog 2 (n + 2) := by
        have := Nat.one_lt_two_pow_iff.mpr (show Nat.clog 2 (n + 2) ≠ 0 from by
          have := Nat.clog_pos (b := 2) (by norm_num) (show 2 ≤ n + 2 by omega); omega)
        omega
      calc _ ≤ 2 * 2 ^ (26 * Nat.clog 2 (n + 2)) := h
        _ ≤ 2 ^ Nat.clog 2 (n + 2) * 2 ^ (26 * Nat.clog 2 (n + 2)) := Nat.mul_le_mul_right _ this
    exact mono (pwX h2) (by omega)
  · have h := C4GateSym.tupleG_len_le Cs ((n + 1) ^ 26) hdesc
    have h2 : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * 2 ^ (26 * C4Cap.bsq n) :=
      le_trans h (Nat.mul_le_mul ha (pwP 26 n))
    exact mono (C4Cap.pw_K hs1 h2) (by rw [show Nat.clog 2 4 = 2 by rfl]; omega)
  · exact le_trans hkk (Nat.mul_le_mul_right _ (by omega))
  · exact mono (pwXsq (FinalPass.HashFr.nE_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs)) (by omega)
  · exact mono (pwX1 (FinalPass.HashFr.M_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs)) (by omega)
  · have h := FinalPass.HashFr.G_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    have h2 : 2 ^ (3 + 26 * Nat.clog 2 (n + 2)) ≤ 2 ^ (30 * C4Cap.bsq n) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := le_trans (clog_le_b n) (C4Cap.b1_le_bsq n)
      omega
    exact mono (le_trans h h2) (by omega)
  · exact mono (pwX (FinalPass.HashFr.cut_le' l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs)) (by omega)
  · exact mono (pwX1 (FinalPass.HashFr.popsW_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs)) (by omega)
  · intro i
    have h := FinalPass.ThrSz.payOf_le (gate0 l F).alg (Cs i) ((n + 1) ^ 26) (hdesc i)
    unfold RepairSource.CloseoutRawRows.sourceChildBound at h
    rw [← hcA, ← hdA] at h
    have p26 := pwP 26 n
    have hL2 : (n + 1) ^ 26 + 2 ≤ 3 * 2 ^ (26 * C4Cap.bsq n) := by
      have : 1 ≤ 2 ^ (26 * C4Cap.bsq n) := Nat.one_le_two_pow
      omega
    have hpow : ((n + 1) ^ 26 + 2) ^ dA ≤ 3 ^ dA * 2 ^ ((26 * dA) * C4Cap.bsq n) := by
      calc ((n + 1) ^ 26 + 2) ^ dA ≤ (3 * 2 ^ (26 * C4Cap.bsq n)) ^ dA := Nat.pow_le_pow_left hL2 _
        _ = 3 ^ dA * 2 ^ ((26 * dA) * C4Cap.bsq n) := by rw [mul_pow, ← pow_mul]; ring_nf
    have hq1 : 1 ≤ 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) := Nat.one_le_two_pow
    have hq2 : 2 ^ (26 * C4Cap.bsq n) ≤ 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hq3 : 2 ^ ((26 * dA) * C4Cap.bsq n) ≤ 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hb : (PrimThrW.TopFront.payOf (gate0 l F).alg (Cs i)).length ≤
        (11 + 2 * cA * 3 ^ dA) * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) := by
      have m1 : cA * ((n + 1) ^ 26 + 2) ^ dA ≤ cA * 3 ^ dA * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) := by
        calc cA * ((n + 1) ^ 26 + 2) ^ dA ≤ cA * (3 ^ dA * 2 ^ ((26 * dA) * C4Cap.bsq n)) := Nat.mul_le_mul_left _ hpow
          _ ≤ cA * (3 ^ dA * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq3)
          _ = cA * 3 ^ dA * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) := by ring
      have e : (11 + 2 * cA * 3 ^ dA) * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) =
          11 * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n) + 2 * (cA * 3 ^ dA * 2 ^ ((26 + 26 * dA) * C4Cap.bsq n)) := by ring
      rw [e]
      omega
    exact mono (C4Cap.pw_K hs1 hb) (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.HashFit
