import Proof.Wire_3_5.Primitive.Writers.ThrSide2

/-! # c4 THR block, piece 6 part 3: the THR rows' degree and words, and the enumeration's capacity

P3:2121-2157 (filt:majorant's windows `W_j = 16t + 20(⌊√(tB_*)⌋+1)/2^{⌊j/2⌋} + 20`), P3:3094-3107 (the THR degree
`d_T = C_D(√(B_T L) + L²)` in the load `Ψ_T = C_D²(k+L)²(√(B_T L) + L²)`), P3:3011-3016: at a THR call the rows'
factor degree `D_T = max(384·w_f + 1, 3·Σ_j(4W_j+1))` is at most `d_{DT}(⌊√(B_T L)⌋ + L²)` (`d_{DT}` fixed before `F`),
every row's word is below `2^{e_b}` (`thr_word_le`), and under the load floor `16·thrC1 ≤ C_D` (fixed before `F`)
and `12 d_T ≤ d_C` the capacity `2^{⌊n/16⌋ + d_C L²}` covers `capC·(qG+1)^6`: the enumeration's hypotheses hold at
every child prefix (the mode-generic `EnumCap.enumOk_of`). The twin of the SymDeg, SymCap1–3.

* `loadThr_le`, `sqrt_le_mul`, `sum_div_pow2_le`; `thrDg`, `dDT`, **`thrDg_lin`**; `eb`, **`thrBsz_le`**;
  `thrC1`, **`thrE_num`**.

Paper quantities of the main types: the THR degree `d_T`, the THR rows' words and the enumeration's group size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (cK pow_N_le one_le_L n2_le_L kh_two cr_le_k pow_mono_mul
  sum_div_pow3_le)
open Finset

/-- **The THR load**: `C_D²(k+L)²(⌊√(B_T L)⌋ + L²) ≤ Ψ`. -/
theorem loadThr_le (CD k L BT BS : ℕ) :
    CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) ≤ loadPsi CD k L BT BS := by
  have h1 : loadThr CD k L BT ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_max_left _ _
  refine le_trans ?_ h1
  unfold loadThr sqrtUp
  have e : CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) =
      CD * ((k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2))) := by ring
  rw [e]
  apply Nat.mul_le_mul_left
  have : (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + 1 + L ^ 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

/-- `⌊√y⌋ ≤ c(⌊√x⌋ + 1)` when `y ≤ c²x`. -/
theorem sqrt_le_mul {x y c : ℕ} (h : y ≤ c * c * x) : Nat.sqrt y ≤ c * (Nat.sqrt x + 1) := by
  have hx : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp at h; subst h; simp
  have h2 : y < c * (Nat.sqrt x + 1) * (c * (Nat.sqrt x + 1)) := by
    have e : c * (Nat.sqrt x + 1) * (c * (Nat.sqrt x + 1)) = c * c * ((Nat.sqrt x + 1) * (Nat.sqrt x + 1)) := by ring
    rw [e]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_left hx (Nat.mul_pos hc hc))
  exact Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (lt_of_lt_of_le h2 (by nlinarith)))

/-- `Σ_{j<J} ⌊C/2^{⌊j/2⌋}⌋ ≤ 6C`. -/
theorem sum_div_pow2_le (C J : ℕ) : ∑ j ∈ range J, C / 2 ^ (j / 2) ≤ 6 * C :=
  (sum_le_sum fun j _ => Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) Nat.one_le_two_pow).trans
    (sum_div_pow3_le C J)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The THR rows' factor degree** (`thr_factors_ok`). -/
noncomputable def thrDg (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) : ℕ :=
  max (384 * ((callInputs l F kclk coef A a ha).filterParams .thr n).walkLen + 1)
    (3 * ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
      translation))

/-- `201326592·(2e_J + 1)`: the square of the constant of `√(t·B_*)`. -/
noncomputable def sqK (l : Literals) : ℕ := 201326592 * (2 * eJ l + 1)

/-- **The THR degree constant** (fixed before `F`). -/
noncomputable def dDT (l : Literals) (fe : ℕ) : ℕ :=
  3 * (eJ l * (128 * eJ l + 145)) + 1440 * sqK l + 2880 + 384 * fe + 385

/-- **The THR degree is `≤ d_{DT}(⌊√(B_T L)⌋ + L²)`**, uniformly in `F` (the paper's `d_T = C_D(√(B_T L) + L²)`). -/
theorem thrDg_lin (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    thrDg l F kclk coef A a ha Cs carriers translation hs ≤ dDT l F.filterErrDeg *
      (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .thr n * Nat.clog 2 (n + 2)) +
        Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hL1 := one_le_L n
  have hJ := thrCallJ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hT := thrCallT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hw : ((callInputs l F kclk coef A a ha).filterParams .thr n).walkLen ≤
      F.filterErrDeg * Nat.clog 2 (n + 2) + 1 :=
    UnionMachine.FiltPipeLe.walkLen_le ((callInputs l F kclk coef A a ha).filterParams .thr n)
  -- the list bound: `J(64t + 81) + 80 Σ_j ⌊C/2^{⌊j/2⌋}⌋`
  obtain ⟨J, hJd⟩ : ∃ J, J = thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers := ⟨_, rfl⟩
  obtain ⟨cT, hcTd⟩ : ∃ c, c = ((gate0 l F).budget kclk coef A a ha).capOf .thr n := ⟨_, rfl⟩
  obtain ⟨Bst, hBd⟩ : ∃ B, B = a' * (4096 * ((carriers.length + 1) * (4096 * cT))) := ⟨_, rfl⟩
  have hLB : ListMachine.listBound (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
      translation) = (∑ j ∈ range J, 4 * (16 * t + 20 * ((Nat.sqrt (t * Bst) + 1) / 2 ^ (j / 2) + 1))) + 1 := by
    rw [hJd, htd, hBd, hcTd]; rfl
  obtain ⟨C, hCd⟩ : ∃ C, C = Nat.sqrt (t * Bst) + 1 := ⟨_, rfl⟩
  rw [← hCd] at hLB
  have hsum : ∑ j ∈ range J, 4 * (16 * t + 20 * (C / 2 ^ (j / 2) + 1)) =
      J * (64 * t + 80) + 80 * ∑ j ∈ range J, C / 2 ^ (j / 2) := by
    rw [show (fun j => 4 * (16 * t + 20 * (C / 2 ^ (j / 2) + 1))) = fun j => (64 * t + 80) + 80 * (C / 2 ^ (j / 2))
      by funext j; ring, sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]
  have h6 := sum_div_pow2_le C J
  -- `√(t·B_*) ≤ sqK·(⌊√(B_T L)⌋ + 1)`
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd] at hL1 hJ hT hw ⊢
  rw [← hJd] at hJ
  rw [← htd] at hT
  rw [← hcTd]
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.sqrt (cT * L) := ⟨_, rfl⟩
  rw [← hSd]
  have hB : Bst ≤ 201326592 * cT := by
    rw [hBd]
    have h1 : a' * (4096 * ((carriers.length + 1) * (4096 * cT))) ≤ 4 * (4096 * (3 * (4096 * cT))) :=
      Nat.mul_le_mul ha' (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
    omega
  have hsq1 : 1 ≤ sqK l := by unfold sqK; omega
  have htB : t * Bst ≤ sqK l * sqK l * (cT * L) := by
    have h1 : t * Bst ≤ ((2 * eJ l + 1) * L) * (201326592 * cT) := Nat.mul_le_mul hT hB
    have h2 : ((2 * eJ l + 1) * L) * (201326592 * cT) = sqK l * (cT * L) := by unfold sqK; ring
    have h3 : sqK l * (cT * L) ≤ sqK l * sqK l * (cT * L) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hsq1)
    omega
  have hC : C ≤ sqK l * (S + 1) + 1 := by rw [hCd, hSd]; have := sqrt_le_mul htB; omega
  -- the degree
  have hLL : L ≤ L * L := Nat.le_mul_of_pos_left _ hL1
  have hL2 : 1 ≤ L * L := Nat.mul_pos hL1 hL1
  have hJt : J * (64 * t + 80) ≤ eJ l * (128 * eJ l + 145) * (L * L) := by
    have h1 : J * (64 * t + 80) ≤ (eJ l * L) * (64 * ((2 * eJ l + 1) * L) + 81) :=
      Nat.mul_le_mul hJ (by omega)
    have h2 : (eJ l * L) * (64 * ((2 * eJ l + 1) * L) + 81) = eJ l * (128 * eJ l + 64) * (L * L) + 81 * eJ l * L := by
      ring
    have h3 : 81 * eJ l * L ≤ 81 * eJ l * (L * L) := Nat.mul_le_mul_left _ hLL
    have h4 : eJ l * (128 * eJ l + 145) * (L * L) = eJ l * (128 * eJ l + 64) * (L * L) + 81 * eJ l * (L * L) := by ring
    omega
  unfold thrDg
  rw [hLB, hsum]
  have eD : dDT l F.filterErrDeg * (S + L * L) = 3 * (eJ l * (128 * eJ l + 145) * S) + 1440 * (sqK l * S) + 2880 * S +
      384 * (F.filterErrDeg * S) + 385 * S + (3 * (eJ l * (128 * eJ l + 145) * (L * L)) + 1440 * (sqK l * (L * L)) +
        2880 * (L * L) + 384 * (F.filterErrDeg * (L * L)) + 385 * (L * L)) := by unfold dDT; ring
  rw [eD]
  have hfe : F.filterErrDeg * L ≤ F.filterErrDeg * (L * L) := Nat.mul_le_mul_left _ hLL
  have hsK : sqK l * (S + 1) = sqK l * S + sqK l := by ring
  have hsK2 : sqK l ≤ sqK l * (L * L) := Nat.le_mul_of_pos_right _ hL2
  have h80 : 80 * ∑ j ∈ range J, C / 2 ^ (j / 2) ≤ 480 * C := by
    have := Nat.mul_le_mul_left 80 h6; omega
  have hC2 : 480 * C ≤ 480 * (sqK l * S) + 480 * sqK l + 480 := by
    have := Nat.mul_le_mul_left 480 hC
    have e : 480 * (sqK l * (S + 1) + 1) = 480 * (sqK l * S) + 480 * sqK l + 480 := by ring
    omega
  apply max_le
  · have := Nat.mul_le_mul_left 384 hw
    have e : 384 * (F.filterErrDeg * L + 1) = 384 * (F.filterErrDeg * L) + 384 := by ring
    omega
  · omega

/-- The fixed hash's list data has the call's occurrences as its states. -/
theorem thrCallD_M (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M =
      (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length := by
  unfold Records.thrCallD FinalPass.MajorantBits.dataBits
  rfl

/-- **The THR pool** `|thrPool| ≤ 8(n+1)^{26}`. -/
theorem thrPool_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 8 * (n + 1) ^ 26 := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hM := occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hP := HashCall.hash_pool (gate0 l F).alg ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
  rw [HashCall.hashNums_M] at hP
  change 2 * (carriers.map List.length).sum + (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length =
    (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length at hP
  have hxs : (carriers.map List.length).sum ≤ 2 * (n + 1) ^ 26 := by
    have hb : ∀ x ∈ carriers.map List.length, x ≤ (n + 1) ^ 26 := by
      intro x hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hcar X hX).1
    have := List.sum_le_card_nsmul (carriers.map List.length) ((n + 1) ^ 26) hb
    rw [List.length_map, smul_eq_mul] at this
    have := Nat.mul_le_mul_right ((n + 1) ^ 26) hnc
    omega
  omega

/-- The THR rows' word exponent. -/
def eb (dig L D k : ℕ) : ℕ :=
  2 * dig * (26 * L + 3) + (2 * dig + 1) + (26 * L + 6) * D + D + (k + 26 * L + 6) + 4

/-- The row-word shape below `2^{e_b}` (pure arithmetic). -/
theorem thr_word_arith (M dig G D N2 k L : ℕ) (hM : M + 1 ≤ 2 ^ (26 * L + 3)) (hG : 4 * G + 1 ≤ 2 ^ (26 * L + 6))
    (hA : 4 * N2 * G + 1 ≤ 2 ^ (k + 26 * L + 6)) :
    ((M + 1) ^ 2) ^ dig * ((2 * dig + 1) * ((4 * G + 1) ^ D * (2 * D * (4 * N2 * G + 1) + 2) + 1 + 1) + 6 + 1) + 1 ≤
      2 ^ eb dig L D k := by
  have hT : ((M + 1) ^ 2) ^ dig ≤ 2 ^ (2 * dig * (26 * L + 3)) := by
    have h2 := pow_mono_mul 2 hM
    have h3 := pow_mono_mul dig h2
    exact h3.trans (le_of_eq (by ring_nf))
  have hw : 2 * dig + 1 ≤ 2 ^ (2 * dig + 1) := (Nat.lt_two_pow_self).le
  have hK := pow_mono_mul D hG
  have hD : D ≤ 2 ^ D := (Nat.lt_two_pow_self).le
  have key := FinalPass.EnumCap.wordB_le _ _ _ _ _ _ _ _ _ _ hT hw hK hD hA
  refine key.trans (le_of_eq ?_)
  unfold eb
  congr 1
  ring

/-- **The THR batch's row words** below `2^{e_b}`. -/
theorem thrBsz_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimT.C4Grp.bsz (thrExprs (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) ≤
      2 ^ eb (thrDigits ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
        (Nat.clog 2 (n + 2)) (thrDg l F kclk coef A a ha Cs carriers translation hs)
        (((gate0 l F).budget kclk coef A a ha).kOf n) := by
  have hM := occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hP := thrPool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hN := pow_N_le n 26
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) := (Nat.pow_le_pow_left (by omega) 26).trans hN
  have h0 := Nat.one_le_two_pow (n := 26 * Nat.clog 2 (n + 2))
  have hM1 : (Records.thrCallD (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation).M + 1 ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 3) := by
    rw [thrCallD_M, pow_add]; omega
  have hG : 4 * (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1 ≤
      2 ^ (26 * Nat.clog 2 (n + 2) + 6) := by
    rw [pow_add]; omega
  have hA : 4 * (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) *
      2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) *
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length + 1 ≤
      2 ^ (((gate0 l F).budget kclk coef A a ha).kOf n + 26 * Nat.clog 2 (n + 2) + 6) := by
    rw [← pow_add, ← two_mul, hkh, pow_add, pow_add]
    obtain ⟨k, hkd⟩ : ∃ k, k = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
    obtain ⟨G, hGd⟩ : ∃ G, G = (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length :=
      ⟨_, rfl⟩
    rw [← hkd, ← hGd]
    rw [← hGd] at hP
    obtain ⟨E, hEd⟩ : ∃ E, E = 2 ^ (26 * Nat.clog 2 (n + 2)) := ⟨_, rfl⟩
    rw [← hEd] at h26 h0 ⊢
    have h1 := Nat.one_le_two_pow (n := k)
    have h3 : G ≤ 8 * E := by omega
    have h4 := Nat.mul_le_mul_left (4 * 2 ^ k) h3
    have e1 : 4 * 2 ^ k * (8 * E) = 32 * (2 ^ k * E) := by ring
    have h5 : 1 ≤ 2 ^ k * E := Nat.mul_pos h1 h0
    have e2 : 2 ^ k * E * 2 ^ 6 = 64 * (2 ^ k * E) := by ring
    omega
  refine FinalPass.EnumCap.bsz_le _ _ Nat.one_le_two_pow (fun V hV =>
    (BShape.thr_word_le (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation V hV).trans
      (thr_word_arith _ _ _ _ _ _ _ hM1 hG hA))

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
