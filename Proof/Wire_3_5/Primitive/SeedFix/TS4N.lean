import Proof.Wire_3_5.Primitive.SeedFix.TS4V
import Proof.Wire_3_5.Primitive.Writers.SymNeed

/-! # thrStage4U, part 12: the v4 stage's capacity need, polynomial in `n`

P3:3425-3430 (the THR cap `B_T(n)`, tr:B), P3:3819, 3400 (the sparse count), P3:2543-2558 (W6's need) and P3:3114-3115
("All powers of `n` are fixed before a fixed `r`"): one polynomial `needT l c_r n` dominates every capacity the v4 stage
uses at the fill `2W + 2`:

* `cEnc_le_cMainT`, **`capNeed_ofT`** (the THR twin of `SymFam.capNeed_of`: `CapNum.capM_spec`'s conditions
  from `2^{40}·capK·(n+2)^{Z_m} + cMain ≤ cap`);
* `ZmL`, `spA`, `spB`, `capTL`, **`needT`**;
* **`p0need_of`** (the prep's `P0Need`), `needW_of` (W6's need `≤ V = W + (n+1)^{26}`), `capTL_pos`;
* `NDeg`, `NCoef`, **`needT_le`** (`needT ≤ NCoef·(n+1)^{NDeg}`, the degree fixed by the literals, the coefficient by
  `c_r`).

Paper quantities of the main type: the THR cap `B_T(n)`, the sparse count's bound, W6's capacity need, all
polynomial in `n`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

theorem cEnc_le_cMainT (l : Literals) : CapNum.cEnc (gateCap l) ≤ CapNum.cMain (gateCap l) .thr := by
  have hb : 1 ≤ gateBetaInv l := one_le_betaInv l
  have e1 : CapNum.cEnc (gateCap l) = 128 * gateBetaInv l ^ 2 := by
    show 32 * 2 ^ 2 * gateBetaInv l ^ 2 = 128 * gateBetaInv l ^ 2; norm_num
  have e2 : CapNum.cMain (gateCap l) .thr = 2 ^ 80 * gateBetaInv l ^ 32 := by
    show 2 ^ 80 * 1 ^ 32 * gateBetaInv l ^ 32 = 2 ^ 80 * gateBetaInv l ^ 32; norm_num
  rw [e1, e2]
  have h1 : gateBetaInv l ^ 2 ≤ gateBetaInv l ^ 32 := Nat.pow_le_pow_right hb (by norm_num)
  have h2 : (128 : ℕ) ≤ 2 ^ 80 := by norm_num
  exact Nat.mul_le_mul h2 h1

theorem capNeed_ofT (l : Literals) (cr n cap : ℕ)
    (h : 2 ^ 40 * (PrimAsm.CallIndexR.capK cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) .thr ≤ cap) :
    SymDec.CapNeed (gateCap l) .thr n (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap := by
  obtain ⟨N, hNd⟩ : ∃ N, N = n + 2 := ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ z, z = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32 := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K, K = PrimAsm.CallIndexR.capK cr := ⟨_, rfl⟩
  have hnum := PrimAsm.CallIndexR.capMain_leR l cr .thr n hNd
  have henc := PrimAsm.CallIndexR.capEnc_leR l cr n hNd
  rw [← hNd, ← hZm, ← hKd] at h
  rw [← hZm, ← hKd] at hnum
  rw [← hKd] at henc
  have hN : 2 ≤ N := by omega
  have hK1 : 1 ≤ K := hKd ▸ PrimAsm.CallIndexR.capK_pos cr
  have hKr : 2 * cr + 2 ≤ K := by
    rw [hKd]; unfold PrimAsm.CallIndexR.capK; exact Nat.le_self_pow (by norm_num) _
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K * N ^ Zm := ⟨_, rfl⟩
  have pw : ∀ d, d ≤ Zm → N ^ d ≤ N ^ Zm := fun d hd => Nat.pow_le_pow_right (by omega) hd
  have kY : ∀ x d, d ≤ Zm → x ≤ K * N ^ d → x ≤ Y := fun x d hd hx =>
    le_trans hx (hYd ▸ Nat.mul_le_mul_left _ (pw d hd))
  have hY1 : 1 ≤ Y := by rw [hYd]; exact Nat.mul_le_mul hK1 (Nat.one_le_pow _ _ (by omega))
  have hNK : ∀ x d, x ≤ N ^ d → x ≤ K * N ^ d := fun x d hx => le_trans hx (Nat.le_mul_of_pos_left _ (by omega))
  have zA : 48 + (gateCsp l + 3) * 32 + 64 ≤ Zm := by omega
  have zB : 174 ≤ Zm := by omega
  have zC : 5 + 3 + 2 + 1 + gateBetaInv l * 2 ≤ Zm := by omega
  have zD : gateCsp l + 3 ≤ Zm := by omega
  -- r, s, q
  have hr : Ledger.rowBr cr n ≤ (2 * cr + 2) * N := hNd ▸ PrimAsm.CallIndexR.rowBr_leR cr n
  have hs : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ N ^ (gateCsp l + 3) :=
    hNd ▸ PrimAsm.CallIndex.sp_le l n
  have hq : n ≤ N := by omega
  have hL : Ledger.Lq n ≤ N := hNd ▸ PrimAsm.CallIndex.Lq_le_N n
  have r1 : Ledger.rowBr cr n ≤ K * N ^ 1 := by
    rw [pow_one]; exact le_trans hr (Nat.mul_le_mul_right _ hKr)
  have r48 : Ledger.rowBr cr n ^ 48 ≤ K * N ^ 48 := by
    have : Ledger.rowBr cr n ^ 48 ≤ ((2 * cr + 2) * N) ^ 48 := Nat.pow_le_pow_left hr 48
    rw [mul_pow] at this
    rw [hKd]; exact this
  have r3 : Ledger.rowBr cr n ^ 3 ≤ K * N ^ 3 := by
    have : Ledger.rowBr cr n ^ 3 ≤ ((2 * cr + 2) * N) ^ 3 := Nat.pow_le_pow_left hr 3
    rw [mul_pow] at this
    have h2 : (2 * cr + 2) ^ 3 ≤ K := by
      rw [hKd]; unfold PrimAsm.CallIndexR.capK; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    exact le_trans this (Nat.mul_le_mul_right _ h2)
  have s32 : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 ≤ N ^ ((gateCsp l + 3) * 32) :=
    PrimAsm.CallIndex.pw_pow hs 32
  have q64 : n ^ 64 ≤ N ^ 64 := Nat.pow_le_pow_left hq 64
  have L142 : Ledger.Lq n ^ Ledger.capExp32 .thr ≤ N ^ 174 := Nat.pow_le_pow_left hL 174
  have rs : Ledger.rowBr cr n ^ 48 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 ≤
      K * N ^ (48 + (gateCsp l + 3) * 32) := by
    calc _ ≤ K * N ^ 48 * N ^ ((gateCsp l + 3) * 32) := Nat.mul_le_mul r48 s32
      _ = K * N ^ (48 + (gateCsp l + 3) * 32) := by rw [pow_add]; ring
  have rsq : Ledger.rowBr cr n ^ 48 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 * n ^ 64 ≤
      K * N ^ (48 + (gateCsp l + 3) * 32 + 64) := by
    calc _ ≤ K * N ^ (48 + (gateCsp l + 3) * 32) * N ^ 64 := Nat.mul_le_mul rs q64
      _ = K * N ^ (48 + (gateCsp l + 3) * 32 + 64) := by rw [pow_add N (48 + (gateCsp l + 3) * 32) 64]; ring
  have r3q : Ledger.rowBr cr n ^ 3 * n ≤ K * N ^ 4 := by
    calc _ ≤ K * N ^ 3 * N := Nat.mul_le_mul r3 hq
      _ = K * N ^ 4 := by ring
  have hpow : Ledger.capMainPow (gateCap l) .thr (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n ≤
      Ledger.capMainNum (gateCap l) .thr (Ledger.rowBr cr n)
        (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n + Ledger.Lq n ^ Ledger.capExp32 .thr := by
    unfold Ledger.capMainPow
    exact le_trans (Nat.div_le_self _ _) (by omega)
  have yN : Ledger.capMainNum (gateCap l) .thr (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n ≤ Y := by rw [hYd]; exact hnum
  have yL : Ledger.Lq n ^ Ledger.capExp32 .thr ≤ Y := kY _ 174 zB (hNK _ _ L142)
  have yE : Ledger.capEncPow (gateCap l) (Ledger.rowBr cr n) n ≤ Y := kY _ _ zC henc
  have hCe := cEnc_le_cMainT l
  exact ⟨by omega, by have := kY _ 1 (by omega) r1; omega,
    by have := kY _ _ zD (hNK _ _ hs); omega,
    by have := kY n 1 (by omega) (hNK _ _ (by rw [pow_one]; exact hq)); omega,
    by have := kY (Ledger.Lq n) 1 (by omega) (hNK _ _ (by rw [pow_one]; exact hL)); omega,
    by have := kY _ 48 (by omega) r48; omega,
    by have := kY _ _ (by omega) (hNK _ _ s32); omega,
    by have := kY _ 64 (by omega) (hNK _ _ q64); omega,
    by have := kY _ _ (by omega) rs; omega,
    by have := kY _ _ zA rsq; omega,
    by omega, by omega, by omega, by omega,
    by omega,
    by have := kY _ 3 (by omega) r3; omega,
    by have := kY _ 4 (by omega) r3q; omega,
    by omega, by omega, by omega⟩

variable (l : Literals)

/-- The main term's exponent. -/
noncomputable def ZmL : ℕ := 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32

/-- The sparse bound's exponents (`SymSizes.sparse_le_gate`). -/
noncomputable def spA : ℕ := 3 + 32 * SymSizes.cXg l * SymSizes.schedJ l
noncomputable def spB : ℕ := 6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1)

/-- The THR cap at the gate. -/
noncomputable def capTL (cr n : ℕ) : ℕ := capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)

/-- The cap computation's own need (`capNeed_ofT`'s bound). -/
noncomputable def capNT (cr n : ℕ) : ℕ :=
  2 ^ 40 * (PrimAsm.CallIndexR.capK cr * (n + 2) ^ ZmL l) + CapNum.cMain (gateCap l) .thr

/-- The sparse bound's majorant. -/
noncomputable def spT (n : ℕ) : ℕ := 2 ^ (spA l * Nat.clog 2 (n + 2) + spB l)

/-- **The v4 stage's capacity need.** -/
noncomputable def needT (cr n : ℕ) : ℕ :=
  16 * n + 2 * cr + 100 + spT l n + capNT l cr n +
    PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l + 2 * (n + 1) ^ 26 +
    2 * W6.needW (W6.litAlg l) 1 (n + capTL l cr n)

theorem capTL_le (cr n : ℕ) : capTL l cr n ≤ PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l :=
  PrimAsm.CallIndexR.cap_leR l cr .thr n

theorem capTL_pos (cr n : ℕ) : 1 ≤ capTL l cr n := by
  unfold capTL capTOf Ledger.rowBCap; omega

/-- **The prep's needs from `needT`.** -/
theorem p0need_of (cr n W a nc : ℕ) (ha : a ≤ 4) (hnc : nc ≤ 2) (h : needT l cr n ≤ 2 * W + 2) :
    P0Need W n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) cr a nc W := by
  unfold needT at h
  have p1 := W6.pow_nbl n
  have p2 := W6.pow_nbl a
  have p3 := W6.pow_nbl nc
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have hs := SymSizes.sparse_le_gate l n
    have e : spT l n = 2 ^ ((3 + 32 * SymSizes.cXg l * SymSizes.schedJ l) * Nat.clog 2 (n + 2) +
        (6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1))) := rfl
    exact hs.trans (by omega)
  · have e : capNT l cr n = 2 ^ 40 * (PrimAsm.CallIndexR.capK cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 +
        gateBetaInv l * 32)) + CapNum.cMain (gateCap l) .thr := rfl
    exact capNeed_ofT l cr n (2 * W + 2) (by omega)
  · have := capTL_le l cr n
    unfold capTL at this
    omega
  · omega

theorem needW_of (cr n W : ℕ) (h : needT l cr n ≤ 2 * W + 2) :
    W6.needW (W6.litAlg l) 1 (n + capTL l cr n) ≤ W + (n + 1) ^ 26 := by
  unfold needT at h; omega

end NearCubicWires.WireExponent3_5.PrimT.TS4
