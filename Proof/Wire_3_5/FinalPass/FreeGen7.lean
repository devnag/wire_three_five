import Proof.Wire_3_5.FinalPass.FreeGen6

/-! # The free numbers, v2, part 2: the program and its run

The compiler's numbers at the paper's own sizes (P3:1886-1906; P3:1596-1615 for the pool children's bits; P3:3094-3100
for `d_S`): `Q' = dQ·(2kh + β)` (`O(k+L)`), `h = dH·(n+1)^{eH}`, `pr = dP·(n+1)^{eP}`; the other slots as FreeGen's.
* `FreeK2` (FreeGen's `FreeK` and the exponents `eH`, `eP`), `FreeK2.base` (`dQ = dH = dP = 0`), **`freeVal2`**;
* `fixW`: after `freeW base`, `Q'` into `FB 2`, `(n+1)^{eH}` and `h` into `FB 3`, `(n+1)^{eP}` and `pr` into `FB 5`
  (scratch `177, 179, 180, 181, 196–198`), `fixOut`, **`fixW_exec`**;
* `freeW2`, `need2`, **`freeW2_run`** (C4.K's `FreeProg.run` shape), **`freeProg2`**.
Paper quantities of the main types: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **The v2 constants**: FreeGen's and the exponents of `h` and `pr`. -/
structure FreeK2 where
  k : FreeK
  eH : ℕ
  eP : ℕ
  m0 : ℕ

/-- The constants of the first pass (`Q'`, `h`, `pr` at `0`). -/
def FreeK2.base (κ : FreeK2) : FreeK := { κ.k with dQ := 0, dH := 0, dP := 0 }

/-- FreeGen's factor count `m`. -/
def mOf (κ : FreeK) (x : FreeIn) : ℕ := κ.mA * x.nc + κ.mB * (x.a * W x) + κ.mC * W x + κ.mD * x.a + κ.mF * x.M + κ.mE

/-- **The v2 free numbers**: `TWd, Cap = 2^{⌊n/16⌋ + dC·β²}`, `Q' = dQ(2kh+β), h = dH(n+1)^{eH}, max(m, m0), pr = dP(n+1)^{eP}, ρ` (the floor
`m0` of `m`: the degenerate call's padded batch, one constant row per entry). -/
def freeVal2 (κ : FreeK2) (x : FreeIn) : Fin 7 → ℕ :=
  ![κ.k.dT * (β x * β x), 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)), κ.k.dQ * (x.kh + x.kh + β x),
    κ.k.dH * (x.n + 1) ^ κ.eH,
    max (mOf κ.k x) κ.m0,
    κ.k.dP * (x.n + 1) ^ κ.eP,
    max (x.n - (x.kh + x.kh) + κ.k.dA * β x) (κ.k.dR * (β x * β x))]

def fQ : Fin 5 ↪ Fin 35 := ⟨![7, 2, 26, 27, 28], by decide⟩
def fH1 : Fin 5 ↪ Fin 35 := ⟨![9, 10, 26, 27, 28], by decide⟩
def fH2 : Fin 5 ↪ Fin 35 := ⟨![9, 3, 26, 27, 28], by decide⟩
def fP1 : Fin 5 ↪ Fin 35 := ⟨![11, 10, 26, 27, 28], by decide⟩
def fP2 : Fin 5 ↪ Fin 35 := ⟨![11, 5, 26, 27, 28], by decide⟩
@[simp] theorem fQ_apply (i : Fin 5) : fQ i = ![7, 2, 26, 27, 28] i := rfl
@[simp] theorem fH1_apply (i : Fin 5) : fH1 i = ![9, 10, 26, 27, 28] i := rfl
@[simp] theorem fH2_apply (i : Fin 5) : fH2 i = ![9, 3, 26, 27, 28] i := rfl
@[simp] theorem fP1_apply (i : Fin 5) : fP1 i = ![11, 10, 26, 27, 28] i := rfl
@[simp] theorem fP2_apply (i : Fin 5) : fP2 i = ![11, 5, 26, 27, 28] i := rfl
def fM : Fin 10 ↪ Fin 35 := ⟨![12, 13, 4, 14, 15, 16, 26, 27, 28, 29], by decide⟩
@[simp] theorem fM_apply (i : Fin 10) : fM i = ![12, 13, 4, 14, 15, 16, 26, 27, 28, 29] i := rfl

/-- **The second pass, part 1**: `Q'`, `h`, `pr`. -/
def fixA (κ : FreeK2) : WM (LNS 0) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Gall 31) (Gall 7) (Gall 26))
  (.seq (ParseNat.addTo (Gall 31) (Gall 7) (Gall 26))
  (.seq (ParseNat.addTo (Gall 8) (Gall 7) (Gall 26))
  (.seq (cmulW κ.k.dQ (fQ.trans Gall))
  (.seq (FinalPass.Hash4.wcopyR (Gall 30) (Gall 10) (Gall 26))
  (.seq (.inc (Gall 10))
  (.seq (StarNums.incN (Gall 9) 1)
  (.seq (powLoop (fH1.trans Gall) κ.eH)
  (.seq (cmulW κ.k.dH (fH2.trans Gall))
  (.seq (StarNums.incN (Gall 11) 1)
  (.seq (powLoop (fP1.trans Gall) κ.eP)
  (cmulW κ.k.dP (fP2.trans Gall))))))))))))

/-- **The second pass, part 2**: `m := max(m, m0)`. -/
def fixM (κ : FreeK2) : WM (LNS 0) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Gall 4) (Gall 12) (Gall 26))
  (.seq (WM.clear (Gall 4))
  (.seq (StarNums.incN (Gall 13) κ.m0)
  (maxW (fM.trans Gall))))

/-- **The second pass, parts 1–2.** -/
def fixAM (κ : FreeK2) : WM (LNS 0) LNR := .seq (fixA κ) (fixM κ)

def fC : Fin 4 ↪ Fin 35 := ⟨![14, 1, 15, 26], by decide⟩
@[simp] theorem fC_apply (i : Fin 4) : fC i = ![14, 1, 15, 26] i := rfl

/-- **The second pass, part 3**: `Cap := 2^{⌊n/16⌋ + dC·β²}`. -/
def fixC : WM (LNS 0) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Gall 30) (Gall 14) (Gall 26))
  (.seq (WriteNat.halveM (Gall 14) (Gall 15) (Gall 16))
  (.seq (WriteNat.halveM (Gall 14) (Gall 15) (Gall 27))
  (.seq (WriteNat.halveM (Gall 14) (Gall 15) (Gall 28))
  (.seq (WriteNat.halveM (Gall 14) (Gall 15) (Gall 29))
  (.seq (ParseNat.addTo (Gall 20) (Gall 14) (Gall 26))
  (.seq (WM.clear (Gall 1))
  (UnaryArith.pow2W (fC.trans Gall))))))))

/-- **The second pass.** -/
def fixW (κ : FreeK2) : WM (LNS 0) LNR := .seq (fixAM κ) fixC

/-- The first part's exit state. -/
def fixAOut (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR :=
  (((((((((((τ.setv (Gall 7) x.kh).setv (Gall 7) (x.kh + x.kh)).setv (Gall 7) (x.kh + x.kh + β x)).setv (Gall 2)
    (κ.k.dQ * (x.kh + x.kh + β x))).setv (Gall 10) x.n).setv (Gall 10) (x.n + 1)).setv (Gall 9) 1).setv (Gall 9)
    (1 * (x.n + 1) ^ κ.eH)).setv (Gall 3) (κ.k.dH * (1 * (x.n + 1) ^ κ.eH))).setv (Gall 11) 1).setv (Gall 11)
    (1 * (x.n + 1) ^ κ.eP)).setv (Gall 5) (κ.k.dP * (1 * (x.n + 1) ^ κ.eP))

/-- The exit state of parts 1–2. -/
def fixAMOut (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR :=
  ((((fixAOut κ x τ).setv (Gall 12) (mOf κ.base x)).setv (Gall 4) 0).setv (Gall 13) κ.m0).setv (Gall 4)
    (max (mOf κ.base x) κ.m0)

/-- The exit state of part 3. -/
def fixCOut (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR :=
  (((((((((((τ.setv (Gall 14) x.n).setv (Gall 14) (x.n / 2)).setv (Gall 16) (x.n % 2)).setv (Gall 14) (x.n / 2 / 2)).setv
    (Gall 27) (x.n / 2 % 2)).setv (Gall 14) (x.n / 2 / 2 / 2)).setv (Gall 28) (x.n / 2 / 2 % 2)).setv (Gall 14)
    (x.n / 2 / 2 / 2 / 2)).setv (Gall 29) (x.n / 2 / 2 / 2 % 2)).setv (Gall 14)
    (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x))).setv (Gall 1) 0).setv (Gall 1)
    (2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)))

/-- The second pass's exit state. -/
def fixOut (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR := fixCOut κ x (fixAMOut κ x τ)

/-- The first part's step units. -/
def fixAN (κ : FreeK2) : ℕ := 40 + 4 * κ.eH + 4 * κ.eP

/-- The step units of parts 1–2. -/
def fixAMN (κ : FreeK2) : ℕ := fixAN κ + 15

/-- The second pass's step units. -/
def fixN (κ : FreeK2) : ℕ := fixAMN κ + 1 + 15

/-- The capacity the second pass needs. -/
def need2 (κ : FreeK2) (x : FreeIn) : ℕ :=
  (x.kh + x.kh + β x) + κ.k.dQ + κ.k.dQ * (x.kh + x.kh + β x) + (x.n + 2) + (x.n + 1) ^ κ.eH + (x.n + 1) ^ κ.eP +
    κ.k.dH + κ.k.dH * (x.n + 1) ^ κ.eH + κ.k.dP + κ.k.dP * (x.n + 1) ^ κ.eP + mOf κ.base x + κ.m0 +
    2 * 2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) + 2 ^ (κ.k.dC * (β x * β x)) + 1

theorem pow_le_pow_of (y e j : ℕ) (hj : j ≤ e) : 1 * (y + 1) ^ j ≤ (y + 1) ^ e := by
  rw [Nat.one_mul]
  exact Nat.pow_le_pow_right (Nat.succ_pos y) hj

/-- **The first part's run.** -/
theorem fixA_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hn : τ.val (Gall 30) = x.n)
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : need2 κ x ≤ cap) :
    WExec cap (fixA κ) τ (fixAOut κ x τ) (fixAN κ * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hc' := hc
  unfold need2 at hc'
  generalize 2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) = P2 at hc'
  generalize 2 ^ (κ.k.dC * (β x * β x)) = P3 at hc'
  have z7 := hz 7 (by decide)
  have z9 := hz 9 (by decide)
  have z10 := hz 10 (by decide)
  have z11 := hz 11 (by decide)
  have z26 := hz 26 (by decide)
  have z27 := hz 27 (by decide)
  have z28 := hz 28 (by decide)
  have z2 := hz 2 (by decide)
  have z3 := hz 3 (by decide)
  have z5 := hz 5 (by decide)
  have hH : (x.n + 1) ^ κ.eH ≤ cap := by omega
  have hPw : (x.n + 1) ^ κ.eP ≤ cap := by omega
  unfold fixA fixAN
  refine seqD cap _ 1 (copy1 cap (Gall 31) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) x.kh τ hkh z7 z26
    (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 31) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) x.kh x.kh _
    (by simp [hkh]) (by simp) (by simp [z26]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 8) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) (β x) (x.kh + x.kh) _
    (by simp [hb]) (by simp) (by simp [z26]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.k.dQ (fQ.trans Gall) _ (x.kh + x.kh + β x) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [z2, z26, z27, z28])
    (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Gall 30) (Gall 10) (Gall 26) (by simp) (by simp) (by simp) x.n _ (by simp [hn])
    (by simp [z10]) (by simp [z26]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (WExec.mono (WExec.inc (cap := cap) (Gall 10) _ (by simp; omega)) (show 3 ≤ 1 * UnaryPow.sq cap by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (Gall 9) 1 _ (by simp [z9]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ (4 * κ.eH) (powLoop_spec cap (fH1.trans Gall) 1 (x.n + 1) (by omega) κ.eH _ (by simp) (by simp)
    (by simp [z26]) (by simp [z27]) (by simp [z28]) (le_trans (pow_le_pow_of _ _ _ le_rfl) hH)
    (fun j hj => le_trans (pow_le_pow_of _ _ _ hj) hH)) (le_of_eq (by ring)) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.k.dH (fH2.trans Gall) _ (1 * (x.n + 1) ^ κ.eH) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [z3, z26, z27, z28])
    (by rw [Nat.one_mul]; exact hH) (by omega) (by rw [Nat.one_mul]; omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (Gall 11) 1 _ (by simp [z11]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ (4 * κ.eP) (powLoop_spec cap (fP1.trans Gall) 1 (x.n + 1) (by omega) κ.eP _ (by simp) (by simp)
    (by simp [z26]) (by simp [z27]) (by simp [z28]) (le_trans (pow_le_pow_of _ _ _ le_rfl) hPw)
    (fun j hj => le_trans (pow_le_pow_of _ _ _ hj) hPw)) (le_of_eq (by ring)) (by omega) ?_
  exact endD cap _ 5 (cmulW_spec cap κ.k.dP (fP2.trans Gall) _ (1 * (x.n + 1) ^ κ.eP) (by simp)
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [z5, z26, z27, z28])
    (by rw [Nat.one_mul]; exact hPw) (by omega) (by rw [Nat.one_mul]; omega))
    rfl (by omega) (by omega)

/-- **The run of parts 1–2.** -/
theorem fixAM_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hn : τ.val (Gall 30) = x.n)
    (hm : τ.val (Gall 4) = mOf κ.base x)
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : need2 κ x ≤ cap) :
    WExec cap (fixAM κ) τ (fixAMOut κ x τ) (fixAMN κ * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hc' := hc
  unfold need2 at hc'
  generalize 2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) = P2 at hc'
  generalize 2 ^ (κ.k.dC * (β x * β x)) = P3 at hc'
  have hA := fixA_exec κ cap x τ hkh hb hn hz hc
  have z26 := hz 26 (by decide)
  have z27 := hz 27 (by decide)
  have z28 := hz 28 (by decide)
  have z12 := hz' 12 (by decide)
  have z13 := hz' 13 (by decide)
  have z14 := hz' 14 (by decide)
  have z15 := hz' 15 (by decide)
  have z16 := hz' 16 (by decide)
  have z29 := hz' 29 (by decide)
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  have kA : ∀ k : Fin 35, k ∉ ({7, 2, 10, 9, 3, 11, 5} : Finset (Fin 35)) → (fixAOut κ x τ).val (Gall k) = τ.val (Gall k) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨h7, h2, h10, h9, h3, h11, h5⟩ := hk
    simp [fixAOut, Function.update_apply, hne h7, hne h2, hne h10, hne h9, hne h3, hne h11, hne h5]
  unfold fixAM fixM fixAMN
  refine seqD cap _ (fixAN κ) hA le_rfl (by omega) ?_
  have e1 : fixAN κ + 15 - fixAN κ - 1 = 14 := by omega
  rw [e1]
  have hmc : mOf κ.base x ≤ cap := by omega
  have hm0 : κ.m0 ≤ cap := by omega
  refine seqD cap _ 1 (copy1 cap (Gall 4) (Gall 12) (Gall 26) (by simp) (by simp) (by simp) (mOf κ.base x) _
    (by rw [kA 4 (by decide), hm]) (by rw [kA 12 (by decide), z12]) (by rw [kA 26 (by decide), z26]) hmc)
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (Gall 4) (mOf κ.base x) _ (by simp [kA 4 (by decide), hm]) hmc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (Gall 13) κ.m0 _ (by simp [kA 13 (by decide), z13]) hm0) (by omega) (by omega) ?_
  refine endD cap _ 6 (maxW_spec cap (fM.trans Gall) _ (mOf κ.base x) κ.m0 (by simp) (by simp)
    (fun i hi => by
      fin_cases i <;> first | exact absurd hi (by decide) |
        simp [kA 14 (by decide), kA 15 (by decide), kA 16 (by decide), kA 26 (by decide), kA 27 (by decide),
          kA 28 (by decide), kA 29 (by decide), z14, z15, z16, z26, z27, z28, z29])
    hmc hm0 (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, fM_apply]
  rfl

/-- **The run of part 3** (`Cap`). -/
theorem fixC_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR) (hn : τ.val (Gall 30) = x.n)
    (h20 : τ.val (Gall 20) = κ.k.dC * (β x * β x)) (h1 : τ.val (Gall 1) = 2 ^ (κ.k.dC * (β x * β x)))
    (hz : ∀ k : Fin 35, k ∈ ({14, 15, 16, 26, 27, 28, 29} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : need2 κ x ≤ cap) :
    WExec cap fixC τ (fixCOut κ x τ) (15 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have z14 := hz 14 (by decide)
  have z15 := hz 15 (by decide)
  have z16 := hz 16 (by decide)
  have z26 := hz 26 (by decide)
  have z27 := hz 27 (by decide)
  have z28 := hz 28 (by decide)
  have z29 := hz 29 (by decide)
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  unfold need2 at hc
  generalize hP : 2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) = P at hc
  generalize hP1 : 2 ^ (κ.k.dC * (β x * β x)) = P1 at hc h1
  have hPl : x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x) < P := by rw [← hP]; exact Nat.lt_two_pow_self
  unfold fixC
  refine seqD cap _ 1 (copy1 cap (Gall 30) (Gall 14) (Gall 26) (by simp) (by simp) (by simp) x.n τ hn z14 z26
    (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (FiltNum.halve1 cap (Gall 14) (Gall 15) (Gall 16) (by simp) (by simp) (by simp) x.n _
    (by simp) (by simp [hne (show (15 : Fin 35) ≠ 14 by decide), z15])
    (by simp [hne (show (16 : Fin 35) ≠ 14 by decide), z16]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (FiltNum.halve1 cap (Gall 14) (Gall 15) (Gall 27) (by simp) (by simp) (by simp) (x.n / 2) _
    (by simp [hne (show (14 : Fin 35) ≠ 16 by decide)]) (by simp [hne (show (15 : Fin 35) ≠ 14 by decide),
      hne (show (15 : Fin 35) ≠ 16 by decide), z15])
    (by simp [hne (show (27 : Fin 35) ≠ 14 by decide), hne (show (27 : Fin 35) ≠ 16 by decide), z27]) (by omega)
    (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (FiltNum.halve1 cap (Gall 14) (Gall 15) (Gall 28) (by simp) (by simp) (by simp) (x.n / 2 / 2) _
    (by simp [hne (show (14 : Fin 35) ≠ 27 by decide), hne (show (14 : Fin 35) ≠ 16 by decide)])
    (by simp [hne (show (15 : Fin 35) ≠ 14 by decide), hne (show (15 : Fin 35) ≠ 16 by decide),
      hne (show (15 : Fin 35) ≠ 27 by decide), z15])
    (by simp [hne (show (28 : Fin 35) ≠ 14 by decide), hne (show (28 : Fin 35) ≠ 16 by decide),
      hne (show (28 : Fin 35) ≠ 27 by decide), z28]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (FiltNum.halve1 cap (Gall 14) (Gall 15) (Gall 29) (by simp) (by simp) (by simp)
    (x.n / 2 / 2 / 2) _
    (by simp [hne (show (14 : Fin 35) ≠ 28 by decide), hne (show (14 : Fin 35) ≠ 27 by decide),
      hne (show (14 : Fin 35) ≠ 16 by decide)])
    (by simp [hne (show (15 : Fin 35) ≠ 14 by decide), hne (show (15 : Fin 35) ≠ 16 by decide),
      hne (show (15 : Fin 35) ≠ 27 by decide), hne (show (15 : Fin 35) ≠ 28 by decide), z15])
    (by simp [hne (show (29 : Fin 35) ≠ 14 by decide), hne (show (29 : Fin 35) ≠ 16 by decide),
      hne (show (29 : Fin 35) ≠ 27 by decide), hne (show (29 : Fin 35) ≠ 28 by decide), z29]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 20) (Gall 14) (Gall 26) (by simp) (by simp) (by simp)
    (κ.k.dC * (β x * β x)) (x.n / 2 / 2 / 2 / 2) _
    (by simp [hne (show (20 : Fin 35) ≠ 14 by decide), hne (show (20 : Fin 35) ≠ 16 by decide),
      hne (show (20 : Fin 35) ≠ 27 by decide), hne (show (20 : Fin 35) ≠ 28 by decide),
      hne (show (20 : Fin 35) ≠ 29 by decide), h20])
    (by simp [hne (show (14 : Fin 35) ≠ 29 by decide)])
    (by simp [hne (show (26 : Fin 35) ≠ 14 by decide), hne (show (26 : Fin 35) ≠ 16 by decide),
      hne (show (26 : Fin 35) ≠ 27 by decide), hne (show (26 : Fin 35) ≠ 28 by decide),
      hne (show (26 : Fin 35) ≠ 29 by decide), z26]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (Gall 1) P1 _
    (by simp [hne (show (1 : Fin 35) ≠ 14 by decide), hne (show (1 : Fin 35) ≠ 16 by decide),
      hne (show (1 : Fin 35) ≠ 27 by decide), hne (show (1 : Fin 35) ≠ 28 by decide),
      hne (show (1 : Fin 35) ≠ 29 by decide), h1]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (SymQM.pow2v cap (fC.trans Gall) (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) _
    (by simp [hne (show (14 : Fin 35) ≠ 1 by decide)]) (by simp)
    (by simp [hne (show (15 : Fin 35) ≠ 1 by decide), hne (show (15 : Fin 35) ≠ 14 by decide),
      hne (show (15 : Fin 35) ≠ 16 by decide), hne (show (15 : Fin 35) ≠ 27 by decide),
      hne (show (15 : Fin 35) ≠ 28 by decide), hne (show (15 : Fin 35) ≠ 29 by decide), z15])
    (by simp [hne (show (26 : Fin 35) ≠ 1 by decide), hne (show (26 : Fin 35) ≠ 14 by decide),
      hne (show (26 : Fin 35) ≠ 16 by decide), hne (show (26 : Fin 35) ≠ 27 by decide),
      hne (show (26 : Fin 35) ≠ 28 by decide), hne (show (26 : Fin 35) ≠ 29 by decide), z26])
    (by rw [pow_succ, hP]; omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, fC_apply]
  rfl

/-- **The second pass's run.** -/
theorem fixW_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hn : τ.val (Gall 30) = x.n)
    (hm : τ.val (Gall 4) = mOf κ.base x) (h20 : τ.val (Gall 20) = κ.k.dC * (β x * β x))
    (h1 : τ.val (Gall 1) = 2 ^ (κ.k.dC * (β x * β x)))
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : need2 κ x ≤ cap) :
    WExec cap (fixW κ) τ (fixOut κ x τ) (fixN κ * UnaryPow.sq cap) := by
  have hAM := fixAM_exec κ cap x τ hkh hb hn hm hz hz' hc
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  have kAM : ∀ k : Fin 35, k ∉ ({7, 2, 10, 9, 3, 11, 5, 12, 4, 13} : Finset (Fin 35)) →
      (fixAMOut κ x τ).val (Gall k) = τ.val (Gall k) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨h7, h2, h10, h9, h3, h11, h5, h12, h4, h13⟩ := hk
    simp [fixAMOut, fixAOut, Function.update_apply, hne h7, hne h2, hne h10, hne h9, hne h3, hne h11, hne h5,
      hne h12, hne h4, hne h13]
  have hC := fixC_exec κ cap x (fixAMOut κ x τ) (by rw [kAM 30 (by decide), hn]) (by rw [kAM 20 (by decide), h20])
    (by rw [kAM 1 (by decide), h1]) (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [kAM 14 (by decide)]; exact hz' 14 (by decide)
      · rw [kAM 15 (by decide)]; exact hz' 15 (by decide)
      · rw [kAM 16 (by decide)]; exact hz' 16 (by decide)
      · rw [kAM 26 (by decide)]; exact hz 26 (by decide)
      · rw [kAM 27 (by decide)]; exact hz 27 (by decide)
      · rw [kAM 28 (by decide)]; exact hz 28 (by decide)
      · rw [kAM 29 (by decide)]; exact hz' 29 (by decide)) hc
  unfold fixW fixN
  exact seqD cap _ (fixAMN κ) hAM le_rfl (by omega) (by rw [show fixAMN κ + 1 + 15 - fixAMN κ - 1 = 15 by omega]; exact hC)

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

