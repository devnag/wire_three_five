import Proof.Wire_3_5.FinalPass.FreeGen9

/-! # The HASH free numbers' program: `freeProgH`, the v2 program with `Q' = d_Q(2k_h + β + β³)`

`filt:soft`, P3:2291-2296 (filt:aux-precision): "a modulus `2^{Q_aux}` with
`Q_aux > log₂Δ₀ + k + s_aux + log₂(H_max+1) = O_D(k + L³)` recovers each value exactly", with `Δ₀ = 2^{s_h}Π_{j<J}W_j^{2t}`
of bit length `O_D(L³)` (P3:2275-2279). The SYM program's `Q' = d_Q(2k_h + β)` (FreeGen7) is linear; the HASH stage's
recovery modulus needs the cubic term. `fixAH` is `fixA` with the accumulator first loaded with `β·β²` (`mulW` on the
first pass's `β` and `β²` registers), so `Q'_H = d_Q(β³ + 2k_h + β)`; every other free number is the v2 program's
(`m = max(mOf, m₀)`, so at `m_D = 2`, `m_E = 1`, `m₀ = 0` and `a = t`, `m = 1 + 2t`).

* `qH`, `fixAH`, `fixAOutH`, `fixANH`, `needH`, **`fixAH_exec`**, `fixAMH`, `fixAMOutH`, `fixAMNH`, **`fixAMH_exec`**,
  `fixWH`, `fixOutH`, `fixNH`, **`fixWH_exec`**, `freeW2H`, **`freeValH`**, **`freeW2H_run`**, **`freeProgH`**.

Paper quantity of the main type: the HASH stage's free numbers, `Q' = Q_aux` of filt:aux-precision. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimT.C4Set

def qH : Fin 6 ↪ Fin 35 := ⟨![8, 17, 7, 26, 27, 28], by decide⟩
@[simp] theorem qH_apply (i : Fin 6) : qH i = ![8, 17, 7, 26, 27, 28] i := rfl

/-- **The HASH second pass, part 1**: `Q'_H = d_Q(β³ + 2k_h + β)`, `h`, `pr`. -/
def fixAH (κ : FreeK2) : WM (LNS 0) LNR :=
  .seq (mulW (qH.trans Gall))
  (.seq (ParseNat.addTo (Gall 31) (Gall 7) (Gall 26))
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
  (cmulW κ.k.dP (fP2.trans Gall)))))))))))))

/-- The HASH first part's exit state. -/
def fixAOutH (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR :=
  ((((((((((((τ.setv (Gall 7) (β x * (β x * β x))).setv (Gall 7) (β x * (β x * β x) + x.kh)).setv (Gall 7)
    (β x * (β x * β x) + x.kh + x.kh)).setv (Gall 7) (β x * (β x * β x) + x.kh + x.kh + β x)).setv (Gall 2)
    (κ.k.dQ * (β x * (β x * β x) + x.kh + x.kh + β x))).setv (Gall 10) x.n).setv (Gall 10) (x.n + 1)).setv (Gall 9)
    1).setv (Gall 9) (1 * (x.n + 1) ^ κ.eH)).setv (Gall 3) (κ.k.dH * (1 * (x.n + 1) ^ κ.eH))).setv (Gall 11) 1).setv
    (Gall 11) (1 * (x.n + 1) ^ κ.eP)).setv (Gall 5) (κ.k.dP * (1 * (x.n + 1) ^ κ.eP))

/-- The HASH first part's step units. -/
def fixANH (κ : FreeK2) : ℕ := fixAN κ + 5

/-- The capacity the HASH second pass needs. -/
def needH (κ : FreeK2) (x : FreeIn) : ℕ :=
  need2 κ x + β x * β x + β x * (β x * β x) + (β x * (β x * β x) + x.kh + x.kh + β x) +
    κ.k.dQ * (β x * (β x * β x) + x.kh + x.kh + β x)

/-- The HASH second pass, parts 1–2. -/
def fixAMH (κ : FreeK2) : WM (LNS 0) LNR := .seq (fixAH κ) (fixM κ)

/-- The exit state of the HASH parts 1–2. -/
def fixAMOutH (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR :=
  ((((fixAOutH κ x τ).setv (Gall 12) (mOf κ.base x)).setv (Gall 4) 0).setv (Gall 13) κ.m0).setv (Gall 4)
    (max (mOf κ.base x) κ.m0)

def fixAMNH (κ : FreeK2) : ℕ := fixANH κ + 15

/-- **The HASH second pass.** -/
def fixWH (κ : FreeK2) : WM (LNS 0) LNR := .seq (fixAMH κ) fixC

def fixOutH (κ : FreeK2) (x : FreeIn) (τ : WState (LNS 0) LNR) : WState (LNS 0) LNR := fixCOut κ x (fixAMOutH κ x τ)

def fixNH (κ : FreeK2) : ℕ := fixAMNH κ + 1 + 15

theorem fixAH_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hb2 : τ.val (Gall 17) = β x * β x)
    (hn : τ.val (Gall 30) = x.n)
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : needH κ x ≤ cap) :
    WExec cap (fixAH κ) τ (fixAOutH κ x τ) (fixANH κ * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hc' := hc
  unfold needH need2 at hc'
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
  unfold fixAH fixANH fixAN
  refine seqD cap _ 5 (mulW_spec cap (qH.trans Gall) τ (β x) (β x * β x) (by simp [hb]) (by simp [hb2])
    (fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | simp [z7, z26, z27, z28])
    (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 31) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) x.kh
    (β x * (β x * β x)) _ (by simp [hkh]) (by simp) (by simp [z26]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 31) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) x.kh
    (β x * (β x * β x) + x.kh) _ (by simp [hkh]) (by simp) (by simp [z26]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (CapNum.add1 cap (Gall 8) (Gall 7) (Gall 26) (by simp) (by simp) (by simp) (β x)
    (β x * (β x * β x) + x.kh + x.kh) _ (by simp [hb]) (by simp) (by simp [z26]) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 5 (cmulW_spec cap κ.k.dQ (fQ.trans Gall) _ (β x * (β x * β x) + x.kh + x.kh + β x) (by simp)
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

theorem fixAMH_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hb2 : τ.val (Gall 17) = β x * β x)
    (hn : τ.val (Gall 30) = x.n) (hm : τ.val (Gall 4) = mOf κ.base x)
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : needH κ x ≤ cap) :
    WExec cap (fixAMH κ) τ (fixAMOutH κ x τ) (fixAMNH κ * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hc' := hc
  unfold needH need2 at hc'
  generalize 2 ^ (x.n / 2 / 2 / 2 / 2 + κ.k.dC * (β x * β x)) = P2 at hc'
  generalize 2 ^ (κ.k.dC * (β x * β x)) = P3 at hc'
  have hA := fixAH_exec κ cap x τ hkh hb hb2 hn hz hc
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
  have kA : ∀ k : Fin 35, k ∉ ({7, 2, 10, 9, 3, 11, 5} : Finset (Fin 35)) → (fixAOutH κ x τ).val (Gall k) = τ.val (Gall k) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨h7, h2, h10, h9, h3, h11, h5⟩ := hk
    simp [fixAOutH, Function.update_apply, hne h7, hne h2, hne h10, hne h9, hne h3, hne h11, hne h5]
  unfold fixAMH fixM fixAMNH
  refine seqD cap _ (fixANH κ) hA le_rfl (by omega) ?_
  have e1 : fixANH κ + 15 - fixANH κ - 1 = 14 := by omega
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

theorem fixWH_exec (κ : FreeK2) (cap : ℕ) (x : FreeIn) (τ : WState (LNS 0) LNR)
    (hkh : τ.val (Gall 31) = x.kh) (hb : τ.val (Gall 8) = β x) (hb2 : τ.val (Gall 17) = β x * β x)
    (hn : τ.val (Gall 30) = x.n) (hm : τ.val (Gall 4) = mOf κ.base x) (h20 : τ.val (Gall 20) = κ.k.dC * (β x * β x))
    (h1 : τ.val (Gall 1) = 2 ^ (κ.k.dC * (β x * β x)))
    (hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) → τ.val (Gall k) = 0)
    (hc : needH κ x ≤ cap) :
    WExec cap (fixWH κ) τ (fixOutH κ x τ) (fixNH κ * UnaryPow.sq cap) := by
  have hAM := fixAMH_exec κ cap x τ hkh hb hb2 hn hm hz hz' hc
  have hc2 : need2 κ x ≤ cap := le_trans (by unfold needH; omega) hc
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  have kAM : ∀ k : Fin 35, k ∉ ({7, 2, 10, 9, 3, 11, 5, 12, 4, 13} : Finset (Fin 35)) →
      (fixAMOutH κ x τ).val (Gall k) = τ.val (Gall k) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨h7, h2, h10, h9, h3, h11, h5, h12, h4, h13⟩ := hk
    simp [fixAMOutH, fixAOutH, Function.update_apply, hne h7, hne h2, hne h10, hne h9, hne h3, hne h11, hne h5,
      hne h12, hne h4, hne h13]
  have hC := fixC_exec κ cap x (fixAMOutH κ x τ) (by rw [kAM 30 (by decide), hn]) (by rw [kAM 20 (by decide), h20])
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
      · rw [kAM 29 (by decide)]; exact hz' 29 (by decide)) hc2
  unfold fixWH fixNH
  exact seqD cap _ (fixAMNH κ) hAM le_rfl (by omega) (by rw [show fixAMNH κ + 1 + 15 - fixAMNH κ - 1 = 15 by omega]; exact hC)

/-- **The HASH program**: FreeGen's first pass, then the HASH second pass. -/
def freeW2H (κ : FreeK2) : WM (LNS 0) LNR := .seq (freeW κ.base) (fixWH κ)

/-- **The HASH free numbers**: the v2 numbers with `Q' = d_Q(β³ + 2k_h + β)` (P3:2291-2296). -/
def freeValH (κ : FreeK2) (x : FreeIn) : Fin 7 → ℕ :=
  ![κ.k.dT * (β x * β x), 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)), κ.k.dQ * (β x * (β x * β x) + x.kh + x.kh + β x),
    κ.k.dH * (x.n + 1) ^ κ.eH,
    max (mOf κ.k x) κ.m0,
    κ.k.dP * (x.n + 1) ^ κ.eP,
    max (x.n - (x.kh + x.kh) + κ.k.dA * β x) (κ.k.dR * (β x * β x))]

theorem freeW2H_run (κ : FreeK2) (cap : ℕ) (σ : WState (LNS 0) LNR) (x : FreeIn) (hR : FreeRegs σ x)
    (hF : ∀ q : Fin LNR, 130 ≤ q.val → q.val < 137 → σ.val q = 0)
    (hS : ∀ q : Fin LNR, 177 ≤ q.val → q.val < 200 → σ.val q = 0) (hc : need κ.base x + needH κ x ≤ cap) :
    ∃ τ, WExec cap (freeW2H κ) σ τ ((201 + fixNH κ) * UnaryPow.sq cap) ∧ (∀ j, τ.val (FB j) = freeValH κ x j) ∧
      (∀ q : Fin LNR, (q.val < 130 ∨ (137 ≤ q.val ∧ q.val < 177) ∨ 200 ≤ q.val) → τ.val q = σ.val q) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hz0 : ∀ k : Fin 35, k.val < 30 → σ.val (Gall k) = 0 := by
    intro k hk
    rcases Gall_range k hk with h | h
    · exact hF _ h.1 h.2
    · exact hS _ h.1 h.2
  have e1 := freeW_exec κ.base cap σ x hR hF hS (by omega)
  have hb := freeOut_base κ x σ
  have hkh : (freeOut κ.base x σ).val (Gall 31) = x.kh := by
    rw [freeOut_val κ.base x σ 31 (by decide)]; exact hR.2.1
  have hn : (freeOut κ.base x σ).val (Gall 30) = x.n := by
    rw [freeOut_val κ.base x σ 30 (by decide)]; exact hR.1
  have hm : (freeOut κ.base x σ).val (Gall 4) = mOf κ.base x := by
    have h := freeOut_fb κ.base x σ 4
    rw [FB_Gall] at h
    exact h
  have hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) →
      (freeOut κ.base x σ).val (Gall k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h | h | h | h | h | h | h <;> subst h
    all_goals first
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2
      | (rw [freeOut_val κ.base x σ _ (by decide)]; exact hz0 _ (by decide))
  have hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) →
      (freeOut κ.base x σ).val (Gall k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h | h | h <;> subst h <;>
      (rw [freeOut_val κ.base x σ _ (by decide)]; exact hz0 _ (by decide))
  have h20 : (freeOut κ.base x σ).val (Gall 20) = κ.k.dC * (β x * β x) := by
    simp [freeOut, FreeK2.base, Function.update_apply]
  have h1 : (freeOut κ.base x σ).val (Gall 1) = 2 ^ (κ.k.dC * (β x * β x)) := by
    simp [freeOut, FreeK2.base, Function.update_apply]
  have hb2 : (freeOut κ.base x σ).val (Gall 17) = β x * β x := by
    simp [freeOut, Function.update_apply]
  have e2 := fixWH_exec κ cap x (freeOut κ.base x σ) hkh (freeOut_beta κ.base x σ) hb2 hn hm h20 h1 hz hz' (by omega)
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  refine ⟨fixOutH κ x (freeOut κ.base x σ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine WExec.mono (WExec.seq e1 e2) ?_
    rw [Nat.add_mul]
    have : 1 ≤ 1 * UnaryPow.sq cap := by omega
    omega
  · intro j
    have hfb := freeOut_fb κ.base x σ j
    rw [FB_Gall] at hfb ⊢
    have h16 : x.n / 2 / 2 / 2 / 2 = x.n / 16 := by omega
    fin_cases j
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, freeOut, Function.update_apply, freeValH, FreeK2.base]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, Function.update_apply, freeValH, h16]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, Function.update_apply, freeValH]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, Function.update_apply, freeValH]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, Function.update_apply, freeValH, mOf, FreeK2.base]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, Function.update_apply, freeValH]
    · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, freeOut, Function.update_apply, freeValH, FreeK2.base, Nat.sub_sub]
  · intro q hq
    have hne' : ∀ k : Fin 35, k.val < 30 → q ≠ Gall k := by
      intro k hk h
      have := Gall_range k hk
      rw [← h] at this
      omega
    have hkept : (freeOut κ.base x σ).val q = σ.val q := by
      simp [freeOut, hne' _ (by decide : (8 : Fin 35).val < 30), hne' _ (by decide : (17 : Fin 35).val < 30),
        hne' _ (by decide : (18 : Fin 35).val < 30), hne' _ (by decide : (19 : Fin 35).val < 30),
        hne' _ (by decide : (0 : Fin 35).val < 30), hne' _ (by decide : (2 : Fin 35).val < 30),
        hne' _ (by decide : (3 : Fin 35).val < 30), hne' _ (by decide : (5 : Fin 35).val < 30),
        hne' _ (by decide : (20 : Fin 35).val < 30), hne' _ (by decide : (1 : Fin 35).val < 30),
        hne' _ (by decide : (21 : Fin 35).val < 30), hne' _ (by decide : (22 : Fin 35).val < 30),
        hne' _ (by decide : (23 : Fin 35).val < 30), hne' _ (by decide : (24 : Fin 35).val < 30),
        hne' _ (by decide : (25 : Fin 35).val < 30), hne' _ (by decide : (4 : Fin 35).val < 30),
        hne' _ (by decide : (6 : Fin 35).val < 30)]
    rw [← hkept]
    simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, hne' _ (by decide : (7 : Fin 35).val < 30),
      hne' _ (by decide : (2 : Fin 35).val < 30), hne' _ (by decide : (14 : Fin 35).val < 30),
      hne' _ (by decide : (16 : Fin 35).val < 30), hne' _ (by decide : (27 : Fin 35).val < 30),
      hne' _ (by decide : (28 : Fin 35).val < 30), hne' _ (by decide : (29 : Fin 35).val < 30),
      hne' _ (by decide : (1 : Fin 35).val < 30),
      hne' _ (by decide : (10 : Fin 35).val < 30), hne' _ (by decide : (9 : Fin 35).val < 30),
      hne' _ (by decide : (3 : Fin 35).val < 30), hne' _ (by decide : (11 : Fin 35).val < 30),
      hne' _ (by decide : (5 : Fin 35).val < 30), hne' _ (by decide : (12 : Fin 35).val < 30),
      hne' _ (by decide : (4 : Fin 35).val < 30), hne' _ (by decide : (13 : Fin 35).val < 30)]
  · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, freeOut]
  · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, freeOut]
  · simp [fixOutH, fixCOut, fixAMOutH, fixAOutH, freeOut]

/-- **The HASH free numbers' program** (C4.K's `FreeProg`). -/
noncomputable def freeProgH (κ : FreeK2) : FreeProg where
  prog := freeW2H κ
  val := freeValH κ
  cost := fun cap _ => (201 + fixNH κ) * UnaryPow.sq cap
  ok := fun cap x => need κ.base x + needH κ x ≤ cap
  run := fun cap σ x hR hF hS hok => freeW2H_run κ cap σ x hR hF hS hok

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen
