import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.SeedFix.C4CapD
import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymFam
import Proof.Wire_3_5.Primitive.Writers.SymHelp
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SYM item (b), part 1: the numbers front's needs at every SYM call (the discharge, at any cap)

P3:2929-2941, 2994-3000 (the numbers `ℓ`, `Q` and the call's sizes the numbers machine holds), P3:3105-3115 (every
size is `2^{O(k)}·poly(n)` at an on-star call): the SYM numbers front (`C4Set.numsSW`, PA's SYM decode numbers) needs
`P1Need`, `CapNeed`, `NumsNeed` and the capacity's call-size conditions at its capacity `cap`. The writer (`SymFam.
sym_fam_run`, rv-pa-m42) discharges them from the atoms of the call below `K_Q = 2^{c_A}·(2^{m}+1)`; here with
`m = k + L + K_F L²` (no POP term: the numbers front reads none) and ANY `cap ≥ 100·K_Q + 200000`.

* **`sym_needs`**: `P1Need`, `hKb`, `hC`, `hcS`, `hcP`, `CapNeed`, `NumsNeed` and the eleven values `≤ cap`.

Paper quantity of the main type: the SYM call's sizes against the numbers machine's capacity. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam

/-- **The SYM numbers front's needs** at any capacity `cap ≥ 100·K_Q + 200000`, `K_Q = 2^{c_A}(2^{k+L+K_F L²}+1)`. -/
theorem sym_needs (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (h : SB)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hfe : h.fe = F.filterErrDeg)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (cap : ℕ)
    (hcapKQ : 100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) +
      h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000 ≤ cap) :
    P1Need cap (symReq n a ha Cs carriers translation).word n (Data.symCodes a Cs) (carriers.map Stars.Carrier.code)
        (carriers.map (·.length)) (cyOf Cs) (UnaryCalc.value h.D2 h.C2 n) ((n + 1) ^ 26) ∧
      (∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ UnaryCalc.value h.D2 h.C2 n) ∧
      (∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ (n + 1) ^ 26) ∧
      (F.filterErrDeg + 4) * (n + 3) + 2 * F.cr + 20 ≤ cap ∧
      SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n)
        (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤ cap ∧
      CapNeed (gateCap l) .sym n (Ledger.rowBr F.cr n)
        (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap ∧
      NumsNeed cap n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)
        (cyOf Cs).sum carriers.length (Ledger.Lq n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
        a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ∧
      (∀ j : Fin 11, (![((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n, n, F.filterErrDeg * Ledger.Lq n,
        Ledger.Lq n, SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs), carriers.length,
        (Data.symCodes a Cs).length, (cyOf Cs).getD 0 0, (cyOf Cs).getD 1 0, (cyOf Cs).getD 2 0,
        (cyOf Cs).getD 3 0] : Fin 11 → ℕ) j ≤ cap) ∧
      2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits *
          2 ^ FlatNums.fbv (cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n))
            (Ledger.Lq n + 5) *
          SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤
        2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) +
          h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1) := by
  -- the base constants' inequalities
  obtain ⟨cw, cc2, c13, csb, cfb, ctot, ccr, csp, cj, c40, ccm, c1, c3, c6, c7⟩ := h.cA_ge
  obtain ⟨kdw, kd2, k26, k1, kz, ksb, kfb, ktot, kfe, kfe4, ksa, kcsp, kzm, k208, k260, kdf, kdp⟩ := h.KF_ge
  obtain ⟨dC2, dD2⟩ := h.data_ge
  rw [hfe] at kfe kfe4 kdf
  -- the call's envelopes
  have hwl : (symReq n a ha Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a0 ha0 _ hcall) (hwb n)
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLd]; exact Nat.clog_pos (by norm_num) (by omega)
  have hLn : L ≤ n + 2 := hLd ▸ clog_le_self _
  have hLq : Ledger.Lq n = L := by rw [hLd]; rfl
  -- the SYM cap
  obtain ⟨BS, hBSd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n := ⟨_, rfl⟩
  have hBS : BS ≤ h.capK * (n + 2) ^ h.Z := by rw [hBSd, hK, hZ]; exact sfam_capS l F kclk coef A a0 ha0 n
  have hBS1 : 1 ≤ BS := by rw [hBSd]; exact ((gate0 l F).budget kclk coef A a0 ha0).capOf_pos .sym n
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).kOf n := ⟨_, rfl⟩
  have h2kh := HashFam.fam_two_kh l F kclk coef A a0 ha0 hs
  rw [← hkd] at h2kh
  obtain ⟨kh, hkhd⟩ : ∃ x, x = SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) := ⟨_, rfl⟩
  have h2k : 2 * kh = k := by rw [hkhd]; exact h2kh
  obtain ⟨cA, hcA⟩ : ∃ x, x = h.cA := ⟨_, rfl⟩
  obtain ⟨m, hmd⟩ : ∃ x, x = k + L + h.KF * L ^ 2 + 0 := ⟨_, rfl⟩
  obtain ⟨KQ, hKQ⟩ : ∃ x, x = 2 ^ cA * (2 ^ m + 1) := ⟨_, rfl⟩
  have hcapKQ' : 100 * KQ + 200000 ≤ cap := by rw [hKQ, hcA, hmd, hLd, hkd]; exact hcapKQ
  have toKQ : ∀ {X c d a' : ℕ}, X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a' * L) * 2 ^ k * 2 ^ 0) → c ≤ h.cA →
      d + a' ≤ h.KF → X ≤ KQ := by
    intro X c d a' hX hc hda
    rw [hLd] at hX
    have := atomQ (cA := h.cA) (KF := h.KF) hX hc hda
    rw [← hLd] at this
    rw [hKQ, hcA, hmd]
    exact this
  have toKQc : ∀ {X c d : ℕ}, X ≤ 2 ^ c * (n + 2) ^ d → c ≤ h.cA → d ≤ h.KF → X ≤ KQ := by
    intro X c d hX hc hd
    apply toKQ (a' := 0) _ hc (le_of_eq_of_le (Nat.add_zero d) hd)
    refine le_trans hX (Nat.mul_le_mul_left _ ?_)
    simp only [zero_mul, pow_zero, mul_one]
    exact Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  have toKQp : ∀ {X K d : ℕ}, X ≤ K * (n + 2) ^ d → Nat.clog 2 K ≤ h.cA → d ≤ h.KF → X ≤ KQ := by
    intro X K d hX hK' hd
    exact toKQc (le_trans hX (Nat.mul_le_mul_right _ (le_two_pow_clog K))) hK' hd
  have p12 : ∀ d, (n + 1) ^ d ≤ (n + 2) ^ d := fun d => Nat.pow_le_pow_left (Nat.le_succ _) d
  have pp1 : ∀ d, 1 ≤ (n + 2) ^ d := fun d => Nat.one_le_pow _ _ (Nat.succ_pos _)
  have aW : (symReq n a ha Cs carriers translation).word.length ≤ KQ :=
    toKQp (le_trans hwl (Nat.mul_le_mul_left _ (p12 _))) cw kdw
  obtain ⟨V, hVd⟩ : ∃ x, x = UnaryCalc.value h.D2 h.C2 n := ⟨_, rfl⟩
  have aV : V ≤ KQ := toKQp (le_of_eq_of_le (hVd.trans (value_eq _ _ _)) (Nat.mul_le_mul_left _ (p12 _))) cc2 kd2
  have a26 : 8 * (n + 1) ^ 26 ≤ KQ :=
    toKQc (c := 3) (d := 26) (le_of_le_of_eq (Nat.mul_le_mul_left 8 (p12 26)) (by norm_num)) c3 k26
  have an : n + 2 ≤ KQ := toKQc (c := 0) (d := 1) (by rw [pow_one, pow_zero, one_mul]) (Nat.zero_le _) k1
  have aBS : 8192 * BS ≤ KQ := by
    apply toKQc (c := 13 + Nat.clog 2 h.capK) (d := h.Z) _ c13 kz
    calc 8192 * BS ≤ 8192 * (h.capK * (n + 2) ^ h.Z) := Nat.mul_le_mul_left _ hBS
      _ ≤ 8192 * (2 ^ Nat.clog 2 h.capK * (n + 2) ^ h.Z) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_two_pow_clog _))
      _ = 2 ^ (13 + Nat.clog 2 h.capK) * (n + 2) ^ h.Z := by rw [pow_add]; norm_num; ring
  have akk : 8 * 2 ^ k ≤ KQ := by
    apply toKQ (c := 3) (d := 0) (a' := 0) _ c3 (Nat.zero_le _)
    simp only [pow_zero, zero_mul, one_mul, mul_one]
    norm_num
  -- the call's counts
  have hcx : ∀ c ∈ carriers.map (·.length), c ≤ (n + 1) ^ 26 := by
    intro c hc
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc
    exact (henv X hX).1
  have hcy : ∀ c ∈ cyOf Cs, c ≤ (n + 1) ^ 26 := by
    intro c hc
    unfold cyOf at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact Data.symGates_len_le (Cs i) _ (hdesc i)
  have hxs : (carriers.map (·.length)).sum ≤ 2 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (carriers.map (·.length)) ((n + 1) ^ 26) hcx
    rw [List.length_map, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ hk2)
  have hys : (cyOf Cs).sum ≤ 4 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (cyOf Cs) ((n + 1) ^ 26) hcy
    rw [cyOf_length, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ ha)
  have hx0 : (carriers.map (·.length)).getD 0 0 ≤ (n + 1) ^ 26 := getD_le hcx 0
  have hx1 : (carriers.map (·.length)).getD 1 0 ≤ (n + 1) ^ 26 := getD_le hcx 1
  have hy : ∀ j, (cyOf Cs).getD j 0 ≤ (n + 1) ^ 26 := fun j => getD_le hcy j
  have hy4 := sum_getD4 (cyOf Cs) (by rw [cyOf_length]; exact ha)
  have hN26 : (n + 1) ^ 26 + 1 ≤ (n + 2) ^ 26 := CallIndex.succ_le_N26 n
  have hp26 := p12 26
  -- the seeds
  obtain ⟨sb, hsbd⟩ : ∃ x, x = (SymDec.gP n BS (F.filterErrDeg * Ledger.Lq n)).seedBits := ⟨_, rfl⟩
  have hsb : sb ≤ h.aSb * L + h.cSb := by
    have := sb_le n BS h.capK h.Z h.fe hBS
    rw [hfe, ← hsbd, ← hLd] at this
    unfold SB.aSb SB.cSb; rw [hfe]
    exact le_of_le_of_eq this (by ring)
  have p2sb : 2 ^ sb ≤ 2 ^ h.cSb * 2 ^ (h.aSb * L) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (le_of_le_of_eq hsb (Nat.add_comm _ _))
  have asb : 2 * 2 ^ sb ≤ KQ :=
    toKQ (c := h.cSb + 1) (d := 0) (a' := h.aSb)
      (atomE2 (le_of_le_of_eq (Nat.mul_le_mul_left 2 p2sb) (by rw [pow_succ, pow_zero]; ring))) csb ksb
  have pfbG : ∀ {M B : ℕ}, M ≤ 4 * (n + 1) ^ 26 → B ≤ 8192 * BS →
      2 ^ FlatNums.fbv M B (L + 5) ≤ 2 ^ h.cFb * 2 ^ (h.aFb * L) := by
    intro M B hM hB
    have hf := fbv_fam h hM (le_trans hB (Nat.mul_le_mul_left _ hBS))
    rw [← hLd] at hf
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (le_of_le_of_eq hf (Nat.add_comm _ _))
  have afbG : ∀ {M B : ℕ}, M ≤ 4 * (n + 1) ^ 26 → B ≤ 8192 * BS → 2 * 2 ^ FlatNums.fbv M B (L + 5) ≤ KQ := by
    intro M B hM hB
    exact toKQ (c := h.cFb + 1) (d := 0) (a' := h.aFb)
      (atomE2 (le_of_le_of_eq (Nat.mul_le_mul_left 2 (pfbG hM hB)) (by rw [pow_succ, pow_zero]; ring))) cfb kfb
  have h8192 : carriers.length * 4096 ≤ 8192 := le_trans (Nat.mul_le_mul_right 4096 hk2) (by norm_num)
  have hbV : SymDec.bV carriers.length BS ≤ 8192 * BS := by
    unfold SymDec.bV; exact Nat.mul_le_mul_right _ h8192
  have afb := afbG hys hbV
  -- the joint states and the units per state
  have ast : SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤
      (n + 2) ^ 208 := by
    have hb : ∀ j, (cyOf Cs).getD j 0 + 1 ≤ (n + 2) ^ 26 := fun j => le_trans (Nat.add_le_add_right (hy j) 1) hN26
    exact le_of_le_of_eq (stV_le (hb 0) (hb 1) (hb 2) (hb 3))
      ((pow_mul (n + 2) 26 8).symm.trans (congrArg _ (by norm_num)))
  have aeu : SymDec.euV (cyOf Cs).sum carriers.length a ≤ 2 ^ 7 * (n + 2) ^ 26 := euV_le hys hk2 ha hp26 (pp1 26)
  have atot : SymDec.totV n BS (F.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n) kh a
      ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤ KQ := by
    unfold SymDec.totV
    rw [← hsbd, hLq, h2k]
    exact toKQ (prod5 p2sb (pfbG hys hbV) ast (le_refl _) aeu) ctot ktot
  -- the n-only atoms
  have aerr : F.filterErrDeg * L ≤ KQ :=
    toKQ (c := 0) (d := 0) (a' := F.filterErrDeg)
      (atomE2 (le_of_le_of_eq (SymSizes.self_le_two_pow _) (by rw [pow_zero, pow_zero]; ring))) (Nat.zero_le _) kfe
  have afe4 : (F.filterErrDeg + 4) * (n + 3) ≤ KQ := by
    apply toKQ (c := 1) (d := 1) (a' := F.filterErrDeg + 4) (atomE2 _) c1 kfe4
    have q1 : F.filterErrDeg + 4 ≤ 2 ^ ((F.filterErrDeg + 4) * L) :=
      le_trans (SymSizes.self_le_two_pow _) (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hL1))
    calc (F.filterErrDeg + 4) * (n + 3) ≤ 2 ^ ((F.filterErrDeg + 4) * L) * (2 * (n + 2)) :=
          Nat.mul_le_mul q1 (n3_le n)
      _ = 2 ^ 1 * ((n + 2) ^ 1 * 2 ^ ((F.filterErrDeg + 4) * L)) := by ring
  have acr : 2 * F.cr + 20 ≤ KQ := by
    apply toKQc (c := 4 + Nat.clog 2 (2 * h.cr + 2)) (d := 0) _ ccr (Nat.zero_le _)
    rw [pow_zero, mul_one, pow_add, ← hcr]
    exact lin16 (le_two_pow_clog _)
  have asp : SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤ KQ := by
    have e1 : 3 + 32 * SymSizes.cXg l * SymSizes.schedJ l = h.sA := by unfold SB.sA; rw [hcX, hJ]
    have e2 : 6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1) = h.sBc := by unfold SB.sBc; rw [hcX, hJ]
    have hsp := SymSizes.sparse_le_gate l n
    rw [e1, e2, ← hLd] at hsp
    apply toKQ (c := h.sBc) (d := 0) (a' := h.sA) (atomE2 (le_trans hsp (le_of_eq _))) csp ksa
    rw [pow_add, pow_zero]; ring
  have acapN : 2 ^ 40 * (CallIndexR.capK F.cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) .sym ≤ 2 * KQ := by
    have t1 := toKQc (X := 2 ^ 40 * (h.capK * (n + 2) ^ h.Zm)) (c := 40 + Nat.clog 2 h.capK) (d := h.Zm)
      (by rw [pow_add, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_two_pow_clog _))) c40 kzm
    have t2 := toKQc (X := h.cM) (c := Nat.clog 2 h.cM) (d := 0) (by rw [pow_zero, mul_one]; exact le_two_pow_clog _)
      ccm (Nat.zero_le _)
    rw [← hK, ← hZm, ← hcM]
    exact le_of_le_of_eq (Nat.add_le_add t1 t2) (by ring)
  have aeuK : SymDec.euV (cyOf Cs).sum carriers.length a ≤ KQ := toKQc (c := 7) (d := 26) aeu c7 k26
  have astK : SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤ KQ :=
    toKQc (c := 0) (d := 208) (by rw [pow_zero, one_mul]; exact ast) (Nat.zero_le _) k208
  have afb' : 2 * 2 ^ FlatNums.fbv (cyOf Cs).sum (SymDec.bV carriers.length BS) (Ledger.Lq n + 5) ≤ KQ := by
    rw [hLq]; exact afb
  have hLqn : Ledger.Lq n ≤ n + 2 := by rw [hLq]; exact hLn
  -- the data's code bound
  have hnwV : PrimT.C4GateSym.needW n ≤ V := by
    rw [hVd, value_eq]
    exact le_trans (hnw n) (Nat.mul_le_mul dC2 (Nat.pow_le_pow_right (Nat.succ_pos _) dD2))
  have td := PrimT.C4GateSym.sym_data_hyps Cs carriers ha hk2 hdesc henv V hnwV
  have hKb : ∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ V := by
    intro c hc
    unfold Data.symCodes at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact td.2.2.2.2.2.2.2.2.2.1 i
  have hC : ∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ (n + 1) ^ 26 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcx c hc
    · exact hcy c hc
  -- the capacity's conditions
  have hKQcap : KQ ≤ cap :=
    le_trans (le_trans (Nat.le_mul_of_pos_left KQ (by norm_num : 0 < 100)) (Nat.le_add_right _ 200000)) hcapKQ'
  have e1 : (Data.symCodes a Cs).length = a := by unfold Data.symCodes; simp
  have hN1 := p1_block (cap := cap) (X := (n + 1) ^ 26) (symReq n a ha Cs carriers translation).word
    (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (cyOf Cs) e1
    (List.length_map _) (List.length_map _) aW ha hk2 aV an hxs hys a26 hcapKQ'
  obtain ⟨_, _, _, hcS, hcP, hX⟩ := cap_block (nc := carriers.length) (b := KQ) hcapKQ' rfl atot aeuK hys a26 h2k akk
    astK afb' hk2 hx0 hx1 (le_trans hbV aBS) hLqn an afe4 acr asp acapN
  have hcC := capNeed_of l F.cr n cap hX
  have hN2 := nn_block (cap := cap) hBS1 hcapKQ' aBS a26 (by rw [hLq]; exact aerr) (by rw [← hsbd]; exact asb) hLqn an
    hbV hys afb' h2k akk atot hk2 ha hy4
  have agfp : 2 ^ sb * 2 ^ FlatNums.fbv (cyOf Cs).sum (SymDec.bV carriers.length BS) (Ledger.Lq n + 5) *
      SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤ KQ := by
    have e1 := prod5 (T := 0) (X4 := 1) (X5 := 1) (c5 := 0) (d5 := 0) p2sb (pfbG hys hbV) ast
      (Nat.one_le_two_pow (n := k)) (by norm_num)
    rw [Nat.mul_one, Nat.mul_one] at e1
    rw [hLq]
    exact toKQ e1 (by omega) (by omega)
  have agfp' := agfp
  rw [hKQ, hcA, hmd, hLd, hkd] at agfp'
  subst hVd hBSd hkhd hsbd
  refine ⟨hN1, hKb, hC, hcS, hcP, hcC, hN2, fun j => ?_, agfp'⟩
  have hkh2 : SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ KQ := by
    have : SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) < 2 ^ k := by
      have := Nat.lt_two_pow_self (n := SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      have : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hy' := hy
  fin_cases j
  · show ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n ≤ cap; omega
  · show n ≤ cap; omega
  · show F.filterErrDeg * Ledger.Lq n ≤ cap; rw [hLq]; omega
  · show Ledger.Lq n ≤ cap; omega
  · show SeedFix.callKh _ ≤ cap; omega
  · show carriers.length ≤ cap; omega
  · show (Data.symCodes a Cs).length ≤ cap; rw [e1]; omega
  · show (cyOf Cs).getD 0 0 ≤ cap; have := hy 0; omega
  · show (cyOf Cs).getD 1 0 ≤ cap; have := hy 1; omega
  · show (cyOf Cs).getD 2 0 ≤ cap; have := hy 2; omega
  · show (cyOf Cs).getD 3 0 ≤ cap; have := hy 3; omega

end NearCubicWires.WireExponent3_5.PrimT.C4SymN

end
