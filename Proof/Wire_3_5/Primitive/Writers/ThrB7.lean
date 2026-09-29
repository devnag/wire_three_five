import Proof.Wire_3_5.Primitive.Writers.ThrK7
import Proof.Wire_3_5.Primitive.Writers.ThrSide11

/-! # c4 THR block, piece 7 part 2: the THR constants and the builder `ThrFreeOkB7`

The THR twin of `symCof`/`symCDs`/`symFreeOk` (SymBuild) at the v7 contract (v6 + the strip):
* the strip's bound: `kbT_codes` (the call's circuit and carrier codes within `kbT n`), `strip_req` (the translation's
  words, at any call), `stripP` (one polynomial above the eight premises: `|req.word| ≤ wordBound`, `|hbF| ≤ c_H L²`,
  `kbT`, the translation, the counts) with **`stripP_poly`**, **`strip_le`** (`ThrStripAt pr` once
  `stripP l n ≤ 2pr + 2`);
* **`thrCof`** (the THR constants at `fe`, fixed before `F`: `d_T = 2e_N`, `d_C = 12d_T`, `d_Q = cST + 1`,
  `d_H = coef·4^{deg} + 2`, `e_H = 26deg + 1`, `d_D = dDT`, `d_P`/`e_P` above the precondition's and the strip's
  polynomial, `d_A = symDAc`, `d_R = 0`), **`thrCDt`** (the load floor: `occCDT + 16·thrC1 + symHC`);
* `c3KT`, **`c3_thr2`** (the C3 load), **`thr_pad`**, **`thr_side`** (`ThrEAt3` from `thrEAt`), **`thr_strip`**;
* **`thrFreeOk`** : `ThrFreeOkB7 l wa`.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the THR stage and their bounds
(P3:2929-2941, 3011-3016, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L kh_two coOf symHC symDAc symKch symKn algL
  small_of kL_le_loadPsi)

/-! ## The strip's bound -/

/-- `kbT` is polynomial. -/
theorem kbT_poly : PolynomiallyBounded ThrFam.kbT :=
  polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_comp CallSize.pb_circBits CallSize.pb_codeParam)
      (polynomiallyBounded_comp CallSize.pb_carrierBits CallSize.pb_codeParam))

/-- **The strip's polynomial**: the call word's bound, `c_H(n+1)²`, `kbT`, the translation's words, `n`, `70`. -/
noncomputable def stripP (l : Literals) (n : ℕ) : ℕ :=
  CallSize.wordBound 26 26 2 n + cH l * ((n + 1) * (n + 1)) + ThrFam.kbT n + 10 * ((2 * n + 3) * (n + 1)) + n + 70

theorem stripP_poly (l : Literals) : PolynomiallyBounded (stripP l) := by
  have h1 : PolynomiallyBounded (fun n : ℕ => n + 1) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)
  have h2 : PolynomiallyBounded (fun n : ℕ => 2 * n + 3) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) polynomiallyBounded_id)
      (polynomiallyBounded_constant 3)
  exact polynomiallyBounded_mono (fun _ => le_of_eq rfl)
    (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add CallSize.wordBound_poly
        (polynomiallyBounded_mul (polynomiallyBounded_constant (cH l)) (polynomiallyBounded_mul h1 h1)))
      kbT_poly)
      (polynomiallyBounded_mul (polynomiallyBounded_constant 10) (polynomiallyBounded_mul h2 h1)))
      polynomiallyBounded_id) (polynomiallyBounded_constant 70))

/-- The strip polynomial's coefficient and degree (fixed by the literals). -/
noncomputable def stripC (l : Literals) : ℕ := Classical.choose (stripP_poly l)
noncomputable def stripD (l : Literals) : ℕ := Classical.choose (Classical.choose_spec (stripP_poly l))

theorem stripP_le (l : Literals) (n : ℕ) : stripP l n ≤ stripC l * (n + 1) ^ stripD l :=
  (Classical.choose_spec (Classical.choose_spec (stripP_poly l))).2 n

/-- **The translation's words at a call** (as in `CallSize.word_length_le`). -/
theorem strip_req {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) (req : PrimRequest)
    (h : I.Call req) :
    8 * req.translation.length + 2 * (RepairRepresentation.natListWord req.translation).length + 16 ≤
      8 * req.n + 2 * ((2 * req.n + 3) * (req.n + 1)) + 16 := by
  obtain ⟨_, _, _, _, ⟨htlen, htval⟩, hstar, _⟩ := h
  have hr4 := hstar.2.2.1
  have hl : req.translation.length ≤ req.n := by rw [htlen]; omega
  have h5 : (RepairRepresentation.natListWord req.translation).length ≤ (2 * req.n + 3) * (req.n + 1) := by
    unfold RepairRepresentation.natListWord
    rw [List.length_append]
    have e1 := CallSize.natWord_len_le_self req.translation.length
    have e2 : (req.translation.flatMap RepairRepresentation.natWord).length ≤
        req.translation.length * (2 * req.n + 3) := by
      apply CallSize.flatMap_length_le
      intro t ht
      have g1 := htval t ht
      have g2 : 2 ^ Nat.log 2 (req.n / B.rOf req.n + 1) ≤ req.n / B.rOf req.n + 1 :=
        Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
      have g3 : req.n / B.rOf req.n ≤ req.n := Nat.div_le_self _ _
      have := CallSize.natWord_len_le_self t
      omega
    have e3 := Nat.mul_le_mul_right (2 * req.n + 3) hl
    have e4 : (2 * req.n + 3) * (req.n + 1) = req.n * (2 * req.n + 3) + (2 * req.n + 3) := by ring
    omega
  omega

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The call's codes within `kbT n`** (`thr_hc3`'s `hKb`, `hKc`). -/
theorem kbT_codes (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) :
    (∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ ThrFam.kbT n) ∧
      (∀ c ∈ carriers.map Carrier.code, natBitLength c ≤ ThrFam.kbT n) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hp : CallSize.codeParam 26 26 n = (n + 1) ^ 26 + (n + 1) ^ 26 + n + 4 := rfl
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · unfold ReqBridge.thrCodes at hc
    rcases List.mem_ofFn.mp hc with ⟨i, rfl⟩
    have h := CallSize.code_bits_le .thr (Cs i) (CallSize.codeParam 26 26 n) (by omega)
      (le_trans (hd i) (by omega))
    unfold ThrFam.kbT
    exact le_trans h (Nat.le_add_right _ _)
  · rcases List.mem_map.mp hc with ⟨X, hX, rfl⟩
    have h := CallSize.carrier_bits_le X 26 (CallSize.codeParam 26 26 n) (hcar X hX) (by omega)
    unfold ThrFam.kbT
    exact le_trans h (Nat.le_add_left _ _)

/-- **The strip's premises at a THR call** once the strip polynomial is below `2pr + 2`. -/
theorem strip_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (pr : ℕ) (hpr : stripP l n ≤ 2 * pr + 2) :
    ThrFam.ThrStripAt pr ha' Cs carriers translation (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs) := by
  have hw : (thrReq n a' ha' Cs carriers translation).word.length ≤ CallSize.wordBound 26 26 2 n :=
    CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have hb := hbC_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htr : 8 * translation.length + 2 * (RepairRepresentation.natListWord translation).length + 16 ≤
      8 * n + 2 * ((2 * n + 3) * (n + 1)) + 16 := strip_req _ _ hcall
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  have hLL : Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hL hL
  have hcL : cH l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤ cH l * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left _ hLL
  have hcod : (ReqBridge.thrCodes Cs).length = a' := List.length_ofFn
  have hcar : (carriers.map Carrier.code).length = carriers.length := List.length_map _
  have hbl : ∀ v, natBitLength v ≤ v + 1 := fun v => Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have p2 : 2 ^ (natBitLength a' + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by have := hbl a'; omega)
  have p3 : 2 ^ (natBitLength carriers.length + 1) ≤ 2 ^ 6 :=
    Nat.pow_le_pow_right (by norm_num) (by have := hbl carriers.length; omega)
  have hn := hbl n
  have e64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hwb : 8 * n + 2 * ((2 * n + 3) * (n + 1)) ≤ 10 * ((2 * n + 3) * (n + 1)) := by nlinarith
  unfold stripP at hpr
  unfold ThrFam.ThrStripAt
  rw [hcod, hcar, List.length_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The THR constants -/

/-- `d_Q = cST + 1`. -/
noncomputable def thrDQ (l : Literals) (fe : ℕ) : ℕ := cST l fe + 1
/-- `d_H = coef·4^{deg} + 2`. -/
noncomputable def thrDH (l : Literals) : ℕ := (algL l).coefficient * 4 ^ (algL l).degree + 2
/-- `e_H = 26·deg + 1`. -/
noncomputable def thrEH (l : Literals) : ℕ := 26 * (algL l).degree + 1
/-- `d_P`: the precondition's `d_H d_Q d_D 2^{50+Z}`, `Q' ≤ pr`'s `2(24 + 8e_Q + d_Q)`, the strip's coefficient. -/
noncomputable def thrDP (l : Literals) (fe : ℕ) : ℕ :=
  thrDH l * thrDQ l fe * dDT l fe * 2 ^ (50 + CallIndexR.capZR l) + 2 * (24 + 8 * eQT l fe + thrDQ l fe) + stripC l
/-- `e_P`: the precondition's `e_H + 50 + Z`, the strip's degree. -/
noncomputable def thrEP (l : Literals) : ℕ := thrEH l + 50 + CallIndexR.capZR l + stripD l

/-- **The THR constants** at the endpoint exponent `fe` (fixed before `F`). -/
noncomputable def thrCof (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) : SymC where
  dT := 2 * eNT l fe
  dC := 12 * (2 * eNT l fe)
  dQ := thrDQ l fe
  dH := thrDH l
  eH := thrEH l
  dP := thrDP l fe
  eP := thrEP l
  dA := symDAc (thrEH l) (thrEP l) (thrDH l) (thrDP l fe) (CompetitorCountTable.coefficient wa)
    (CompetitorCrossScheduler.exponent wa)
  dR := 0
  dD := dDT l fe

/-- **The THR load floor** `C_{D,t}` (fixed before `F`). -/
noncomputable def thrCDt (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) : ℕ :=
  occCDT (algL l) (thrCof l wa fe) (A1T l fe) (10 * CallIndex.algX l + 32) +
    16 * thrC1 (eNT l fe) (eQT l fe) (10 * CallIndex.algX l + 32) (dDT l fe) +
    symHC (thrCof l wa fe).dC (cDa (algL l) + cmT l) (thrCof l wa fe).dQ (thrCof l wa fe).dD
      (coOf (A1T l fe + 1392 * (10 * CallIndex.algX l + 32) + cmT l) (thrCof l wa fe).dQ (cDa (algL l)) (thrCof l wa fe).dD) (eNT l fe) (eQT l fe)

/-- The C3 load's coefficient. -/
noncomputable def c3KT (l : Literals) (c : SymC) : ℕ := c.dH + c.dQ + cmT l + c.dP

/-- **The C3 load** (`c3_le` at `freeProg2 (thrK2 c)`, `K3 = c3KT`, `D3 = e_H + e_P`). -/
theorem c3_thr2 (c : SymC) : 1 ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) + ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) +
        ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) + ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) ≤
        c3KT l c * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ (c.eH + c.eP) := by
  intro hCD kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hkL : ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤ ((gate0 l F).budget kclk coef A a ha).psiOf n := by
    unfold TimeBudget.psiOf
    exact kL_le_loadPsi _ _ _ _ _ hCD
  have hm := m_le_thr l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq_thr l F c kclk coef A a ha Cs carriers hs
  have hPH : (n + 1) ^ c.eH ≤ (n + 1) ^ (c.eH + c.eP) := Nat.pow_le_pow_right (by omega) (by omega)
  have hPP : (n + 1) ^ c.eP ≤ (n + 1) ^ (c.eH + c.eP) := Nat.pow_le_pow_right (by omega) (by omega)
  have hP1 : 1 ≤ (n + 1) ^ (c.eH + c.eP) := Nat.one_le_pow _ _ (by omega)
  have e3 : ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) = c.dH * (n + 1) ^ c.eH := rfl
  have e5 : ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) = c.dP * (n + 1) ^ c.eP := rfl
  rw [e3, e5, hQ]
  obtain ⟨M, hMd⟩ : ∃ M, M = ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4) := ⟨_, rfl⟩
  rw [← hMd] at hm ⊢
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ, ψ = ((gate0 l F).budget kclk coef A a ha).psiOf n := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hkL hm ⊢
  rw [← hψd] at hkL ⊢
  obtain ⟨N, hNd⟩ : ∃ N, N = (n + 1) ^ (c.eH + c.eP) := ⟨_, rfl⟩
  rw [← hNd] at hPH hPP hP1 ⊢
  have t1 : c.dH * (n + 1) ^ c.eH ≤ c.dH * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans hPH (Nat.le_mul_of_pos_left _ (by omega)))
  have t2 : c.dP * (n + 1) ^ c.eP ≤ c.dP * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans hPP (Nat.le_mul_of_pos_left _ (by omega)))
  have t3 : c.dQ * (K + L) ≤ c.dQ * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.le_mul_of_pos_right _ hP1))
  have t4 : (16 + 16 * (10 * CallIndex.algX l + 32)) * (K + L) ≤ cmT l * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.le_mul_of_pos_right _ hP1))
  have e : c3KT l c * (ψ + 1) * N = c.dH * ((ψ + 1) * N) + c.dQ * ((ψ + 1) * N) + cmT l * ((ψ + 1) * N) +
      c.dP * ((ψ + 1) * N) := by unfold c3KT; ring
  rw [e]
  omega

/-- **The pad** at `freeProg2 (thrK2 c)` (`Kp = 4^{d_A} + 1`, `Dp = d_A + d_R`). -/
theorem thr_pad (c : SymC) : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      2 ^ ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) ≤
        (4 ^ c.dA + 1) * (2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) * (n + 1) ^ (c.dA + c.dR) +
          2 ^ (n / 2) * 2 ^ ((c.dA + c.dR) * (natBitLength n + 1) ^ 2)) := by
  intro kclk coef A a ha n a' ha' Cs carriers translation _ hs
  have h := pad2 (thrK2 c) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)
  have hk : (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs).kh + (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs).kh = ((gate0 l F).budget kclk coef A a ha).kOf n := by
    rw [← kh_two l F kclk coef A a ha hs]
    show SeedFix.callKh _ + SeedFix.callKh _ = _
    ring
  rw [hk] at h
  exact h

end Gate

/-- **`ThrEAt3` at every THR call** at the THR constants, above the load floor. -/
theorem thr_side (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) (F : GateFree l) (hfe : F.filterErrDeg = fe)
    (hCD : thrCDt l wa fe ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi) : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ThrFam.ThrEAt3 (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
        ((freeProg2 (thrK2 (thrCof l wa fe))).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (thrDF (thrCof l wa fe) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
        (symKn (thrCof l wa fe) n) (symKch l F (thrCof l wa fe) n) F.E := by
  subst hfe
  intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg (thrCof l wa F.filterErrDeg) :=
    ⟨by show 1 ≤ cST l F.filterErrDeg + 1; omega, le_refl _, le_refl _,
      by show _ ≤ _ + _ + _; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _),
      by show _ ≤ _ + _; exact Nat.le_add_right _ _,
      by show _ ≤ _ + _ + _; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _),
      by show 1 ≤ thrEH l + 50 + CallIndexR.capZR l + stripD l; unfold thrEH; omega, le_refl _⟩
  have eCD : thrCDt l wa F.filterErrDeg = occCDT (gate0 l F).alg (thrCof l wa F.filterErrDeg) (A1T l F.filterErrDeg)
      (10 * CallIndex.algX l + 32) + 16 * thrC1 (eNT l F.filterErrDeg) (eQT l F.filterErrDeg)
        (10 * CallIndex.algX l + 32) (dDT l F.filterErrDeg) +
      symHC (thrCof l wa F.filterErrDeg).dC (cDa (gate0 l F).alg + cmT l) (thrCof l wa F.filterErrDeg).dQ
        (thrCof l wa F.filterErrDeg).dD (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l)
          (thrCof l wa F.filterErrDeg).dQ (cDa (gate0 l F).alg) (thrCof l wa F.filterErrDeg).dD)
        (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) := rfl
  rw [eCD] at hCD
  exact thrEAt l F (thrCof l wa F.filterErrDeg) wa F.E hc le_rfl le_rfl le_rfl le_rfl (by omega) (by omega)
    (by omega) hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs

/-- **The strip's premises at every THR call** at the THR constants (`pr = d_P(n+1)^{e_P}`). -/
theorem thr_strip (l : Literals) (wa : WilliamsAlgorithm) (fe : ℕ) (F : GateFree l) :
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ThrFam.ThrStripAt ((freeProg2 (thrK2 (thrCof l wa fe))).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) ha' Cs carriers translation
        (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs) := by
  intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  refine strip_le l F kclk coef A a ha ha' Cs carriers translation hcall hs _ ?_
  have h1 := stripP_le l n
  show _ ≤ 2 * (thrDP l fe * (n + 1) ^ thrEP l) + 2
  have h2 : stripC l ≤ thrDP l fe := by unfold thrDP; omega
  have h3 : (n + 1) ^ stripD l ≤ (n + 1) ^ thrEP l := Nat.pow_le_pow_right (by omega) (by unfold thrEP; omega)
  have h4 : stripC l * (n + 1) ^ stripD l ≤ thrDP l fe * (n + 1) ^ thrEP l := Nat.mul_le_mul h2 h3
  omega

/-- **The THR free numbers at every gate** (v7): `ThrFreeOkB7`. -/
noncomputable def thrFreeOk (l : Literals) (wa : WilliamsAlgorithm) : ThrFam.ThrFreeOkB7 l wa :=
  fun fe => ⟨thrCDt l wa fe, c3KT l (thrCof l wa fe), (thrCof l wa fe).eH + (thrCof l wa fe).eP,
    4 ^ (thrCof l wa fe).dA + 1, (thrCof l wa fe).dA + (thrCof l wa fe).dR, fun F hfe hCD hcpsi =>
    { Fp := freeProg2 (thrK2 (thrCof l wa fe))
      dF := thrDF (thrCof l wa fe)
      K := symKn (thrCof l wa fe)
      Kch := symKch l F (thrCof l wa fe)
      E3 := F.E
      ok_le := fun Ds => by
        obtain ⟨Ko, hKo⟩ := ok2_le (thrK2 (thrCof l wa fe)) Ds
        exact ⟨Ko, fun cap x hx hc => hKo cap x (small_of hx) hc⟩
      cost_le := cost2_le _
      val_le := fun Ds => by
        obtain ⟨Kv, hKv⟩ := val2_le (thrK2 (thrCof l wa fe)) Ds
        exact ⟨Kv, fun x j hx hj => hKv x j (small_of hx) hj⟩
      rho_le := rho2_le _
      pad_le := thr_pad l F (thrCof l wa fe)
      c3_le := c3_thr2 l F (thrCof l wa fe)
      side := thr_side l wa fe F hfe hCD hcpsi
      strip := thr_strip l wa fe F }⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
