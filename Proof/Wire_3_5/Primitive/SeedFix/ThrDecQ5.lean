import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ4
import Proof.Wire_3_5.UnionMachine.ThrUnitMeas
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Primitive.SeedFix.W6L
import Proof.Wire_3_5.Primitive.SeedFix.GeoPackBase
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrBBase
import Proof.Wire_3_5.FinalPass.SymSz1
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide2
import Proof.Wire_3_5.Primitive.Writers.ThrSide3
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 THR decode front, packaging part 5: the call's atom bounds

At a THR call of the gate (`Call`, `StarAt n`), with `L = ⌈log₂(n+2)⌉`, `Y = L²`: every register value of the front is
at most `Q_F·2^{A·Y}` (`Atoms`): the request `|thrCallW| ≤ 2^{K_R Y + 3}` (the `ThrMeas.word_le`), the THR numbers
`≤ K_t(F)·(n+1)^{D_t}` (`W6.thrNumsPoly` at the cap's degree `48 + Z`, `ThrSide.capT_le2`), the carriers' sizes and the
tuple's gates `≤ 8(n+1)^{26}`, the THR filter's seed length `≤ 6000(80 + Z + f_e)·Y` (`Filters.seedBits_le`), `2k_h = k ≤
L²` (`SymFr.kh_two`, `k_le_L2`), `c_r ≤ k/4`, the numbers machine's need constants. The exponent `A = A(l, f_e)` is
fixed before the gate; `Q_F = K_t(F) + 1` after it.

* `capD`, `capC`, `dT`, `kT`, `NW`, `TW`, `aE`, `qF`; **`call_atoms`**.

Paper quantity of the main type: the THR call's sizes within `2^{O(L²)}` (P3:2543-2558, 2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine

/-- The THR cap's degree `48 + Z` and coefficient `4^{48+Z}` (both from `l`). -/
noncomputable def capD (l : Literals) : ℕ := 48 + CallIndexR.capZR l
noncomputable def capC (l : Literals) : ℕ := 4 ^ capD l

/-- The THR numbers' degree (from `l`) and coefficient (from `F`). -/
noncomputable def dT (l : Literals) : ℕ := Classical.choose (PrimT.W6.thrNumsPoly l (capD l))
noncomputable def kT (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (PrimT.W6.thrNumsPoly l (capD l)) (capC l) F)

/-- The docked machines (from `l`): W6 at the call's `D = 1`, the THR front end. -/
noncomputable def NW (l : Literals) : PrimThrW.Nums4.NumsPort4 (PrimT.W6.litAlg l) 1 :=
  PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1
noncomputable def TW (l : Literals) : PrimThrW.PortsE.TopFrontPort3 (PrimT.W6.litAlg l) :=
  PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)

/-- The atoms' exponent (from `l` and `f_e`). -/
noncomputable def aE (l : Literals) (fe : ℕ) : ℕ :=
  ThrMeas.KR l + 6000 * (80 + CallIndexR.capZR l + fe) + dT l + (NW l).Cn + (NW l).Dn + fe + 64

/-- The atoms' coefficient (from `F`). -/
noncomputable def qF (l : Literals) (F : GateFree l) : ℕ := kT l F + 1

theorem capT_poly (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ capC l * (n + 1) ^ capD l := by
  have h := ThrSide.capT_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL : 2 ^ Nat.clog 2 (n + 2) ≤ 2 * (n + 2) := two_pow_clog_le n
  have e1 : 2 ^ ((48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) = (2 ^ Nat.clog 2 (n + 2)) ^ capD l := by
    rw [← pow_mul, Nat.mul_comm]; rfl
  have b : 2 ^ Nat.clog 2 (n + 2) ≤ 4 * (n + 1) := by omega
  calc ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ 2 ^ ((48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := h
    _ = (2 ^ Nat.clog 2 (n + 2)) ^ capD l := e1
    _ ≤ (4 * (n + 1)) ^ capD l := Nat.pow_le_pow_left b _
    _ = capC l * (n + 1) ^ capD l := by rw [mul_pow]; rfl

theorem aE_ge (l : Literals) (fe : ℕ) :
    ThrMeas.KR l + 64 ≤ aE l fe ∧ 6000 * (80 + CallIndexR.capZR l + fe) + 64 ≤ aE l fe ∧ dT l + 1 ≤ aE l fe ∧
      (NW l).Cn ≤ aE l fe ∧ (NW l).Dn ≤ aE l fe ∧ fe + 64 ≤ aE l fe ∧ 8 ≤ aE l fe := by
  unfold aE; omega

section Nums

end Nums

section Star
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n)

theorem lfw_le : ((callInputs l F kclk coef A a ha).filterParams .thr n).labelBits +
    ((callInputs l F kclk coef A a ha).filterParams .thr n).fieldBits +
    ((callInputs l F kclk coef A a ha).filterParams .thr n).walkLen ≤
      ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits + 1 := by
  rw [GapNums.seedBits_eq, GapNums.sbOf_eq]; omega

theorem kh_le : 2 * (((callInputs l F kclk coef A a ha).starParams n hs).s *
    (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) ≤ Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := by
  have h1 := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  have h2 := FinalPass.SymFr.k_le_L2 l F kclk coef A a ha hs
  rw [pow_two] at h2
  unfold SeedFix.callKh at h1
  omega

include hs in
theorem cr_le : F.cr ≤ Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) := by
  have h1 := FinalPass.SymFr.cr_le_k l F kclk coef A a ha hs
  have h2 := FinalPass.SymFr.k_le_L2 l F kclk coef A a ha hs
  rw [pow_two] at h2
  omega

end Star

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

/-- The THR numbers below `Q_F·2^{d_T·Y}`. -/
theorem hs_le : ∀ k, (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
    (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD k 0 ≤
      QY (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 1 (dT l) := by
  intro k
  have hmem : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
      v ≤ kT l F * (n + 1) ^ dT l :=
    Classical.choose_spec (Classical.choose_spec (PrimT.W6.thrNumsPoly l (capD l)) (capC l) F) kclk coef A a ha n
      hs Cs carriers _ ha' hcall.2.2.2.1 hcall.2.2.1 (capT_poly l F kclk coef A a ha ha' Cs carriers translation hcall hs)
  have hv : (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).getD k 0 ≤
      kT l F * (n + 1) ^ dT l := by
    rcases Nat.lt_or_ge k (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).length
      with hk | hk
    · rw [List.getD_eq_getElem _ _ hk]; exact hmem _ (List.getElem_mem hk)
    · rw [List.getD_eq_default _ _ hk]; exact Nat.zero_le _
  have hp := pow_le_L n (dT l)
  have hY := L_le_Y n
  unfold QY qF
  calc _ ≤ kT l F * (n + 1) ^ dT l := hv
    _ ≤ (kT l F + 1) ^ 1 * 2 ^ (dT l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
      rw [pow_one]
      exact Nat.mul_le_mul (by omega) (hp.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hY)))

/-- The carriers' sizes and the tuple's gates below `8(n+1)^{26}`. -/
theorem xs_le : ∀ k, ((carriers.map List.length) ++ [(PrimT.ThrTab.tupleG Cs).length]).getD k 0 ≤ 8 * (n + 1) ^ 26 := by
  have hpool := ThrSide.thrPool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [RadBnd.thrPool_length, Records.thrOff_eq] at hpool
  have htg := PrimT.C4GateSym.tupleG_len_le Cs ((n + 1) ^ 26) hcall.2.2.1
  have htg4 : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * (n + 1) ^ 26 := htg.trans (Nat.mul_le_mul_right _ ha')
  have hS : 2 * (carriers.map List.length).sum ≤ 8 * (n + 1) ^ 26 := (Nat.le_add_right _ _).trans hpool
  intro k
  rcases Nat.lt_or_ge k (carriers.map List.length).length with hk | hk
  · rw [List.getD_append _ _ _ _ hk]
    have := getD_le_sum (carriers.map List.length) k
    omega
  · rw [List.getD_append_right _ _ _ _ hk]
    rw [List.length_map] at hk ⊢
    rcases Nat.eq_zero_or_pos (k - carriers.length) with h0 | h0
    · rw [h0]; simp; omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

theorem sbT_le : ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits + 64 ≤
    aE l F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by
  have hcap := ThrSide.capT_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have h := Filters.seedBits_le ((callInputs l F kclk coef A a ha).filterParams .thr n)
  have hL1 := FinalPass.SymFr.one_le_L n
  have hn := FinalPass.SymFr.n2_le_L n
  have hlen : Nat.clog 2 (((callInputs l F kclk coef A a ha).filterParams .thr n).len + 1) ≤
      26 * Nat.clog 2 (n + 2) + 2 := by
    show Nat.clog 2 (2 * (n + 1) ^ 26 + 1) ≤ _
    apply Nat.clog_le_of_le_pow
    have a1 := pow_le_L n 26
    rw [pow_add]; have := Nat.one_le_two_pow (n := 26 * Nat.clog 2 (n + 2)); omega
  have hcp : Nat.clog 2 (((callInputs l F kclk coef A a ha).filterParams .thr n).cap + 1) ≤
      (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2) + 1 := by
    apply Nat.clog_le_of_le_pow
    have : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤
        2 ^ ((48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := hcap
    rw [pow_add]; have := Nat.one_le_two_pow (n := (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)); omega
  have herr : ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp = F.filterErrDeg * Nat.clog 2 (n + 2) := rfl
  rw [herr] at h
  have k := sbT_core F.filterErrDeg (CallIndexR.capZR l) (Nat.clog 2 (n + 2)) _ _ _ hL1 hlen hcp h
  have hA := (aE_ge l F.filterErrDeg).2.1
  exact k.trans (Nat.mul_le_mul_right _ hA)

/-- The request word at the call (the data stage's fields, the framed hash bits as the tail). -/
theorem aw_le : (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
    (RepairRepresentation.natListWord translation ++
      ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length ≤
      QY (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 0 (aE l F.filterErrDeg) := by
  rw [ReqBridge.reqW_thrReq ha']
  have h := ThrMeas.word_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hL1 := FinalPass.SymFr.one_le_L n
  have hY := Y_ge n
  have hE := (aE_ge l F.filterErrDeg).1
  have k1 : (ThrMeas.KR l + 64) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤
      aE l F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := Nat.mul_le_mul_right _ hE
  have k2 : (ThrMeas.KR l + 64) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) =
      ThrMeas.KR l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 64 * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by
    ring
  exact qy0_of (by unfold qF; omega) h (by omega)

/-- The primes list's unary word below `Q_F·2^{(d_T+1)Y}`. -/
theorem aL_le : (Data.unaryList (PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals
    ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1 (carriers.map List.length).length
    ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).cut)).length ≤
      QY (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) 1 (aE l F.filterErrDeg) := by
  rw [SymDec.unaryList_length_le, PrimT.W6.primesList_sum, PrimT.W6.primesList_length]
  have h5 := hs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs 5
  have h6 := hs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs 6
  rw [hashNums_get5] at h5
  rw [hashNums_get6] at h6
  have hY := Y_ge n
  have k := qy_add hY h6 h5
  exact qy_mono (by unfold qF; omega) k le_rfl (aE_ge l F.filterErrDeg).2.2.1

/-- **The call's atom bounds** at `Q_F = K_t(F)+1`, `Y = L²`, `A = aE l f_e`. -/
theorem call_atoms : Atoms (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (aE l F.filterErrDeg)
    (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)) n
    (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
    (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length
    F.cr F.filterErrDeg
    (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap)
    (carriers.map List.length) (PrimT.ThrTab.tupleG Cs).length ((callInputs l F kclk coef A a ha).filterParams .thr n)
    (((callInputs l F kclk coef A a ha).starParams n hs).s * (((callInputs l F kclk coef A a ha).starParams n hs).r / 2))
    (PrimThrW.Joins.primesList (PrimThrW.Joins.thrNumVals
      ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1 (carriers.map List.length).length
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).cut)
    (NW l).Cn (NW l).Dn := by
  have hQ : 1 ≤ qF l F := by unfold qF; omega
  have hY := Y_ge n
  have hL1 := FinalPass.SymFr.one_le_L n
  have hLY := L_le_Y n
  obtain ⟨eK, eS, eT, eC, eD, eF, e8⟩ := aE_ge l F.filterErrDeg
  obtain ⟨n1, n2, n3, n4⟩ := n_atoms (qF l F) (aE l F.filterErrDeg) n hQ (by omega)
  have hEY : aE l F.filterErrDeg ≤ aE l F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) :=
    Nat.le_mul_of_pos_right _ hY
  have hfY : F.filterErrDeg * Nat.clog 2 (n + 2) ≤ F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) :=
    Nat.mul_le_mul_left _ hLY
  have hFE : (F.filterErrDeg + 64) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤
      aE l F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := Nat.mul_le_mul_right _ eF
  have eFE : (F.filterErrDeg + 64) * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) =
      F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) + 64 * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) := by
    ring
  have hsb := sbT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hlfw := lfw_le l F kclk coef A a ha (n := n)
  have hkh := kh_le l F kclk coef A a ha hs
  have hcr := cr_le l F kclk coef A a ha hs
  have hxs := xs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hhs := hs_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hsbp : ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits + 513 ≤
      2 ^ (((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits + 10) := by
    have := x_le_two_pow ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits
    have := Nat.one_le_two_pow (n := ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits)
    rw [pow_add]; omega
  exact {
    hQ := hQ
    hY := hY
    hA := e8
    aw := aw_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    an := n1
    an26 := n2
    acodes := by unfold ReqBridge.thrCodes; rw [List.length_ofFn]; exact ha'
    acc := by rw [List.length_map]; exact hk2
    aKb := le_rfl
    acr := qy0_of hQ (x_le_two_pow F.cr) (by omega)
    afe := qy0_of hQ (x_le_two_pow _) (by omega)
    afeL := qy0_of hQ (x_le_two_pow _) (by omega)
    ahsl := ThrData.hashNums_length _ _ _ _ _ _
    ahs := fun k => qy_mono hQ (hhs k) le_rfl (by omega)
    axsl := by rw [List.length_map]; exact hk2
    axs := fun k => (hxs k).trans n3
    acap := rfl
    alen := n4
    aerr := qy0_of hQ (x_le_two_pow _) (by show F.filterErrDeg * Nat.clog 2 (n + 2) + 4 ≤ _; omega)
    asb := by omega
    alfw := qy0_of hQ (e := ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits + 10) (by omega) (by omega)
    akh := by omega
    aCn := qy0_of hQ (x_le_two_pow _) (by omega)
    aDn := eD
    aL := aL_le l F kclk coef A a ha ha' Cs carriers translation hcall hs }

end Call

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF

end
