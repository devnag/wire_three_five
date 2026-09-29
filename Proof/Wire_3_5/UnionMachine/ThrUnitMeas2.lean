import Proof.Wire_3_5.UnionMachine.ThrUnitMeas

/-! # The THR unit's measure absorbed by `Ψ_T`, part 2: the FILTER setup's arguments and the data counts

At a THR call (`L = ⌈log₂(n+2)⌉`): the FILTER setup's arguments at every carrier row and star row (the THR filter's
length `2(n+1)^{26}`, cap `B_T ≤ 2^{(48+Z)L}`, error `f_e·L`, the slice and its offset within the pool, `4·row`, the
pool, the seeds `2^{seedBits}`, filt:gap P3:2019-2030) are `2^{K_F·L²}` uniformly in the gate (**`fArgs_le`**); the
data tape's counts (the sixteen THR numbers, `ThrNumsPoly`, and the carriers' and the tuple's sizes) are
`≤ (16K_t + 32)·2^{(D_t+26)L}` (**`u_le`**; `K_t` after the gate, `D_t` before).

Paper quantity: the THR unit's FILTER rows and data word, within `2^{O(Ψ_T)}` (P3:3094-3108). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

theorem sliceOff_succ {α : Type} (ls : List (List α)) (j : ℕ) :
    Records.sliceOff ls (j + 1) = Records.sliceOff ls j + (ls.getD j []).length := by
  unfold Records.sliceOff
  rw [List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD]
  cases ls[j]? <;> simp

theorem sliceOff_mono {α : Type} (ls : List (List α)) {j k : ℕ} (h : j ≤ k) :
    Records.sliceOff ls j ≤ Records.sliceOff ls k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [sliceOff_succ]; omega

/-- **The FILTER setup's constant** (from `l` and `f_e`). -/
noncomputable def KF (l : Literals) (fe : ℕ) : ℕ := 6000 * (200 + CallIndexR.capZR l + fe) + 200

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
  (hs : (callInputs l F kclk coef A a ha).StarAt n)
include hcall hs

/-- A carrier row's slice and its offset lie within the pool. -/
theorem slice_le (jr : ℕ) (hjr : jr < carriers.length) :
    Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) jr + ((Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).getD jr []).length ≤ (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length := by
  rw [← sliceOff_succ]
  have h1 := sliceOff_mono (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) (show jr + 1 ≤ carriers.length by omega)
  have h2 : Records.thrOff ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers = Records.sliceOff (Records.thrSlices ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) carriers.length := rfl
  rw [RadBnd.thrPool_length]
  omega

/-- **The FILTER setup's arguments** at a carrier row and a star row. -/
theorem fArgs_le (jr row : ℕ) (hjr : jr < carriers.length) (hrow : row < ThrDec.thrN2 l F kclk coef A a ha hs) :
    ThrUnitRun.fArgs kclk coef A a ha n hs a' Cs carriers jr row ≤ 2 ^ (KF l F.filterErrDeg * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2))) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLd ▸ one_le_L n
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL1
  have hG := pool_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hsl := slice_le l F kclk coef A a ha ha' Cs carriers translation hcall hs jr hjr
  have hN2 := row_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hcap := ThrSide.capT_le2 l F kclk coef A a ha ha' Cs carriers translation hcall hs
  rw [← hLd] at hG hN2 hcap ⊢
  obtain ⟨Z, hZ⟩ : ∃ z, z = CallIndexR.capZR l := ⟨_, rfl⟩
  obtain ⟨fe, hfe⟩ : ∃ f, f = F.filterErrDeg := ⟨_, rfl⟩
  rw [← hZ] at hcap
  have hlen : ((callInputs l F kclk coef A a ha).filterParams .thr n).len = 2 * (n + 1) ^ 26 := rfl
  have herr : ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp = fe * L := by rw [hfe, hLd]; rfl
  have hcp : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap = ((gate0 l F).budget kclk coef A a ha).capOf .thr n := rfl
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * L) := by
    have := pow_N_le n 26; rw [← hLd] at this
    exact (Nat.pow_le_pow_left (by omega) 26).trans this
  have hlen2 : ((callInputs l F kclk coef A a ha).filterParams .thr n).len + 1 ≤ 2 ^ (26 * L + 2) := by
    have e : 2 ^ (26 * L + 2) = 4 * 2 ^ (26 * L) := by ring
    have : 1 ≤ 2 ^ (26 * L) := Nat.one_le_two_pow
    omega
  have hcap2 : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap + 1 ≤ 2 ^ ((48 + Z) * L + 1) := by
    have e : 2 ^ ((48 + Z) * L + 1) = 2 * 2 ^ ((48 + Z) * L) := by ring
    have : 1 ≤ 2 ^ ((48 + Z) * L) := Nat.one_le_two_pow
    omega
  have hc1 := Nat.clog_le_of_le_pow hlen2
  have hc2 := Nat.clog_le_of_le_pow hcap2
  have hsb := Filters.seedBits_le ((callInputs l F kclk coef A a ha).filterParams .thr n)
  have hcard := Filters.card_gapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n)
  obtain ⟨Y, hYd⟩ : ∃ y, y = L * L := ⟨_, rfl⟩
  rw [← hYd] at hLY hN2 ⊢
  have mZ : (48 + Z) * L ≤ (48 + Z) * Y := Nat.mul_le_mul_left _ hLY
  have mf : fe * L ≤ fe * Y := Nat.mul_le_mul_left _ hLY
  obtain ⟨E, hE⟩ : ∃ e, e = 6000 * (78 + Z + fe) * Y := ⟨_, rfl⟩
  have eE : 6000 * (78 + Z + fe) * Y = 468000 * Y + 6000 * (Z * Y) + 6000 * (fe * Y) := by ring
  have e48 : (48 + Z) * Y = 48 * Y + Z * Y := by ring
  have hsbE : ((callInputs l F kclk coef A a ha).filterParams .thr n).seedBits ≤ E := by rw [herr] at hsb; omega
  have t1 : ((callInputs l F kclk coef A a ha).filterParams .thr n).len ≤ 2 ^ E := (by omega : ((callInputs l F kclk coef A a ha).filterParams .thr n).len ≤ 2 ^ (26 * L + 2)).trans (two_pow_mono (by omega))
  have t2 : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ 2 ^ E := (by omega : ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤ 2 ^ ((48 + Z) * L + 1)).trans (two_pow_mono (by omega))
  have t3 : ((callInputs l F kclk coef A a ha).filterParams .thr n).errExp ≤ 2 ^ E := by
    rw [herr]; exact (le_two_pow_self _).trans (two_pow_mono (by omega))
  have t4 : 4 * row ≤ 2 ^ E := by
    have e : 2 ^ (8 * Y + 2) = 4 * 2 ^ (8 * Y) := by ring
    exact (by omega : 4 * row ≤ 2 ^ (8 * Y + 2)).trans (two_pow_mono (by omega))
  have t5 : (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers).length ≤ 2 ^ E := hG.trans (two_pow_mono (by omega))
  have t6 : Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n)) ≤ 2 ^ E := by rw [hcard]; exact two_pow_mono hsbE
  have hKF : E + 3 ≤ KF l F.filterErrDeg * Y := by
    rw [← hfe, hE]; unfold KF; rw [← hZ]
    have e2 : (6000 * (200 + Z + fe) + 200) * Y = 1200200 * Y + 6000 * (Z * Y) + 6000 * (fe * Y) := by ring
    have : 1 ≤ Y := by omega
    omega
  have e8 : 2 ^ (E + 3) = 8 * 2 ^ E := by ring
  have hfin : 2 ^ (E + 3) ≤ 2 ^ (KF l F.filterErrDeg * Y) := two_pow_mono hKF
  unfold ThrUnitRun.fArgs
  omega

/-- **The data tape's counts** from the THR numbers' polynomial bound. -/
theorem u_le (Kt Dt : ℕ)
    (hKt : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap,
      v ≤ Kt * (n + 1) ^ Dt) :
    (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers).length ≤ (16 * Kt + 32) * 2 ^ ((Dt + 26) * Nat.clog 2 (n + 2)) := by
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hLd]
  have hN : 1 ≤ n + 1 := by omega
  have hP : (n + 1) ^ (Dt + 26) ≤ 2 ^ ((Dt + 26) * L) := by
    have := pow_N_le n (Dt + 26); rw [← hLd] at this
    exact (Nat.pow_le_pow_left (by omega) _).trans this
  have hDt : (n + 1) ^ Dt ≤ (n + 1) ^ (Dt + 26) := Nat.pow_le_pow_right hN (by omega)
  have h26 : (n + 1) ^ 26 ≤ (n + 1) ^ (Dt + 26) := Nat.pow_le_pow_right hN (by omega)
  have h1 : 1 ≤ (n + 1) ^ (Dt + 26) := Nat.one_le_pow _ _ hN
  obtain ⟨Q, hQ⟩ : ∃ q, q = (n + 1) ^ (Dt + 26) := ⟨_, rfl⟩
  rw [← hQ] at hP hDt h26 h1
  have hnum : ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).map
      (· + 1)).sum ≤ 16 * (Kt * Q + 1) := by
    have := List.sum_le_card_nsmul ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      ((callInputs l F kclk coef A a ha).filterParams .thr n).cap).map (· + 1)) (Kt * Q + 1) (fun x hx => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        have := hKt v hv
        have : Kt * (n + 1) ^ Dt ≤ Kt * Q := Nat.mul_le_mul_left _ hDt
        omega)
    rw [List.length_map, ThrData.hashNums_length, smul_eq_mul] at this
    exact this
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have henv : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hcar : ((carriers.map (·.length)).map (· + 1)).sum ≤ 2 * (Q + 1) := by
    have := List.sum_le_card_nsmul ((carriers.map (·.length)).map (· + 1)) (Q + 1) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hy
      have := (henv X hX).1
      omega)
    rw [List.length_map, List.length_map, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hnc)
  have hM := ThrSide.occ_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htup : (PrimT.ThrTab.tupleG Cs).length ≤ 4 * Q := by
    have e : (thrOccs ((callInputs l F kclk coef A a ha).starParams n hs) Cs).length = (PrimT.ThrTab.tupleG Cs).length := by
      rw [← List.length_map (f := fun o => o.gate), PrimT.ThrTab.thrOccs_gates]; rfl
    omega
  unfold ThrDec.thrCallU ThrData.thrCounts
  rw [FinalPass.ThrPt.unaryList_length, List.map_append, List.sum_append, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hQ2 : (16 * Kt + 32) * Q ≤ (16 * Kt + 32) * 2 ^ ((Dt + 26) * L) := Nat.mul_le_mul_left _ hP
  have e : (16 * Kt + 32) * Q = 16 * (Kt * Q) + 32 * Q := by ring
  omega

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
