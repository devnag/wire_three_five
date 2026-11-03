import Lean
import Proof.Wire_3_5.Primitive.Writers.HashFit1
import Proof.Wire_3_5.Primitive.SeedFix.C4CapF
import Proof.Wire_3_5.Filters.FilterGap
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashFit2Base


noncomputable section
set_option maxRecDepth 4096


/-! # HASH setup (C), fit part 2: the HASH cell's capacity facts at every THR call

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`") and P3:3170-3181 (the seed phase's capacity
`2^{⌊n/8⌋ + C}`): with `q = 2^{E·(B+1)²}` bounding the call's sizes (`CallSz`), the cell's capacity facts `CellFit`
hold at the capacity `2^30·q⁴`, with the digit program's bound `Bm = C·(8q+1)^D` and the digit populations' words
`Sm = 4q³`; `2^30·q⁴ ≤ 2^{(4E+30)(B+1)²} ≤ 2^{⌊n/8⌋ + C}` once `C` is past a threshold fixed by the literals.

* `getD_le`, `num_mem`, `segW_flat_le`, `digL_len`, `digsN_le`; `bmOf`, `smOf`, `capOf`; **`cell_sizes`**;
  **`cellFit_mono`**; `capOf_le`, `bmOf_le`; **`cell_fits`** (`∃ Cc₀, ∀ Cc ≥ Cc₀`, `CellFit` at `2·2^{capExp2 Cc n} + 2`,
  with `Bm` within that capacity).

Paper quantities of the main type: the seed phase's capacity `2^{⌊n/8⌋+C}` (P3:3170-3181). -/

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

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)

/-- **The cell's capacity facts at the unit `q = 2^{E·(B+1)²}`.** -/
theorem cell_sizes (E : ℕ) (hE : CallSz l F kclk coef A a0 ha0 ha Cs carriers translation hs E)
    (hnc : carriers.length ≤ 2) :
    HashCell.CellFit (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr (bmOf (2 ^ (E * C4Cap.bsq n)))
      (smOf (2 ^ (E * C4Cap.bsq n))) (capOf (2 ^ (E * C4Cap.bsq n))) := by
  obtain ⟨hw, hn3, hhn, hsx, htg, hcp, hkh, hnE, hM, hG, hcut, hpops, hpay, hcr⟩ := hE
  have hs1 := C4Cap.bsq_pos n
  have hE1 : 1 ≤ E := by omega
  have hEs : E ≤ E * C4Cap.bsq n := Nat.le_mul_of_pos_right _ hs1
  have hlt : E * C4Cap.bsq n < 2 ^ (E * C4Cap.bsq n) := Nat.lt_two_pow_self
  have hb2 : 2 ^ (natBitLength n + 1) ≤ 2 ^ (E * C4Cap.bsq n) :=
    Nat.pow_le_pow_right (by norm_num) (le_trans (C4Cap.b1_le_bsq n) (Nat.le_mul_of_pos_left _ hE1))
  have hkh2 : 2 * (((callInputs l F kclk coef A a0 ha0).starParams n hs).s * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2)) ≤ E * C4Cap.bsq n := by
    have := hkh; unfold SeedFix.callKh at this; omega
  have hk3 : 2 ^ (2 * (((callInputs l F kclk coef A a0 ha0).starParams n hs).s * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2))) ≤ 2 ^ (E * C4Cap.bsq n) :=
    Nat.pow_le_pow_right (by norm_num) hkh2
  have hk1 : 2 ^ (((callInputs l F kclk coef A a0 ha0).starParams n hs).s * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2)) ≤ 2 ^ (E * C4Cap.bsq n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ (E * C4Cap.bsq n) := ⟨_, rfl⟩
  rw [← hq] at hw hn3 hhn hsx htg hcp hnE hM hG hcut hpops hpay hlt hb2 hk3 hk1 ⊢
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  obtain ⟨q2, hq2⟩ : ∃ x, x = q * q := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ x, x = q2 * q := ⟨_, rfl⟩
  obtain ⟨q4, hq4⟩ : ∃ x, x = q3 * q := ⟨_, rfl⟩
  have l1 : q ≤ q2 := by rw [hq2]; exact Nat.le_mul_of_pos_left q hq1
  have l2 : q2 ≤ q3 := by rw [hq3]; exact Nat.le_mul_of_pos_right q2 hq1
  have l3 : q3 ≤ q4 := by rw [hq4]; exact Nat.le_mul_of_pos_right q3 hq1
  have e3 : q * q * q = q3 := by rw [hq3, hq2]
  have e4 : q * q * q * q = q4 := by rw [hq4, hq3, hq2]
  unfold smOf capOf
  rw [e4, e3]
  have K30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  rw [K30]
  -- the call's numbers
  have hnG : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).nG ≤ q :=
    hhn _ (num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 0)
  have hdig : thrDigits ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) ≤ q :=
    hhn _ (num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 5)
  have hdig' : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).dig ≤ q := hdig
  have h13 := getD_le hhn 13
  have hee : thrCallE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers ≤ q := by rw [← HashCall.hashNums_ee]; exact h13
  have hac : (carriers.length + 1) * 4096 * ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ 12288 * q := by
    calc (carriers.length + 1) * 4096 * ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ 3 * 4096 * q :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hcp
      _ = 12288 * q := by ring
  have hsb : 2 ^ (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).seedBits ≤ q := by
    rw [← Filters.card_gapSeed]; exact hnE
  have hmem : ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ++
      (carriers.map List.length ++ [(PrimT.ThrTab.tupleG Cs).length]), v ≤ q := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hhn v h
    · rcases List.mem_append.mp h with h' | h'
      · exact le_trans (List.le_sum_of_mem h') hsx
      · rw [List.mem_singleton] at h'; rw [h']; exact htg
  refine
    { c1 := ?c1, c2 := ?c2, c3 := ?c3, cl := ?cl, cs := ?cs, cD1 := ?cD1, cG1 := ?cG1, cG2 := ?cG2, cG3 := ?cG3,
      cG4 := ?cG4, cG5 := ?cG5, cD3 := ?cD3, ckh := ?ckh, cB := ?cB, cneed := ?cneed, cBm := ?cBm, cSm := ?cSm,
      cn := ?cn, cc := ?cc, cP := ?cP, cG := ?cG }
  case c1 =>
    show 2 * (thrReq n a ha Cs carriers translation).word.length + 2 ≤ _
    omega
  case c2 => omega
  case c3 => omega
  case cl => exact fun k => le_trans (getD_le hmem k) (by omega)
  case cs => omega
  case cD1 => omega
  case cG1 => rw [HashCall.auxP_cap]; omega
  case cG2 => rw [HashCall.auxP_len]; omega
  case cG3 => rw [HashCall.auxP_err]; omega
  case cG4 => rw [pow_succ]; omega
  case cG5 =>
    have h1 : (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).labelBits + (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).fieldBits +
        (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).walkLen ≤ (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).seedBits + 1 := by
      unfold Filters.GapParams.seedBits; omega
    have h2 : (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).seedBits < 2 ^ (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).seedBits :=
      Nat.lt_two_pow_self
    omega
  case cD3 =>
    have hp : 2 ^ (WriterIface.auxP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).seedBits * 2 ^ (2 * (((callInputs l F kclk coef A a0 ha0).starParams n hs).s * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2))) ≤ q2 := by
      rw [hq2]; exact Nat.mul_le_mul hsb hk3
    rw [pow_succ]
    omega
  case ckh => rw [pow_succ]; omega
  case cB =>
    rw [HashCell.bs_eq, HashCall.auxP_len, HashCall.auxP_cap]
    have hB : a * (4096 * ((carriers.length + 1) * 4096 * ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap)) ≤
        4 * (4096 * (12288 * q)) := Nat.mul_le_mul ha (Nat.mul_le_mul_left _ hac)
    omega
  case cneed =>
    intro pr
    have hN := digsN_le ((callInputs l F kclk coef A a0 ha0).starParams n hs) ha Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) pr.val q hpay
      (le_trans (SupplierPrime.mem_primesUpTo.mp pr.2).2 hcut) hdig hsx
    rw [need_eq]
    have h4 : (FinalPass.Digs.digsN ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) pr.val + 1) ^ 4 ≤ (9 * q) ^ 4 :=
      Nat.pow_le_pow_left (by omega) 4
    have e : (9 * q) ^ 4 = 6561 * q4 := by rw [hq4, hq3, hq2]; ring
    omega
  case cBm =>
    intro pr
    have hN := digsN_le ((callInputs l F kclk coef A a0 ha0).starParams n hs) ha Cs carriers (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) pr.val q hpay
      (le_trans (SupplierPrime.mem_primesUpTo.mp pr.2).2 hcut) hdig hsx
    unfold bmOf
    exact le_trans (FinalPass.DigsBody.digsWImpl.bound_le _)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  case cSm =>
    intro g pr
    refine le_trans (digL_len (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers g pr) ?_
    have hMG : (thrOccs ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs).length * ((Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers).length + 2) ≤ q * (q + 2) :=
      Nat.mul_le_mul hM (by omega)
    have e1 : q * (q + 2) = q2 + 2 * q := by rw [hq2]; ring
    have hX : thrDigits ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) *
        ((thrOccs ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs).length * ((Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers).length + 2) + 1) ≤ q * (4 * q2) :=
      Nat.mul_le_mul hdig (by omega)
    have e2 : q * (4 * q2) = 4 * q3 := by rw [hq3]; ring
    omega
  case cn => omega
  case cc => omega
  case cP =>
    have h := FinalPass.ThrSz.primesWord_le (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))
    have h' : (PrimAsm.Data.unaryList (HashPops.hPrimes (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)).length ≤
        (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) + 1) * (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) + 1) := h
    have hc : (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) + 1) * (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) + 1) ≤
        (q + 1) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
    have e : (q + 1) * (q + 1) = q2 + 2 * q + 1 := by rw [hq2]; ring
    omega
  case cG => rw [HashCell.hng_eq (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers]; omega

end Call

/-- **The cell's capacity facts at every THR call** of the gate, at the seed phase's capacity `2^{⌊n/8⌋ + Cc}`
(`W = 2^{capExp2 Cc n}`, cell capacity `2W + 2`) for every `Cc` past a threshold fixed by the literals and the gate,
with the digit program's bound `Bm` within the cell's capacity. -/
theorem cell_fits (l : Literals) (F : GateFree l) : ∃ Cc0 : ℕ, ∀ Cc : ℕ, Cc0 ≤ Cc →
    ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n, ∃ Bm Sm : ℕ,
        HashCell.CellFit (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr Bm Sm
          (2 * 2 ^ C4Cap.capExp2 Cc n + 2) ∧ Bm ≤ 2 * 2 ^ C4Cap.capExp2 Cc n + 2 := by
  obtain ⟨E, hE⟩ := call_sizes l F
  obtain ⟨K0, hK0⟩ := C4Cap.mul_sq_le_div16 (4 * E + 30)
  obtain ⟨K1, hK1⟩ := C4Cap.mul_sq_le_div16 (E * FinalPass.DigsBody.digsWImpl.D)
  obtain ⟨c0, hc0⟩ : ∃ c, c = Nat.clog 2 (FinalPass.DigsBody.digsWImpl.C * 9 ^ FinalPass.DigsBody.digsWImpl.D) :=
    ⟨_, rfl⟩
  refine ⟨K0 + (c0 + K1), fun Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs => ?_⟩
  obtain ⟨hk2, -, -⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  refine ⟨bmOf (2 ^ (E * C4Cap.bsq n)), smOf (2 ^ (E * C4Cap.bsq n)), cellFit_mono _ _ hs ha Cs carriers translation F.cr
    _ _ (capOf (2 ^ (E * C4Cap.bsq n))) _
    (cell_sizes l F kclk coef A a0 ha0 ha Cs carriers translation hs E
      (hE kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs) hk2) ?_, ?_⟩
  · have h1 := capOf_le E (C4Cap.bsq n) (C4Cap.bsq_pos n)
    have h2 : (4 * E + 30) * C4Cap.bsq n ≤ C4Cap.capExp2 Cc n := by
      have := hK0 n
      unfold C4Cap.bsq C4Cap.capExp2
      omega
    have h3 : 2 ^ ((4 * E + 30) * C4Cap.bsq n) ≤ 2 ^ C4Cap.capExp2 Cc n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  · have h1 := bmOf_le E (C4Cap.bsq n)
    have h2 : FinalPass.DigsBody.digsWImpl.C * 9 ^ FinalPass.DigsBody.digsWImpl.D ≤ 2 ^ c0 := by
      rw [hc0]; exact Nat.le_pow_clog (by norm_num) _
    have h3 : 2 ^ ((E * FinalPass.DigsBody.digsWImpl.D) * C4Cap.bsq n) ≤ 2 ^ (n / 16 + K1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := hK1 n
      unfold C4Cap.bsq
      exact this
    have h4 : 2 ^ c0 * 2 ^ (n / 16 + K1) ≤ 2 ^ C4Cap.capExp2 Cc n := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      unfold C4Cap.capExp2
      omega
    have h5 := Nat.mul_le_mul h2 h3
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.HashFit

end
