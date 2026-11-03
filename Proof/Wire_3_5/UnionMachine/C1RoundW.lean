import Proof.Wire_3_5.UnionMachine.GateConv
import Proof.Wire_3_5.UnionMachine.C1Cnt
import Proof.Wire_3_5.UnionMachine.C1Rat
import Proof.Wire_3_5.FinalPass.LiftR
import Proof.Wire_3_5.Primitive.Writers.SymDecStreams

/-! # C6 front, the C1 dock: one variable's round, the register program (P3:1326-1330, 3395-3399, 3673)

C1's request lists the positive-weight variables' carriers' gates and, per such variable, its gate indices and weight
(`FrontSelReq.selReqOf`, `Plan.selWord`). One round handles variable `X` (`X = |XS|`): the carrier table's region
`accHdr ++ tabSeg C` (`C` the carrier's gates) on stream `0`, the PCPP output word on `2`, and the running outputs.
* the count `c_X` (`C1Cnt.cntW`); if `c_X > 0`: the gates in C1's format (`GateConv.gconv`, lifted,
  `FinalPass.WExec.liftW`), the population's index list (`C1Rng.rangeW`) and weight `c_X/2^{cb+1}` (`C1Rat.ratW`),
  the running gate total and the positive count advanced;
* **`roundW_spec`**: every register back at `0`, the streams as above.

Layout `WState 7 64`: streams `0` REGN, `1` G, `2` PO, `3` XS, `4` POPS, `5` GT, `6` NP, `7` QS; registers `0 … 15`
GateConv's, `16 … 35` the count's `W`, `36 … 43` the writer's `R`, `44 … 53` the weight's `Z`, `54 … 57` the index
list's `K T S LEN`, `58` a temporary.

Paper quantity of the main type: one weighted carrier of `star:selection`'s request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1RoundW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-! ## The layout -/

abbrev RS := WState 7 64

def Wm : Fin 20 ↪ Fin 64 := ⟨fun i => ⟨16 + i.val, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩
def Rm : Fin 8 ↪ Fin 64 := ⟨fun i => ⟨36 + i.val, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩
def Zm : Fin 10 ↪ Fin 64 := ⟨fun i => ⟨44 + i.val, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩

abbrev rK : Fin 64 := 54
abbrev rT : Fin 64 := 55
abbrev rS : Fin 64 := 56
abbrev rLEN : Fin 64 := 57
abbrev rTT : Fin 64 := 58

@[simp] theorem Wm_val (i : Fin 20) : (Wm i).val = 16 + i.val := rfl
@[simp] theorem Rm_val (i : Fin 8) : (Rm i).val = 36 + i.val := rfl
@[simp] theorem Zm_val (i : Fin 10) : (Zm i).val = 44 + i.val := rfl

/-- GateConv's streams and registers. -/
def fsG : Fin 2 → Fin 8 := Fin.castLE (by decide)
def frG : Fin 16 → Fin 64 := Fin.castLE (by decide)

theorem fsG_inj : Function.Injective fsG := Fin.castLE_injective _
@[simp] theorem fsG_zero : fsG 0 = 0 := rfl
@[simp] theorem fsG_one : fsG 1 = 1 := rfl
theorem frG_inj : Function.Injective frG := Fin.castLE_injective _

/-- The carrier table's accumulator header. -/
def hdr4 : List Bool := [true, false, false, false]

/-! ## Stream moves -/

/-- Move to the end of a `marks` stream. -/
def seekM (s : Fin 8) : WM 7 64 := .whs s (.seq (.fwd s) (.fwd s))

theorem seekM_spec (cap : ℕ) (s : Fin 8) : ∀ (u : List Bool) (σ : RS) (pre : List Bool),
    σ.st s = pre ++ marks u → σ.sh s = pre.length →
    WExec cap (seekM s) σ (σ.seth s (pre.length + 2 * u.length)) (5 * u.length + 1)
  | [], σ, pre, hs, hsh => by
    have hb : wbit σ s = false := by
      unfold wbit readTapeBit; rw [hs, hsh]; simp [marks]
    have e : σ.seth s (pre.length + 2 * ([] : List Bool).length) = σ := by
      rw [List.length_nil, Nat.mul_zero, Nat.add_zero, ← hsh, wseth_same]
    rw [e]; exact WExec.whsF hb
  | b :: u, σ, pre, hs, hsh => by
    have hb : wbit σ s = true := by
      unfold wbit readTapeBit; rw [hs, hsh]; simp [marks]
    have h1 := WExec.fwd (cap := cap) s σ
    have h2 := WExec.fwd (cap := cap) s (σ.seth s (σ.sh s + 1))
    have ih := seekM_spec cap s u ((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1)) (pre ++ [true, b])
      (by simp [hs, marks]) (by simp [hsh]; try omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) ?_ (by simp; omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp; omega
      · simp [hj]
    · rfl
    · rfl
    · rfl

/-- Append `LEN` ones to a raw unary stream (head at its end), `LEN := 0`. -/
def onesW (s : Fin 8) (r : Fin 64) : WM 7 64 := .whr r (.seq (.dec r) (.seq (.wr s true) (.fwd s)))

theorem onesW_spec (cap : ℕ) (s : Fin 8) (r : Fin 64) : ∀ (n : ℕ) (σ : RS) (m : ℕ),
    σ.st s = List.replicate m true → σ.sh s = m → σ.val r = n → n ≤ cap →
    WExec cap (onesW s r) σ (((σ.sets s (List.replicate (m + n) true)).seth s (m + n)).setv r 0) (7 * n + 1)
  | 0, σ, m, hs, hsh, hr, _ => by
    have e : ((σ.sets s (List.replicate (m + 0) true)).seth s (m + 0)).setv r 0 = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = s
        · subst hj; simp [hsh]
        · simp [hj]
      · funext j; by_cases hj : j = s
        · subst hj; simp [hs]
        · simp [hj]
      · funext j; by_cases hj : j = r
        · subst hj; simp [hr]
        · simp [hj]
      · rfl
    rw [e]; exact WExec.whrF hr
  | n + 1, σ, m, hs, hsh, hr, hc => by
    have h1 := WExec.dec (cap := cap) r σ (by omega)
    set σ1 := σ.setv r (σ.val r - 1) with hσ1
    have h2 := WExec.wr (cap := cap) s true σ1
    set σ2 := σ1.sets s (writeTapeBit (σ1.st s) (σ1.sh s) true) with hσ2
    have h3 := WExec.fwd (cap := cap) s σ2
    set σ3 := σ2.seth s (σ2.sh s + 1) with hσ3
    have hw : writeTapeBit (σ1.st s) (σ1.sh s) true = List.replicate (m + 1) true := by
      simp only [hσ1, WState.setv_st, WState.setv_sh, hs, hsh]
      exact FrontFill.write_replicate_end m true
    have ih := onesW_spec cap s r n σ3 (m + 1) (by simp [hσ3, hσ2, hw]) (by simp [hσ3, hσ2, hσ1, hsh])
      (by simp [hσ3, hσ2, hσ1, hr]) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp; omega
      · simp [hσ3, hσ2, hσ1, hj]
    · funext j; by_cases hj : j = s
      · subst hj; simp [show m + 1 + n = m + (n + 1) by omega]
      · simp [hσ3, hσ2, hσ1, hj]
    · funext j; by_cases hj : j = r
      · subst hj; simp
      · simp [hσ3, hσ2, hσ1, hj]
    · rfl

/-! ## The gates (skip the header, seek the end of `G`, convert) -/

/-- The gate phase. -/
def gateP : WM 7 64 :=
  .seq (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.fwd 0) (.fwd 0)))) (.seq (seekM 1)
    (.seq (FinalPass.Hash4.wcopyR (Wm 1) (frG 8) rTT) (.seq (GateConv.gconv.liftW fsG frG)
      (.seq (WM.clear (frG 8)) (WM.clear (frG 6))))))

/-- The gate phase's cost. -/
def gateC {q : ℕ} (C : List (NormalizedThresholdGate q)) (g : ℕ) : ℕ :=
  4 + 8 + (5 * g + 1) + (18 * q + 3) + GateConv.gsCost C + 3 * q + 1 + 3 * (2 * (C.flatMap GateConv.selGate).length) + 1

theorem gateP_spec (cap : ℕ) {q : ℕ} (C : List (NormalizedThresholdGate q)) (ω : RS) (rest0 Gacc : List Bool)
    (h0 : ω.st 0 = hdr4 ++ GateConv.tabL C ++ rest0) (hr0 : readTapeBit rest0 0 = false) (hs0 : ω.sh 0 = 0)
    (h1 : ω.st 1 = marks Gacc) (hs1 : ω.sh 1 = 0) (hq : ω.val (Wm 1) = q) (hz : ∀ r : Fin 16, ω.val (frG r) = 0)
    (htt : ω.val rTT = 0)
    (hcap : q + GateConv.capNeed C + 2 * (C.flatMap GateConv.selGate).length + 1 ≤ cap) :
    ∃ ω' : RS, WExec cap gateP ω ω' (gateC C Gacc.length) ∧
      ω'.st 1 = marks Gacc ++ marks (C.flatMap GateConv.selGate) ∧ ω'.sh 1 = (ω'.st 1).length ∧
      ω'.val (frG 9) = C.length ∧ (∀ r : Fin 16, r ≠ 9 → ω'.val (frG r) = 0) ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → ω'.st i = ω.st i ∧ ω'.sh i = ω.sh i) ∧ ω'.st 0 = ω.st 0 ∧
      (∀ r : Fin 64, (∀ k, frG k ≠ r) → ω'.val r = ω.val r) ∧ ω'.cell = ω.cell := by
  have ml := C1Rng.marks_length
  -- 1. skip the header
  have a1 := WExec.fwd (cap := cap) 0 ω
  have a2 := WExec.fwd (cap := cap) 0 (ω.seth 0 (ω.sh 0 + 1))
  have a3 := WExec.fwd (cap := cap) 0 ((ω.seth 0 (ω.sh 0 + 1)).seth 0 ((ω.seth 0 (ω.sh 0 + 1)).sh 0 + 1))
  have a4 := WExec.fwd (cap := cap) 0 (((ω.seth 0 (ω.sh 0 + 1)).seth 0 ((ω.seth 0 (ω.sh 0 + 1)).sh 0 + 1)).seth 0
    (((ω.seth 0 (ω.sh 0 + 1)).seth 0 ((ω.seth 0 (ω.sh 0 + 1)).sh 0 + 1)).sh 0 + 1))
  obtain ⟨ω1, hω1⟩ : ∃ τ : RS, τ = ω.seth 0 4 := ⟨_, rfl⟩
  have e14 : WExec cap (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.fwd 0) (.fwd 0)))) ω ω1 7 := by
    refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 a4))) ?_ le_rfl
    rw [hω1]; simp only [wseth_seth, WState.seth_sh, Function.update_self, hs0]
  -- 2. seek the end of `G`
  have b1 := seekM_spec cap 1 Gacc ω1 [] (by rw [hω1]; simp [h1]) (by rw [hω1]; simp [hs1])
  obtain ⟨ω2, hω2⟩ : ∃ τ : RS, τ = ω1.seth 1 (([] : List Bool).length + 2 * Gacc.length) := ⟨_, rfl⟩
  rw [← hω2] at b1
  -- 3. gconv's `q`
  have g2 : ∀ r, ω2.val r = ω.val r := fun r => by rw [hω2, hω1]; rfl
  have c1 := FinalPass.Hash4.wcopyR_spec cap (Wm 1) (frG 8) rTT (by decide) (by decide) (by decide) ω2
    (by rw [g2]; exact hz 8) (by rw [g2]; exact htt) (by rw [g2, hq]; omega)
  rw [g2, hq] at c1
  obtain ⟨ω3, hω3⟩ : ∃ τ : RS, τ = ω2.setv (frG 8) q := ⟨_, rfl⟩
  rw [← hω3] at c1
  -- 4. the lifted converter
  set σs : WState 1 16 := ⟨fun i => ω3.sh (fsG i), fun i => ω3.st (fsG i), fun r => ω3.val (frG r), ω3.cell⟩ with hσs
  have v3 : ∀ r : Fin 16, r ≠ 8 → ω3.val (frG r) = 0 := fun r hr => by
    rw [hω3]; simp only [WState.setv_val, Function.update_apply, if_neg (fun e => hr (frG_inj e)), g2, hz]
  have v38 : ω3.val (frG 8) = q := by rw [hω3]; simp
  have st30 : ω3.st 0 = ω.st 0 := by rw [hω3, hω2, hω1]; rfl
  have st31 : ω3.st 1 = ω.st 1 := by rw [hω3, hω2, hω1]; rfl
  have sh30 : ω3.sh 0 = 4 := by rw [hω3, hω2, hω1]; simp
  have sh31 : ω3.sh 1 = 2 * Gacc.length := by rw [hω3, hω2]; simp
  have gc := GateConv.gconv_spec cap C σs hdr4 rest0 (by show ω3.st 0 = _; rw [st30, h0])
    (by show ω3.sh 0 = _; rw [sh30]; rfl) hr0 (by show ω3.sh 1 = (ω3.st 1).length; rw [sh31, st31, h1, ml])
    (by show ω3.val (frG 8) = q; exact v38) (v3 0 (by decide)) (v3 1 (by decide)) (v3 2 (by decide))
    (v3 3 (by decide)) (v3 4 (by decide)) (v3 5 (by decide)) (v3 7 (by decide)) (v3 10 (by decide))
    (v3 11 (by decide)) (by show ω3.val (frG 6) + ω3.val (frG 9) + _ ≤ cap; rw [v3 6 (by decide), v3 9 (by decide)]; omega)
  obtain ⟨ω4, d4, hl4, ho4⟩ := WExec.liftW cap cap le_rfl fsG fsG_inj frG frG_inj gc ω3 ⟨fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl⟩
  set τs := (appendO (σs.seth 0 (hdr4.length + (GateConv.tabL C).length)) 1 6
    (marks (C.flatMap GateConv.selGate))).setv 9 (σs.val 9 + C.length) with hτs
  have v46 : ω4.val (frG 6) = (marks (C.flatMap GateConv.selGate)).length := by
    rw [hl4.val 6, hτs]; simp [hσs, v3 6 (by decide)]
  have v48 : ω4.val (frG 8) = q := by rw [hl4.val 8, hτs]; simp [hσs, v38]
  -- 5, 6. clear `q` and the output counter
  have d5 := wclear_spec cap (frG 8) q ω4 v48 (by rw [v48]; omega)
  have d6 := wclear_spec cap (frG 6) (marks (C.flatMap GateConv.selGate)).length (ω4.setv (frG 8) 0)
    (by rw [WState.setv_val, Function.update_of_ne (show frG 6 ≠ frG 8 by decide), v46])
    (by rw [WState.setv_val, Function.update_of_ne (show frG 6 ≠ frG 8 by decide), v46, ml]; omega)
  refine ⟨_, WExec.mono (WExec.seq e14 (WExec.seq b1 (WExec.seq c1 (WExec.seq d4 (WExec.seq d5 d6))))) ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold gateC; simp only [ml] at *; omega
  · show ω4.st 1 = _
    rw [show (1 : Fin 8) = fsG 1 from rfl, hl4.st 1, hτs]; simp [hσs, st31, h1]
  · show ω4.sh 1 = (ω4.st 1).length
    rw [show (1 : Fin 8) = fsG 1 from rfl, hl4.st 1, hl4.sh 1, hτs]; simp [hσs, sh31, st31, h1, ml]
  · simp only [WState.setv_val, Function.update_apply, show frG 9 ≠ frG 6 by decide, show frG 9 ≠ frG 8 by decide,
      if_false]
    rw [hl4.val 9, hτs]; simp [hσs, v3 9 (by decide)]
  · intro r hr
    simp only [WState.setv_val, Function.update_apply]
    by_cases h6 : frG r = frG 6
    · simp [h6]
    · by_cases h8 : frG r = frG 8
      · simp [h8, show frG 8 ≠ frG 6 by decide]
      · simp only [h6, h8, if_false]
        rw [hl4.val r, hτs]
        have hr6 : r ≠ 6 := fun e => h6 (by rw [e])
        have hr8 : r ≠ 8 := fun e => h8 (by rw [e])
        simp [hσs, Function.update_apply, hr, hr6, v3 r hr8]
  · intro i hi0 hi1
    have hout : ∀ k, fsG k ≠ i := by
      intro k; fin_cases k
      · exact fun e => hi0 (by rw [← e]; rfl)
      · exact fun e => hi1 (by rw [← e]; rfl)
    have o := ho4.1 i hout
    refine ⟨?_, ?_⟩
    · show ω4.st i = ω.st i
      rw [o.2, hω3, hω2, hω1]; rfl
    · show ω4.sh i = ω.sh i
      rw [o.1, hω3, hω2, hω1]
      simp [Function.update_apply, hi0, hi1]
  · show ω4.st 0 = ω.st 0
    rw [show (0 : Fin 8) = fsG 0 from rfl, hl4.st 0, hτs]; simp [hσs, st30]
  · intro r hr
    simp only [WState.setv_val, Function.update_apply, if_neg (Ne.symm (hr 6)), if_neg (Ne.symm (hr 8))]
    rw [ho4.2 r hr, hω3]
    simp only [WState.setv_val, Function.update_apply, if_neg (Ne.symm (hr 8)), g2]
  · show ω4.cell = ω.cell
    rw [hl4.cell, hτs]; simp [hσs, hω3, hω2, hω1]

/-! ## The population (indices, weight) and the running counts -/

/-- The population phase. -/
def popP : WM 7 64 :=
  .seq (PrimAsm.SymDec.readUW 5 rS) (.seq (WM.move (frG 9) rLEN) (.seq (seekM 4)
    (.seq (C1Rng.rangeW 4 Rm rK rT rS rLEN) (.seq (WM.move (Wm 2) (Zm 0))
      (.seq (FinalPass.Hash4.wcopyR (Wm 3) (Zm 1) rTT) (.seq (.inc (Zm 1)) (.seq (C1Rat.ratW 4 Rm Zm)
        (.seq (WM.clear (Zm 1)) (.seq (WM.clear (Rm 7)) (.seq (onesW 5 rLEN) (.seq (WM.clear rS)
          (.seq (PrimAsm.SymDec.readUW 6 rTT) (.seq (WM.clear rTT) (.wr 6 true))))))))))))))

/-- The population phase's cost (`NL`, `RW` the written words' lengths). -/
def popC (gt len c cb P np NL RW : ℕ) : ℕ :=
  7 * gt + 1 + (7 * len + 1) + (5 * P + 1) + C1Rng.rangeCost gt len + (7 * c + 1) + (18 * cb + 3) + 3 +
    C1Rat.ratCost c (cb + 1) + (3 * (cb + 1) + 1) + (3 * (NL + RW) + 1) + (7 * len + 1) + (3 * gt + 1) +
    (7 * np + 1) + (3 * np + 1) + 1 + 14

/-- The registers the population phase may meet nonzero. -/
def popLive (r : Fin 64) : Prop := r = Wm 0 ∨ r = Wm 1 ∨ r = Wm 2 ∨ r = Wm 3 ∨ r = frG 9

instance (r : Fin 64) : Decidable (popLive r) := by unfold popLive; infer_instance

theorem popP_spec (cap : ℕ) (ω : RS) (Pacc : List Bool) (gt np len c cb : ℕ) (hc : 1 ≤ c)
    (h4 : ω.st 4 = marks Pacc) (hs4 : ω.sh 4 = 0) (h5 : ω.st 5 = List.replicate gt true) (hs5 : ω.sh 5 = 0)
    (h6 : ω.st 6 = List.replicate np true) (hs6 : ω.sh 6 = 0) (h9 : ω.val (frG 9) = len) (hC : ω.val (Wm 2) = c)
    (hB : ω.val (Wm 3) = cb) (hz : ∀ r, ¬ popLive r → ω.val r = 0)
    (hcap : gt + len + c + cb + np + 2 ^ (cb + 2) + (marks (natListWord (List.range' gt len))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1)))).length +
      6 * natBitLength (gt + len) + 6 * natBitLength (c + 2 ^ (cb + 1)) + 40 ≤ cap) :
    ∃ ω' : RS, WExec cap popP ω ω' (popC gt len c cb Pacc.length np
        (marks (natListWord (List.range' gt len))).length
        (marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1)))).length) ∧
      ω'.st 4 = marks Pacc ++ marks (natListWord (List.range' gt len)) ++
        marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1))) ∧
      ω'.st 5 = List.replicate (gt + len) true ∧ ω'.st 6 = List.replicate (np + 1) true ∧
      (∀ i : Fin 8, i ≠ 4 → i ≠ 5 → i ≠ 6 → ω'.st i = ω.st i ∧ ω'.sh i = ω.sh i) ∧
      ω'.val (Wm 0) = ω.val (Wm 0) ∧ ω'.val (Wm 1) = ω.val (Wm 1) ∧ ω'.val (Wm 3) = cb ∧
      (∀ r, r ≠ Wm 0 → r ≠ Wm 1 → r ≠ Wm 3 → ω'.val r = 0) ∧ ω'.cell = ω.cell := by
  have ml := C1Rng.marks_length
  have z : ∀ r, ¬ popLive r → ω.val r = 0 := hz
  have zS : ω.val rS = 0 := z _ (by decide)
  have zL : ω.val rLEN = 0 := z _ (by decide)
  have zT : ω.val rTT = 0 := z _ (by decide)
  have zK : ω.val rK = 0 := z _ (by decide)
  have zt : ω.val rT = 0 := z _ (by decide)
  have zR : ∀ i : Fin 8, ω.val (Rm i) = 0 := fun i => z _ (by fin_cases i <;> decide)
  have zZ : ∀ i : Fin 10, ω.val (Zm i) = 0 := fun i => z _ (by fin_cases i <;> decide)
  have hp1 : 2 ^ (cb + 2) = 4 * 2 ^ cb := by rw [pow_add]; ring
  have hp3 : 2 ^ (cb + 1) = 2 * 2 ^ cb := by rw [pow_succ]; ring
  have hp0 := Nat.two_pow_pos cb
  -- 1. S := gt
  have p1 := PrimAsm.SymDec.readU_spec cap 5 rS gt 0 ω h5 hs5 zS (by omega)
  obtain ⟨ω1, hω1⟩ : ∃ τ : RS, τ = (ω.seth 5 gt).setv rS (0 + gt) := ⟨_, rfl⟩
  rw [← hω1] at p1
  -- 2. LEN := len
  have v19 : ω1.val (frG 9) = len := by rw [hω1]; simp [show frG 9 ≠ rS by decide, h9]
  have v1L : ω1.val rLEN = 0 := by rw [hω1]; simp [show rLEN ≠ rS by decide, zL]
  have p2 := wmove_spec cap (frG 9) rLEN (by decide) len ω1 v19 (by rw [v19]; omega) (by rw [v19, v1L]; omega)
  rw [v19, v1L] at p2
  obtain ⟨ω2, hω2⟩ : ∃ τ : RS, τ = (ω1.setv (frG 9) 0).setv rLEN (0 + len) := ⟨_, rfl⟩
  rw [← hω2] at p2
  -- 3. seek the end of `POPS`
  have p3 := seekM_spec cap 4 Pacc ω2 [] (by rw [hω2, hω1]; simp [h4]) (by rw [hω2, hω1]; simp [hs4])
  obtain ⟨ω3, hω3⟩ : ∃ τ : RS, τ = ω2.seth 4 (([] : List Bool).length + 2 * Pacc.length) := ⟨_, rfl⟩
  rw [← hω3] at p3
  have g3 : ∀ r, r ≠ rS → r ≠ frG 9 → r ≠ rLEN → ω3.val r = ω.val r := fun r a b d => by
    rw [hω3, hω2, hω1]; simp [a, b, d]
  -- 4. the index list
  have p4 := C1Rng.rangeW_spec cap 4 Rm rK rT rS rLEN (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ω3 gt len
    (by rw [hω3, hω2, hω1]; simp [show rS ≠ rLEN by decide, show rS ≠ frG 9 by decide]) (by rw [hω3, hω2]; simp)
    (by rw [g3 _ (by decide) (by decide) (by decide), zK]) (by rw [g3 _ (by decide) (by decide) (by decide), zt])
    (by rw [g3 _ (by decide) (by decide) (by decide), zR 0]) (by rw [g3 _ (by decide) (by decide) (by decide), zR 1])
    (by rw [g3 _ (by decide) (by decide) (by decide), zR 2]) (by rw [g3 _ (by decide) (by decide) (by decide), zR 3])
    (by rw [g3 _ (by decide) (by decide) (by decide), zR 4]) (by rw [g3 _ (by decide) (by decide) (by decide), zR 5])
    (by rw [g3 _ (by decide) (by decide) (by decide), zR 6])
    (by rw [hω3, hω2, hω1]; simp [h4, ml])
    (by rw [g3 _ (by decide) (by decide) (by decide), zR 7]; omega)
  obtain ⟨ω4, hω4⟩ : ∃ τ : RS, τ = appendO ω3 4 (Rm 7) (marks (natListWord (List.range' gt len))) := ⟨_, rfl⟩
  rw [← hω4] at p4
  have g4 : ∀ r, r ≠ rS → r ≠ frG 9 → r ≠ rLEN → r ≠ Rm 7 → ω4.val r = ω.val r := fun r a b d e => by
    rw [hω4]; simp [e, g3 r a b d]
  have v4R7 : ω4.val (Rm 7) = (marks (natListWord (List.range' gt len))).length := by
    rw [hω4]; simp; rw [g3 _ (by decide) (by decide) (by decide), zR 7]
  -- 5. Z 0 := c
  have v42 : ω4.val (Wm 2) = c := by rw [g4 _ (by decide) (by decide) (by decide) (by decide), hC]
  have v4Z : ω4.val (Zm 0) = 0 := by rw [g4 _ (by decide) (by decide) (by decide) (by decide), zZ 0]
  have p5 := wmove_spec cap (Wm 2) (Zm 0) (by decide) c ω4 v42 (by rw [v42]; omega) (by rw [v42, v4Z]; omega)
  rw [v42, v4Z] at p5
  obtain ⟨ω5, hω5⟩ : ∃ τ : RS, τ = (ω4.setv (Wm 2) 0).setv (Zm 0) (0 + c) := ⟨_, rfl⟩
  rw [← hω5] at p5
  have g5 : ∀ r, r ≠ Wm 2 → r ≠ Zm 0 → ω5.val r = ω4.val r := fun r a b => by rw [hω5]; simp [a, b]
  -- 6, 7. Z 1 := cb + 1
  have v53 : ω5.val (Wm 3) = cb := by
    rw [g5 _ (by decide) (by decide), g4 _ (by decide) (by decide) (by decide) (by decide), hB]
  have v5Z1 : ω5.val (Zm 1) = 0 := by
    rw [g5 _ (by decide) (by decide), g4 _ (by decide) (by decide) (by decide) (by decide), zZ 1]
  have v5T : ω5.val rTT = 0 := by
    rw [g5 _ (by decide) (by decide), g4 _ (by decide) (by decide) (by decide) (by decide), zT]
  have p6 := FinalPass.Hash4.wcopyR_spec cap (Wm 3) (Zm 1) rTT (by decide) (by decide) (by decide) ω5 v5Z1 v5T
    (by rw [v53]; omega)
  rw [v53] at p6
  have p7 := WExec.inc (cap := cap) (Zm 1) (ω5.setv (Zm 1) cb) (by simp; omega)
  obtain ⟨ω7, hω7⟩ : ∃ τ : RS, τ = (ω5.setv (Zm 1) cb).setv (Zm 1) ((ω5.setv (Zm 1) cb).val (Zm 1) + 1) :=
    ⟨_, rfl⟩
  rw [← hω7] at p7
  have g7 : ∀ r, r ≠ Zm 1 → ω7.val r = ω5.val r := fun r a => by rw [hω7]; simp [a]
  have v7Z1 : ω7.val (Zm 1) = cb + 1 := by rw [hω7]; simp
  have v7Z0 : ω7.val (Zm 0) = c := by rw [g7 _ (by decide), hω5]; simp
  have ne2 : ∀ i : Fin 10, 2 ≤ i.val → Zm i ≠ Zm 1 ∧ Zm i ≠ Zm 0 ∧ Zm i ≠ Wm 2 ∧ Zm i ≠ rS ∧ Zm i ≠ frG 9 ∧
      Zm i ≠ rLEN ∧ Zm i ≠ Rm 7 := by
    intro i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; have := congrArg Fin.val e; simp [frG] at this; omega)
  have v7Z : ∀ i : Fin 10, 2 ≤ i.val → ω7.val (Zm i) = 0 := fun i hi => by
    obtain ⟨a, b, d, e, f, g, h⟩ := ne2 i hi
    rw [g7 _ a, g5 _ d b, g4 _ e f g h, zZ i]
  have neR : ∀ i : Fin 8, i.val < 7 → Rm i ≠ Zm 1 ∧ Rm i ≠ Zm 0 ∧ Rm i ≠ Wm 2 ∧ Rm i ≠ rS ∧ Rm i ≠ frG 9 ∧
      Rm i ≠ rLEN ∧ Rm i ≠ Rm 7 := by
    intro i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; have := congrArg Fin.val e; simp [frG] at this; omega)
  have v7R : ∀ i : Fin 8, i.val < 7 → ω7.val (Rm i) = 0 := fun i hi => by
    obtain ⟨a, b, d, e, f, g, h⟩ := neR i hi
    rw [g7 _ a, g5 _ d b, g4 _ e f g h, zR i]
  have v7R7 : ω7.val (Rm 7) = (marks (natListWord (List.range' gt len))).length := by
    rw [g7 _ (by decide), g5 _ (by decide) (by decide), v4R7]
  have s7 : ω7.sh 4 = (ω7.st 4).length := by
    rw [hω7, hω5, hω4, hω3]; simp [hω2, hω1, h4, ml]
  -- 8. the weight
  have p8 := C1Rat.ratW_spec cap 4 Rm Zm (fun i j => by
      intro e; have := congrArg Fin.val e; simp at this; omega) ω7 c (cb + 1) v7Z0 v7Z1
    (v7Z 2 (by decide)) (v7Z 3 (by decide)) (v7Z 4 (by decide)) (v7Z 5 (by decide)) (v7Z 6 (by decide))
    (v7Z 7 (by decide)) (v7Z 8 (by decide)) (v7Z 9 (by decide))
    (v7R 0 (by decide)) (v7R 1 (by decide)) (v7R 2 (by decide)) (v7R 3 (by decide)) (v7R 4 (by decide))
    (v7R 5 (by decide)) (v7R 6 (by decide)) s7 (by rw [v7R7, show cb + 1 + 1 = cb + 2 by ring]; omega)
  obtain ⟨ω8, hω8⟩ : ∃ τ : RS, τ = (appendO ω7 4 (Rm 7)
      (marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1))))).setv (Zm 0) 0 := ⟨_, rfl⟩
  rw [← hω8] at p8
  have g8 : ∀ r, r ≠ Zm 0 → r ≠ Rm 7 → ω8.val r = ω7.val r := fun r a b => by rw [hω8]; simp [a, b]
  -- 9, 10. Z 1, R 7 := 0
  have v8Z1 : ω8.val (Zm 1) = cb + 1 := by rw [g8 _ (by decide) (by decide), v7Z1]
  have p9 := wclear_spec cap (Zm 1) (cb + 1) ω8 v8Z1 (by rw [v8Z1]; omega)
  have v9R7 : (ω8.setv (Zm 1) 0).val (Rm 7) = (marks (natListWord (List.range' gt len))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1)))).length := by
    rw [WState.setv_val, Function.update_of_ne (show Rm 7 ≠ Zm 1 by decide), hω8]
    simp [show Rm 7 ≠ Zm 0 by decide, v7R7]
  have p10 := wclear_spec cap (Rm 7) _ (ω8.setv (Zm 1) 0) v9R7 (by rw [v9R7]; omega)
  obtain ⟨ω10, hω10⟩ : ∃ τ : RS, τ = (ω8.setv (Zm 1) 0).setv (Rm 7) 0 := ⟨_, rfl⟩
  rw [← hω10] at p10
  -- streams through step 10
  have st10 : ∀ i : Fin 8, i ≠ 4 → ω10.st i = ω.st i := fun i hi => by
    rw [hω10, hω8, hω7, hω5, hω4, hω3, hω2, hω1]; simp [hi]
  have sh10 : ∀ i : Fin 8, i ≠ 4 → i ≠ 5 → ω10.sh i = ω.sh i := fun i a b => by
    rw [hω10, hω8, hω7, hω5, hω4, hω3, hω2, hω1]; simp [a, b]
  have sh105 : ω10.sh 5 = gt := by rw [hω10, hω8, hω7, hω5, hω4, hω3, hω2, hω1]; simp
  have st104 : ω10.st 4 = marks Pacc ++ marks (natListWord (List.range' gt len)) ++
      marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1))) := by
    rw [hω10, hω8, hω7, hω5, hω4, hω3, hω2, hω1]; simp [h4]
  have g10 : ∀ r, r ≠ Zm 1 → r ≠ Rm 7 → r ≠ Zm 0 → ω10.val r = ω7.val r := fun r a b d => by
    rw [hω10]; simp [a, b]; exact g8 r d b
  have v10L : ω10.val rLEN = len := by
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), g5 _ (by decide) (by decide), hω4]
    simp [show rLEN ≠ Rm 7 by decide]; rw [hω3, hω2]; simp
  -- 11. GT += len
  have p11 := onesW_spec cap 5 rLEN len ω10 gt (by rw [st10 5 (by decide), h5]) sh105 v10L (by omega)
  obtain ⟨ω11, hω11⟩ : ∃ τ : RS, τ = ((ω10.sets 5 (List.replicate (gt + len) true)).seth 5 (gt + len)).setv rLEN 0 :=
    ⟨_, rfl⟩
  rw [← hω11] at p11
  -- 12. S := 0
  have v11S : ω11.val rS = gt := by
    rw [hω11]; simp [show rS ≠ rLEN by decide]
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), g5 _ (by decide) (by decide), hω4]
    simp [show rS ≠ Rm 7 by decide]; rw [hω3, hω2, hω1]; simp [show rS ≠ rLEN by decide, show rS ≠ frG 9 by decide]
  have p12 := wclear_spec cap rS gt ω11 v11S (by rw [v11S]; omega)
  -- 13, 14. seek the end of `NP`
  have st12_6 : (ω11.setv rS 0).st 6 = List.replicate np true := by
    rw [WState.setv_st, hω11]; simp; rw [st10 6 (by decide), h6]
  have sh12_6 : (ω11.setv rS 0).sh 6 = 0 := by
    rw [WState.setv_sh, hω11]; simp; rw [sh10 6 (by decide) (by decide), hs6]
  have v12T : (ω11.setv rS 0).val rTT = 0 := by
    rw [WState.setv_val, Function.update_of_ne (show rTT ≠ rS by decide), hω11]; simp [show rTT ≠ rLEN by decide]
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), g5 _ (by decide) (by decide),
      g4 _ (by decide) (by decide) (by decide) (by decide), zT]
  have p13 := PrimAsm.SymDec.readU_spec cap 6 rTT np 0 (ω11.setv rS 0) st12_6 sh12_6 v12T (by omega)
  obtain ⟨ω13, hω13⟩ : ∃ τ : RS, τ = ((ω11.setv rS 0).seth 6 np).setv rTT (0 + np) := ⟨_, rfl⟩
  rw [← hω13] at p13
  have v13T : ω13.val rTT = np := by rw [hω13]; simp
  have p14 := wclear_spec cap rTT np ω13 v13T (by rw [v13T]; omega)
  -- 15. NP += 1
  have p15 := WExec.wr (cap := cap) 6 true (ω13.setv rTT 0)
  have hw15 : writeTapeBit ((ω13.setv rTT 0).st 6) ((ω13.setv rTT 0).sh 6) true = List.replicate (np + 1) true := by
    rw [WState.setv_st, WState.setv_sh, hω13]; simp [st12_6]
  rw [hw15] at p15
  refine ⟨_, WExec.mono (WExec.seq p1 (WExec.seq p2 (WExec.seq p3 (WExec.seq p4 (WExec.seq p5 (WExec.seq p6
    (WExec.seq p7 (WExec.seq p8 (WExec.seq p9 (WExec.seq p10 (WExec.seq p11 (WExec.seq p12 (WExec.seq p13
      (WExec.seq p14 p15)))))))))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold popC; omega
  · rw [hω13, hω11]; simp only [List.append_assoc] at st104; simp; exact st104
  · rw [hω13, hω11]; simp
  · simp
  · intro i a b d
    refine ⟨?_, ?_⟩
    · rw [hω13, hω11]; simp [b, d]; exact st10 i a
    · rw [hω13, hω11]; simp [b, d]; exact sh10 i a b
  · rw [hω13, hω11]; simp [show Wm 0 ≠ rTT by decide, show Wm 0 ≠ rS by decide, show Wm 0 ≠ rLEN by decide]
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), g5 _ (by decide) (by decide),
      g4 _ (by decide) (by decide) (by decide) (by decide)]
  · rw [hω13, hω11]; simp [show Wm 1 ≠ rTT by decide, show Wm 1 ≠ rS by decide, show Wm 1 ≠ rLEN by decide]
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), g5 _ (by decide) (by decide),
      g4 _ (by decide) (by decide) (by decide) (by decide)]
  · rw [hω13, hω11]; simp [show Wm 3 ≠ rTT by decide, show Wm 3 ≠ rS by decide, show Wm 3 ≠ rLEN by decide]
    rw [g10 _ (by decide) (by decide) (by decide), g7 _ (by decide), v53]
  · intro r a b d
    rw [hω13, hω11]
    simp only [WState.sets_val, WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases eT : r = rTT
    · simp [eT]
    by_cases eS : r = rS
    · subst eS; simp [show rS ≠ rTT by decide]
    by_cases eL : r = rLEN
    · subst eL; simp [show rLEN ≠ rTT by decide, show rLEN ≠ rS by decide]
    simp only [eT, eS, eL, if_false]
    by_cases eZ1 : r = Zm 1
    · subst eZ1; rw [hω10]; simp [show Zm 1 ≠ Rm 7 by decide]
    by_cases eR7 : r = Rm 7
    · subst eR7; rw [hω10]; simp
    by_cases eZ0 : r = Zm 0
    · subst eZ0; rw [hω10, hω8]; simp [show Zm 0 ≠ Rm 7 by decide, show Zm 0 ≠ Zm 1 by decide]
    rw [g10 r eZ1 eR7 eZ0, g7 r eZ1]
    by_cases e2 : r = Wm 2
    · subst e2; rw [hω5]; simp [show Wm 2 ≠ Zm 0 by decide]
    rw [g5 r e2 eZ0]
    by_cases e9 : r = frG 9
    · subst e9; rw [hω4, hω3, hω2]; simp [show frG 9 ≠ Rm 7 by decide, show frG 9 ≠ rLEN by decide]
    rw [g4 r eS e9 eL eR7]
    exact z r (by unfold popLive; tauto)
  · rw [hω13, hω11, hω10, hω8, hω7, hω5, hω4, hω3, hω2, hω1]; simp

/-! ## The round -/

/-- **One variable's round.** -/
def roundW : WM 7 64 :=
  .seq (PrimAsm.SymDec.readUW 3 (Wm 0)) (.seq (PrimAsm.SymDec.readUW 7 (Wm 1)) (.seq (C1Cnt.cntW 2 Wm)
    (.seq (.wr 3 true) (.seq (.ifr (Wm 2) (.seq gateP popP) .skip)
      (.seq (WM.clear (Wm 0)) (.seq (WM.clear (Wm 1)) (WM.clear (Wm 3))))))))

/-- The round's cost (`B` the positive branch's). -/
def roundC (x q V nl cb B : ℕ) : ℕ :=
  7 * x + 1 + (7 * q + 1) + C1Cnt.cntC V q nl + 1 + (B + 1) + (3 * x + 1) + (3 * q + 1) + (3 * cb + 1) + 7

theorem roundW_spec (cap : ℕ) {q : ℕ} (C : List (NormalizedThresholdGate q)) (σ : RS)
    (rest0 Gacc Pacc bits rest2 : List Bool) (lits : List ℕ) (sys aux cb x gt np V : ℕ)
    (h0 : σ.st 0 = hdr4 ++ GateConv.tabL C ++ rest0) (hr0 : readTapeBit rest0 0 = false)
    (h1 : σ.st 1 = marks Gacc) (h2 : σ.st 2 = C1Cnt.poWord sys aux cb bits lits ++ rest2)
    (hbits : bits.length = sys * q) (h3 : σ.st 3 = List.replicate x true) (h4 : σ.st 4 = marks Pacc)
    (h5 : σ.st 5 = List.replicate gt true) (h6 : σ.st 6 = List.replicate np true)
    (h7 : σ.st 7 = List.replicate q true) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hsV : sys ≤ V) (haV : aux ≤ V) (hcV : cb ≤ V) (hlV : lits.length ≤ V) (hV : ∀ l ∈ lits, l ≤ V) (hxV : x ≤ V)
    (h3V : 3 ≤ V)
    (hcap : sys * q + q + lits.length + 6 * V + 8 + x + q + GateConv.capNeed C +
      2 * (C.flatMap GateConv.selGate).length + gt + C.length + C1Cnt.cntOf x lits + cb + np + 2 ^ (cb + 2) +
      (marks (natListWord (List.range' gt C.length))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length +
      6 * natBitLength (gt + C.length) + 6 * natBitLength (C1Cnt.cntOf x lits + 2 ^ (cb + 1)) + 40 ≤ cap) :
    ∃ τ : RS, WExec cap roundW σ τ (roundC x q V lits.length cb (gateC C Gacc.length + 1 +
        popC gt C.length (C1Cnt.cntOf x lits) cb Pacc.length np
          (marks (natListWord (List.range' gt C.length))).length
          (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length)) ∧
      τ.st 0 = σ.st 0 ∧ τ.st 2 = σ.st 2 ∧ τ.st 7 = σ.st 7 ∧ τ.st 3 = List.replicate (x + 1) true ∧
      τ.st 1 = (if 0 < C1Cnt.cntOf x lits then marks Gacc ++ marks (C.flatMap GateConv.selGate) else marks Gacc) ∧
      τ.st 4 = (if 0 < C1Cnt.cntOf x lits then marks Pacc ++ marks (natListWord (List.range' gt C.length)) ++
        marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1))) else marks Pacc) ∧
      τ.st 5 = List.replicate (gt + if 0 < C1Cnt.cntOf x lits then C.length else 0) true ∧
      τ.st 6 = List.replicate (np + if 0 < C1Cnt.cntOf x lits then 1 else 0) true ∧
      (∀ r, τ.val r = 0) ∧ τ.cell = σ.cell := by
  have hpw := Nat.two_pow_pos (cb + 2)
  have hpw1 := Nat.two_pow_pos (cb + 1)
  set c := C1Cnt.cntOf x lits with hcdef
  have hcx : c ≤ lits.length := by
    rw [hcdef]; unfold C1Cnt.cntOf; exact List.length_filter_le _ _
  -- 1, 2. X, Q
  have s1 := PrimAsm.SymDec.readU_spec cap 3 (Wm 0) x 0 σ h3 (hsh 3) (hv _) (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : RS, τ = (σ.seth 3 x).setv (Wm 0) (0 + x) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have s2 := PrimAsm.SymDec.readU_spec cap 7 (Wm 1) q 0 σ1 (by rw [hσ1]; simpa using h7) (by rw [hσ1]; simp [hsh 7])
    (by rw [hσ1]; simp [show Wm 1 ≠ Wm 0 by decide, hv]) (by omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : RS, τ = (σ1.seth 7 q).setv (Wm 1) (0 + q) := ⟨_, rfl⟩
  rw [← hσ2] at s2
  -- 3. the count
  have s3 := C1Cnt.cntW_spec cap 2 Wm σ2 x q sys aux cb V bits lits rest2
    (by rw [hσ2, hσ1]; simpa using h2) (by rw [hσ2, hσ1]; simp [hsh 2]) hbits
    (by rw [hσ2, hσ1]; simp [show Wm 0 ≠ Wm 1 by decide])
    (by rw [hσ2]; simp)
    (fun i hi => by
      rw [hσ2, hσ1]
      have a : Wm i ≠ Wm 1 := fun e => by have := Wm.injective e; subst this; simp at hi
      have b : Wm i ≠ Wm 0 := fun e => by have := Wm.injective e; subst this; simp at hi
      simp [a, b, hv])
    hsV haV hcV hlV hV hxV h3V (by omega)
  rw [← hcdef] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ τ : RS, τ = ((σ2.seth 2 (C1Cnt.poWord sys aux cb bits lits).length).setv (Wm 2) c).setv (Wm 3) cb :=
    ⟨_, rfl⟩
  rw [← hσ3] at s3
  -- 4. XS += 1
  have s4 := WExec.wr (cap := cap) 3 true σ3
  have hw4 : writeTapeBit (σ3.st 3) (σ3.sh 3) true = List.replicate (x + 1) true := by
    rw [hσ3, hσ2, hσ1]; simp [h3]
  rw [hw4] at s4
  obtain ⟨σ4, hσ4⟩ : ∃ τ : RS, τ = σ3.sets 3 (List.replicate (x + 1) true) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  -- the state before the branch
  have st4 : ∀ i : Fin 8, i ≠ 3 → σ4.st i = σ.st i := fun i hi => by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [hi]
  have st43 : σ4.st 3 = List.replicate (x + 1) true := by rw [hσ4]; simp
  have sh4 : ∀ i : Fin 8, i ≠ 3 → i ≠ 7 → i ≠ 2 → σ4.sh i = 0 := fun i a b d => by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [a, b, d, hsh]
  have v40 : σ4.val (Wm 0) = x := by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [show Wm 0 ≠ Wm 3 by decide, show Wm 0 ≠ Wm 2 by decide, show Wm 0 ≠ Wm 1 by decide]
  have v41 : σ4.val (Wm 1) = q := by
    rw [hσ4, hσ3, hσ2]; simp [show Wm 1 ≠ Wm 3 by decide, show Wm 1 ≠ Wm 2 by decide]
  have v42 : σ4.val (Wm 2) = c := by rw [hσ4, hσ3]; simp [show Wm 2 ≠ Wm 3 by decide]
  have v43 : σ4.val (Wm 3) = cb := by rw [hσ4, hσ3]; simp
  have v4z : ∀ r, r ≠ Wm 0 → r ≠ Wm 1 → r ≠ Wm 2 → r ≠ Wm 3 → σ4.val r = 0 := fun r a b d e => by
    rw [hσ4, hσ3, hσ2, hσ1]; simp [a, b, d, e, hv]
  have c4 : σ4.cell = σ.cell := by rw [hσ4, hσ3, hσ2, hσ1]; rfl
  -- 5. the branch
  have key : ∃ ω : RS, WExec cap (.ifr (Wm 2) (.seq gateP popP) .skip) σ4 ω (gateC C Gacc.length + 1 +
        popC gt C.length c cb Pacc.length np (marks (natListWord (List.range' gt C.length))).length
          (marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1)))).length + 1) ∧
      ω.st 0 = σ.st 0 ∧ ω.st 2 = σ.st 2 ∧ ω.st 7 = σ.st 7 ∧ ω.st 3 = List.replicate (x + 1) true ∧
      ω.st 1 = (if 0 < c then marks Gacc ++ marks (C.flatMap GateConv.selGate) else marks Gacc) ∧
      ω.st 4 = (if 0 < c then marks Pacc ++ marks (natListWord (List.range' gt C.length)) ++
        marks (NearCubicWires.WireExponent3_5.ratWord ((c : ℚ) / 2 ^ (cb + 1))) else marks Pacc) ∧
      ω.st 5 = List.replicate (gt + if 0 < c then C.length else 0) true ∧
      ω.st 6 = List.replicate (np + if 0 < c then 1 else 0) true ∧
      ω.val (Wm 0) = x ∧ ω.val (Wm 1) = q ∧ ω.val (Wm 3) = cb ∧
      (∀ r, r ≠ Wm 0 → r ≠ Wm 1 → r ≠ Wm 3 → ω.val r = 0) ∧ ω.cell = σ.cell := by
    by_cases hc0 : 0 < c
    · -- the gates
      obtain ⟨ω1, g1, gst1, gsh1, gv9, gvz, gout, gst0, gval, gcell⟩ := gateP_spec cap C σ4 rest0 Gacc
        (by rw [st4 0 (by decide), h0]) hr0 (sh4 0 (by decide) (by decide) (by decide))
        (by rw [st4 1 (by decide), h1]) (sh4 1 (by decide) (by decide) (by decide)) v41
        (fun r => v4z _ (fun e => by have := congrArg Fin.val e; simp [frG] at this; omega)
          (fun e => by have := congrArg Fin.val e; simp [frG] at this; omega)
          (fun e => by have := congrArg Fin.val e; simp [frG] at this; omega)
          (fun e => by have := congrArg Fin.val e; simp [frG] at this; omega))
        (v4z _ (by decide) (by decide) (by decide) (by decide)) (by omega)
      have nfr : ∀ r : Fin 64, 16 ≤ r.val → ∀ k, frG k ≠ r := fun r hr k e => by
        have := congrArg Fin.val e; simp [frG] at this; omega
      -- the population
      obtain ⟨ω2, p2, pst4, pst5, pst6, pout, pv0, pv1, pv3, pvz, pcell⟩ := popP_spec cap ω1 Pacc gt np C.length c cb
        hc0 (by rw [(gout 4 (by decide) (by decide)).1, st4 4 (by decide), h4])
        (by rw [(gout 4 (by decide) (by decide)).2, sh4 4 (by decide) (by decide) (by decide)])
        (by rw [(gout 5 (by decide) (by decide)).1, st4 5 (by decide), h5])
        (by rw [(gout 5 (by decide) (by decide)).2, sh4 5 (by decide) (by decide) (by decide)])
        (by rw [(gout 6 (by decide) (by decide)).1, st4 6 (by decide), h6])
        (by rw [(gout 6 (by decide) (by decide)).2, sh4 6 (by decide) (by decide) (by decide)])
        gv9 (by rw [gval _ (nfr _ (by simp)), v42]) (by rw [gval _ (nfr _ (by simp)), v43])
        (fun r hr => by
          unfold popLive at hr
          by_cases hf : ∃ k, frG k = r
          · obtain ⟨k, rfl⟩ := hf
            exact gvz k (fun e => hr (by right; right; right; right; rw [e]))
          · simp only [not_exists] at hf
            rw [gval r hf]
            exact v4z r (fun e => hr (by left; exact e)) (fun e => hr (by right; left; exact e))
              (fun e => hr (by right; right; left; exact e)) (fun e => hr (by right; right; right; left; exact e)))
        (by omega)
      refine ⟨ω2, WExec.ifrT (by rw [v42]; omega) (WExec.seq g1 p2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [(pout 0 (by decide) (by decide) (by decide)).1, gst0, st4 0 (by decide)]
      · rw [(pout 2 (by decide) (by decide) (by decide)).1, (gout 2 (by decide) (by decide)).1, st4 2 (by decide)]
      · rw [(pout 7 (by decide) (by decide) (by decide)).1, (gout 7 (by decide) (by decide)).1, st4 7 (by decide)]
      · rw [(pout 3 (by decide) (by decide) (by decide)).1, (gout 3 (by decide) (by decide)).1, st43]
      · rw [if_pos hc0, (pout 1 (by decide) (by decide) (by decide)).1, gst1]
      · rw [if_pos hc0, pst4]
      · rw [if_pos hc0, pst5]
      · rw [if_pos hc0, pst6]
      · rw [pv0, gval _ (nfr _ (by simp)), v40]
      · rw [pv1, gval _ (nfr _ (by simp)), v41]
      · exact pv3
      · exact pvz
      · rw [pcell, gcell, c4]
    · have hc00 : c = 0 := by omega
      refine ⟨σ4, WExec.mono (WExec.ifrF (by rw [v42, hc00]) (WExec.skip σ4)) (by omega), st4 0 (by decide),
        st4 2 (by decide),
        st4 7 (by decide), st43, ?_, ?_, ?_, ?_, v40, v41, v43, ?_, c4⟩
      · rw [if_neg hc0, st4 1 (by decide), h1]
      · rw [if_neg hc0, st4 4 (by decide), h4]
      · rw [if_neg hc0, st4 5 (by decide), h5]; simp
      · rw [if_neg hc0, st4 6 (by decide), h6]; simp
      · intro r a b d
        by_cases e2 : r = Wm 2
        · subst e2; rw [v42, hc00]
        · exact v4z r a b e2 d
  obtain ⟨ω, k5, kst0, kst2, kst7, kst3, kst1, kst4, kst5, kst6, kv0, kv1, kv3, kvz, kcell⟩ := key
  -- 6–8. clear X, Q, CB
  have s6 := wclear_spec cap (Wm 0) x ω kv0 (by rw [kv0]; omega)
  have s7 := wclear_spec cap (Wm 1) q (ω.setv (Wm 0) 0) (by simp [show Wm 1 ≠ Wm 0 by decide, kv1])
    (by simp [show Wm 1 ≠ Wm 0 by decide, kv1]; omega)
  have s8 := wclear_spec cap (Wm 3) cb ((ω.setv (Wm 0) 0).setv (Wm 1) 0)
    (by simp [show Wm 3 ≠ Wm 0 by decide, show Wm 3 ≠ Wm 1 by decide, kv3])
    (by simp [show Wm 3 ≠ Wm 0 by decide, show Wm 3 ≠ Wm 1 by decide, kv3]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq k5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_, kst0, kst2, kst7, kst3, kst1, kst4, kst5, kst6, ?_, kcell⟩
  · unfold roundC; omega
  · intro r
    simp only [WState.setv_val, Function.update_apply]
    by_cases a3 : r = Wm 3
    · simp [a3]
    by_cases a1 : r = Wm 1
    · simp [a1, show Wm 1 ≠ Wm 3 by decide]
    by_cases a0 : r = Wm 0
    · simp [a0, show Wm 0 ≠ Wm 3 by decide, show Wm 0 ≠ Wm 1 by decide]
    simp only [a3, a1, a0, if_false]
    exact kvz r a0 a1 a3

end NearCubicWires.WireExponent3_5.UnionMachine.C1RoundW
