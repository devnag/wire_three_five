import Proof.Wire_3_5.FinalPass.S5TPre4
import Proof.Wire_3_5.Primitive.Writers.DataSetup

/-! # S5-THR, part 5: the request's head fields and the mode (P3:3083-3086)

The THR half reads, from the framed input `frame (reqW n mb codes cc tl)` on stream `I` (the call's word and its
seed word, `ReqBridge`), the length `n`, the mode bit `mb` (THR iff `true`) and the tuple size `a = |codes|` into
registers (PA's `ParseNat.readNatM`), then returns the input's head to `0` without a counter: in lockstep with the
template `T = sent (|w|+1)` of the prelude (`rewLock2`, two input cells per template cell).

* `fwdEnd_spec` (a head to the end of `sent c`); **`rewIn_spec`** (the input's head from anywhere up to `2(c)` back
  to `0`, the template's too); **`parseW_spec`**.

Paper quantities of the main type: the call's `n`, mode and tuple size (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec enc stp off enc_length read_enc_bit
  natWord_length)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The input's head back to `0` through the template -/

theorem fwdLoop_spec (S : Fin (ns + 1)) (c : ℕ) : ∀ (k : ℕ) (σ : WState ns nr), σ.st S = sent c →
    σ.sh S + k = c + 1 → 1 ≤ σ.sh S → WExec cap (.whs S (.fwd S)) σ (σ.seth S (c + 1)) (3 * k + 1)
  | 0, σ, hs, hp, _ => by
    have hb : wbit σ S = false := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e : σ.seth S (c + 1) = σ := by rw [show c + 1 = σ.sh S by omega, HashSeed.seth_same]
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | k + 1, σ, hs, hp, h1 => by
    have hb : wbit σ S = true := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e1 := WExec.fwd (cap := cap) S σ
    have ih := fwdLoop_spec S c k (σ.seth S (σ.sh S + 1)) (by simpa using hs) (by simp; omega) (by simp)
    refine WExec.cast cap (WExec.whsT hb e1 ih) (by rw [wseth_seth]) (by omega)

/-- A head from `0` to the end of `sent c`. -/
def fwdEnd (S : Fin (ns + 1)) : WM ns nr := .seq (.fwd S) (.whs S (.fwd S))

theorem fwdEnd_spec (S : Fin (ns + 1)) (c : ℕ) (σ : WState ns nr) (hs : σ.st S = sent c) (hp : σ.sh S = 0) :
    WExec cap (fwdEnd S) σ (σ.seth S (c + 1)) (3 * c + 3) := by
  have e1 := WExec.fwd (cap := cap) S σ
  rw [hp] at e1
  have e2 := fwdLoop_spec cap S c c (σ.seth S (0 + 1)) (by simpa using hs) (by simp; omega) (by simp)
  refine WExec.cast cap (WExec.seq e1 e2) (by rw [wseth_seth]) (by omega)

/-- **The input's head back to `0`**: the template to its end, then back in lockstep (two input cells per step). -/
def rewIn (I T : Fin (ns + 1)) : WM ns nr := .seq (fwdEnd T) (.seq (.bwd T) (rewLock2 T I))

theorem rewIn_spec (I T : Fin (ns + 1)) (hIT : I ≠ T) (c : ℕ) (σ : WState ns nr) (hs : σ.st T = sent c)
    (hp : σ.sh T = 0) (hI : σ.sh I ≤ 2 * c) :
    WExec cap (rewIn I T) σ (σ.seth I 0) (10 * c + 7) := by
  have e1 := fwdEnd_spec cap T c σ hs hp
  have e2 := WExec.bwd (cap := cap) T (σ.seth T (c + 1))
  rw [wseth_seth, show (σ.seth T (c + 1)).sh T - 1 = c by simp] at e2
  have e3 := rewLock2_spec cap T I (Ne.symm hIT) c c (σ.seth T c) (by simpa using hs) (by simp) le_rfl
    (by simp [Function.update_apply, hIT]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  rw [wseth_seth, ← hp]
  apply WState.eq
  · funext j
    by_cases hjI : j = I
    · subst hjI; simp [Function.update_apply, hIT]
    · by_cases hjT : j = T
      · subst hjT; simp [Function.update_apply, hjI]
      · simp [Function.update_apply, hjI, hjT]
  · rfl
  · rfl
  · rfl

/-! ## The head fields -/

/-- The parse's registers: `0 f`, `1 c`, `2 n`, `3 a`, `4 p`, `5 t`, `6` the mode flag. -/
abbrev PReg (nr : ℕ) := Fin 7 ↪ Fin nr

/-- **The parse**: `n`, the mode bit, `a`, then the input's head back to `0`. -/
def parseW (I T : Fin (ns + 1)) (R : PReg nr) : WM ns nr :=
  .seq (readNatM true I (R 0) (R 1) (R 2) (R 4) (R 5))
  (.seq (.fwd I) (.seq (.ifs I (.inc (R 6)) .skip) (.seq (.fwd I)
  (.seq (readNatM true I (R 0) (R 1) (R 3) (R 4) (R 5)) (rewIn I T)))))

/-- The parse's cost. -/
def parseCost (n a c : ℕ) : ℕ :=
  (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (1 + 1 + (4 + 1 + (1 + 1 +
    ((natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) + 1 + (10 * c + 7)))))

theorem parseW_spec (I T : Fin (ns + 1)) (hIT : I ≠ T) (R : PReg nr) (n : ℕ) (mb : Bool) (codes cc : List ℕ)
    (tl : List Bool) (c : ℕ) (σ : WState ns nr) (hI : σ.st I = frame (PrimAsm.Data.reqW n mb codes cc tl))
    (hIh : σ.sh I = 0) (hT : σ.st T = sent c) (hTh : σ.sh T = 0)
    (hc : (PrimAsm.Data.reqW n mb codes cc tl).length ≤ c)
    (hz : ∀ j, σ.val (R j) = 0) (hcap : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 1 ≤ cap) :
    WExec cap (parseW I T R) σ
      (((σ.setv (R 2) n).setv (R 3) codes.length).setv (R 6) (if mb then 1 else 0))
      (parseCost n codes.length c) := by
  have hne : ∀ {i j : Fin 7}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hR : ∀ i j : Fin 7, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have he := PrimAsm.Data.enc_reqW n mb codes cc tl
  rw [he] at hI
  obtain ⟨rest, hrest⟩ : ∃ r, r = enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false])))) := ⟨_, rfl⟩
  rw [← hrest] at hI
  have hnl := natWord_length n
  have hal := natWord_length codes.length
  have q1 := Nat.one_le_two_pow (n := natBitLength n)
  have q2 := Nat.one_le_two_pow (n := natBitLength codes.length)
  have q3 : 2 ^ (natBitLength n + 1) = 2 * 2 ^ natBitLength n := by rw [pow_succ]; ring
  have q4 : 2 ^ (natBitLength codes.length + 1) = 2 * 2 ^ natBitLength codes.length := by rw [pow_succ]; ring
  rw [q3, q4] at hcap
  -- 1: n
  have e1 := readNatM_spec cap true I (R 0) (R 1) (R 2) (R 4) (R 5) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) n [] (enc true [mb] ++ rest) σ (by rw [hI]; rfl) (by simpa using hIh)
    (hz 0) (hz 1) (hz 4) (hz 5) (by rw [hz 2, q3]; omega)
  simp only [List.length_nil, Nat.zero_add, hz 2] at e1
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = (σ.seth I (stp true * (RepairRepresentation.natWord n).length)).setv (R 2) n :=
    ⟨_, rfl⟩
  rw [← hσ1] at e1
  have hstp : stp true = 2 := rfl
  -- 2, 3, 4: the mode bit
  have e2 := WExec.fwd (cap := cap) I σ1
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.seth I (σ1.sh I + 1) := ⟨_, rfl⟩
  rw [← hσ2] at e2
  have hb2 : wbit σ2 I = mb := by
    unfold wbit
    rw [hσ2, hσ1]
    simp only [WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh, Function.update_self, hI]
    have h := read_enc_bit true rest [mb] 0 (by simp)
    have h2 := PrimAsm.ParseNat.read_pre (enc true (RepairRepresentation.natWord n)) (enc true [mb] ++ rest) 1
    rw [enc_length] at h2
    rw [h2]
    simpa [stp, off] using h
  have e3 : WExec cap (.ifs I (.inc (R 6)) .skip) σ2 (σ2.setv (R 6) (if mb then 1 else 0)) 4 := by
    cases hmb : mb
    · rw [hmb] at hb2
      have e := WExec.ifsF (cap := cap) (P := .inc (R 6)) hb2 (WExec.skip σ2)
      have hv : σ2.val (R 6) = 0 := by rw [hσ2, hσ1]; simp [Function.update_apply, hR, hz 6]
      refine WExec.mono (WExec.cast cap e ?_ le_rfl) (by omega)
      rw [if_neg (by decide), ← hv, wsetv_same]
    · rw [hmb] at hb2
      have hv : σ2.val (R 6) = 0 := by rw [hσ2, hσ1]; simp [Function.update_apply, hR, hz 6]
      have e := WExec.inc (cap := cap) (R 6) σ2 (by rw [hv]; omega)
      rw [hv] at e
      exact WExec.ifsT hb2 e
  have e4 := WExec.fwd (cap := cap) I (σ2.setv (R 6) (if mb then 1 else 0))
  -- 5: a
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = (σ2.setv (R 6) (if mb then 1 else 0)).seth I
      ((σ2.setv (R 6) (if mb then 1 else 0)).sh I + 1) := ⟨_, rfl⟩
  rw [← hσ4] at e4
  have hsh4 : σ4.sh I = (enc true (RepairRepresentation.natWord n) ++ enc true [mb]).length := by
    rw [hσ4, hσ2, hσ1]; simp [enc_length, stp]; try ring
  have e5 := readNatM_spec cap true I (R 0) (R 1) (R 3) (R 4) (R 5) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) codes.length (enc true (RepairRepresentation.natWord n) ++ enc true [mb])
    (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false])))) σ4
    (by rw [hσ4, hσ2, hσ1]; simp only [WState.seth_st, WState.setv_st, hI, hrest, List.append_assoc])
    hsh4 (by rw [hσ4, hσ2, hσ1]; simp [Function.update_apply, hR, hz 0])
    (by rw [hσ4, hσ2, hσ1]; simp [Function.update_apply, hR, hz 1])
    (by rw [hσ4, hσ2, hσ1]; simp [Function.update_apply, hR, hz 4])
    (by rw [hσ4, hσ2, hσ1]; simp [Function.update_apply, hR, hz 5])
    (by rw [hσ4, hσ2, hσ1, q4]; simp [Function.update_apply, hR, hz 3]; omega)
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = (σ4.seth I ((enc true (RepairRepresentation.natWord n) ++ enc true [mb]).length +
      stp true * (RepairRepresentation.natWord codes.length).length)).setv (R 3)
      (σ4.val (R 3) + codes.length) := ⟨_, rfl⟩
  rw [← hσ5] at e5
  -- 6: back to 0
  have hlen : (PrimAsm.Data.reqW n mb codes cc tl).length ≥
      (RepairRepresentation.natWord n).length + 1 + (RepairRepresentation.natWord codes.length).length := by
    simp [PrimAsm.Data.reqW]; omega
  have e6 := rewIn_spec cap I T hIT c σ5
    (by rw [hσ5, hσ4, hσ2, hσ1]; simpa [Function.update_apply, Ne.symm hIT] using hT)
    (by rw [hσ5, hσ4, hσ2, hσ1]; simp [Function.update_apply, Ne.symm hIT, hTh])
    (by rw [hσ5]; simp [enc_length, stp]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · rw [hσ5, hσ4, hσ2, hσ1]
    apply WState.eq
    · funext j
      by_cases hjI : j = I
      · subst hjI; simp [hIh]
      · simp [Function.update_apply, hjI]
    · rfl
    · funext j
      simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases a2 : j = R 2 <;> by_cases a3 : j = R 3 <;> by_cases a6 : j = R 6 <;> simp_all [hR]
    · rfl
  · unfold parseCost
    have := enc_length true (RepairRepresentation.natWord n)
    omega

end NearCubicWires.WireExponent3_5.FinalPass.S5T
