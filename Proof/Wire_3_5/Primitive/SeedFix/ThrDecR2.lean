import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR1

/-! # THR decode front, RADIX part 2: the docks' inputs on the unit's scratch tapes

At a RADIX unit, before the docks (`ThrDecR1`): the count `V = |w| + (n+1)^{26} + n + 40 + C_N·(n + cap_T + 1)^{D_N}`
(`TF2Ok`'s request-split bounds at `L = (n+1)^{26}`, and W6's capacity need `need (n + cap_T) ≤ C_N(n+cap_T+1)^{D_N}`,
`NumsPort4.need_poly`) computed in registers, then `1^V`, `1^{|carriers|}`, `1^{cap_T}` written on the scratch tapes
`bT`, `bT + 1`, `bT + 2` (`HashCell.wrU_spec`), heads back at `0`, and the RADIX marker `rRadK := 1`.

* `tV`, **`tf2ok_tV`** (`TF2Ok` at `tV`), `need_le_tV`;
* `tVAW`, `tVBW`, `tVW`, **`tV_run`**; `sVx`, `pbPreW`, **`pbPre_run`** (the docks' entry `DockInT`).

Paper quantities of the main types: the front end's and the numbers machine's inputs at the THR call (P3:2543-2558,
3071-3091). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum

/-- **The docks' count.** -/
def tV (len n capT Cn Dn : ℕ) : ℕ := len + (n + 1) ^ 26 + n + 40 + (n + capT + 1) ^ Dn * Cn

theorem nbl_le_succ'' (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    have h2 : Nat.log 2 x < 2 ^ Nat.log 2 x := Nat.lt_two_pow_self
    omega

theorem natWord_le_reqW (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    (∀ c ∈ codes, (RepairRepresentation.natWord c).length ≤ (Data.reqW n mb codes cc tl).length) ∧
    (∀ c ∈ cc, (RepairRepresentation.natWord c).length ≤ (Data.reqW n mb codes cc tl).length) := by
  constructor
  · intro c hc
    have h1 : (RepairRepresentation.natWord c).length ≤ (codes.flatMap RepairRepresentation.natWord).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
    unfold Data.reqW; simp only [List.length_append]; omega
  · intro c hc
    have h1 : (RepairRepresentation.natWord c).length ≤ (cc.flatMap RepairRepresentation.natWord).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
    unfold Data.reqW RepairRepresentation.natListWord; simp only [List.length_append]; omega

/-- **`TF2Ok` at the docks' count.** -/
theorem tf2ok_tV {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (cc : List ℕ) (tl : List Bool)
    (ha : a' ≤ 4) (hk : cc.length ≤ 2) (capT Cn Dn : ℕ) :
    PrimThrW.TopFront2.TF2Ok Cs cc
      (tV (Data.reqW n true (ReqBridge.thrCodes Cs) cc tl).length n capT Cn Dn) := by
  obtain ⟨hx, hy⟩ := natWord_le_reqW n true (ReqBridge.thrCodes Cs) cc tl
  unfold tV
  set m := (Data.reqW n true (ReqBridge.thrCodes Cs) cc tl).length with hm
  have hA : natBitLength a' ≤ 5 := (nbl_le_succ'' a').trans (by omega)
  have hK : natBitLength cc.length ≤ 3 := (nbl_le_succ'' _).trans (by omega)
  have hA' : 2 ^ (natBitLength a' + 1) ≤ 64 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega : natBitLength a' + 1 ≤ 6)).trans (by norm_num)
  have hK' : 2 ^ (natBitLength cc.length + 1) ≤ 16 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega : natBitLength cc.length + 1 ≤ 4)).trans (by norm_num)
  have hN := nbl_le_succ'' n
  refine ⟨hk, by omega, by omega, by omega, fun y hym => ?_, fun y hym => ?_⟩
  · have := hx y hym; omega
  · have := hy y hym; omega

theorem need_le_tV {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
    (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (len n capT : ℕ) :
    N.need (n + capT) ≤ tV len n capT N.Cn N.Dn := by
  have h := N.need_poly (n + capT)
  unfold ValidatorPolynomialDomination.PolyBounded at h
  unfold tV
  rw [Nat.mul_comm] at h
  omega

def tQ26 : Fin 5 ↪ Fin LNR := ⟨![H 21, H 22, H 23, H 24, H 25], by decide⟩
def tQD : Fin 5 ↪ Fin LNR := ⟨![H 21, H 22, H 23, H 24, H 25], by decide⟩
def tQM : Fin 5 ↪ Fin LNR := ⟨![H 22, H 23, H 24, H 25, H 26], by decide⟩
@[simp] theorem tQ26_apply (i : Fin 5) : tQ26 i = ![H 21, H 22, H 23, H 24, H 25] i := rfl
@[simp] theorem tQD_apply (i : Fin 5) : tQD i = ![H 21, H 22, H 23, H 24, H 25] i := rfl
@[simp] theorem tQM_apply (i : Fin 5) : tQM i = ![H 22, H 23, H 24, H 25, H 26] i := rfl

section R2
variable (cap : ℕ) (x : ℕ)

/-- The count, part A: `H 20 := |w| + (n+1)^{26} + n + 40`, `H 21 := n + cap_T + 1`. -/
def tVAW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (LEN) (H 20) (TM)) (.seq (FinalPass.Hash4.wcopyR (dN) (H 21) (TM)) (.seq (.inc (H 21)) (.seq (UnaryPow.powConstW tQ26 26) (.seq (addTo (H 22) (H 20) (TM)) (.seq (WM.clear (H 22)) (.seq (WM.clear (H 21)) (.seq (addTo (dN) (H 20) (TM)) (.seq (StarNums.incN (H 20) 40) (.seq (FinalPass.Hash4.wcopyR (dN) (H 21) (TM)) (.seq (addTo (Hb 1) (H 21) (TM)) ((.inc (H 21)))))))))))))

def tVAOut (σ : WState (LNS x) LNR) (len n capT : ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0))).setv (H 20) (len + (n + 1) ^ 26 + n))).setv (H 20) (len + (n + 1) ^ 26 + n + 40))).setv (H 21) (n))).setv (H 21) (n + capT))).setv (H 21) (n + capT + 1))

theorem tVA_run (σ : WState (LNS x) LNR) (len n capT : ℕ) (hL : σ.val LEN = len) (hN : σ.val dN = n)
    (h1 : σ.val (Hb 1) = capT) (zH : ∀ k : Fin 40, 20 ≤ k.val → σ.val (H k) = 0) (zT : σ.val TM = 0)
    (hc : len + (n + 1) ^ 26 * 2 + n + capT + 42 ≤ cap) :
    WExec cap (tVAW x) σ (tVAOut x σ len n capT) (133 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hp : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have zH20 := zH 20 (by decide)
  have zH21 := zH 21 (by decide)
  have zH22 := zH 22 (by decide)
  have zH23 := zH 23 (by decide)
  have zH24 := zH 24 (by decide)
  have zH25 := zH 25 (by decide)
  unfold tVAW tVAOut
  exact (seqD cap 133 1 (copy1 cap (LEN) (H 20) (TM) (by decide) (by decide) (by decide) (len) σ (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (dN) (H 21) (TM) (by decide) (by decide) (by decide) (n) ((σ).setv (H 20) (len)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (inc1 cap (H 21) (n) ((((σ).setv (H 20) (len))).setv (H 21) (n)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 108 (pow1 cap tQ26 (n + 1) 26 ((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap (H 22) (H 20) (TM) (by decide) (by decide) (by decide) ((n + 1) ^ 26) (len) ((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (H 22) ((n + 1) ^ 26) ((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (H 21) (n + 1) ((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap (dN) (H 20) (TM) (by decide) (by decide) (by decide) (n) (len + (n + 1) ^ 26) ((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (FiltNum.incN1 cap (H 20) (len + (n + 1) ^ 26 + n) 40 ((((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0))).setv (H 20) (len + (n + 1) ^ 26 + n)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (dN) (H 21) (TM) (by decide) (by decide) (by decide) (n) ((((((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0))).setv (H 20) (len + (n + 1) ^ 26 + n))).setv (H 20) (len + (n + 1) ^ 26 + n + 40)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap (Hb 1) (H 21) (TM) (by decide) (by decide) (by decide) (capT) (n) ((((((((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0))).setv (H 20) (len + (n + 1) ^ 26 + n))).setv (H 20) (len + (n + 1) ^ 26 + n + 40))).setv (H 21) (n)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (inc1 cap (H 21) (n + capT) ((((((((((((((((((((((σ).setv (H 20) (len))).setv (H 21) (n))).setv (H 21) (n + 1))).setv (H 22) ((n + 1) ^ 26))).setv (H 20) (len + (n + 1) ^ 26))).setv (H 22) (0))).setv (H 21) (0))).setv (H 20) (len + (n + 1) ^ 26 + n))).setv (H 20) (len + (n + 1) ^ 26 + n + 40))).setv (H 21) (n))).setv (H 21) (n + capT)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, hL, hN, h1, zH, zT]) (by omega)) rfl (by omega) (by omega)))))))))))))

/-- The count, part B (after `H 22 := (n + cap_T + 1)^{D_N}`): `H 20 := V`, `H 21`, `H 22`, `H 23` back at `0`. -/
def tVBW (Cn : ℕ) : WM (LNS x) LNR :=
  .seq (StarNums.incN (H 23) (Cn)) (.seq (mulByW tQM) (.seq (WM.clear (H 23)) (.seq (addTo (H 22) (H 20) (TM)) (.seq (WM.clear (H 22)) ((WM.clear (H 21)))))))

def tVBOut (σ : WState (LNS x) LNR) (len n capT Cn Dn : ℕ) : WState (LNS x) LNR :=
  ((((((((((((σ).setv (H 23) ((Cn)))).setv (H 22) (((n + capT + 1) ^ Dn) * (Cn)))).setv (H 23) (0))).setv (H 20) (len + (n + 1) ^ 26 + n + 40 + (n + capT + 1) ^ Dn * Cn))).setv (H 22) (0))).setv (H 21) (0))

theorem tVB_run (σ : WState (LNS x) LNR) (len n capT Cn Dn : ℕ)
    (h20 : σ.val (H 20) = len + (n + 1) ^ 26 + n + 40) (h21 : σ.val (H 21) = n + capT + 1)
    (h22 : σ.val (H 22) = (n + capT + 1) ^ Dn) (zH : ∀ k : Fin 40, 23 ≤ k.val → σ.val (H k) = 0)
    (zT : σ.val TM = 0) (hCn : Cn ≤ cap) (hPD : (n + capT + 1) ^ Dn ≤ cap)
    (hc : tV len n capT Cn Dn + n + capT + 42 ≤ cap) :
    WExec cap (tVBW x Cn) σ (tVBOut x σ len n capT Cn Dn) (16 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  unfold tV at hc
  have zH23 := zH 23 (by decide)
  have zH24 := zH 24 (by decide)
  have zH25 := zH 25 (by decide)
  have zH26 := zH 26 (by decide)
  unfold tVBW tVBOut
  exact (seqD cap 16 1 (incN0 cap (H 23) (Cn) σ (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 3 (mulBy1 cap tQM ((n + capT + 1) ^ Dn) (Cn) ((σ).setv (H 23) ((Cn))) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (H 23) (Cn) ((((σ).setv (H 23) ((Cn)))).setv (H 22) (((n + capT + 1) ^ Dn) * (Cn))) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap (H 22) (H 20) (TM) (by decide) (by decide) (by decide) ((n + capT + 1) ^ Dn * Cn) (len + (n + 1) ^ 26 + n + 40) ((((((σ).setv (H 23) ((Cn)))).setv (H 22) (((n + capT + 1) ^ Dn) * (Cn)))).setv (H 23) (0)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (H 22) ((n + capT + 1) ^ Dn * Cn) ((((((((σ).setv (H 23) ((Cn)))).setv (H 22) (((n + capT + 1) ^ Dn) * (Cn)))).setv (H 23) (0))).setv (H 20) (len + (n + 1) ^ 26 + n + 40 + (n + capT + 1) ^ Dn * Cn)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (clear1 cap (H 21) (n + capT + 1) ((((((((((σ).setv (H 23) ((Cn)))).setv (H 22) (((n + capT + 1) ^ Dn) * (Cn)))).setv (H 23) (0))).setv (H 20) (len + (n + 1) ^ 26 + n + 40 + (n + capT + 1) ^ Dn * Cn))).setv (H 22) (0)) (by simp [Function.update_apply, Fin.ext_iff, H_val, Hb_val, rv_TM', rv_dN', rv_LEN', tQ26_apply, tQD_apply, tQM_apply, h20, h21, h22, zH, zT]) (by omega)) rfl (by omega) (by omega)))))))

/-- **The count** `H 20 := V`. -/
def tVW (Cn Dn : ℕ) : WM (LNS x) LNR := .seq (tVAW x) (.seq (UnaryPow.powConstW tQD Dn) (tVBW x Cn))

/-- **The count, run**: `H 20 = tV`, `H 21 … H 26` back at `0`, everything else kept. -/
theorem tV_run (σ : WState (LNS x) LNR) (len n capT Cn Dn : ℕ) (hL : σ.val LEN = len) (hN : σ.val dN = n)
    (h1 : σ.val (Hb 1) = capT) (zH : ∀ k : Fin 40, 20 ≤ k.val → σ.val (H k) = 0) (zT : σ.val TM = 0)
    (hcA : len + (n + 1) ^ 26 * 2 + n + capT + 42 ≤ cap) (hCn : Cn ≤ cap) (hPD : (n + capT + 1) ^ Dn ≤ cap)
    (hcB : tV len n capT Cn Dn + n + capT + 42 ≤ cap) :
    ∃ τ, WExec cap (tVW x Cn Dn) σ τ (133 * UnaryPow.sq cap + 1 + ((Dn + 1) * (4 * UnaryPow.sq cap) + 1 +
        16 * UnaryPow.sq cap)) ∧
      τ.val (H 20) = tV len n capT Cn Dn ∧ (∀ r, r ≠ H 20 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have e1 := tVA_run cap x σ len n capT hL hN h1 zH zT hcA
  set σA := tVAOut x σ len n capT with hσA
  have kA : ∀ r, (∀ k : Fin 40, r ≠ H k) → σA.val r = σ.val r := fun r hr => by
    rw [hσA]; unfold tVAOut; simp [Function.update_apply, hr]
  have a20 : σA.val (H 20) = len + (n + 1) ^ 26 + n + 40 := by
    rw [hσA]; unfold tVAOut; simp [Function.update_apply, Fin.ext_iff, H_val]
  have a21 : σA.val (H 21) = n + capT + 1 := by
    rw [hσA]; unfold tVAOut; simp [Function.update_apply, Fin.ext_iff, H_val]
  have aH : ∀ k : Fin 40, 22 ≤ k.val → σA.val (H k) = 0 := fun k hk => by
    rw [hσA]; unfold tVAOut
    have : ∀ i : ℕ, i ≤ 21 → k.val ≠ i := fun i hi => by omega
    by_cases h22 : k.val = 22
    · simp [Function.update_apply, Fin.ext_iff, H_val, h22]
    · simp [Function.update_apply, Fin.ext_iff, H_val, this 20 (by omega), this 21 (by omega), h22]
      exact zH k (by omega)
  have e2 := pow1 cap tQD (n + capT + 1) Dn σA (by simpa using a21) (by simpa using aH 22 (by decide))
    (by simpa using aH 23 (by decide)) (by simpa using aH 24 (by decide)) (by simpa using aH 25 (by decide))
    (by omega) (by unfold tV at hcB; omega) hPD
  have e22 : tQD 1 = H 22 := rfl
  rw [e22] at e2
  set σP := σA.setv (H 22) ((n + capT + 1) ^ Dn) with hσP
  have e3 := tVB_run cap x σP len n capT Cn Dn (by rw [hσP]; simp [Function.update_apply, Fin.ext_iff, H_val, a20])
    (by rw [hσP]; simp [Function.update_apply, Fin.ext_iff, H_val, a21]) (by rw [hσP]; simp)
    (fun k hk => by
      rw [hσP, WState.setv_val]
      have : k ≠ 22 := fun e => by rw [e] at hk; simp at hk
      rw [Function.update_of_ne (fun e => this (H.injective e))]
      exact aH k (by omega))
    (by rw [hσP, WState.setv_val, Function.update_of_ne (by decide)]
        rw [kA _ (fun k => H_ne k TM (by rw [rv_TM']; omega))]; exact zT) hCn hPD hcB
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_⟩
  · unfold tVBOut tV; simp [Function.update_apply, Fin.ext_iff, H_val]
  · intro r hr
    by_cases hH : ∃ k : Fin 40, r = H k
    · obtain ⟨k, rfl⟩ := hH
      have hk20 : k ≠ 20 := fun e => hr (by rw [e])
      unfold tVBOut
      simp only [WState.setv_val, tQM_apply, tQD_apply]
      by_cases h21 : k.val = 21
      · simp [Function.update_apply, Fin.ext_iff, H_val, h21]; exact (zH k (by omega)).symm
      by_cases h22 : k.val = 22
      · simp [Function.update_apply, Fin.ext_iff, H_val, h22]; exact (zH k (by omega)).symm
      by_cases h23 : k.val = 23
      · simp [Function.update_apply, Fin.ext_iff, H_val, h23]; exact (zH k (by omega)).symm
      have hk20' : k.val ≠ 20 := fun e => hk20 (Fin.ext e)
      simp [Function.update_apply, Fin.ext_iff, H_val, hk20', h21, h22, h23, hσP, hσA]
      unfold tVAOut
      simp [Function.update_apply, Fin.ext_iff, H_val, hk20', h21, h22]
    · have hH' : ∀ k : Fin 40, r ≠ H k := fun k e => hH ⟨k, e⟩
      unfold tVBOut
      simp [Function.update_apply, hH', hσP]
      exact kA r hH'
  · unfold tVBOut; simp [hσP, hσA]; unfold tVAOut; simp
  · unfold tVBOut; simp [hσP, hσA]; unfold tVAOut; simp
  · unfold tVBOut; simp [hσP, hσA]; unfold tVAOut; simp

end R2

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
