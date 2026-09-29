import Proof.Wire_3_5.UnionMachine.CWParTimeB
import Proof.Wire_3_5.UnionMachine.CWPack

/-! # C6 front, U5, the code writers: the parity writers

"Constants, complemented atoms, and the systematic encoding parity are permitted at the same fixed description
envelope" (P3:3092-3094): the union setup's encoding parity of a variable with support `S` is `unionParityAtom m q S`. The parity writer of class mode `m` reads the bitmap of `S` and writes the atom's code:
* **`par_ready`**: the core (`CWParCore.parCoreM`) with any top whose run, fuel and codes are bounded, as a ready run
  within `9^149·(n+q+1)^148` (the fuel `core_y` and the lengths `ready_lengths`);
* **`symPar_ready`**, **`thrPar_ready`**: at the `SYM∘THR` and `THR∘THR` tops, the code written is
  `natWord (Mode.code m (unionParityAtom m q S))` (`CWParSem.sym_code`, `thr_code`);
* **`parityWriters : ∀ m, ParityWriterJ m`** (the `parity` field of `CWIface.WritersJ`).

Paper quantity of the main types: the code of the encoding parity atom of each class mode. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Transfer (unionParityAtom)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (accOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (WLv P3v)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf (sufCode)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCore (parCoreM coreIn topIn parCore_step)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTops (topSymM topSymIn topSymCost topSym_step topSv
  topThrM topThrIn topThrCost topThr_step topTv)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParYb
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTimeB
open NearCubicWires.WireExponent3_5.UnionMachine.CWParFit (CP cwP loop_fit)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- The parity writers' time coefficient. -/
def Kp : ℕ := 9 ^ 149

/-- The parity writers' time degree. -/
def dp : ℕ := 148

theorem inBank_core (tT : ℕ) (l : List Bool) : inBank (⟨0, by omega⟩ : Fin (1300 + tT)) l = coreIn tT l := by
  funext j; unfold inBank coreIn
  by_cases h : j.val = 0
  · rw [if_pos (Fin.ext h), if_pos h]
  · rw [if_neg (fun e => h (by rw [e])), if_neg h]

theorem outBank_core (tT : ℕ) (u v : List Bool) (tout : Fin (1300 + tT) → List Bool)
    (h0 : tout ⟨0, by omega⟩ = frame u) (h1 : tout ⟨1, by omega⟩ = frame v) :
    outBankJ ⟨0, by omega⟩ ⟨1, by omega⟩ u v tout = tout := by
  funext j; unfold outBankJ
  by_cases e0 : j = ⟨0, by omega⟩
  · rw [if_pos e0, e0, h0]
  · rw [if_neg e0]
    by_cases e1 : j = ⟨1, by omega⟩
    · rw [if_pos e1, e1, h1]
    · rw [if_neg e1]

/-- The fuel against the interface's polynomial. -/
theorem fuel_fit (n q c : ℕ) (hq : n = q) (hc : c ≤ (9 * n + 9) ^ 148) :
    c + 1 ≤ Kp * (n + q + 1) ^ dp ∧ 2 * n + 1 ≤ Kp * (n + q + 1) ^ dp := by
  have eY : (9 * n + 9) ^ 148 = 9 ^ 148 * (n + 1) ^ 148 := by
    rw [show 9 * n + 9 = 9 * (n + 1) by ring, mul_pow]
  have hP : (n + 1) ^ 148 ≤ (n + q + 1) ^ 148 := Nat.pow_le_pow_left (by omega) _
  have hP1 : 1 ≤ (n + q + 1) ^ 148 := Nat.one_le_pow _ _ (by omega)
  have hP2 : 2 * n + 1 ≤ (n + q + 1) ^ 148 :=
    (show 2 * n + 1 ≤ n + q + 1 by omega).trans (Nat.le_self_pow (by norm_num) _)
  have e9 : (1 : ℕ) ≤ 9 ^ 148 := Nat.one_le_pow _ _ (by norm_num)
  rw [eY] at hc
  unfold Kp dp
  rw [pow_succ]
  generalize (n + 1) ^ 148 = A at *
  generalize (n + q + 1) ^ 148 = P at *
  generalize (9 : ℕ) ^ 148 = K at *
  have m1 : K * A ≤ K * P := Nat.mul_le_mul_left _ hP
  have m2 : P ≤ K * P := Nat.le_mul_of_pos_left _ (by omega)
  have e : K * 9 * P = 9 * (K * P) := by ring
  rw [e]
  omega

/-- **The parity writer's run** with any top: a ready run within `Kp·(n+q+1)^dp`, the bitmap kept on tape `0`, the
code on tape `1`. -/
theorem par_ready {tT sT : ℕ} (topM : Machine tT sT) (aT bT : ℕ) (haT : 1 ≤ aT) (hbT : 1 ≤ bT) (haTb : aT < tT)
    (hbTb : bT < tT) (hab : aT ≠ bT) (topv ctop : ℕ → ℕ) (tagv : ℕ)
    (htop : ∀ k, ∃ out : Fin tT → List Bool, Step topM (ctop k) (fun _ => 0) (topIn tT k) (fun _ => 0) out ∧
      out ⟨0, by omega⟩ = CompareMachine.word k ∧ out ⟨aT, haTb⟩ = frame (topv k).bits ∧
      out ⟨bT, hbTb⟩ = frame tagv.bits)
    (hct : ∀ Y k : ℕ, 9 ≤ Y → 9 * k + 9 ≤ Y → ctop k ≤ Y ^ 44)
    (htv : ∀ Y k : ℕ, 9 ≤ Y → 9 * k + 9 ≤ Y → (topv k).bits.length ≤ Y ^ 20)
    (htg : ∀ Y : ℕ, 9 ≤ Y → tagv.bits.length ≤ Y ^ 20) (l : List Bool) (q : ℕ) (hq : l.length = q) :
    ∃ J : Fin (1300 + tT) → List Bool, (∀ j, (J j).length ≤ Kp * (l.length + q + 1) ^ dp) ∧
      ClockJoin.ReadyRun (parCoreM CP topM aT bT haTb hbTb) (Kp * (l.length + q + 1) ^ dp)
        (inBank ⟨0, by omega⟩ l)
        (outBankJ ⟨0, by omega⟩ ⟨1, by omega⟩ l
          (natWord (sufCode (accOf (WLv l) (P3v l) (l.count true)) (l.count true) (topv (l.count true)) tagv)) J) := by
  obtain ⟨f1, f2, f3⟩ := loop_fit l
  have hk : l.count true ≤ l.length := List.count_le_length
  have hY : 9 ≤ 9 * l.length + 9 := by omega
  have hkY : 9 * l.count true + 9 ≤ 9 * l.length + 9 := by omega
  obtain ⟨out, st, o0, o1⟩ := parCore_step l CP (cwP l.length) f1 f2 f3 topM aT bT haT hbT haTb hbTb hab
    (topv (l.count true)) tagv (ctop (l.count true)) (htop (l.count true))
  have hcost := core_y l (9 * l.length + 9) rfl (ctop (l.count true)) (topv (l.count true)) tagv
    (hct _ _ hY hkY) (htv _ _ hY hkY) (htg _ hY)
  have hr := FrontKit.ready_of_step st
  have hlen := NearCubicWires.WireExponent3_5.Transfer.ready_lengths hr (2 * l.length + 1) (by
    intro i; unfold coreIn; split_ifs
    · rw [CWParSize.frame_len]
    · simp)
  obtain ⟨g1, g2⟩ := fuel_fit l.length q _ hq hcost
  refine ⟨out, fun j => (hlen j).trans (max_le g2 g1), ?_⟩
  rw [inBank_core, outBank_core tT _ _ out o0 o1]
  exact ClockJoin.enlarge _ _ _ _ _ hr (by omega)

/-! ## The two class modes -/

/-- **The `SYM∘THR` parity writer's machine.** -/
noncomputable def symParM := parCoreM CP topSymM 133 135 (by norm_num) (by norm_num)

/-- **The `THR∘THR` parity writer's machine.** -/
noncomputable def thrParM := parCoreM CP topThrM 493 495 (by norm_num) (by norm_num)

theorem bitmap_length {q : ℕ} (S : Finset (Fin q)) : (bitmap S).length = q := by simp [bitmap]

/-- **The `SYM∘THR` parity writer's run**: the code of `unionParityAtom .sym q S`. -/
theorem symPar_ready (q : ℕ) (S : Finset (Fin q)) :
    ∃ J : Fin (1300 + 136) → List Bool, (∀ j, (J j).length ≤ Kp * ((bitmap S).length + q + 1) ^ dp) ∧
      ClockJoin.ReadyRun symParM (Kp * ((bitmap S).length + q + 1) ^ dp) (inBank 0 (bitmap S))
        (outBankJ 0 1 (bitmap S) (natWord (Mode.code .sym (unionParityAtom .sym q S))) J) := by
  obtain ⟨J, hJ, hr⟩ := par_ready topSymM 133 135 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) topSv topSymCost 0 (fun k => topSym_step k)
    (fun Y k hY hk => yle hY (by norm_num) (topSym_y hY k hk))
    (fun Y k hY hk => yle hY (by norm_num) (topSv_y hY k hk))
    (fun Y _ => CWParTime.zero_bits_y 20) (bitmap S) q (bitmap_length S)
  have e : sufCode (accOf (WLv (bitmap S)) (P3v (bitmap S)) ((bitmap S).count true)) ((bitmap S).count true)
      (topSv ((bitmap S).count true)) 0 = Mode.code .sym (unionParityAtom .sym q S) := CWParSem.sym_code S
  rw [e] at hr
  exact ⟨J, hJ, hr⟩

theorem three_bits_y {Y : ℕ} (hY : 9 ≤ Y) : (3 : ℕ).bits.length ≤ Y ^ 20 := by
  have h : (3 : ℕ).bits.length = 2 := by decide
  have := yle hY (show 1 ≤ 20 by norm_num) (yc hY 2 1 (by norm_num))
  omega

/-- **The `THR∘THR` parity writer's run**: the code of `unionParityAtom .thr q S`. -/
theorem thrPar_ready (q : ℕ) (S : Finset (Fin q)) :
    ∃ J : Fin (1300 + 497) → List Bool, (∀ j, (J j).length ≤ Kp * ((bitmap S).length + q + 1) ^ dp) ∧
      ClockJoin.ReadyRun thrParM (Kp * ((bitmap S).length + q + 1) ^ dp) (inBank 0 (bitmap S))
        (outBankJ 0 1 (bitmap S) (natWord (Mode.code .thr (unionParityAtom .thr q S))) J) := by
  obtain ⟨J, hJ, hr⟩ := par_ready topThrM 493 495 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) topTv topThrCost 3 (fun k => topThr_step k)
    (fun Y k hY hk => topThr_y hY k hk)
    (fun Y k hY hk => topTv_y hY k hk)
    (fun Y hY => three_bits_y hY) (bitmap S) q (bitmap_length S)
  have e : sufCode (accOf (WLv (bitmap S)) (P3v (bitmap S)) ((bitmap S).count true)) ((bitmap S).count true)
      (topTv ((bitmap S).count true)) 3 = Mode.code .thr (unionParityAtom .thr q S) := CWParSem.thr_code S
  rw [e] at hr
  exact ⟨J, hJ, hr⟩

/-! ## The writers -/

/-- **The `SYM∘THR` parity writer.** -/
noncomputable def symParityWriter : ParityWriterJ .sym :=
  CWPack.parityWriterOf .sym symParM 0 1 (by decide) Kp dp symPar_ready

/-- **The `THR∘THR` parity writer.** -/
noncomputable def thrParityWriter : ParityWriterJ .thr :=
  CWPack.parityWriterOf .thr thrParM 0 1 (by decide) Kp dp thrPar_ready

/-- **The parity writers of both class modes** (the `parity` field of `CWIface.WritersJ`). -/
noncomputable def parityWriters : (m : Mode) → ParityWriterJ m
  | .sym => symParityWriter
  | .thr => thrParityWriter

end NearCubicWires.WireExponent3_5.UnionMachine.CWParReady
