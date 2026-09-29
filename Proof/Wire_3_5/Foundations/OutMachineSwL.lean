import Proof.Wire_3_5.Foundations.OutMachineSwLK
import Proof.Wire_3_5.FinalPass.SymFront3
import Proof.Wire_3_5.FinalPass.SWParts

/-! # SWl, part 2: **`swL : ∀ l, SWParts.SWlT l`**

The SYM words writer's templates (slots `28 … 31`: `symWords` word `4·3 + j` = `S3.templJ`, the stage-5 template
`levelWord M J W (blank rows of length |G_j|)` of the base list, P3:1449-1477, 1508-1520, 3170-3178) at a SYM request,
from the core's blank entry, on NW's bank `x = DT + 7`:

1. The SYM front `frontM` (`front_run`, `FrontOut`: `M`, `B` in `G 32`, `G 33`, `|G_j|` in `330 + j`);
2. `swlP`: the low registers `0 … 55` cleared; **`numsP`** (`S = ⌈√(64²B)⌉` by `sqrtW`, `J = ⌈log₂B⌉ + 9` by
   `clogW`, into E's `W 0`, `W 1`); `circ` per circuit on the blank streams `sT (DT + 3 + j)`; every
   register cleared.

* `wL`, `qL`, `sL`, `rL`, **`numsP_spec`**, `circCap`, `swlP`, **`swlP_spec`**, **`swl_word`** (slot `12 + j` is `templJ`),
  constants, **`lRun`**, **`swL`**.

Paper quantity of the main type: the SYM call's stage-5 templates (`symWords`, kind `3`, P3:1449-1477,
3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout (LNS LNR sT)
open NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl (tplWord)

/-- E's block: registers `0 … 29`. -/
def wL : Fin 30 ↪ Fin LNR :=
  ⟨fun i => ⟨i.val, by have := i.isLt; show i.val < 512; omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
@[simp] theorem wL_val (i : Fin 30) : (wL i).val = i.val := rfl
theorem wL0 : wL 0 = (0 : Fin LNR) := rfl
theorem wL1 : wL 1 = (1 : Fin LNR) := rfl

/-- `sqrtW` registers `30 … 39`, `clogW` registers `40 … 49`, `mulAddW` registers. -/
def qL : Fin 10 ↪ Fin LNR := ⟨![30, 31, 32, 33, 34, 35, 36, 37, 38, 39], by decide⟩
def sL : Fin 10 ↪ Fin LNR := ⟨![40, 41, 42, 43, 44, 45, 46, 47, 48, 49], by decide⟩
def rL : Fin 5 ↪ Fin LNR := ⟨![51, 50, 30, 52, 53], by decide⟩
@[simp] theorem qL_apply (i : Fin 10) : qL i = ![30, 31, 32, 33, 34, 35, 36, 37, 38, 39] i := rfl
@[simp] theorem sL_apply (i : Fin 10) : sL i = ![40, 41, 42, 43, 44, 45, 46, 47, 48, 49] i := rfl
@[simp] theorem rL_apply (i : Fin 5) : rL i = ![51, 50, 30, 52, 53] i := rfl

theorem sL_low : ∀ i : Fin 10, (sL i).val < 56 := by decide

/-- **`S = ⌈√(64²B)⌉` and `J = ⌈log₂B⌉ + 9`** from `B` in `441`, into `W 0`, `W 1` (scratch `30 … 54` back to `0`). -/
noncomputable def numsP {ns : ℕ} : WM ns LNR :=
  .seq (FinalPass.Hash4.wcopyR 441 (sL 0) 54)
  (.seq (PrimAsm.SymQM.clogW sL)
  (.seq (PrimAsm.StarNums.incN (sL 1) 9)
  (.seq (FinalPass.Hash4.wcopyR (sL 1) (wL 1) 54)
  (.seq (WM.clear (sL 1))
  (.seq (WM.clear (sL 0))
  (.seq (PrimAsm.StarNums.incN (rL 0) 4096)
  (.seq (FinalPass.Hash4.wcopyR 441 (rL 1) 54)
  (.seq (PrimAsm.UnaryArith.mulAddW rL)
  (.seq (WM.clear (rL 0))
  (.seq (WM.clear (rL 1))
  (.seq (PrimAsm.LevelW.sqrtW qL)
  (.seq (FinalPass.Hash4.wcopyR (qL 1) (wL 0) 54)
  (.seq (WM.clear (qL 1)) (WM.clear (qL 0)))))))))))))))

theorem clog_le (B : ℕ) : Nat.clog 2 B ≤ 2 * B ∧ 2 ^ Nat.clog 2 B ≤ 2 * B + 1 := by
  have hp : 2 ^ Nat.clog 2 B ≤ 2 * B + 1 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · have := PrimAsm.LevelW.pow_clog_le B h; omega
  have := Nat.lt_two_pow_self (n := Nat.clog 2 B)
  exact ⟨by omega, hp⟩

theorem sqrt_le (B : ℕ) : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B) ≤ 4096 * B + 1 := by
  have := PrimAsm.LevelW.natCeilSqrt_le (64 ^ 2 * B)
  norm_num at this ⊢; omega

theorem numsCap (B cap : ℕ) (hc : 2 ^ 25 * (B + 10) ^ 2 ≤ cap) :
    (4096 * B + 2) * (4096 * B + 2) + 4096 * B + 10 ≤ cap ∧ 2 * B + 4096 * B + 4096 + 20 ≤ cap := by
  have h1 : (4096 * B + 2) * (4096 * B + 2) + 4096 * B + 10 ≤ 2 ^ 25 * (B + 10) ^ 2 := by nlinarith
  have h2 : B + 10 ≤ (B + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  constructor <;> omega

variable {ns : ℕ} (cap : ℕ)

set_option maxHeartbeats 1000000 in
theorem numsP_spec (σ : WState ns LNR) (B : ℕ) (hB : σ.val 441 = B) (hz : ∀ q : Fin LNR, q.val < 56 → σ.val q = 0)
    (hc : 2 ^ 25 * (B + 10) ^ 2 ≤ cap) :
    ∃ n, n ≤ 7000 * (cap + 2) ^ 3 ∧
      WExec cap numsP σ ((σ.setv 1 (Nat.clog 2 B + 9)).setv 0 (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B))) n := by
  have z0 : σ.val (0 : Fin LNR) = 0 := hz 0 (by decide)
  have z1 : σ.val (1 : Fin LNR) = 0 := hz 1 (by decide)
  have z30 : σ.val (30 : Fin LNR) = 0 := hz 30 (by decide)
  have z31 : σ.val (31 : Fin LNR) = 0 := hz 31 (by decide)
  have z32 : σ.val (32 : Fin LNR) = 0 := hz 32 (by decide)
  have z33 : σ.val (33 : Fin LNR) = 0 := hz 33 (by decide)
  have z34 : σ.val (34 : Fin LNR) = 0 := hz 34 (by decide)
  have z35 : σ.val (35 : Fin LNR) = 0 := hz 35 (by decide)
  have z36 : σ.val (36 : Fin LNR) = 0 := hz 36 (by decide)
  have z37 : σ.val (37 : Fin LNR) = 0 := hz 37 (by decide)
  have z38 : σ.val (38 : Fin LNR) = 0 := hz 38 (by decide)
  have z39 : σ.val (39 : Fin LNR) = 0 := hz 39 (by decide)
  have z40 : σ.val (40 : Fin LNR) = 0 := hz 40 (by decide)
  have z41 : σ.val (41 : Fin LNR) = 0 := hz 41 (by decide)
  have z42 : σ.val (42 : Fin LNR) = 0 := hz 42 (by decide)
  have z43 : σ.val (43 : Fin LNR) = 0 := hz 43 (by decide)
  have z44 : σ.val (44 : Fin LNR) = 0 := hz 44 (by decide)
  have z45 : σ.val (45 : Fin LNR) = 0 := hz 45 (by decide)
  have z46 : σ.val (46 : Fin LNR) = 0 := hz 46 (by decide)
  have z47 : σ.val (47 : Fin LNR) = 0 := hz 47 (by decide)
  have z48 : σ.val (48 : Fin LNR) = 0 := hz 48 (by decide)
  have z49 : σ.val (49 : Fin LNR) = 0 := hz 49 (by decide)
  have z50 : σ.val (50 : Fin LNR) = 0 := hz 50 (by decide)
  have z51 : σ.val (51 : Fin LNR) = 0 := hz 51 (by decide)
  have z52 : σ.val (52 : Fin LNR) = 0 := hz 52 (by decide)
  have z53 : σ.val (53 : Fin LNR) = 0 := hz 53 (by decide)
  have z54 : σ.val (54 : Fin LNR) = 0 := hz 54 (by decide)
  obtain ⟨hc1, hc2⟩ := numsCap B cap hc
  obtain ⟨hcl, _⟩ := clog_le B
  have hsB := sqrt_le B
  have e64 : (64 : ℕ) ^ 2 * B = 4096 * B := by norm_num
  have s1 := PrimAsm.SparseNum.copy1 cap 441 (sL 0) 54 (by decide) (by decide) (by decide) B σ hB (by simp [z40])
    (by simp [z54]) (by omega)
  set σ1 := σ.setv (sL 0) B with hσ1
  have s2 := PrimAsm.SymQM.clogW_spec cap sL σ1 B (by simp [hσ1]) (fun i hi => by
    have hne : sL i ≠ sL 0 := fun e => by have := sL.injective e; subst this; simp at hi
    simp only [hσ1, WState.setv_val, Function.update_apply, if_neg hne]
    exact hz _ (sL_low i)) (by omega)
  set σ2 := σ1.setv (sL 1) (Nat.clog 2 B) with hσ2
  have s3 := PrimAsm.FiltNum.incN1 cap (sL 1) (Nat.clog 2 B) 9 σ2 (by simp [hσ2]) (by omega)
  set σ3 := σ2.setv (sL 1) (Nat.clog 2 B + 9) with hσ3
  have s4 := PrimAsm.SparseNum.copy1 cap (sL 1) (wL 1) 54 (by decide) (by decide) (by decide) (Nat.clog 2 B + 9) σ3
    (by simp [hσ3]) (by simp [hσ3, hσ2, hσ1, Function.update_apply, wL1, z1])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, z54]) (by omega)
  set σ4 := σ3.setv (wL 1) (Nat.clog 2 B + 9) with hσ4
  have s5 := PrimAsm.SparseNum.clear1 cap (sL 1) (Nat.clog 2 B + 9) σ4 (by simp [hσ4, hσ3, Function.update_apply, wL1])
    (by omega)
  set σ5 := σ4.setv (sL 1) 0 with hσ5
  have s6 := PrimAsm.SparseNum.clear1 cap (sL 0) B σ5 (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1])
    (by omega)
  set σ6 := σ5.setv (sL 0) 0 with hσ6
  have s7 := PrimAsm.SparseNum.incN0 cap (rL 0) 4096 σ6
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z51]) (by omega)
  set σ7 := σ6.setv (rL 0) 4096 with hσ7
  have s8 := PrimAsm.SparseNum.copy1 cap 441 (rL 1) 54 (by decide) (by decide) (by decide) B σ7
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, hB])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z50])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z54]) (by omega)
  set σ8 := σ7.setv (rL 1) B with hσ8
  have s9 := PrimAsm.SparseNum.mulAdd1 cap rL 4096 B 0 σ8
    (by simp [hσ8, hσ7, Function.update_apply]) (by simp [hσ8])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z30])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z52])
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z53])
    (by omega) (by omega) (by omega)
  set σ9 := σ8.setv (rL 2) (0 + 4096 * B) with hσ9
  have s10 := PrimAsm.SparseNum.clear1 cap (rL 0) 4096 σ9 (by simp [hσ9, hσ8, hσ7, Function.update_apply]) (by omega)
  set σ10 := σ9.setv (rL 0) 0 with hσ10
  have s11 := PrimAsm.SparseNum.clear1 cap (rL 1) B σ10 (by simp [hσ10, hσ9, hσ8, Function.update_apply]) (by omega)
  set σ11 := σ10.setv (rL 1) 0 with hσ11
  have s12 := PrimAsm.LevelW.sqrtW_spec cap qL σ11 (4096 * B)
    (by simp [hσ11, hσ10, hσ9, Function.update_apply])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z31])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z32])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z33])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z34])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z35])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z36])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z37])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z38])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z39]) hc1
  set σ12 := σ11.setv (qL 1) (CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B)) with hσ12
  have s13 := PrimAsm.SparseNum.copy1 cap (qL 1) (wL 0) 54 (by decide) (by decide) (by decide) (CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B))
    σ12 (by simp [hσ12])
    (by simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL0, wL1, z0])
    (by simp [hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, wL1, z54])
    (by rw [← e64]; omega)
  set σ13 := σ12.setv (wL 0) (CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B)) with hσ13
  have s14 := PrimAsm.SparseNum.clear1 cap (qL 1) (CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B)) σ13
    (by simp [hσ13, hσ12, Function.update_apply, wL0]) (by rw [← e64]; omega)
  set σ14 := σ13.setv (qL 1) 0 with hσ14
  have s15 := PrimAsm.SparseNum.clear1 cap (qL 0) (4096 * B) σ14
    (by simp [hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, Function.update_apply, wL0]) (by omega)
  have hsq : PrimAsm.UnaryPow.sq cap ≤ 200 * (cap + 2) ^ 3 := by
    have h := Nat.pow_le_pow_right (show 1 ≤ cap + 2 by omega) (show 2 ≤ 3 by norm_num)
    have e : PrimAsm.UnaryPow.sq cap = 200 * (cap + 2) ^ 2 := by unfold PrimAsm.UnaryPow.sq; ring
    omega
  have hq := sqrtCost_le (4096 * B)
  have hq2 : (4096 * B + 2) ^ 3 ≤ (cap + 2) ^ 3 := Nat.pow_le_pow_left (by nlinarith) 3
  have h3 : cap + 2 ≤ (cap + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 (WExec.seq s12 (WExec.seq s13
    (WExec.seq s14 s15)))))))))))))) ?_ le_rfl⟩
  · omega
  · refine WState.eq (by simp only [hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_sh]) (by simp only [hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_st]) ?_
      (by simp only [hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_cell])
    funext q
    rw [e64]
    simp only [hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, WState.setv_val,
      Function.update_apply, qL_apply, sL_apply, rL_apply, wL0, wL1]
    by_cases q0 : q = 0
    · subst q0; simp
    · by_cases q1 : q = 1
      · subst q1; simp
      · by_cases q30 : q = 30
        · subst q30; simp [z30]
        · by_cases q31 : q = 31
          · subst q31; simp [z31]
          · by_cases q40 : q = 40
            · subst q40; simp [z40]
            · by_cases q41 : q = 41
              · subst q41; simp [z41]
              · by_cases q50 : q = 50
                · subst q50; simp [z50]
                · by_cases q51 : q = 51
                  · subst q51; simp [z51]
                  · simp [q0, q1, q30, q31, q40, q41, q50, q51]

end NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
