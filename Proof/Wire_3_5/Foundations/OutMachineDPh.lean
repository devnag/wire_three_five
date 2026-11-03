import Proof.Wire_3_5.Foundations.OutMachineDPhK
import Proof.Wire_3_5.UnionMachine.NumsPh4Base

/-! # NW phase (d), part 2: **`phD : ∀ x, NumsPh4.PhD' x`**

NW's last phase prints the final pass's denominator `Den = max (2^e·V, 1)` in `T_f`-bit binary (P3:3044-3048,
3170-3181) from the unary registers `rT = T_f`, `rE = e`, `rV = V`: word 0 `frame (binary T 0)` on `sW0`, word 1
`frame (binary T Den)` on `sW1`, both heads back at `0`, every register `0`. The program is part 1's generic
`dProg` on the writer's bank (`sW0`, `sW1`; scratch registers `0`, `1`, `2`), its run `dProg_spec` at
`C = 300`, `D = 2`:

* `sW01_ne`, `sInW0_ne`, `sInW1_ne` (the three word streams are distinct), `dRegsX` (the six registers);
* `finalX` (`dProg_spec`'s exit is `NumsPh3.Final`);
* **`phD x : NumsPh4.PhD' x`**.

Paper quantity of the main type: the final pass's denominator `max(2^e·V, 1)` in `T_f`-bit binary, NW's printed
word 1 (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.DPh
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout (LNS LNR sk)
open NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2 (sIn sW0 sW1 rE rT rV)
open NearCubicWires.WireExponent3_5.UnionMachine (NumsPh3.DBank NumsPh3.Final NumsPh4.PhD')

/-- (d)'s scratch registers. -/
def rK : Fin LNR := ⟨0, by decide⟩
def rH : Fin LNR := ⟨1, by decide⟩
def rB : Fin LNR := ⟨2, by decide⟩

theorem dRegsX : DRegs rT rE rV rK rH rB :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem sW01_ne (x : ℕ) : sW0 x ≠ sW1 x := by
  intro h; have := congrArg Fin.val h; simp [sW0, sW1, sk] at this

theorem sInW0_ne (x : ℕ) : sIn x ≠ sW0 x := by
  intro h; have := congrArg Fin.val h; simp [sIn, sW0, sk] at this

theorem sInW1_ne (x : ℕ) : sIn x ≠ sW1 x := by
  intro h; have := congrArg Fin.val h; simp [sIn, sW1, sk] at this

/-- (d)'s program on the writer's bank. -/
def dProgX (x : ℕ) : WM (LNS x) LNR := dProg (sW0 x) (sW1 x) rT rE rV rK rH rB

/-- `dProg_spec`'s exit is the writer's `Final`. -/
theorem finalX (x : ℕ) (T e v B b : ℕ) (w : List Bool) (σ : WState (LNS x) LNR) (hD : NumsPh3.DBank x σ w T e v B)
    (hregs : ∀ q, q ≠ rT → q ≠ rE → q ≠ rV → σ.val q = 0) :
    NumsPh3.Final x (((((σ.sets (sW0 x) (frame (binary T 0))).sets (sW1 x)
      (frame (binary T (max (2 ^ e * v) 1)))).setv rT 0).setv rE 0).setv rV 0) w T (max (2 ^ e * v) 1) (B + b) where
  hw0 := by simp [Function.update_apply, sW01_ne x]
  hw1 := by simp
  hin := by simp [Function.update_apply, sInW0_ne x, sInW1_ne x, hD.hin]
  resid := fun i h1 h2 h3 => by
    simp only [WState.setv_st, WState.sets_st, Function.update_apply, if_neg h2, if_neg h3]
    exact (hD.resid i h1 h2 h3).trans (Nat.le_add_right _ _)
  heads := fun i => by simp [hD.heads i]
  regs := fun q => by
    by_cases qV : q = rV
    · subst qV; simp
    · by_cases qE : q = rE
      · subst qE; simp [Function.update_apply, qV]
      · by_cases qT : q = rT
        · subst qT; simp [Function.update_apply, qV, qE]
        · simp [Function.update_apply, qV, qE, qT, hregs q qT qE qV]

/-- **Phase (d)** (X6): `NumsPh4.PhD' x` at `C = 300`, `D = 2`. -/
def phD (x : ℕ) : NumsPh4.PhD' x where
  s := (dProgX x).toProg.size
  M := (dProgX x).toProg.compile
  C := 300
  D := 2
  run := fun cap T e v B w σ hc hden hD hregs => by
    have hK : σ.val rK = 0 := hregs rK (by decide) (by decide) (by decide)
    have hH : σ.val rH = 0 := hregs rH (by decide) (by decide) (by decide)
    have hB : σ.val rB = 0 := hregs rB (by decide) (by decide) (by decide)
    have hx := dProg_spec cap (sW0 x) (sW1 x) (sW01_ne x) rT rE rV rK rH rB dRegsX T e v σ hD.ht hD.he hD.hv hK hH hB
      hD.hw0 (hD.heads _) hD.hw1 (hD.heads _) hden hc
    exact ⟨_, _, le_rfl, Exec.step (WExec.exec cap hx), finalX x T e v B _ w σ hD hregs⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.DPh
