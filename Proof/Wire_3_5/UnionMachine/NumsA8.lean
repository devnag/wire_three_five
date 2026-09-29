import Proof.Wire_3_5.UnionMachine.NumsA7
import Proof.Wire_3_5.UnionMachine.DataDock

/-! # NW phase (a), part 8: the data stage's inputs and the role stash

On NW's bank (`x ≥ DT + 3`): the data stage's tapes are `DataDock.nwTmap` (the request on `sIn`, tape `j` on stream
`161 + j`); the stash streams `161 + DT`, `162 + DT`, `163 + DT` hold `1^n`, `1^e`, `1^{T_f}` while the numbers program
owns the registers; stream `1` gets the cell's `[false]` (the numbers program's `blankCell` output stream).

* `fne`, `tmapA`, `tNT`, `tLT`, `tCT`, `tOUT`, `sNs`, `sEs`, `sTs` (and their values), `PreDock`, `tapesW`,
  **`tapes_run`** (from `g 2 = W` and the roles: `1^n`, `1^W`, `1^W` on the data stage's inputs, the stash, `[false]`
  on stream `1`, every register `0`).

Paper quantity: none (plumbing: the data stage's inputs, the roles kept across the numbers program). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

theorem fne {k : ℕ} {a b : Fin k} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

section Bank
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x)

/-- The data stage's tapes on NW's bank. -/
def tmapA : Fin DataDock.DT → Fin (LNS x + 1) := DataDock.nwTmap x (by omega) (sIn x)

/-- The data stage's `1^n`, `1^L`, `1^W` and output tapes. -/
def tNT : Fin (LNS x + 1) := tmapA x hx (DataDock.iOf Data.sNT)
def tLT : Fin (LNS x + 1) := tmapA x hx (DataDock.iOf Data.sLT)
def tCT : Fin (LNS x + 1) := tmapA x hx (DataDock.iOf Data.sCT)
def tOUT : Fin (LNS x + 1) := tmapA x hx DataDock.iOUT

/-- The stash streams. -/
def sNs : Fin (LNS x + 1) := ⟨161 + DataDock.DT, by unfold LNS; omega⟩
def sEs : Fin (LNS x + 1) := ⟨162 + DataDock.DT, by unfold LNS; omega⟩
def sTs : Fin (LNS x + 1) := ⟨163 + DataDock.DT, by unfold LNS; omega⟩

theorem tmapA_val (j : Fin DataDock.DT) (hj : j ≠ DataDock.iIN) : (tmapA x hx j).val = 161 + j.val := by
  unfold tmapA DataDock.nwTmap; rw [if_neg hj]

theorem tNT_val : (tNT x hx).val = 163 := by unfold tNT; rw [tmapA_val x hx _ (by decide)]; decide
theorem tLT_val : (tLT x hx).val = 164 := by unfold tLT; rw [tmapA_val x hx _ (by decide)]; decide
theorem tCT_val : (tCT x hx).val = 165 := by unfold tCT; rw [tmapA_val x hx _ (by decide)]; decide
theorem tOUT_val : (tOUT x hx).val = 167 := by unfold tOUT; rw [tmapA_val x hx _ (by decide)]; decide
theorem sNs_val : (sNs x hx).val = 161 + DataDock.DT := rfl
theorem sEs_val : (sEs x hx).val = 162 + DataDock.DT := rfl
theorem sTs_val : (sTs x hx).val = 163 + DataDock.DT := rfl
theorem DT_val : DataDock.DT = 9902 := by decide

/-- **Before the data stage**: the request, `1^n`, `1^W`, `1^W` on its inputs, the stash `1^n`, `1^e`, `1^T`, `[false]`
on stream `1`, every other stream blank, every head, register and the cell `0`. -/
structure PreDock (w : List Bool) (n W e T : ℕ) (σ : St x) : Prop where
  hin : σ.st (sIn x) = frame w
  hNT : σ.st (tNT x hx) = List.replicate n true
  hLT : σ.st (tLT x hx) = List.replicate W true
  hCT : σ.st (tCT x hx) = List.replicate W true
  hSN : σ.st (sNs x hx) = List.replicate n true
  hSE : σ.st (sEs x hx) = List.replicate e true
  hST : σ.st (sTs x hx) = List.replicate T true
  h1 : σ.st (sk x 1) = [false]
  blank : ∀ i : Fin (LNS x + 1), i.val ≠ 150 → i.val ≠ 163 → i.val ≠ 164 → i.val ≠ 165 → i.val ≠ 10063 →
    i.val ≠ 10064 → i.val ≠ 10065 → i.val ≠ 1 → σ.st i = []
  heads : ∀ i, σ.sh i = 0
  regs : ∀ q, σ.val q = 0
  cell : σ.cell = false

/-- **The tapes program**: `1^n`, `1^W`, `1^W` on the data stage's inputs, the roles stashed, `[false]` on stream `1`. -/
def tapesW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rN (g 3) (g 1)) (.seq (onesU (tNT x hx) (g 3) (g 1))
    (.seq (FinalPass.Hash4.wcopyR (g 2) (g 3) (g 1)) (.seq (onesU (tLT x hx) (g 3) (g 1))
    (.seq (onesU (tCT x hx) (g 2) (g 1)) (.seq (onesU (sNs x hx) rN (g 1)) (.seq (onesU (sEs x hx) rE (g 1))
    (.seq (onesU (sTs x hx) rT (g 1)) (.wr (sk x 1) false))))))))

theorem tapes_run (cap : ℕ) (w : List Bool) (n W e T : ℕ) (σ : St x) (hin : σ.st (sIn x) = frame w)
    (hcl : ∀ i, i ≠ sIn x → σ.st i = []) (hh : ∀ i, σ.sh i = 0) (hcell : σ.cell = false) (hN : σ.val rN = n)
    (hW : σ.val (g 2) = W) (hE : σ.val rE = e) (hT : σ.val rT = T)
    (hz : ∀ q, q ≠ rN → q ≠ rE → q ≠ rT → q ≠ g 2 → σ.val q = 0) (hc : n + W + e + T ≤ cap) :
    ∃ (τ : St x) (c : ℕ), WExec cap (tapesW x hx) σ τ c ∧ PreDock x hx w n W e T τ ∧
      c ≤ 100 * (n + W + e + T + 1) := by
  -- the streams' values and distinctness
  have v0 := tNT_val x hx
  have v1 := tLT_val x hx
  have v2 := tCT_val x hx
  have v3 := sNs_val x hx
  have v4 := sEs_val x hx
  have v5 := sTs_val x hx
  have vD := DT_val
  have vI : (sIn x).val = 150 := rfl
  have vQ : (sk x 1).val = 1 := rfl
  have a01 : tNT x hx ≠ tLT x hx := fne (by omega)
  have a02 : tNT x hx ≠ tCT x hx := fne (by omega)
  have a03 : tNT x hx ≠ sNs x hx := fne (by omega)
  have a04 : tNT x hx ≠ sEs x hx := fne (by omega)
  have a05 : tNT x hx ≠ sTs x hx := fne (by omega)
  have a0Q : tNT x hx ≠ sk x 1 := fne (by omega)
  have a12 : tLT x hx ≠ tCT x hx := fne (by omega)
  have a13 : tLT x hx ≠ sNs x hx := fne (by omega)
  have a14 : tLT x hx ≠ sEs x hx := fne (by omega)
  have a15 : tLT x hx ≠ sTs x hx := fne (by omega)
  have a1Q : tLT x hx ≠ sk x 1 := fne (by omega)
  have a23 : tCT x hx ≠ sNs x hx := fne (by omega)
  have a24 : tCT x hx ≠ sEs x hx := fne (by omega)
  have a25 : tCT x hx ≠ sTs x hx := fne (by omega)
  have a2Q : tCT x hx ≠ sk x 1 := fne (by omega)
  have a34 : sNs x hx ≠ sEs x hx := fne (by omega)
  have a35 : sNs x hx ≠ sTs x hx := fne (by omega)
  have a3Q : sNs x hx ≠ sk x 1 := fne (by omega)
  have a45 : sEs x hx ≠ sTs x hx := fne (by omega)
  have a4Q : sEs x hx ≠ sk x 1 := fne (by omega)
  have a5Q : sTs x hx ≠ sk x 1 := fne (by omega)
  have b0 : tNT x hx ≠ sIn x := fne (by omega)
  have b1 : tLT x hx ≠ sIn x := fne (by omega)
  have b2 : tCT x hx ≠ sIn x := fne (by omega)
  have b3 : sNs x hx ≠ sIn x := fne (by omega)
  have b4 : sEs x hx ≠ sIn x := fne (by omega)
  have b5 : sTs x hx ≠ sIn x := fne (by omega)
  have bQ : sk x 1 ≠ sIn x := fne (by omega)
  -- the registers
  have r31 : g 3 ≠ g 1 := by decide
  have r21 : g 2 ≠ g 1 := by decide
  have r23 : g 2 ≠ g 3 := by decide
  have rN3 : rN ≠ g 3 := by decide
  have rN1 : rN ≠ g 1 := by decide
  have rN2 : rN ≠ g 2 := by decide
  have rE1 : rE ≠ g 1 := by decide
  have rE2 : rE ≠ g 2 := by decide
  have rE3 : rE ≠ g 3 := by decide
  have rEN : rE ≠ rN := by decide
  have rT1 : rT ≠ g 1 := by decide
  have rT2 : rT ≠ g 2 := by decide
  have rT3 : rT ≠ g 3 := by decide
  have rTN : rT ≠ rN := by decide
  have rTE : rT ≠ rE := by decide
  have z1 : σ.val (g 1) = 0 := hz _ rN1.symm rE1.symm rT1.symm r21.symm
  have z3 : σ.val (g 3) = 0 := hz _ rN3.symm rE3.symm rT3.symm r23.symm
  -- 1: `g 3 := n`
  have e1 := FinalPass.Hash4.wcopyR_spec cap rN (g 3) (g 1) rN3 rN1 r31 σ z3 z1 (by omega)
  rw [hN] at e1
  -- 2: `1^n` on the `n` tape
  have e2 := onesU_spec cap (tNT x hx) (g 3) (g 1) r31 n (σ.setv (g 3) n) (by simp [hcl _ b0]) (by simp [hh])
    (by simp) (by simp [Function.update_of_ne r31.symm, z1]) (by omega)
  -- 3: `g 3 := W`
  have e3 := FinalPass.Hash4.wcopyR_spec cap (g 2) (g 3) (g 1) r23 r21 r31
    (((σ.setv (g 3) n).sets (tNT x hx) (List.replicate n true)).setv (g 3) 0) (by simp)
    (by simp [Function.update_of_ne r31.symm, z1]) (by simp [Function.update_of_ne r23, hW]; omega)
  have w3 : (((σ.setv (g 3) n).sets (tNT x hx) (List.replicate n true)).setv (g 3) 0).val (g 2) = W := by
    simp [Function.update_of_ne r23, hW]
  rw [w3] at e3
  -- 4: `1^W` on the `L` tape
  have e4 := onesU_spec cap (tLT x hx) (g 3) (g 1) r31 W
    ((((σ.setv (g 3) n).sets (tNT x hx) (List.replicate n true)).setv (g 3) 0).setv (g 3) W)
    (by simp [Function.update_of_ne a01.symm, hcl _ b1]) (by simp [hh]) (by simp)
    (by simp [Function.update_of_ne r31.symm, z1]) (by omega)
  -- 5: `1^W` on the `W` tape
  have e5 := onesU_spec cap (tCT x hx) (g 2) (g 1) r21 W
    ((((((σ.setv (g 3) n).sets (tNT x hx) (List.replicate n true)).setv (g 3) 0).setv (g 3) W).sets (tLT x hx)
      (List.replicate W true)).setv (g 3) 0)
    (by simp [Function.update_of_ne a02.symm, Function.update_of_ne a12.symm, hcl _ b2]) (by simp [hh])
    (by simp [Function.update_of_ne r23, hW]) (by simp [Function.update_of_ne r31.symm, z1]) (by omega)
  -- 6, 7, 8: the stash
  obtain ⟨σ5, h5⟩ : ∃ s, s = (((((((σ.setv (g 3) n).sets (tNT x hx) (List.replicate n true)).setv (g 3) 0).setv (g 3)
      W).sets (tLT x hx) (List.replicate W true)).setv (g 3) 0).sets (tCT x hx) (List.replicate W true)).setv (g 2) 0 :=
    ⟨_, rfl⟩
  rw [← h5] at e5
  have e6 := onesU_spec cap (sNs x hx) rN (g 1) rN1 n σ5
    (by rw [h5]; simp [Function.update_of_ne a03.symm, Function.update_of_ne a13.symm, Function.update_of_ne a23.symm,
      hcl _ b3]) (by rw [h5]; simp [hh])
    (by rw [h5]; simp [Function.update_of_ne rN2, Function.update_of_ne rN3, hN])
    (by rw [h5]; simp [Function.update_of_ne r21.symm, Function.update_of_ne r31.symm, z1]) (by omega)
  have e7 := onesU_spec cap (sEs x hx) rE (g 1) rE1 e ((σ5.sets (sNs x hx) (List.replicate n true)).setv rN 0)
    (by rw [h5]; simp [Function.update_of_ne a04.symm, Function.update_of_ne a14.symm, Function.update_of_ne a24.symm,
      Function.update_of_ne a34.symm, hcl _ b4]) (by rw [h5]; simp [hh])
    (by rw [h5]; simp [Function.update_of_ne rEN, Function.update_of_ne rE2, Function.update_of_ne rE3, hE])
    (by rw [h5]; simp [Function.update_of_ne rN1.symm, Function.update_of_ne r21.symm, Function.update_of_ne r31.symm,
      z1]) (by omega)
  have e8 := onesU_spec cap (sTs x hx) rT (g 1) rT1 T
    ((((σ5.sets (sNs x hx) (List.replicate n true)).setv rN 0).sets (sEs x hx) (List.replicate e true)).setv rE 0)
    (by rw [h5]; simp [Function.update_of_ne a05.symm, Function.update_of_ne a15.symm, Function.update_of_ne a25.symm,
      Function.update_of_ne a35.symm, Function.update_of_ne a45.symm, hcl _ b5]) (by rw [h5]; simp [hh])
    (by rw [h5]; simp [Function.update_of_ne rTE, Function.update_of_ne rTN, Function.update_of_ne rT2,
      Function.update_of_ne rT3, hT])
    (by rw [h5]; simp [Function.update_of_ne rE1.symm, Function.update_of_ne rN1.symm, Function.update_of_ne r21.symm,
      Function.update_of_ne r31.symm, z1]) (by omega)
  -- 9: `[false]` on stream `1`
  obtain ⟨σ8, h8⟩ : ∃ s, s = ((((((σ5.sets (sNs x hx) (List.replicate n true)).setv rN 0).sets (sEs x hx)
      (List.replicate e true)).setv rE 0).sets (sTs x hx) (List.replicate T true)).setv rT 0) := ⟨_, rfl⟩
  rw [← h8] at e8
  have e9 := WExec.wr (cap := cap) (sk x 1) false σ8
  have s81 : σ8.st (sk x 1) = [] := by
    rw [h8, h5]
    simp [Function.update_of_ne a0Q.symm, Function.update_of_ne a1Q.symm, Function.update_of_ne a2Q.symm,
      Function.update_of_ne a3Q.symm, Function.update_of_ne a4Q.symm, Function.update_of_ne a5Q.symm, hcl _ bQ]
  have h81 : σ8.sh (sk x 1) = 0 := by rw [h8, h5]; simp [hh]
  rw [s81, h81] at e9
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 e9))))))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
  · rw [h8, h5]
    simp [Function.update_of_ne bQ.symm, Function.update_of_ne b0.symm, Function.update_of_ne b1.symm,
      Function.update_of_ne b2.symm, Function.update_of_ne b3.symm, Function.update_of_ne b4.symm,
      Function.update_of_ne b5.symm, hin]
  · rw [h8, h5]
    simp [Function.update_of_ne a0Q, Function.update_of_ne a03, Function.update_of_ne a04, Function.update_of_ne a05,
      Function.update_of_ne a01, Function.update_of_ne a02]
  · rw [h8, h5]
    simp [Function.update_of_ne a1Q, Function.update_of_ne a13, Function.update_of_ne a14, Function.update_of_ne a15,
      Function.update_of_ne a12]
  · rw [h8, h5]
    simp [Function.update_of_ne a2Q, Function.update_of_ne a23, Function.update_of_ne a24, Function.update_of_ne a25]
  · rw [h8]
    simp [Function.update_of_ne a3Q, Function.update_of_ne a34, Function.update_of_ne a35]
  · rw [h8]
    simp [Function.update_of_ne a4Q, Function.update_of_ne a45]
  · rw [h8]
    simp [Function.update_of_ne a5Q]
  · simp only [WState.sets_st, Function.update_self]
    rfl
  · intro i i0 i1 i2 i3 i4 i5 i6 i7
    rw [h8, h5]
    have c0 : i ≠ tNT x hx := fne (by omega)
    have c1 : i ≠ tLT x hx := fne (by omega)
    have c2 : i ≠ tCT x hx := fne (by omega)
    have c3 : i ≠ sNs x hx := fne (by omega)
    have c4 : i ≠ sEs x hx := fne (by omega)
    have c5 : i ≠ sTs x hx := fne (by omega)
    have cQ : i ≠ sk x 1 := fne (by omega)
    have cI : i ≠ sIn x := fne (by omega)
    simp [Function.update_of_ne c0, Function.update_of_ne c1, Function.update_of_ne c2, Function.update_of_ne c3,
      Function.update_of_ne c4, Function.update_of_ne c5, Function.update_of_ne cQ, hcl i cI]
  · intro i
    rw [h8, h5]
    simp [hh]
  · intro q
    rw [h8, h5]
    simp only [WState.sets_val, WState.setv_val, Function.update_apply]
    split_ifs <;> first | rfl | exact hz q (by assumption) (by assumption) (by assumption) (by assumption)
  · rw [h8, h5]
    simp [hcell]

end Bank

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
