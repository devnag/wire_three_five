import Proof.Wire_3_5.UnionMachine.NumsA4Base
import Proof.Wire_3_5.UnionMachine.NumsA5
import Proof.Wire_3_5.FinalPass.LiftR
import Proof.Wire_3_5.FinalPass.S5TUtil

/-! # NW phase (a), part 6: the SYM numbers program on NW's bank

The SYM numbers program `numsP` is a word program on the `x = 0` bank, reading its request on stream `0` and its counts
on stream `113`; NW's input is on `sIn = 150`. Renamed by the swap `0 ↔ 150` (`fsN`, every other stream `sk x j`,
the registers the identity) it runs on NW's bank at ANY capacity `cap ≥ cap₀` (`WExec.liftW`), from a state carrying
the cell's entry: the framed input on `sIn`, `[false]` on stream `1`, the counts on stream `113`, the other images
blank, every head at `0`, every register `0`, the cell `0`. Its exit: the streams as at entry, every head `0` except
stream `113`'s (at most the step count, `WExec.sh_le`), the registers the program's (each `≤ cap₀`), the three
factors of `V`.

* `swp`, `swp_swp`, `fsN`, `fsN_inj`, `fsN_val`, `NumsIn`, `liftIn`, **`numsBank`**.

Paper quantities of the main type: `|E|`, `|FlatSeed|`, `Q` at the request (`V = |E|·|FlatSeed|·Q`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- The swap `0 ↔ 150` of the layout streams. -/
def swp (j : Fin 161) : Fin 161 :=
  if j.val = 0 then ⟨150, by omega⟩ else if j.val = 150 then ⟨0, by omega⟩ else j

theorem swp_swp (j : Fin 161) : swp (swp j) = j := by
  apply Fin.ext
  unfold swp
  by_cases h0 : j.val = 0
  · simp [h0]
  · by_cases h1 : j.val = 150
    · simp [h1]
    · simp [h0, h1]

theorem swp_inj : Function.Injective swp := fun a b h => by rw [← swp_swp a, h, swp_swp]

/-- **The numbers program's streams on NW's bank.** -/
def fsN (x : ℕ) (j : Fin (LNS 0 + 1)) : Fin (LNS x + 1) := sk x (swp j)

theorem fsN_val (x : ℕ) (j : Fin (LNS 0 + 1)) : (fsN x j).val = (swp j).val := rfl

theorem fsN_inj (x : ℕ) : Function.Injective (fsN x) := by
  intro a b h
  have e : (swp a).val = (swp b).val := by rw [← fsN_val x a, ← fsN_val x b, h]
  exact swp_inj (Fin.ext e)

/-- **The cell's entry on NW's bank**: the framed request `w` on `sIn`, `[false]` on stream `1`, the counts `u` on
stream `113`, the other layout streams blank, every head, register and the cell `0`. -/
structure NumsIn (x : ℕ) (w u : List Bool) (ω : WState (LNS x) LNR) : Prop where
  hin : ω.st (sk x 150) = frame w
  h1 : ω.st (sk x 1) = [false]
  hu : ω.st (sk x 113) = u
  blank : ∀ j : Fin 161, j.val ≠ 150 → j.val ≠ 1 → j.val ≠ 113 → ω.st (sk x j) = []
  heads : ∀ i, ω.sh i = 0
  regs : ∀ q, ω.val q = 0
  cell : ω.cell = false

theorem liftIn (x : ℕ) (w u : List Bool) (ω : WState (LNS x) LNR) (h : NumsIn x w u ω) :
    LiftW (fsN x) id ω (CellLoopD.blankCellD 0 w [] 0 u) := by
  refine ⟨fun i => ?_, fun i => ?_, fun r => ?_, ?_⟩
  · rw [h.heads]
    simp only [CellLoopD.blankCellD, CellState.blankCell, WState.sets_sh]
    split_ifs <;> rfl
  · have e : fsN x i = sk x (swp i) := rfl
    have hsrc : ∀ k : Fin (LNS 0 + 1), (CellLoopD.blankCellD 0 w [] 0 u).st k =
        if k = sk 0 113 then u else if k = sk 0 0 then frame w else if k = sk 0 1 then [false] else [] := by
      intro k
      simp only [CellLoopD.blankCellD, CellState.blankCell, WState.sets_st, Function.update_apply]
      split_ifs <;> simp
    have n0 : sk 0 0 ≠ sk 0 113 := by decide
    have n1 : sk 0 1 ≠ sk 0 113 := by decide
    have n10 : sk 0 1 ≠ sk 0 0 := by decide
    have n150 : sk 0 150 ≠ sk 0 113 := by decide
    have n150a : sk 0 150 ≠ sk 0 0 := by decide
    have n150b : sk 0 150 ≠ sk 0 1 := by decide
    rw [e, hsrc]
    by_cases h0 : i.val = 0
    · have hs : swp i = ⟨150, by omega⟩ := by unfold swp; simp [h0]
      have hi : i = sk 0 0 := Fin.ext h0
      rw [hs, show sk x (⟨150, by omega⟩ : Fin 161) = sk x 150 from rfl, h.hin, hi, if_neg n0, if_pos rfl]
    · by_cases h150 : i.val = 150
      · have hs : swp i = ⟨0, by omega⟩ := by unfold swp; simp [h150]
        have hi : i = sk 0 150 := Fin.ext h150
        rw [hs, h.blank ⟨0, by omega⟩ (by show (0 : ℕ) ≠ 150; omega) (by show (0 : ℕ) ≠ 1; omega)
          (by show (0 : ℕ) ≠ 113; omega), hi, if_neg n150, if_neg n150a, if_neg n150b]
      · have hs : swp i = i := by unfold swp; simp [h0, h150]
        rw [hs]
        by_cases h1 : i.val = 1
        · have hi : i = sk 0 1 := Fin.ext h1
          have hx : sk x (i : Fin 161) = sk x 1 := by rw [hi]; rfl
          rw [hx, h.h1, hi, if_neg n1, if_neg n10, if_pos rfl]
        · by_cases h113 : i.val = 113
          · have hi : i = sk 0 113 := Fin.ext h113
            have hx : sk x (i : Fin 161) = sk x 113 := by rw [hi]; rfl
            rw [hx, h.hu, hi, if_pos rfl]
          · rw [h.blank i h150 h1 h113]
            have m0 : i ≠ sk 0 0 := fun e => h0 (by rw [e]; rfl)
            have m1 : i ≠ sk 0 1 := fun e => h1 (by rw [e]; rfl)
            have m2 : i ≠ sk 0 113 := fun e => h113 (by rw [e]; rfl)
            rw [if_neg m2, if_neg m0, if_neg m1]
  · rw [h.regs]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
  · rw [h.cell]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
