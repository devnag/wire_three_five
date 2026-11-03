import Proof.Wire_3_5.Primitive.SeedFix.SWt3Base

/-! # T3 SWt, part 4: **the top tables' writer** `swT x hx l : SWParts.SWtT l`

At a SYM request: the SYM front (`front_runA`: every filled slot's scan word
`natWord bottomCount ++ (frame (ofFn top) ++ tabSeg)` on `sS j`, the empty slots blank, the region past the data
blank), then `tW` (every register cleared, `topW` at each slot): `sO j = frame (topJ k j)` (**`slot_step`**,
**`tops_run`**), every head `0`, every register `0`, the residue the front's. The capacity `K_t·X^{D_t}`, the steps
and residue `C_t·X^{D_t'}` (**`tRun`**), and **`swT`**.

Paper quantity of the main type: the SYM call's framed top tables (`symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.NumsA NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section Gate
variable (x : ℕ) (hx : DataDock.DT + 7 ≤ x)

/-- **One slot**: a filled scan tape's top table framed on `sO j`, or `frame []` for a blank one. -/
theorem slot_step (cap : ℕ) (j : Fin 4) (σ : St x) (w : List Bool)
    (hS : (∃ (x0 : ℕ) (y rest : List Bool), σ.st (sS x hx j) = natWord x0 ++ (frame y ++ rest) ∧ w = frame y ∧
      2 * natBitLength x0 + 2 * y.length + 2 ≤ cap) ∨ (σ.st (sS x hx j) = [] ∧ w = frame []))
    (hSh : σ.sh (sS x hx j) = 0) (hO : σ.st (sO x hx j) = []) (hOh : σ.sh (sO x hx j) = 0)
    (hz : ∀ i, σ.val (RT i) = 0) :
    ∃ c, WExec cap (topW (sS x hx j) (sO x hx j) RT) σ (σ.sets (sO x hx j) w) c ∧
      c ≤ 20 * UnaryPow.sq cap + 40 * cap + 200 := by
  have hsq := UnaryPow.lin_le_sq cap
  rcases hS with ⟨x0, y, rest, h1, rfl, h3⟩ | ⟨h1, rfl⟩
  · obtain ⟨c, e, hc⟩ := top_fill cap (sS x hx j) (sO x hx j) (sS_ne_sO x hx j j) RT x0 y rest σ h1 hSh hO hOh hz h3
    exact ⟨c, e, by omega⟩
  · exact ⟨2, top_empty cap (sS x hx j) (sO x hx j) RT σ h1 hSh hO hOh, by omega⟩

/-- **The four slots.** -/
theorem tops_run (cap : ℕ) (σ : St x) (w : Fin 4 → List Bool)
    (hS : ∀ j : Fin 4, (∃ (x0 : ℕ) (y rest : List Bool), σ.st (sS x hx j) = natWord x0 ++ (frame y ++ rest) ∧
      w j = frame y ∧ 2 * natBitLength x0 + 2 * y.length + 2 ≤ cap) ∨ (σ.st (sS x hx j) = [] ∧ w j = frame []))
    (hsh : ∀ i, σ.sh i = 0) (hO : ∀ j, σ.st (sO x hx j) = []) (hz : ∀ i, σ.val (RT i) = 0) :
    ∃ c, WExec cap (.seq (topW (sS x hx 0) (sO x hx 0) RT) (.seq (topW (sS x hx 1) (sO x hx 1) RT)
      (.seq (topW (sS x hx 2) (sO x hx 2) RT) (topW (sS x hx 3) (sO x hx 3) RT)))) σ
      ((((σ.sets (sO x hx 0) (w 0)).sets (sO x hx 1) (w 1)).sets (sO x hx 2) (w 2)).sets (sO x hx 3) (w 3)) c ∧
      c ≤ 4 * (20 * UnaryPow.sq cap + 40 * cap + 200) + 3 := by
  have nSO : ∀ i j : Fin 4, sS x hx i ≠ sO x hx j := sS_ne_sO x hx
  have nOO : ∀ i j : Fin 4, i ≠ j → sO x hx i ≠ sO x hx j := fun i j h => (sO_inj x hx).ne h
  have keepS : ∀ (ρ : St x) (j : Fin 4) (v : List Bool) (i : Fin 4), (ρ.sets (sO x hx j) v).st (sS x hx i) =
      ρ.st (sS x hx i) := fun ρ j v i => by simp [Function.update_of_ne (nSO i j)]
  have keepO : ∀ (ρ : St x) (j : Fin 4) (v : List Bool) (i : Fin 4), i ≠ j → (ρ.sets (sO x hx j) v).st (sO x hx i) =
      ρ.st (sO x hx i) := fun ρ j v i h => by simp [Function.update_of_ne (nOO i j h)]
  obtain ⟨c0, e0, h0⟩ := slot_step x hx cap 0 σ (w 0) (hS 0) (hsh _) (hO 0) (hsh _) hz
  obtain ⟨c1, e1, h1⟩ := slot_step x hx cap 1 (σ.sets (sO x hx 0) (w 0)) (w 1)
    (by rw [keepS]; exact hS 1) (by simp [hsh]) (by rw [keepO _ _ _ _ (by decide)]; exact hO 1) (by simp [hsh]) hz
  obtain ⟨c2, e2, h2⟩ := slot_step x hx cap 2 ((σ.sets (sO x hx 0) (w 0)).sets (sO x hx 1) (w 1)) (w 2)
    (by rw [keepS, keepS]; exact hS 2) (by simp [hsh])
    (by rw [keepO _ _ _ _ (by decide), keepO _ _ _ _ (by decide)]; exact hO 2) (by simp [hsh]) hz
  obtain ⟨c3, e3, h3⟩ := slot_step x hx cap 3 (((σ.sets (sO x hx 0) (w 0)).sets (sO x hx 1) (w 1)).sets
    (sO x hx 2) (w 2)) (w 3)
    (by rw [keepS, keepS, keepS]; exact hS 3) (by simp [hsh])
    (by rw [keepO _ _ _ _ (by decide), keepO _ _ _ _ (by decide), keepO _ _ _ _ (by decide)]; exact hO 3)
    (by simp [hsh]) hz
  exact ⟨_, WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)), by omega⟩

variable (l : Literals)


theorem time_le (X cap B c0 c1 mF Kc Dk CF DFs : ℕ) (hX : 1 ≤ X) (hcap : cap = Kc * X ^ Dk) (hB : B = CF * X ^ DFs)
    (hBc : B ≤ cap) (hmF : mF ≤ B) (h0 : c0 ≤ 512 * (3 * B + 2))
    (h1 : c1 ≤ 4 * (20 * UnaryPow.sq cap + 40 * cap + 200) + 3) :
    mF + 1 + (c0 + 1 + c1) ≤ (CF + 10000000 * (Kc + 2) ^ 2) * X ^ (DFs + 2 * Dk) := by
  have hsq : UnaryPow.sq cap = 200 * ((cap + 2) * (cap + 2)) := by unfold UnaryPow.sq; ring
  have hQ : cap + 2 ≤ (Kc + 2) * X ^ Dk := by
    have := Nat.one_le_pow Dk X hX
    rw [hcap]; nlinarith
  have hQ2 : (cap + 2) * (cap + 2) ≤ (Kc + 2) ^ 2 * X ^ (2 * Dk) := by
    have := Nat.mul_le_mul hQ hQ
    calc (cap + 2) * (cap + 2) ≤ (Kc + 2) * X ^ Dk * ((Kc + 2) * X ^ Dk) := this
      _ = (Kc + 2) ^ 2 * X ^ (2 * Dk) := by rw [two_mul, pow_add]; ring
  have hlin : cap ≤ (cap + 2) * (cap + 2) := by nlinarith
  have p1 : X ^ DFs ≤ X ^ (DFs + 2 * Dk) := Nat.pow_le_pow_right hX (by omega)
  have p2 : X ^ (2 * Dk) ≤ X ^ (DFs + 2 * Dk) := Nat.pow_le_pow_right hX (by omega)
  have q1 : CF * X ^ DFs ≤ CF * X ^ (DFs + 2 * Dk) := Nat.mul_le_mul_left _ p1
  have q2 : (Kc + 2) ^ 2 * X ^ (2 * Dk) ≤ (Kc + 2) ^ 2 * X ^ (DFs + 2 * Dk) := Nat.mul_le_mul_left _ p2
  have hn1 : 1 ≤ (Kc + 2) ^ 2 * X ^ (DFs + 2 * Dk) :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ hX)
  have e : (CF + 10000000 * (Kc + 2) ^ 2) * X ^ (DFs + 2 * Dk) =
      CF * X ^ (DFs + 2 * Dk) + 10000000 * ((Kc + 2) ^ 2 * X ^ (DFs + 2 * Dk)) := by ring
  rw [e]
  rw [hsq] at h1
  omega

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt
