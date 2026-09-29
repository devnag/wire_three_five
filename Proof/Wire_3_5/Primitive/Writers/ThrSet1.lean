import Proof.Wire_3_5.Primitive.Writers.BigBank
import Proof.Wire_3_5.Primitive.SeedFix.C4CapC

/-! # c4 THR block, the THR data stage on the big bank

The v4 data stage (`ThrData.ThrDataStage4`: `9902 + x3` tapes, the last `x3` its scratch) at a THR call. Its first
`9902` tapes are docked on the big bank exactly where the SYM setup docks its data stage (`slx L.oDA … L.extDA`,
lifted): the request, `1^n` and the two powers are read from the front's tapes, the outputs are left in the data
region. Its `x3` scratch tapes go to their own region above the layout (`extD`, `off = 3 + L.X`). On the first tapes
the exit bank is the after its data stage: the request on `gP0`, the data word on `gDO`, `gUW` kept, the bank blank
from the copy's region `oCP` up (**`data_dock`**).

Paper quantity of the main type: the THR call's data word `dataWord (hashNums ++ thrCounts)` on its tape
(P3:2543-2558). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank

variable (L : Lay) {x' : ℕ} (hx : 3 + L.X ≤ 3 + x')

theorem hDA : L.oDA + (Data.DS + 2 + Data.DR + 1) ≤ L.N := by
  have := L.U_eq; have : Data.DS = 9883 := rfl; have : Data.DR = 16 := rfl; unfold Lay.oDA; rw [Lay.N_eq]; omega

theorem extDA_inj : ∀ i j g, L.extDA i = some g → L.extDA j = some g → i = j := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  intro i j g hi hj
  unfold Lay.extDA at hi hj
  split_ifs at hi hj <;> simp at hi hj <;> subst_vars <;>
    first
    | exact Fin.ext (by omega)
    | (exfalso; revert hj; lv)

theorem extDA_lt : ∀ i g, L.extDA i = some g → g.val < L.oDA := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  intro i g hi
  unfold Lay.extDA at hi
  split_ifs at hi <;> simp at hi <;> subst hi <;> lv

/-- The data stage's slots on the big bank: its first `9902` tapes as the (lifted), its scratch on its own region. -/
def extD (x3 : ℕ) (j : Fin (Data.DS + 2 + Data.DR + 1 + x3)) : Option (Fin (3 + x')) :=
  if h : j.val < Data.DS + 2 + Data.DR + 1 then some (liftE hx (slx L.oDA (hDA L) L.extDA ⟨j.val, h⟩)) else none

/-- **The THR data stage docked on the big bank.** -/
theorem data_dock (x3 s3 n3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3) (w : List Bool) (n LL W : ℕ)
    (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ) (J : Fin x3 → List Bool)
    (h3 : Step M3 n3 (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases (Data.rawIn w n LL W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J))
    (cs : List ℕ) (hO : tout (sTape Data.sOUT) = Data.dataWord cs) (hI : tout (sTape Data.sIN) = frame w)
    (hoff : 3 + L.X + (Data.DS + 2 + Data.DR + 1 + x3) ≤ 3 + x')
    (B : Fin (3 + x') → List Bool) (B5 : Fin L.N → List Bool) (hBB : ∀ i, B (liftE hx i) = B5 i)
    (hP0 : B5 L.gP0 = frame w) (hN : B5 L.gN1 = List.replicate n true) (hL : B5 L.gUL = List.replicate LL true)
    (hD : B5 L.gUD = List.replicate W true) (hbl5 : ∀ i : Fin L.N, L.oDA ≤ i.val → B5 i = [])
    (hblB : ∀ i : Fin (3 + x'), 3 + L.X ≤ i.val → B i = []) :
    ∃ B' : Fin (3 + x') → List Bool,
      Step (RecoveryFocus.machine (slx (3 + L.X) hoff (extD L hx x3)) M3) n3 (fun _ => 0) B (fun _ => 0) B' ∧
      B' (liftE hx L.gP0) = frame w ∧ B' (liftE hx L.gDO) = Data.dataWord cs ∧
      (∀ i : Fin L.N, i.val < L.oDA → i ≠ L.gP0 → i ≠ L.gN1 → i ≠ L.gUL → i ≠ L.gUD → B' (liftE hx i) = B5 i) ∧
      (∀ i : Fin L.N, L.oCP ≤ i.val → B' (liftE hx i) = []) ∧
      (∀ i : Fin (3 + x'), 3 + L.X + (Data.DS + 2 + Data.DR + 1 + x3) ≤ i.val → B' i = []) := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  have eDS : Data.DS = 9883 := rfl
  have eDR : Data.DR = 16 := rfl
  have hsl := slx_inj L.oDA (hDA L) L.extDA (extDA_inj L) (extDA_lt L)
  -- the v3 part of the entry
  have hin : ∀ j : Fin (Data.DS + 2 + Data.DR + 1), B5 (slx L.oDA (hDA L) L.extDA j) =
      Fin.addCases (Data.rawIn w n LL W) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    cases hj : L.extDA j with
    | some g =>
      rw [slx_some hj]
      unfold Lay.extDA at hj
      split_ifs at hj with a0 a2 a3 a4 <;> simp at hj <;> subst hj <;> rw [ac_lt _ _ j (by omega)]
      · rw [hP0]; simp [Data.rawIn, Fin.ext_iff, C4Set.vIN, a0]
      · rw [hN]; simp [Data.rawIn, Fin.ext_iff, C4Set.vIN, C4Set.vNT, a2]
      · rw [hL]; simp [Data.rawIn, Fin.ext_iff, C4Set.vIN, C4Set.vNT, C4Set.vLT, a3]
      · rw [hD]; simp [Data.rawIn, Fin.ext_iff, C4Set.vIN, C4Set.vNT, C4Set.vLT, C4Set.vCT, a4]
    | none =>
      rw [hbl5 _ (by rw [slx_none hj]; omega)]
      unfold Lay.extDA at hj
      split_ifs at hj with a0 a2 a3 a4
      by_cases hlt : j.val < Data.DS + 2 + Data.DR
      · rw [ac_lt _ _ j hlt]
        simp [Data.rawIn, Fin.ext_iff, C4Set.vIN, C4Set.vNT, C4Set.vLT, C4Set.vCT, a0, a2, a3, a4]
      · rw [ac_ge _ _ j (by omega)]
        rfl
  obtain ⟨st, bl, un, -, ex⟩ := stageP h3 (3 + L.X) hoff (extD L hx x3)
    (fun i j g hi hj => by
      unfold extD at hi hj
      split_ifs at hi hj with h1 h2
      simp only [Option.some.injEq] at hi hj
      rw [← hj] at hi
      have := hsl (liftE_inj hx hi)
      have := congrArg Fin.val this
      exact Fin.ext this)
    (fun i g hi => by
      unfold extD at hi
      split_ifs at hi with h1
      simp only [Option.some.injEq] at hi
      rw [← hi, liftE_val]
      exact (slx L.oDA (hDA L) L.extDA _).isLt)
    B
    (fun j g hj => by
      unfold extD at hj
      split_ifs at hj with h1
      simp only [Option.some.injEq] at hj
      rw [← hj, hBB, hin, ac_lt _ _ j h1])
    hblB
    (fun j hj => by
      unfold extD at hj
      split_ifs at hj with h1
      rw [ac_ge _ _ j (by omega)])
  -- the lifted data tapes
  have exv : ∀ j : Fin (Data.DS + 2 + Data.DR + 1),
      install (slx (3 + L.X) hoff (extD L hx x3)) B
        (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J)
        (liftE hx (slx L.oDA (hDA L) L.extDA j)) = Fin.addCases tout (fun _ : Fin 1 => List.replicate m false) j := by
    intro j
    have e : extD L hx x3 ⟨j.val, by omega⟩ = some (liftE hx (slx L.oDA (hDA L) L.extDA j)) := by
      unfold extD; rw [dif_pos j.isLt]
    rw [ex _ _ e, ac_lt _ _ _ j.isLt]
  refine ⟨_, st, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : slx L.oDA (hDA L) L.extDA ⟨0, by omega⟩ = L.gP0 := slx_some (by simp [Lay.extDA])
    rw [← e0, exv, ac_lt _ _ _ (by norm_num)]
    exact hI
  · have hn6 : L.extDA ⟨6, by omega⟩ = none := by simp [Lay.extDA]
    have e6 : slx L.oDA (hDA L) L.extDA ⟨6, by omega⟩ = L.gDO := Fin.ext (by rw [slx_none hn6]; lv)
    rw [← e6, exv, ac_lt _ _ _ (by norm_num)]
    exact hO
  · intro i hi a0 a2 a3 a4
    rw [un _ (by rw [liftE_val]; exact i.isLt), hBB]
    intro j e
    unfold extD at e
    split_ifs at e with h1
    simp only [Option.some.injEq] at e
    have e' := liftE_inj hx e
    cases hj : L.extDA ⟨j.val, h1⟩ with
    | some g =>
      rw [slx_some hj] at e'
      subst e'
      unfold Lay.extDA at hj
      split_ifs at hj <;> simp at hj <;> subst hj <;> simp_all
    | none =>
      have := congrArg Fin.val e'
      rw [slx_none hj] at this
      omega
  · intro i hi
    rw [un _ (by rw [liftE_val]; exact i.isLt), hBB, hbl5 i (by unfold Lay.oCP at hi; unfold Lay.oDA; omega)]
    intro j e
    unfold extD at e
    split_ifs at e with h1
    simp only [Option.some.injEq] at e
    have e' := liftE_inj hx e
    cases hj : L.extDA ⟨j.val, h1⟩ with
    | some g =>
      rw [slx_some hj] at e'
      have := extDA_lt L _ g hj
      rw [← e'] at hi
      unfold Lay.oCP at hi; unfold Lay.oDA at this; omega
    | none =>
      have := congrArg Fin.val e'
      rw [slx_none hj] at this
      unfold Lay.oCP at hi; unfold Lay.oDA at this; omega
  · intro i hi
    exact bl i hi

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
