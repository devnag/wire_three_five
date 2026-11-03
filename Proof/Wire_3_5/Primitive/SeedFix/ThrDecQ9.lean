import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ8
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.UnionMachine.ThrUnitIface
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ9Base


noncomputable section
set_option maxRecDepth 120000


/-! # T3 THR decode front, packaging part 9: `ThrDecFront` and its uniform family

**`thrDecFront x hx : ThrDec.ThrDecFront x l F`** at every cell layout `x ≥ dX (TW l) (NW l)`: the machine `frontM`, the
capacity `need n = c₀(n) = cZero (Q_F) (L²) (aE l f_e)` and the cost `bound n = fK·(c₀(n)+1)^{fD}`, both
quasi-bounded with exponents `nK l f_e`, `bK l f_e` from `(l, f_e)` only and coefficients from `F`; the run at every
THR call, unit and capacity `≥ need n + j` (`call_run`). **`thrDecU`**: the fronts as a uniform family
(`Seams.StageU`, `ThrUnit.decDeg`/`decCf`) at any cells `xF F ≥ dX (TW l) (NW l)`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape within
`2^{O(L²)}` (P3:2543-2558, 2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine

/-- The capacity's coefficient (from `F`) and exponent (from `(l, f_e)`). -/
noncomputable def nC (l : Literals) (F : GateFree l) : ℕ := qF l F ^ (3 * aE l F.filterErrDeg + 20)
noncomputable def nK (l : Literals) (fe : ℕ) : ℕ := (aE l fe + 2) * (3 * aE l fe + 20)

/-- The cost's coefficient (from `F`) and exponent (from `(l, f_e)`). -/
noncomputable def bC (l : Literals) (F : GateFree l) : ℕ :=
  fK (TW l) (NW l) * qF l F ^ ((3 * aE l F.filterErrDeg + 21) * fD (TW l) (NW l))
noncomputable def bK (l : Literals) (fe : ℕ) : ℕ := (aE l fe + 2) * ((3 * aE l fe + 21) * fD (TW l) (NW l))

theorem need_q (l : Literals) (F : GateFree l) (n : ℕ) :
    PrimThrW.RadSetup.QuasiBounded (needT l F n) n (nC l F) 0 (nK l F.filterErrDeg) := by
  have h := qy_pow (Q := qF l F) (Y := Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (i := 1) (a := aE l F.filterErrDeg + 2)
    (X := UQ (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (aE l F.filterErrDeg)) le_rfl
    (3 * aE l F.filterErrDeg + 20)
  rw [one_mul] at h
  exact qb_of_QY h

theorem bound_q (l : Literals) (F : GateFree l) (n : ℕ) :
    PrimThrW.RadSetup.QuasiBounded (boundT l F n) n (bC l F) 0 (bK l F.filterErrDeg) := by
  obtain ⟨U, hU⟩ : ∃ U, U = UQ (qF l F) (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (aE l F.filterErrDeg) := ⟨_, rfl⟩
  have hU2 : 2 ≤ U := hU ▸ UQ_two _ _ _ (by unfold qF; omega) (Y_ge n)
  have hN : needT l F n = U ^ (3 * aE l F.filterErrDeg + 20) := by rw [hU]; rfl
  have h1 : needT l F n + 1 ≤ U ^ (3 * aE l F.filterErrDeg + 21) := by
    have e : U ^ (3 * aE l F.filterErrDeg + 21) = U ^ (3 * aE l F.filterErrDeg + 20) * U := pow_succ _ _
    rw [hN, e]
    have : 1 ≤ U ^ (3 * aE l F.filterErrDeg + 20) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h2 : (needT l F n + 1) ^ fD (TW l) (NW l) ≤ U ^ ((3 * aE l F.filterErrDeg + 21) * fD (TW l) (NW l)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 _
  have h3 := qy_pow (Q := qF l F) (Y := Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) (i := 1) (a := aE l F.filterErrDeg + 2)
    (X := U) (by rw [hU]; exact le_rfl) ((3 * aE l F.filterErrDeg + 21) * fD (TW l) (NW l))
  rw [one_mul] at h3
  have h4 := qb_of_QY (h2.trans h3)
  unfold PrimThrW.RadSetup.QuasiBounded at h4 ⊢
  unfold boundT bC
  calc fK (TW l) (NW l) * (needT l F n + 1) ^ fD (TW l) (NW l)
      ≤ fK (TW l) (NW l) * (qF l F ^ ((3 * aE l F.filterErrDeg + 21) * fD (TW l) (NW l)) * (n + 2) ^ 0 *
          2 ^ ((aE l F.filterErrDeg + 2) * ((3 * aE l F.filterErrDeg + 21) * fD (TW l) (NW l)) *
            Nat.clog 2 (n + 2) ^ 2)) := Nat.mul_le_mul_left _ h4
    _ = _ := by unfold bK; ring

/-- **The THR unit's decode front** at every cell layout `x ≥ dX (TW l) (NW l)`. -/
noncomputable def thrDecFront (x : ℕ) (l : Literals) (hx : dX (TW l) (NW l) ≤ x) (F : GateFree l) :
    ThrDec.ThrDecFront x l F where
  s := _
  M := frontM (TW l) (NW l) x hx F.cr F.filterErrDeg
  need := needT l F
  bound := boundT l F
  Cn := nC l F
  Dn := 0
  Kn := nK l F.filterErrDeg
  need_q := need_q l F
  Cb := bC l F
  Db := 0
  Kb := bK l F.filterErrDeg
  bound_q := bound_q l F
  run := fun kclk coef A a ha n hs a' ha' Cs carriers translation hcall out j cap hcap =>
    call_run x l hx F kclk coef A a ha ha' Cs carriers translation hcall hs out j cap (by omega)

/-- The fronts' exponent bound (from `(l, f_e)`). -/
noncomputable def dD (l : Literals) (fe : ℕ) : ℕ := nK l fe + bK l fe

theorem decDeg_le (x : ℕ) (l : Literals) (hx : dX (TW l) (NW l) ≤ x) (F : GateFree l) :
    ThrUnit.decDeg (thrDecFront x l hx F) ≤ dD l F.filterErrDeg := by
  show max (max 0 (nK l F.filterErrDeg)) (max 0 (bK l F.filterErrDeg)) ≤ nK l F.filterErrDeg + bK l F.filterErrDeg
  omega

/-- **The decode fronts as a uniform family** (`Seams.StageU`) at any cells `xF F ≥ dX (TW l) (NW l)`. -/
noncomputable def thrDecU (l : Literals) (xF : GateFree l → ℕ) (hxF : ∀ F, dX (TW l) (NW l) ≤ xF F) :
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => ThrUnit.decDeg D)
      (fun D => ThrUnit.decCf D) :=
  fun fe => ⟨dD l fe, (⟨0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost.Envelope), 0, fun F hF _ _ =>
    ⟨ThrUnit.decCf (thrDecFront (xF F) l (hxF F) F), fun _ _ _ _ _ =>
      ⟨thrDecFront (xF F) l (hxF F) F, hF ▸ decDeg_le (xF F) l (hxF F) F, le_rfl⟩⟩⟩

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF

end
