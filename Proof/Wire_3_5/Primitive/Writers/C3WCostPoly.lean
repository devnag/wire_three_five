import Proof.Wire_3_5.Primitive.Writers.C3WCallBase

/-! # C3 request writer, part 17: the run's steps as one polynomial

`Rm Dv Z`: the run's steps with every quantity replaced by `Z` (`runCost_le`), polynomially bounded in `Z` (`pb_Rm`).

Paper quantity: the request writer's steps within the preprocessing class `2^{O(Ψ)}` (P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires.RepairRepresentation (natWord)

/-- The squared capacity at `Z`. -/
def SQ (Z : ℕ) : ℕ := 200 * (258 * Z + 4) * (258 * Z + 4)

/-- The two header numbers' words at `Z`. -/
def NW (Z : ℕ) : ℕ := 2 * (Z + 1) + 1 + (2 * (Z + 2) + 1)

/-- The first program's steps at `Z`. -/
def c1Z (Z : ℕ) : ℕ :=
  (Z + Z + Z + Z + Z) * 7 + (Z + 1 + 2) * (40 * (2 * Z + 2) + 40) + (5 * Z + Z * (SQ Z + 9 * Z + 30)) + 20 +
    ((Z + 1 + 2) * (40 * (2 * Z + 2) + 40) + 5 * SQ Z + Z * (SQ Z + 6 * (4 * Z + 2) + 10) + 10) +
    (3 * SQ Z + 25 * Z + 50 * Z + 50 * Z + 60 * Z + 21 * (Z + Z + Z) + 400) + 2

/-- **The run's steps with every quantity by `Z`.** -/
def Rm (Dv Z : ℕ) : ℕ :=
  2 * (2 * Z + 1) + 2 + 1 + (2 * (8 * Z + 20 * (Z + 1) + 17) + 2) + 1 + (2 * Z + 9 + (2 * Z + 2 + Dv * (10 * Z + 7))) +
    1 + (2 * (3 * Z + 1 + 1 + ((2 * 32 + 3) * Z + 1 + 1 + ((2 * 32 + 3) * Z + 1 + 1 + ((2 * 32 + 3) * Z + 1 + 1 +
    ((2 * 32 + 3) * Z + 1))))) + 2) + 1 +
    (Z + 1 + Z + 1 + Z + 1 + Z + 1 + Z + 1 + Z + 1 + Z + 1 + Z) + 1 +
    (2 * (11 * (129 * Z) + 20 + 1 + 1 + 1 + c1Z Z) + 2) + 1 + Z + 1 +
    (2 * (5 * Z + 11 * Z + 2 * SQ Z + (Z + Z + 13) * (200 * (Z + Z + 1) + 400) + 40) + 2) + 1 +
    (2 * (5 * SQ Z + 21 * (Z + Z + Z + (Z + 1) + Z) + 25 * Z + 60 * Z + 70 * Z + 50 * (NW Z + Z) + 330) + 2)

theorem pb_Rm (Dv : ℕ) : PolynomiallyBounded (fun Z => Rm Dv Z) := by
  simp only [Rm, c1Z, SQ, NW]
  iterate 120 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

/-- The polynomial's coefficient and degree. -/
noncomputable def cR (Dv : ℕ) : ℕ := Classical.choose (pb_Rm Dv)
noncomputable def dR (Dv : ℕ) : ℕ := Classical.choose (Classical.choose_spec (pb_Rm Dv))

theorem Rm_le (Dv Z : ℕ) : Rm Dv Z ≤ cR Dv * (Z + 1) ^ dR Dv :=
  (Classical.choose_spec (Classical.choose_spec (pb_Rm Dv))).2 Z

theorem sq_le (c Z : ℕ) (h : c ≤ 258 * Z + 2) : UnaryPow.sq c ≤ SQ Z := by
  unfold UnaryPow.sq SQ
  have : c + 2 ≤ 258 * Z + 4 := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) this

theorem nbl_le (x Z : ℕ) (h : x ≤ Z) : natBitLength x ≤ Z + 1 := by
  have := PrimAsm.CopyNat.natBitLength_le_self_succ x; omega

theorem pnbl_le (x Z : ℕ) (h : x ≤ Z) : 2 ^ natBitLength x ≤ 2 * Z + 2 := by
  have := PrimAsm.CopyNat.two_pow_natBitLength_le x; omega

/-- **The run's steps below `Rm`** when every quantity is at most `Z`. -/
theorem runCost_le (P : Wr5) (Dv Cv : ℕ) {Ua : ℕ} (w : List Bool)
    (n h Q m pr BG BS BW BF BC wd g wd' nc FL F gyl syl nA ysl atl S y10l Z : ℕ)
    (hw : w.length ≤ Z) (hn : n ≤ Z) (hh : h ≤ Z) (hQ : Q ≤ Z) (hm : m ≤ Z) (hpr : pr ≤ Z) (hBG : BG ≤ Z)
    (hBS : BS ≤ Z) (hBW : BW ≤ Z) (hBF : BF ≤ Z) (hBC : BC ≤ Z) (hwd : wd ≤ Z) (hg : g ≤ Z) (hwd' : wd' ≤ Z)
    (hnc : nc ≤ Z) (hFL : FL ≤ Z) (hF : F ≤ Z) (hgyl : gyl ≤ Z) (hsyl : syl ≤ Z) (hnA : nA ≤ Z) (hysl : ysl ≤ Z)
    (hatl : atl ≤ Z) (hS : S ≤ Z) (hy10 : y10l ≤ Z) (hV : UnaryCalc.value Dv Cv n ≤ Z) (hCv : Cv ≤ Z) :
    P.runCost Dv Cv (Ua := Ua) w n h Q m pr BG BS BW BF BC wd g wd' nc FL F gyl syl nA ysl atl S y10l ≤ Rm Dv Z := by
  have hfill : (P.lay Ua Dv Cv).fillW n h Q m pr ≤ 129 * Z := by
    show UnaryCalc.value Dv Cv n + 32 * (h + Q + m + pr) ≤ 129 * Z; omega
  have hsq : UnaryPow.sq (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) ≤ SQ Z := sq_le _ _ (by omega)
  have hpow : PCPSerializerCapacity.Power.budget Dv Cv n ≤ 2 * Z + 9 + (2 * Z + 2 + Dv * (10 * Z + 7)) := by
    have p := PrimT.FlipsPack.power_le Dv Cv n
    have hV' : Cv * (n + 1) ^ Dv ≤ Z := hV
    have e : 10 * Cv * (n + 1) ^ Dv ≤ 10 * Z := by rw [mul_assoc]; omega
    have e2 : Dv * (10 * Cv * (n + 1) ^ Dv + 7) ≤ Dv * (10 * Z + 7) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hnw : (natWord nc ++ natWord (pr + 1)).length ≤ NW Z := by
    rw [List.length_append, RepairOrdinary.DecompositionSource.natWord_length,
      RepairOrdinary.DecompositionSource.natWord_length]
    have := nbl_le nc Z hnc
    have := nbl_le (pr + 1) (Z + 1) (by omega)
    unfold NW; omega
  unfold Wr5.runCost Lay.frCost crCost appCost appCostP Wr5.wrCost c1Cost Rm c1Z
  gcongr
  all_goals first
    | assumption
    | exact nbl_le _ _ (by assumption)
    | exact pnbl_le _ _ (by assumption)
    | omega

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
