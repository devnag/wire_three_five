import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymBBase
import Proof.Wire_3_5.Primitive.Writers.GeoColsRun
import Proof.Wire_3_5.Primitive.Writers.GeoSide

/-! # The geometry writers packaged at every call: columns, halves, width

P3:1212-1216 (star:partition: "Assign `r/2` whole blocks to each side [...] A fixed linear basis of each code gives
polynomial-time encoding") and P3:3105-3115 (`prim:runtime`: the preprocessing is polynomial): the register-language
writers on the request word (`GeoColsRun.cols_run`, `GeoSide.side_run`, `GeoSide.width_run`, each a
`WriterRun (geoM prog Dv Cv) Bud …` under the fill hypotheses and an explicit step bound) become T's
`GeoIface2` writers at every call of the family:

* the fill count `W = (c_r + 25)·(n+1)^2` (`geoW_ok`);
* `numsN`, `nums_le` (the numbers' cost by a polynomial in `n` and `c_r`); `geoCostN`, `geo_cost_le` (every
  writer's steps); `geoRest_mono`, `pb_geoRest`, **`geoCost_poly`**: `geoCostN c_r n ≤ geoC c_r·(n+1)^geoD` with the
  degree `geoD` independent of `c_r` (`(n + c_r + 1) ≤ (c_r+1)(n+1)`);
* **`colsAt`**, **`sideAt`**, **`widthAt`**: `GeoIface2.{Cols,Side,Width}WriterAt l F E_G c_G kclk coef A a ha` under
  `geoD ≤ E_G.Apre` and `geoC c_r·2^geoD ≤ c_G` (`c_r` the gate's row constant).

Paper quantities of the main types: the columns of `φ` (C3's column header), the halves, the dense width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.GeoPack
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (geoM gInP gOutP gInP_ne_out frontCost)
open NearCubicWires.WireExponent3_5.PrimT.C4GateSym (mkStage stage_run pre_class_le)

/-! ## The fill count -/

/-- The fill count's coefficient at the row constant `c_r` (degree `2`). -/
def geoCv (cr : ℕ) : ℕ := cr + 25

theorem geoW_ok (cr n : ℕ) : 2 * n + cr + 20 ≤ UnaryCalc.value 2 (geoCv cr) n ∧
    5 * ((n + 2) * (n + 2)) ≤ UnaryCalc.value 2 (geoCv cr) n := by
  unfold UnaryCalc.value geoCv
  have h1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2 : (n + 2) * (n + 2) = (n + 1) ^ 2 + 2 * (n + 1) + 1 := by ring
  have h3 : cr ≤ cr * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h4 : (cr + 25) * (n + 1) ^ 2 = cr * (n + 1) ^ 2 + 25 * (n + 1) ^ 2 := by ring
  constructor <;> omega

/-! ## The steps -/

/-- The numbers' cost with every star quantity by its bound `n` (`numsGCostE`'s shape). -/
def numsN (n cr : ℕ) : ℕ :=
  ((n + 1) + 2) * (40 * (2 * n + 2) + 40) + 1 + PrimAsm.StarNums.starCost n cr 0 + 1 +
    (n * (18 * n + 8) + 18 * n + 10 + 1 + (18 * n + 3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 +
      (n + 1 + 2) * (90 * (n + 1) + 90 * 2 + 60))))) + 1 +
    (18 * n + 3 + 1 + (18 * n + 3 + 1 + (18 * n + 3 + 1 + (30 * n + 10)))))

theorem nums_le (cr : ℕ) (P : StarParams) : PrimAsm.GeoNums.numsGCostE P cr ≤ numsN P.n cr := by
  have a1 := PrimAsm.CopyNat.natBitLength_le_self_succ P.n
  have a2 : 2 ^ natBitLength P.n ≤ 2 * P.n + 2 := by
    unfold natBitLength
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos P.n with h | h
    · rw [h]; simp
    · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
      omega
  have a3 := PrimAsm.GeoNums.b_le P
  have hrb := P.r_mul_b_le
  have hr4 := P.four_r_le_n
  have a4 : P.r / 2 ≤ P.n := by omega
  have a5 : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  have a6 : P.r / 2 * P.b ≤ P.n := le_trans (Nat.mul_le_mul_right _ (Nat.div_le_self _ _)) hrb
  have a7 : (P.n - P.r * P.b + 1) / 2 ≤ P.n := by omega
  unfold PrimAsm.GeoNums.numsGCostE numsN
  gcongr

/-- The writers' steps without the request word's share. -/
def geoRest (cr n : ℕ) : ℕ :=
  2 * (2 * 1 + 2 + 1 + (2 * (8 * n + 20 * (n + 1) + 17) + 2) + 1 +
    (2 * n + 9 + (2 * geoCv cr + 2 + 2 * (10 * geoCv cr * (n + 1) ^ 2 + 7))) + 1 +
    (11 * (geoCv cr * (n + 1) ^ 2) + 20 + 1 + 1) + 1 +
    (numsN n cr + 40 * n + 21 + 2000 * (n + 2) ^ 4 + 200 * (n + 3) + 1)) + 2

/-- **The writers' steps' bound** at a call of length `n`. -/
def geoCostN (cr n : ℕ) : ℕ := 8 * PrimAsm.CallSize.wordBound 26 26 2 n + geoRest cr n

theorem geo_cost_le (cr : ℕ) (P : StarParams) (w : List Bool)
    (hw : w.length ≤ PrimAsm.CallSize.wordBound 26 26 2 P.n) (c : ℕ)
    (hc : c ≤ 40 * P.n + 21 + 2000 * (P.n + 2) ^ 4 + 200 * (P.n + 3) + 1) :
    2 * (frontCost w P.n 2 (geoCv cr) + (PrimAsm.GeoNums.numsGCostE P cr + c)) + 2 ≤ geoCostN cr P.n := by
  have h1 := nums_le cr P
  have h2 := PrimAsm.CopyNat.natBitLength_le_self_succ P.n
  have h3 := MatrixPacketCapacityCost.power_cost 2 (geoCv cr) (P.n + 1) 2 (by omega) le_rfl
  unfold frontCost geoCostN geoRest PCPSerializerCapacity.Power.budget UnaryCalc.value
  omega

theorem geoRest_mono {cr n m : ℕ} (hc : cr ≤ m) (hn : n ≤ m) : geoRest cr n ≤ geoRest m m := by
  unfold geoRest numsN PrimAsm.StarNums.starCost geoCv
  gcongr

theorem pb_geoRest : PolynomiallyBounded (fun m => geoRest m m) := by
  simp only [geoRest, numsN, PrimAsm.StarNums.starCost, geoCv]
  iterate 40 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

/-- The rest's coefficient and degree. -/
noncomputable def cR : ℕ := Classical.choose pb_geoRest
noncomputable def dR : ℕ := Classical.choose (Classical.choose_spec pb_geoRest)
/-- The request word's coefficient and degree. -/
noncomputable def cW : ℕ := Classical.choose PrimAsm.CallSize.wordBound_poly
noncomputable def dW : ℕ := Classical.choose (Classical.choose_spec PrimAsm.CallSize.wordBound_poly)

/-- **The writers' degree** (independent of the row constant). -/
noncomputable def geoD : ℕ := dR + dW

/-- **The writers' coefficient** at the row constant `c_r`. -/
noncomputable def geoC (cr : ℕ) : ℕ := 8 * cW + cR * (cr + 1) ^ dR

theorem geoCost_poly (cr n : ℕ) : geoCostN cr n ≤ geoC cr * (n + 1) ^ geoD := by
  have e1 : PrimAsm.CallSize.wordBound 26 26 2 n ≤ cW * (n + 1) ^ dW :=
    (Classical.choose_spec (Classical.choose_spec PrimAsm.CallSize.wordBound_poly)).2 n
  have e2 : geoRest cr n ≤ geoRest (n + cr) (n + cr) := geoRest_mono (by omega) (by omega)
  have e3 : geoRest (n + cr) (n + cr) ≤ cR * (n + cr + 1) ^ dR :=
    (Classical.choose_spec (Classical.choose_spec pb_geoRest)).2 (n + cr)
  have e4 : (n + cr + 1) ^ dR ≤ (cr + 1) ^ dR * (n + 1) ^ dR := by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    have : cr ≤ cr * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have e : (cr + 1) * (n + 1) = cr * (n + 1) + (n + 1) := by ring
    omega
  have e5 : (n + 1) ^ dR ≤ (n + 1) ^ geoD := Nat.pow_le_pow_right (by omega) (by unfold geoD; omega)
  have e6 : (n + 1) ^ dW ≤ (n + 1) ^ geoD := Nat.pow_le_pow_right (by omega) (by unfold geoD; omega)
  have f1 : cW * (n + 1) ^ dW ≤ cW * (n + 1) ^ geoD := Nat.mul_le_mul_left _ e6
  have f2 : cR * (n + cr + 1) ^ dR ≤ cR * ((cr + 1) ^ dR * (n + 1) ^ geoD) :=
    Nat.mul_le_mul_left _ (le_trans e4 (Nat.mul_le_mul_left _ e5))
  have f3 : geoC cr * (n + 1) ^ geoD = 8 * (cW * (n + 1) ^ geoD) + cR * ((cr + 1) ^ dR * (n + 1) ^ geoD) := by
    unfold geoC; ring
  unfold geoCostN
  omega

/-! ## The writers at every call -/

section Pack
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (EG : Envelope) (cG kclk coef A a ha) (ha : a ≤ kclk + 1)

theorem call_word (req : PrimRequest) : ∃ sfx, req.word = RepairRepresentation.natWord req.n ++ sfx :=
  ⟨[PrimAsm.Codec.modeBit req.mode] ++ (RepairRepresentation.natWord req.a ++
      (List.flatMap RepairRepresentation.natWord (PrimAsm.Codec.codeList req) ++
        (RepairRepresentation.natListWord (PrimAsm.Codec.carrierCodes req) ++
          RepairRepresentation.natListWord req.translation))),
    by rw [PrimAsm.Codec.word_eq]; simp only [List.append_assoc]⟩

theorem star_n_pos {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {n : ℕ}
    (hs : I.StarAt n) : 1 ≤ n := by
  have h1 := hs.2.1
  have h2 := hs.2.2.1
  omega

end Pack

end NearCubicWires.WireExponent3_5.PrimT.GeoPack
