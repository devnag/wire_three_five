import Proof.Wire_3_5.Primitive.SeedFix.FlipsRun
import Proof.Wire_3_5.Primitive.SeedFix.GeoPackBase

/-! # FLIPS, part 14: the flips writer at every call, within the selection class

"The running time, including an optional common-coset selection, is `2^{n/2+O(k)}n^{C_D} + …`" (P3:3105-3108): the
flips field lists the four corners of all `2^{k/2}·2^{k/2} = 2^k` cells (P3:1224), so its writer runs in
`2^k·poly(n)` steps, within the selection class `2^{n/2 + c_sel·k}·n^{A_sel}` once `c_sel ≥ 1`. Here:

* the fill count `W = (c_r + 25 + 2c_W)(n+1)^{d_W+2}` (`fill_ok`: the numbers and the request's codes fit);
* the steps' bounds by polynomials in one variable `m ≥ |w|, n, c_r`: `loop_le` (the cell loops, `2^k·QN m`),
  `init_le`, `front_le`, `cost_le_all`, `pb_allM`, `cost_poly` (coefficient `flipsC c_r`, degree `flipsD`
  independent of `c_r`);
* `sel_class_le`, `flips_budget`: the steps within `c_G·classBound E_G .selection n k ψ` under `flipsD ≤ E_G.Asel`,
  `1 ≤ E_G.csel`, `flipsC c_r·2^flipsD ≤ c_G`;
* **`flipsAt`**: `GeoIface2.FlipsWriterAt l F E_G c_G kclk coef A a ha` (the machine `geoM (flipsW c_r) …`).

Paper quantity of the main type: C3a's flips field (`C4Geo.flipsField P σ`, the corner points of every cell, P3:1224)
within the selection class. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.FlipsPack
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT σG geoM gInP gOutP gInP_ne_out frontCost)
open NearCubicWires.WireExponent3_5.PrimT.C4GateSym (mkStage stage_run)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimT.Flips

/-! ## The fill count -/

/-- The fill count's degree. -/
noncomputable def flD : ℕ := GeoPack.dW + 2

/-- The fill count's coefficient at the row constant `c_r`. -/
noncomputable def flCv (cr : ℕ) : ℕ := cr + 25 + 2 * GeoPack.cW

theorem word_le (n : ℕ) : PrimAsm.CallSize.wordBound 26 26 2 n ≤ GeoPack.cW * (n + 1) ^ GeoPack.dW :=
  (Classical.choose_spec (Classical.choose_spec PrimAsm.CallSize.wordBound_poly)).2 n

theorem fill_ok (cr n L : ℕ) (hL : L ≤ PrimAsm.CallSize.wordBound 26 26 2 n) :
    2 * n + cr + 20 ≤ UnaryCalc.value flD (flCv cr) n ∧
      4 * L + 8 * n + 8 ≤ 2 * UnaryCalc.value flD (flCv cr) n + 2 := by
  have hw := word_le n
  have e1 : (n + 1) ^ GeoPack.dW ≤ (n + 1) ^ flD := Nat.pow_le_pow_right (by omega) (by unfold flD; omega)
  have e2 : (n + 1) ^ 1 ≤ (n + 1) ^ flD := Nat.pow_le_pow_right (by omega) (by unfold flD; omega)
  rw [pow_one] at e2
  have e3 : GeoPack.cW * (n + 1) ^ GeoPack.dW ≤ GeoPack.cW * (n + 1) ^ flD := Nat.mul_le_mul_left _ e1
  have e4 : cr ≤ cr * (n + 1) ^ flD := Nat.le_mul_of_pos_right _ (by positivity)
  have e5 : UnaryCalc.value flD (flCv cr) n = cr * (n + 1) ^ flD + 25 * (n + 1) ^ flD +
      2 * (GeoPack.cW * (n + 1) ^ flD) := by
    unfold UnaryCalc.value flCv
    ring
  constructor <;> omega

/-! ## The cell loops' steps -/

section Bounds
variable {s b h tl m : ℕ}

def blkN (m : ℕ) : ℕ := m * (43 * (m + 1) + 30) + 3 * (m + 1) + 7 * m + 34 * m + 22
def decN (m : ℕ) : ℕ := m * blkN m + m * (30 * m + 11) + 14 * m + 30 * m + 10 * (2 * (m * m) + m) + 30
def decStageN (m : ℕ) : ℕ := decN m + 1 + ((2 * (m * m) + 1) * 5 + 1)

/-- One cell's steps' bound (the column body and the row body's share). -/
def QN (m : ℕ) : ℕ := 2 * decStageN m + cornersCost m + 2 * ctrCost m + 41 * m + 18

theorem blk_le (hs : s ≤ m) (hb : b ≤ m) (hbs : b + 1 = 2 ^ s) : FinalPass.Sample.blkCost s b ≤ blkN m := by
  unfold FinalPass.Sample.blkCost blkN
  rw [← hbs]
  gcongr

theorem dec_le (hs : s ≤ m) (hb : b ≤ m) (hh : h ≤ m) (htl : tl ≤ m) (hbs : b + 1 = 2 ^ s) :
    FinalPass.Sample.decCost s b h tl ≤ decN m := by
  have := blk_le hs hb hbs
  unfold FinalPass.Sample.decCost decN
  gcongr

theorem decStage_le (hs : s ≤ m) (hb : b ≤ m) (hh : h ≤ m) (htl : tl ≤ m) (hbs : b + 1 = 2 ^ s) :
    decStageCost s b h tl ≤ decStageN m := by
  have := dec_le hs hb hh htl hbs
  unfold decStageCost decStageN
  gcongr

theorem corners_mono {x y : ℕ} (hxy : x ≤ y) : cornersCost x ≤ cornersCost y := by
  unfold cornersCost cornerCost
  gcongr

theorem ctr_mono {x y : ℕ} (hxy : x ≤ y) : ctrCost x ≤ ctrCost y := by
  unfold ctrCost onesCost
  gcongr

/-- **The cell loops' steps**: `2^{kh}` rows of `2^{kh}` cells, each within `QN m`. -/
theorem loop_le (hs : s ≤ m) (hb : b ≤ m) (hh : h ≤ m) (htl : tl ≤ m) (hbs : b + 1 = 2 ^ s)
    (hn : h * b + h * b + tl ≤ m) (hsh : s * h ≤ m) :
    (2 ^ (s * h) - 1 + 1) * (lBodyCost s b h tl + 2) ≤ 2 ^ (s * h) * 2 ^ (s * h) * QN m := by
  have hN : 1 ≤ 2 ^ (s * h) := Nat.one_le_two_pow
  have hNm : 2 ^ (s * h) - 1 + 1 = 2 ^ (s * h) := by omega
  have q1 := decStage_le hs hb hh htl hbs
  have q2 := corners_mono hn
  have q3 := ctr_mono hsh
  have hA : 2 ^ (s * h) * (rBodyCost s b h tl + 2) +
      2 ^ (s * h) * (decStageCost s b h tl + 41 * (s * h) + ctrCost (s * h) + 13) ≤ 2 ^ (s * h) * QN m := by
    rw [← Nat.mul_add]
    apply Nat.mul_le_mul_left
    unfold rBodyCost QN
    omega
  have h1 : decStageCost s b h tl + 41 * (s * h) + ctrCost (s * h) + 13 ≤
      2 ^ (s * h) * (decStageCost s b h tl + 41 * (s * h) + ctrCost (s * h) + 13) := Nat.le_mul_of_pos_left _ hN
  have h3 : lBodyCost s b h tl + 2 ≤ 2 ^ (s * h) * QN m := by
    unfold lBodyCost
    rw [hNm]
    omega
  rw [hNm, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h3

/-! ## The set-up's and the front's steps -/

/-- The numbers' steps with every quantity by `m`. -/
def numsM (m : ℕ) : ℕ := (m + 1 + 2) * (40 * (2 * m + 2) + 40) + 1 + PrimAsm.StarNums.starCost m m 0

theorem nums_le {n cr : ℕ} (hn : n ≤ m) (hc : cr ≤ m) : numsCost n cr ≤ numsM m := by
  have a1 := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have a2 := PrimAsm.CopyNat.two_pow_natBitLength_le n
  have b1 : natBitLength n ≤ m + 1 := by omega
  have b2 : 2 ^ natBitLength n ≤ 2 * m + 2 := by omega
  unfold numsCost numsM PrimAsm.StarNums.starCost
  gcongr

theorem skipSum_le : ∀ xs : List ℕ,
    (xs.map fun x => 20 * natBitLength x + 24).sum ≤ 24 * (xs.flatMap natWord).length
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have := skipSum_le xs
    have := natWord_length' x
    omega

theorem skipCost_le (xs : List ℕ) : skipCost xs ≤ 24 * (xs.flatMap natWord).length + 1 := by
  have := skipSum_le xs
  unfold skipCost
  omega

theorem word_len (r : PrimRequest) : r.word.length = (natWord r.n).length + 1 + (natWord r.a).length +
    ((PrimAsm.Codec.codeList r).flatMap natWord).length + (natWord (PrimAsm.Codec.carrierCodes r).length).length +
    ((PrimAsm.Codec.carrierCodes r).flatMap natWord).length + (natWord r.translation.length).length +
    (r.translation.flatMap natWord).length := by
  rw [word_split]
  simp only [preT, List.length_append, List.length_singleton]
  try omega

/-- The header skip's steps with every quantity by `m`. -/
def skipM (m : ℕ) : ℕ :=
  1 + 1 + (1 + 1 + ((m + 1 + 2) * (40 * (2 * m + 2) + 40) + 1 +
    ((24 * m + 1) + 1 + ((m + 1 + 2) * (40 * (2 * m + 2) + 40) + 1 +
    ((24 * m + 1) + 1 + (20 * (m + 1) + 20))))))

theorem skip_le (r : PrimRequest) (hw : r.word.length ≤ m) : skipHeadCost r ≤ skipM m := by
  have hlen := word_len r
  have hcl' : (PrimAsm.Codec.codeList r).length = r.a := by simp [PrimAsm.Codec.codeList]
  have c1 := count_le_flatMap (PrimAsm.Codec.codeList r)
  have c2 := count_le_flatMap (PrimAsm.Codec.carrierCodes r)
  have c3 := count_le_flatMap r.translation
  have k1 := skipCost_le (PrimAsm.Codec.codeList r)
  have k2 := skipCost_le (PrimAsm.Codec.carrierCodes r)
  have p1 := PrimAsm.CopyNat.two_pow_natBitLength_le r.a
  have p2 := PrimAsm.CopyNat.two_pow_natBitLength_le (PrimAsm.Codec.carrierCodes r).length
  have q1 := PrimAsm.CopyNat.natBitLength_le_self_succ r.a
  have q2 := PrimAsm.CopyNat.natBitLength_le_self_succ (PrimAsm.Codec.carrierCodes r).length
  have q3 := PrimAsm.CopyNat.natBitLength_le_self_succ r.translation.length
  have b1 : natBitLength r.a ≤ m + 1 := by omega
  have b2 : 2 ^ natBitLength r.a ≤ 2 * m + 2 := by omega
  have b3 : skipCost (PrimAsm.Codec.codeList r) ≤ 24 * m + 1 := by omega
  have b4 : natBitLength (PrimAsm.Codec.carrierCodes r).length ≤ m + 1 := by omega
  have b5 : 2 ^ natBitLength (PrimAsm.Codec.carrierCodes r).length ≤ 2 * m + 2 := by omega
  have b6 : skipCost (PrimAsm.Codec.carrierCodes r) ≤ 24 * m + 1 := by omega
  have b7 : natBitLength r.translation.length ≤ m + 1 := by omega
  unfold skipHeadCost skipM
  gcongr

/-- One code's step bound with every quantity by `m`. -/
def tM (m : ℕ) : ℕ :=
  1 + 1 + ((m + 1 + 2) * (40 * (2 * m + 2) + 40) + 1 + (18 * m + 3 + 1 + (m * 24 + 1))) + 2

theorem tCost_le {b t : ℕ} (hb : b ≤ m) (ht : t ≤ m) : tCost b t ≤ tM m := by
  have a1 := PrimAsm.CopyNat.natBitLength_le_self_succ t
  have a2 := PrimAsm.CopyNat.two_pow_natBitLength_le t
  have b1 : natBitLength t ≤ m + 1 := by omega
  have b2 : 2 ^ natBitLength t ≤ 2 * m + 2 := by omega
  unfold tCost tM
  gcongr

theorem transSum_le (b X : ℕ) : ∀ ts : List ℕ, (∀ t ∈ ts, tCost b t ≤ X) →
    (ts.map (tCost b)).sum ≤ ts.length * X
  | [], _ => by simp
  | t :: ts, hX => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hX t (by simp)
    have h2 := transSum_le b X ts (fun u hu => hX u (by simp [hu]))
    have e : (ts.length + 1) * X = ts.length * X + X := by ring
    omega

/-- The offset's steps with every quantity by `m`. -/
def offM (m : ℕ) : ℕ :=
  18 * m + 3 + 1 + ((m * tM m + 1) + 1 + (18 * m + 3 + 1 + (m * 20 + 1 + 1 + (3 + 1 + (3 + 1 +
    ((2 * m * m + 2 * m + 1) * 5 + 1))))))

theorem off_le {b tl : ℕ} (ts : List ℕ) (hb : b ≤ m) (htl : tl ≤ m) (hl : ts.length ≤ m)
    (ht : ∀ t ∈ ts, t ≤ m) : offCost b tl ts ≤ offM m := by
  have h1 := transSum_le b (tM m) ts (fun t htt => tCost_le hb (ht t htt))
  have h2 : ts.length * tM m ≤ m * tM m := Nat.mul_le_mul_right _ hl
  have h3 : (ts.map (tCost b)).sum ≤ m * tM m := le_trans h1 h2
  unfold offCost offM transCost
  gcongr

theorem initAll_le {n kh : ℕ} (hn : n ≤ m) (hk : kh ≤ m) : initAllCost n kh ≤ initAllCost m m := by
  unfold initAllCost initCost
  gcongr

/-- The set-up's steps with every quantity by `m`. -/
def initM (m : ℕ) : ℕ := numsM m + 1 + (skipM m + 1 + (offM m + 1 + (initAllCost m m + 1 + 3)))

theorem init_le (r : PrimRequest) (P : StarParams) (cr : ℕ) (hn : P.n ≤ m) (hc : cr ≤ m)
    (hw : r.word.length ≤ m) (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) :
    initWCost r P cr ≤ initM m := by
  have hbn := PrimAsm.GeoNums.b_le P
  have hbs := P.b_succ
  have hr4 := P.four_r_le_n
  have hkh := kh_le P
  have a1 := nums_le (m := m) hn hc
  have a2 := skip_le (m := m) r hw
  have a3 := off_le (m := m) (b := P.b) (tl := P.n - P.r * P.b) r.translation (by omega) (by omega) (by omega)
    (fun t ht => by have := hts t ht; omega)
  have a4 := initAll_le (m := m) (n := P.n) (kh := P.s * (P.r / 2)) hn (by omega)
  unfold initWCost initM
  omega

theorem power_le (Dv Cv n : ℕ) : PCPSerializerCapacity.Power.budget Dv Cv n ≤
    2 * n + 9 + (2 * Cv + 2 + Dv * (10 * Cv * (n + 1) ^ Dv + 7)) := by
  have := MatrixPacketCapacityCost.power_cost Dv Cv (n + 1) Dv (by omega) (le_refl _)
  unfold PCPSerializerCapacity.Power.budget
  omega

/-- The front's steps with every quantity by `m`. -/
noncomputable def frontM (m : ℕ) : ℕ :=
  2 * (2 * m + 1) + 2 + 1 + (2 * (8 * m + 20 * (m + 1) + 17) + 2) + 1 +
    (2 * m + 9 + (2 * (m + 25 + 2 * GeoPack.cW) + 2 + flD * (10 * (m + 25 + 2 * GeoPack.cW) * (m + 1) ^ flD + 7))) +
    1 + (11 * ((m + 25 + 2 * GeoPack.cW) * (m + 1) ^ flD) + 20 + 1 + 1) + 1

theorem front_le (w : List Bool) (n cr : ℕ) (hw : w.length ≤ m) (hn : n ≤ m) (hc : cr ≤ m) :
    frontCost w n flD (flCv cr) ≤ frontM m := by
  have p := power_le flD (flCv cr) n
  have q : 2 * n + 9 + (2 * flCv cr + 2 + flD * (10 * flCv cr * (n + 1) ^ flD + 7)) ≤
      2 * m + 9 + (2 * (m + 25 + 2 * GeoPack.cW) + 2 +
        flD * (10 * (m + 25 + 2 * GeoPack.cW) * (m + 1) ^ flD + 7)) := by
    unfold flCv
    gcongr
  have v : UnaryCalc.value flD (flCv cr) n ≤ (m + 25 + 2 * GeoPack.cW) * (m + 1) ^ flD := by
    unfold UnaryCalc.value flCv
    gcongr
  have bn := PrimAsm.CopyNat.natBitLength_le_self_succ n
  unfold frontCost frontM
  omega

/-- **All the writer's steps** with every quantity by `m`, per cell block `2^k`. -/
noncomputable def allM (m : ℕ) : ℕ := 2 * frontM m + 2 * initM m + 2 * QN m + 14

theorem cost_le_all (r : PrimRequest) (P : StarParams) (cr : ℕ) (hn : P.n ≤ m) (hc : cr ≤ m)
    (hw : r.word.length ≤ m) (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) :
    2 * (frontCost r.word P.n flD (flCv cr) + flipsCost r P cr) + 2 ≤
      2 ^ (2 * (P.s * (P.r / 2))) * allM m := by
  have hrb := P.r_mul_b_le
  have hsplit := half_split P
  have hkh := kh_le P
  have hbs := P.b_succ
  have hbn := PrimAsm.GeoNums.b_le P
  have hr4 := P.four_r_le_n
  have h0 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have f1 := front_le r.word P.n cr hw hn hc
  have f2 := init_le r P cr hn hc hw hl hts
  have f3 := loop_le (m := m) (s := P.s) (b := P.b) (h := P.r / 2) (tl := P.n - P.r * P.b) (by omega) (by omega)
    (by omega) (by omega) hbs (by omega) (by omega)
  have hK : 2 ^ (P.s * (P.r / 2)) * 2 ^ (P.s * (P.r / 2)) = 2 ^ (2 * (P.s * (P.r / 2))) := by
    rw [two_mul, pow_add]
  rw [hK] at f3
  have hK1 : 1 ≤ 2 ^ (2 * (P.s * (P.r / 2))) := Nat.one_le_two_pow
  have g1 : 2 * frontM m + 2 * initM m + 14 ≤ 2 ^ (2 * (P.s * (P.r / 2))) * (2 * frontM m + 2 * initM m + 14) :=
    Nat.le_mul_of_pos_left _ hK1
  have g2 : 2 ^ (2 * (P.s * (P.r / 2))) * allM m = 2 ^ (2 * (P.s * (P.r / 2))) * (2 * frontM m + 2 * initM m + 14) +
      2 * (2 ^ (2 * (P.s * (P.r / 2))) * QN m) := by
    unfold allM
    ring
  unfold flipsCost
  omega

end Bounds

/-! ## The steps' polynomial bound -/

theorem pb_allM : PolynomiallyBounded (fun m => allM m) := by
  simp only [allM, frontM, initM, numsM, skipM, offM, tM, QN, decStageN, decN, blkN, cornersCost, cornerCost,
    ctrCost, onesCost, initAllCost, initCost, PrimAsm.StarNums.starCost]
  iterate 80 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

/-- The steps' coefficient and degree in `m`. -/
noncomputable def cA : ℕ := Classical.choose pb_allM
noncomputable def dA : ℕ := Classical.choose (Classical.choose_spec pb_allM)

theorem allM_le (m : ℕ) : allM m ≤ cA * (m + 1) ^ dA :=
  (Classical.choose_spec (Classical.choose_spec pb_allM)).2 m

/-- **The flips writer's degree** (independent of the row constant). -/
noncomputable def flipsD : ℕ := (GeoPack.dW + 1) * dA

/-- **The flips writer's coefficient** at the row constant `c_r`. -/
noncomputable def flipsC (cr : ℕ) : ℕ := cA * (GeoPack.cW + cr + 2) ^ dA

theorem m_le (cr n : ℕ) : GeoPack.cW * (n + 1) ^ GeoPack.dW + n + cr + 1 ≤
    (GeoPack.cW + cr + 2) * (n + 1) ^ (GeoPack.dW + 1) := by
  have e1 : (n + 1) ^ GeoPack.dW ≤ (n + 1) ^ (GeoPack.dW + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (n + 1) ^ 1 ≤ (n + 1) ^ (GeoPack.dW + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at e2
  have e3 : GeoPack.cW * (n + 1) ^ GeoPack.dW ≤ GeoPack.cW * (n + 1) ^ (GeoPack.dW + 1) := Nat.mul_le_mul_left _ e1
  have e4 : cr ≤ cr * (n + 1) ^ (GeoPack.dW + 1) := Nat.le_mul_of_pos_right _ (by positivity)
  have e5 : (GeoPack.cW + cr + 2) * (n + 1) ^ (GeoPack.dW + 1) = GeoPack.cW * (n + 1) ^ (GeoPack.dW + 1) +
      cr * (n + 1) ^ (GeoPack.dW + 1) + 2 * (n + 1) ^ (GeoPack.dW + 1) := by ring
  omega

/-- **The flips writer's steps**: `2^{2kh}·flipsC c_r·(n+1)^flipsD` at a call. -/
theorem cost_poly (r : PrimRequest) (P : StarParams) (cr : ℕ)
    (hw : r.word.length ≤ PrimAsm.CallSize.wordBound 26 26 2 P.n) (hl : r.translation.length = P.r)
    (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) :
    2 * (frontCost r.word P.n flD (flCv cr) + flipsCost r P cr) + 2 ≤
      2 ^ (2 * (P.s * (P.r / 2))) * (flipsC cr * (P.n + 1) ^ flipsD) := by
  have hwb := word_le P.n
  have c1 := cost_le_all (m := GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr) r P cr (by omega) (by omega)
    (by omega) hl hts
  have c2 := allM_le (GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr)
  have c3 : (GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr + 1) ^ dA ≤
      (GeoPack.cW + cr + 2) ^ dA * (P.n + 1) ^ flipsD := by
    rw [flipsD, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (m_le cr P.n) dA
  have c4 : allM (GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr) ≤ flipsC cr * (P.n + 1) ^ flipsD := by
    unfold flipsC
    calc allM (GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr)
        ≤ cA * (GeoPack.cW * (P.n + 1) ^ GeoPack.dW + P.n + cr + 1) ^ dA := c2
      _ ≤ cA * ((GeoPack.cW + cr + 2) ^ dA * (P.n + 1) ^ flipsD) := Nat.mul_le_mul_left _ c3
      _ = cA * (GeoPack.cW + cr + 2) ^ dA * (P.n + 1) ^ flipsD := by ring
  exact le_trans c1 (Nat.mul_le_mul_left _ c4)

/-! ## The flips writer at every call -/

section Pack
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

theorem kh_two (P : StarParams) : 2 * (P.s * (P.r / 2)) = P.r * P.s := by
  obtain ⟨j, hj⟩ := P.r_even
  rw [hj, show (j + j) / 2 = j by omega]
  ring

end Pack

end NearCubicWires.WireExponent3_5.PrimT.FlipsPack
