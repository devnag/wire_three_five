import Proof.Wire_3_5.Primitive.SeedFix.FlipsSetup

/-! # FLIPS, part 13: the flips writer's run (P3:1224, 1206-1207)

"Its corners are `c+u+v`, `c+u`, `c+v`, `c`" (P3:1224): for every cell of the partition's two halves (left-major,
right-minor) the flips writer prints the four corner points at the coset offset. The writer **`flipsW cr`** is the
set-up (`init_spec`), the row loop (`lLoop_spec`, every row's column loop) and the field's end bit. Here:

* `loopCap_of`: the loops' register bounds from `8n + 8 ≤ cap`;
* **`flips_spec`**: from the writer's start state, `flipsW cr` keeps the request and prints C3a's flips field
  `C4Geo.flipsField P σ` (`flipsField_eq`, `offW_eq`) within `flipsCost`;
* **`flips_run`**: the machine `geoM (flipsW cr) Dv Cv` writes the flips field from `frame req.word`
  (`WriterIfaceJ.WriterRun`, `geo_run`).

Paper quantity of the main types: C3a's flips field (the corner points of every cell at the coset offset). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT σG geoM gInP gOutP frontCost)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

/-- The loops' register bounds at the call's star numbers. -/
theorem loopCap_of (P : StarParams) (cap : ℕ) (hc : 8 * P.n + 8 ≤ cap) :
    LoopCap P.s P.b (P.r / 2) (P.n - P.r * P.b) cap := by
  have hrb := P.r_mul_b_le
  have hsplit := half_split P
  have hkh := kh_le P
  have hbs := P.b_succ
  have hbn := PrimAsm.GeoNums.b_le P
  have hr4 := P.four_r_le_n
  have h0 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  unfold LoopCap DecCap
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- **The flips writer**: the set-up, the row loop, the field's end bit. -/
def flipsW (cr : ℕ) : WM GS GR := .seq (initW cr) (.seq lLoop (emitW gOUT false))

/-- Its cost at a call. -/
def flipsCost (r : PrimRequest) (P : StarParams) (cr : ℕ) : ℕ :=
  initWCost r P cr + 1 + ((2 ^ (P.s * (P.r / 2)) - 1 + 1) *
    (lBodyCost P.s P.b (P.r / 2) (P.n - P.r * P.b) + 2) + 1 + 1 + 3)

theorem word_nat (r : PrimRequest) (P : StarParams) (hn : r.n = P.n) :
    r.word = natWord P.n ++ ([PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++
      (PrimAsm.Codec.codeList r).flatMap natWord ++ natWord (PrimAsm.Codec.carrierCodes r).length ++
      (PrimAsm.Codec.carrierCodes r).flatMap natWord ++ natWord r.translation.length ++
      r.translation.flatMap natWord) := by
  rw [word_split, ← hn]
  simp only [preT, List.append_assoc]

/-- **The flips writer prints C3a's flips field** and keeps the request (P3:1224). -/
theorem flips_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (r : PrimRequest)
    (hn : r.n = P.n) (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s)
    (hW : 2 * P.n + cr + 20 ≤ W) (hcap : 4 * r.word.length + 8 * P.n + 8 ≤ 2 * W + 2) :
    ∃ σF, WExec (2 * W + 2) (flipsW cr) (σG r.word P.n W) σF (flipsCost r P cr) ∧
      σF.st gIN = RepairOrdinary.frame r.word ∧
      σF.st gOUT = C4Geo.flipsField P (P.translationOfCodes r.translation) := by
  obtain ⟨σI, eI, fI⟩ := init_spec cr W P hrP r hn hl hts hW hcap
  have hN : 1 ≤ 2 ^ (P.s * (P.r / 2)) := Nat.one_le_two_pow
  have e0 : ([] : List Bool) ++ outL P.s P.b (P.r / 2) (P.n - P.r * P.b)
      (List.ofFn (C4Geo.offset P (P.translationOfCodes r.translation))) 0 = [] := by simp [outL]
  rw [← e0] at fI
  obtain ⟨τ, EL', ER', eL, fL⟩ := lLoop_spec (2 * W + 2) P.s P.b (P.r / 2) (P.n - P.r * P.b) (σG r.word P.n W)
    (List.ofFn (C4Geo.offset P (P.translationOfCodes r.translation))) P.b_succ (loopCap_of P _ (by omega)) []
    (2 ^ (P.s * (P.r / 2)) - 1) 0 σI _ _ (by omega) fI
  have eE := emitW_spec (cap := 2 * W + 2) gOUT false τ (by rw [fL.hO, fL.sO])
  refine ⟨_, WExec.seq eI (WExec.seq eL eE), ?_, ?_⟩
  · simp only [WState.sets, WState.seth, Function.update_apply, if_neg (show gIN ≠ gOUT by decide)]
    rw [fL.sIN]
    simp [σG]
  · simp only [WState.sets, WState.seth, Function.update_apply, ↓reduceIte]
    rw [fL.sO, List.nil_append, flipsField_eq]
    rfl

/-- **The flips writer's run** (`WriterIfaceJ.WriterRun`): the machine `geoM (flipsW cr) Dv Cv` writes C3a's flips
field from `frame req.word` within any budget above its steps. -/
theorem flips_run (cr Dv Cv : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (r : PrimRequest)
    (hn : r.n = P.n) (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s)
    (hW : 2 * P.n + cr + 20 ≤ UnaryCalc.value Dv Cv P.n)
    (hcap : 4 * r.word.length + 8 * P.n + 8 ≤ 2 * UnaryCalc.value Dv Cv P.n + 2) (Bud : ℕ)
    (hB : 2 * (frontCost r.word P.n Dv Cv + flipsCost r P cr) + 2 ≤ Bud) :
    PrimAsm.WriterIfaceJ.WriterRun (geoM (flipsW cr) Dv Cv) Bud (gInP Dv) (gOutP Dv) r.word
      (C4Geo.flipsField P (P.translationOfCodes r.translation)) := by
  obtain ⟨σF, e, hI, hO⟩ := flips_spec cr (UnaryCalc.value Dv Cv P.n) P hrP r hn hl hts hW hcap
  exact PrimAsm.GeoFront.geo_run (flipsW cr) Dv Cv P.n _ Bud r.word _ _ (word_nat r P hn) σF e hI hO hB

end NearCubicWires.WireExponent3_5.PrimT.Flips
