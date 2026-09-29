import Proof.Wire_3_5.Primitive.SeedFix.FlipsPack

/-! # SA's slot 0, part 1: the geo writer prints the offset word

"The coset offset" (P3:1206-1207, 1224): the flips set-up `initW` leaves the offset `List.ofFn (C4Geo.offset P σ)`
framed on `sOFF`; one more frame copy puts it on the geo bank's output `gOUT`. Wrapped by `geoM` at the flips
parameters (`flD`, `flCv c_r`), the writer runs from `frame r.word`:

* **`offW cr`**, **`offW_spec`** (the offset word on `gOUT`, the request kept);
* **`offCost`**, **`offRun`** (`WriterRun (geoM (offW cr) flD (flCv cr)) … r.word (frame OFFw)` at a call's
  parameters);
* **`offCost_le`**: the writer's budget within `(cA + 100)·(m+1)^{dA+1}` for any `m ≥ n, c_r, |r.word|` (`front_le`, `init_le`, `allM_le`).

Paper quantity of the main type: the coset offset word (P3:1206-1207, 1224; S4's word 0, P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT σG geoM gInP gOutP frontCost)
open NearCubicWires.WireExponent3_5.PrimT.Flips NearCubicWires.WireExponent3_5.PrimT.FlipsPack

/-- **The offset writer's program**: the set-up, then the offset frame copied to the output. -/
def offW (cr : ℕ) : WM GS GR := .seq (initW cr) (PrimT.CarWM.copyFrameW sOFF gOUT)

/-- The offset word at a star parameter set and translation. -/
noncomputable def offWord (P : StarParams) (r : PrimRequest) : List Bool :=
  List.ofFn (PrimT.C4Geo.offset P (P.translationOfCodes r.translation))

theorem offW_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (r : PrimRequest) (hn : r.n = P.n)
    (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) (hW : 2 * P.n + cr + 20 ≤ W)
    (hcap : 4 * r.word.length + 8 * P.n + 8 ≤ 2 * W + 2) :
    ∃ σF, WExec (2 * W + 2) (offW cr) (σG r.word P.n W) σF
        (initWCost r P cr + 1 + (14 * (offWord P r).length + 5)) ∧
      σF.st gIN = frame r.word ∧ σF.st gOUT = frame (offWord P r) ∧
      (offWord P r).length = P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) := by
  obtain ⟨σ, e, hF⟩ := init_spec cr W P hrP r hn hl hts hW hcap
  obtain ⟨τ, s2, eO, -, -, -, oth, -, -⟩ := PrimT.CarWM.copyFrame_spec (2 * W + 2) sOFF gOUT (by decide) []
    (offWord P r) [] σ (by rw [hF.stOF, frame_eq_frameP]; simp [offWord]) (by rw [hF.shOF]; rfl)
    (by rw [hF.hO, hF.sO])
  refine ⟨τ, WExec.seq e s2, ?_, ?_, hF.lOF⟩
  · rw [(oth gIN (by decide) (by decide)).1, hF.sIN]
    simp [σG]
  · rw [eO, hF.sO]; simp

/-- **The offset writer's budget** at a call. -/
noncomputable def offBud (r : PrimRequest) (P : StarParams) (cr : ℕ) : ℕ :=
  2 * (frontCost r.word P.n flD (flCv cr) + (initWCost r P cr + 1 + (14 * (offWord P r).length + 5))) + 2

/-- **The offset writer from `frame r.word`** (`geo_run` at the flips parameters). -/
theorem offRun (cr : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (r : PrimRequest) (hn : r.n = P.n)
    (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s)
    (hwb : r.word.length ≤ PrimAsm.CallSize.wordBound 26 26 2 P.n) :
    PrimAsm.WriterIfaceJ.WriterRun (geoM (offW cr) flD (flCv cr)) (offBud r P cr) (gInP flD) (gOutP flD) r.word
      (frame (offWord P r)) := by
  obtain ⟨hW, hcap⟩ := fill_ok cr P.n r.word.length hwb
  obtain ⟨σF, e, hI, hO, -⟩ := offW_spec cr (UnaryCalc.value flD (flCv cr) P.n) P hrP r hn hl hts hW hcap
  exact PrimAsm.GeoFront.geo_run (offW cr) flD (flCv cr) P.n _ _ r.word _ _ (word_nat r P hn) σF e hI hO le_rfl

/-- **The offset writer's budget, polynomially**: for any `m` above `n`, `c_r` and `|r.word|`. -/
theorem offBud_le (r : PrimRequest) (P : StarParams) (cr m : ℕ) (hn : P.n ≤ m) (hc : cr ≤ m)
    (hw : r.word.length ≤ m) (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) :
    offBud r P cr ≤ (cA + 100) * (m + 1) ^ (dA + 1) := by
  have f1 := front_le (m := m) r.word P.n cr hw hn hc
  have f2 := init_le (m := m) r P cr hn hc hw hl hts
  have f3 := allM_le m
  have hlen : (offWord P r).length ≤ 3 * m := by
    unfold offWord; rw [List.length_ofFn]; omega
  have e1 : (m + 1) ^ dA ≤ (m + 1) ^ (dA + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : m + 1 ≤ (m + 1) ^ (dA + 1) := Nat.le_self_pow (by omega) _
  have e3 := Nat.mul_le_mul_left cA e1
  have e4 : (cA + 100) * (m + 1) ^ (dA + 1) = cA * (m + 1) ^ (dA + 1) + 100 * (m + 1) ^ (dA + 1) := by ring
  unfold offBud
  rw [e4]
  unfold allM at f3
  omega

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
