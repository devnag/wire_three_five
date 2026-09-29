import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2
import Proof.Wire_3_5.Primitive.Writers.HashFit2

/-! # HASH setup (C), fit part 3: the setup's side conditions at the HASH leaf's instance

P3:3011-3016 (the setup before the loop: the front end and the numbers machine read the call at the unary number
`V = value D C_d n`): at the HASH leaf's instance (the layout `symLay wa S3 (hDl l Dnw)`, `C_d = hCd l F Cnw`, the front
end `topFront3`, the numbers machine `numsW6`), from the data stage's premises (`ThrLf.thr_data_W`: `needW n ≤ V` and the
v4 stage's need `needT ≤ 2V + 2`, whose summand `2·needW₆(n + cap)` is the numbers machine's need): the star
parameters' `r = rowBr c_r n`, `1 ≤ n`, `1 ≤ cap_T`, the front end's `TF2Ok` at `V`, the numbers machine's need `≤ V`.

* **`side_ok`**; **`hash_fits`** (one `C_c` threshold for the THR fit `ThrFitAt` (`thr_fits2`), the HASH numbers' fit
  `HashFitX` (`hash_fitsX`) and the cell's `CellFit` with `Bm` within the cell's capacity (`cell_fits`)).

Paper quantities of the main type: the call's unary number `V` and the setup's capacity needs (P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.BlockPlatform

/-- **The setup's side conditions at a THR call** at the HASH leaf's instance. -/
theorem side_ok (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (Cnw Dnw : ℕ)
    (hnw : PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) (wa : RepairRepresentation.WilliamsAlgorithm)
    (S3 : C3ReqIface.C3Stage) :
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).r = Ledger.rowBr F.cr n ∧ 1 ≤ n ∧
      1 ≤ ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ∧
      PrimThrW.TopFront2.TF2Ok Cs (carriers.map Carrier.code)
        (UnaryCalc.value (PrimT.C4SymLf.symLay wa S3 (C4HL.hDl l Dnw)).D (C4HL.hCd l F Cnw) n) ∧
      (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D).need
          (n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤
        UnaryCalc.value (PrimT.C4SymLf.symLay wa S3 (C4HL.hDl l Dnw)).D (C4HL.hCd l F Cnw) n := by
  obtain ⟨hk2, hdesc, henv⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hWL, hLW, -, hneed⟩ := ThrLf.thr_data_W l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs Cnw Dnw
    hnw (PrimT.TS4.NCoef l F.cr) (PrimT.TS4.NDeg l) ((PrimT.TS4.stage4At l F kclk coef A a0 ha0).need n)
    ((PrimT.TS4.stage4At l F kclk coef A a0 ha0).need_le n)
  obtain ⟨V, hV⟩ : ∃ V, V = UnaryCalc.value (PrimT.C4SymLf.symLay wa S3 (C4HL.hDl l Dnw)).D (C4HL.hCd l F Cnw) n :=
    ⟨_, rfl⟩
  have hW : PrimT.C4GateSym.needW n ≤ V := by rw [hV]; exact le_trans hWL hLW
  have hN : PrimT.TS4.needT l F.cr n ≤ 2 * V + 2 := by rw [hV]; exact hneed
  rw [← hV]
  obtain ⟨-, -, -, hcN, hcA, hcK, hcx, hcy, -⟩ :=
    C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc henv V hW
  have h26 : (n + 1) ^ 26 ≤ V := le_trans (by unfold PrimT.C4GateSym.needW; omega) hW
  have h2r := ((callInputs l F kclk coef A a0 ha0).starParams n hs).two_le_r
  have h4r : 4 * ((callInputs l F kclk coef A a0 ha0).starParams n hs).r ≤ n :=
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).four_r_le_n
  refine ⟨rfl, by omega, PrimT.TS4.capTL_pos l F.cr n, ⟨by rw [List.length_map]; exact hk2, hcN, hcA,
    by rw [List.length_map]; exact hcK, fun x hx => by have := hcx x hx; omega,
    fun y hy => by have := hcy y hy; omega⟩, ?_⟩
  show PrimT.W6.needW (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D
    (n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤ V
  have e1 : (callInputs l F kclk coef A a0 ha0).D = 1 := rfl
  have e2 : ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap = PrimT.TS4.capTL l F.cr n := rfl
  have e3 : (gate0 l F).alg = PrimT.W6.litAlg l := rfl
  rw [e1, e2, e3]
  unfold PrimT.TS4.needT at hN
  omega

/-- **The HASH setup's capacity fits at every THR call** past one threshold `C_c₀`: the THR numbers' fit, the HASH
numbers' fit and the cell's capacity facts (with the digit program's bound within the cell's capacity). -/
theorem hash_fits (l : Literals) (F : GateFree l) (Fp : PrimT.C4Set.FreeProg)
    (hok : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : PrimT.C4Set.FreeIn), C4SymW.FreeSmall Ds x → Ko * 2 ^ (x.n / 8) ≤ cap →
      Fp.ok cap x)
    (hval : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : PrimT.C4Set.FreeIn) (j : Fin 7), C4SymW.FreeSmall Ds x → j.val ≠ 6 →
      Fp.val x j ≤ Kv * 2 ^ (x.n / 8))
    (hrho : ∃ Kr Dr : ℕ, ∀ x : PrimT.C4Set.FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr)
    (Cw Dw Cnw Dnw : ℕ) (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ Cw * (n + 1) ^ Dw)
    (hnw : ∀ n, C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) :
    ∃ Cc0 : ℕ, ∀ Cc : ℕ, Cc0 ≤ Cc → ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
        ThrCap.ThrFitAt Fp F.cr F.filterErrDeg (2 ^ C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0)
          (gate0 l F).alg ha Cs carriers translation hs ∧
        ThrCap.HashFitX Fp (2 ^ C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs ∧
        ∃ Bm Sm : ℕ, HashCell.CellFit (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation
          F.cr Bm Sm (2 * 2 ^ C4Cap.capExp2 Cc n + 2) ∧ Bm ≤ 2 * 2 ^ C4Cap.capExp2 Cc n + 2 := by
  obtain ⟨C1, h1⟩ := ThrCap.thr_fits2 l F Fp hok hval hrho Cw Dw Cnw Dnw hwb hnw
  obtain ⟨C2, h2⟩ := ThrCap.hash_fitsX l F Fp hok hval hrho Cw Dw Cnw Dnw hwb hnw
  obtain ⟨C3, h3⟩ := cell_fits l F
  refine ⟨C1 + C2 + C3, fun Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs =>
    ⟨h1 Cc (by omega) kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs,
      h2 Cc (by omega) kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs,
      h3 Cc (by omega) kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.HashFit
