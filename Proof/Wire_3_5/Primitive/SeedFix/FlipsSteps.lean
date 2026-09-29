import Proof.Wire_3_5.Primitive.SeedFix.FlipsOnes
import Proof.Wire_3_5.Primitive.Writers.GeoFront

/-! # FLIPS, part 4: the cell loops' steps (P3:1224, 1655-1664)

C3a's flips field lists, for every cell `(L, R)` of the two halves (left-major, right-minor) and every corner `k`, the
corner point `offset ⊕ [k < 2]·u_L ⊕ [k even]·v_R` (P3:1224). On the geometry-writer layout (`GeoFront`, `WM 12 64`),
the flips writer keeps: the offset's frame (`sOFF`), the left and right error vectors (`sEL`, `sER`, C5's decoder),
the two cell counters (`sCL`, `sCR`, `frame (binary kh ·)`), a zero partner counter (`sTOT`), the output (`gOUT`).

* the invariant **`FS`** (every stream and register the loops read);
* `decR_step`, `decL_step` (C5's decoder), `corner_step`, `corners_step` (the cell's four corners, `blk`),
  `ctr_step` (the last-index test and the counter increment).

Paper quantity of the main type: the cell's four corner points (`blk`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-! ## The layout -/

def sOFF : Fin (GS + 1) := 5
def sEL : Fin (GS + 1) := 6
def sER : Fin (GS + 1) := 7
def sCL : Fin (GS + 1) := 8
def sCR : Fin (GS + 1) := 9
def sTOT : Fin (GS + 1) := 10

/-- C5's decoder's registers: `s, b, r/2, tail` are PA's star registers `4 … 7`; its scratch is `30 … 37`. -/
def RD : Fin 12 ↪ Fin GR := ⟨![4, 5, 6, 7, 30, 31, 32, 33, 34, 35, 36, 37], by decide⟩

def rAcc : Fin GR := 40
def rCnt : Fin GR := 41
def rNz : Fin GR := 42
def rGoR : Fin GR := 43
def rGoL : Fin GR := 44
def rScn : Fin GR := 45
def rF : Fin GR := 46
def rR : Fin GR := 47

/-! ## The words -/

/-- The left errors' word of the cell row `L` (C5's `decWord`). -/
def elW (s b h tl L : ℕ) : List Bool :=
  FinalPass.Sample.decWord b h tl false (FinalPass.Sample.digitsOf s h (binary (s * h) L))

/-- The right errors' word of the cell column `R`. -/
def erW (s b h tl R : ℕ) : List Bool :=
  FinalPass.Sample.decWord b h tl true (FinalPass.Sample.digitsOf s h (binary (s * h) R))

theorem decWord_len (b h tl : ℕ) (right : Bool) (ds : List ℕ) (hds : ds.length = h) :
    (FinalPass.Sample.decWord b h tl right ds).length = h * b + h * b + tl := by
  unfold FinalPass.Sample.decWord
  cases right <;> simp only [Bool.false_eq_true, eq_self_iff_true, ite_true, ite_false, if_true, if_false,
    List.length_append, List.length_replicate] <;> rw [FinalPass.Sample.length_flatMap_oneHot, hds] <;> ring

theorem elW_len (s b h tl L : ℕ) : (elW s b h tl L).length = h * b + h * b + tl :=
  decWord_len b h tl false _ (FinalPass.Sample.digitsOf_length s h _)

theorem erW_len (s b h tl R : ℕ) : (erW s b h tl R).length = h * b + h * b + tl :=
  decWord_len b h tl true _ (FinalPass.Sample.digitsOf_length s h _)

/-- **The cell's four corner points**, framed: `c+u+v`, `c+u`, `c+v`, `c` (P3:1224). -/
def blk (OFFw EL ER : List Bool) : List Bool :=
  frame (xw true true OFFw EL ER) ++ frame (xw true false OFFw EL ER) ++ frame (xw false true OFFw EL ER) ++
    frame (xw false false OFFw EL ER)

/-! ## The invariant -/

/-- **The loops' invariant**: the offset's frame, the two error words (framed), the two cell counters and the zero
partner (`NumOn`), the output, the request kept, the decoder's constants, every scratch register `0`, the two loop
flags. -/
structure FS (s b h tl : ℕ) (σ0 σ : WState GS GR) (OFFw ELc ERc : List Bool) (L R : ℕ) (out : List Bool)
    (gR gL : ℕ) : Prop where
  lOF : OFFw.length = h * b + h * b + tl
  lEL : ELc.length = h * b + h * b + tl
  lER : ERc.length = h * b + h * b + tl
  stOF : σ.st sOFF = frameP OFFw ++ [false]
  shOF : σ.sh sOFF = 0
  stEL : σ.st sEL = frameP ELc ++ [false]
  shEL : σ.sh sEL = 0
  stER : σ.st sER = frameP ERc ++ [false]
  shER : σ.sh sER = 0
  nL : NumOn σ sCL (s * h) L
  nR : NumOn σ sCR (s * h) R
  nT : NumOn σ sTOT (s * h) 0
  sO : σ.st gOUT = out
  hO : σ.sh gOUT = out.length
  sIN : σ.st gIN = σ0.st gIN
  vS : σ.val (RD 0) = s
  vB : σ.val (RD 1) = b
  vH : σ.val (RD 2) = h
  vT : σ.val (RD 3) = tl
  vZ : ∀ i : Fin 12, 4 ≤ i.val → σ.val (RD i) = 0
  vAcc : σ.val rAcc = 0
  vCnt : σ.val rCnt = 0
  vNz : σ.val rNz = 0
  vScn : σ.val rScn = 0
  vF : σ.val rF = 0
  vR : σ.val rR = 0
  vgR : σ.val rGoR = gR
  vgL : σ.val rGoL = gL

theorem RD_acc : ∀ i : Fin 12, RD i ≠ rAcc := by decide
theorem RD_cnt : ∀ i : Fin 12, RD i ≠ rCnt := by decide
theorem RD_nz : ∀ i : Fin 12, RD i ≠ rNz := by decide
theorem RD_scn : ∀ i : Fin 12, RD i ≠ rScn := by decide
theorem RD_goR : ∀ i : Fin 12, RD i ≠ rGoR := by decide
theorem RD_goL : ∀ i : Fin 12, RD i ≠ rGoL := by decide

/-! ## The decoder steps -/

section Steps
variable (cap : ℕ) (s b h tl : ℕ) (σ0 : WState GS GR) (OFFw : List Bool)

/-- The decoder's capacity needs. -/
def DecCap (s b h tl cap : ℕ) : Prop :=
  2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * (s * h) + 1 ≤ cap ∧ 2 * (h * b + h * b + tl) ≤ cap ∧ b ≤ cap ∧ h ≤ cap ∧ tl ≤ cap

/-- **The right errors of the column `R`** onto `sER`. -/
theorem decR_step (hbs : b + 1 = 2 ^ s) (hc : DecCap s b h tl cap) (σ : WState GS GR) (ELc ERc : List Bool)
    (L R : ℕ) (out : List Bool) (gR gL : ℕ) (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) :
    ∃ τ, WExec cap (decStage true sCR sER RD) σ τ (decStageCost s b h tl) ∧
      FS s b h tl σ0 τ OFFw ELc (erW s b h tl R) L R out gR gL := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  obtain ⟨τ, e, t1, t2, t3, t4, t5, t6, t7⟩ := decStage_spec cap true sCR sER (by decide) RD σ s b h tl R hbs ERc
    hf.lER (by rw [hf.nR.1, frame_eq_frameP]) hf.nR.2 hf.stER hf.shER hf.vS hf.vB hf.vH hf.vT hf.vZ c1 c2 c3
    (by rw [hf.lER]; exact c4) c5 c6 c7
  refine ⟨τ, e, ⟨hf.lOF, hf.lEL, erW_len s b h tl R, ?_, ?_, ?_, ?_, t1, t2, ?_, ⟨?_, t4⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [(t5 sOFF (by decide) (by decide)).1, hf.stOF]
  · rw [(t5 sOFF (by decide) (by decide)).2, hf.shOF]
  · rw [(t5 sEL (by decide) (by decide)).1, hf.stEL]
  · rw [(t5 sEL (by decide) (by decide)).2, hf.shEL]
  · exact ⟨by rw [(t5 sCL (by decide) (by decide)).1, hf.nL.1], by rw [(t5 sCL (by decide) (by decide)).2, hf.nL.2]⟩
  · rw [t3, hf.nR.1]
  · exact ⟨by rw [(t5 sTOT (by decide) (by decide)).1, hf.nT.1], by rw [(t5 sTOT (by decide) (by decide)).2, hf.nT.2]⟩
  · rw [(t5 gOUT (by decide) (by decide)).1, hf.sO]
  · rw [(t5 gOUT (by decide) (by decide)).2, hf.hO]
  · rw [(t5 gIN (by decide) (by decide)).1, hf.sIN]
  · rw [t6, hf.vS]
  · rw [t6, hf.vB]
  · rw [t6, hf.vH]
  · rw [t6, hf.vT]
  · intro i hi; rw [t6, hf.vZ i hi]
  · rw [t6, hf.vAcc]
  · rw [t6, hf.vCnt]
  · rw [t6, hf.vNz]
  · rw [t6, hf.vScn]
  · rw [t6, hf.vF]
  · rw [t6, hf.vR]
  · rw [t6, hf.vgR]
  · rw [t6, hf.vgL]

/-- **The left errors of the row `L`** onto `sEL`. -/
theorem decL_step (hbs : b + 1 = 2 ^ s) (hc : DecCap s b h tl cap) (σ : WState GS GR) (ELc ERc : List Bool)
    (L R : ℕ) (out : List Bool) (gR gL : ℕ) (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) :
    ∃ τ, WExec cap (decStage false sCL sEL RD) σ τ (decStageCost s b h tl) ∧
      FS s b h tl σ0 τ OFFw (elW s b h tl L) ERc L R out gR gL := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  obtain ⟨τ, e, t1, t2, t3, t4, t5, t6, t7⟩ := decStage_spec cap false sCL sEL (by decide) RD σ s b h tl L hbs ELc
    hf.lEL (by rw [hf.nL.1, frame_eq_frameP]) hf.nL.2 hf.stEL hf.shEL hf.vS hf.vB hf.vH hf.vT hf.vZ c1 c2 c3
    (by rw [hf.lEL]; exact c4) c5 c6 c7
  refine ⟨τ, e, ⟨hf.lOF, elW_len s b h tl L, hf.lER, ?_, ?_, t1, t2, ?_, ?_, ⟨?_, t4⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [(t5 sOFF (by decide) (by decide)).1, hf.stOF]
  · rw [(t5 sOFF (by decide) (by decide)).2, hf.shOF]
  · rw [(t5 sER (by decide) (by decide)).1, hf.stER]
  · rw [(t5 sER (by decide) (by decide)).2, hf.shER]
  · rw [t3, hf.nL.1]
  · exact ⟨by rw [(t5 sCR (by decide) (by decide)).1, hf.nR.1], by rw [(t5 sCR (by decide) (by decide)).2, hf.nR.2]⟩
  · exact ⟨by rw [(t5 sTOT (by decide) (by decide)).1, hf.nT.1], by rw [(t5 sTOT (by decide) (by decide)).2, hf.nT.2]⟩
  · rw [(t5 gOUT (by decide) (by decide)).1, hf.sO]
  · rw [(t5 gOUT (by decide) (by decide)).2, hf.hO]
  · rw [(t5 gIN (by decide) (by decide)).1, hf.sIN]
  · rw [t6, hf.vS]
  · rw [t6, hf.vB]
  · rw [t6, hf.vH]
  · rw [t6, hf.vT]
  · intro i hi; rw [t6, hf.vZ i hi]
  · rw [t6, hf.vAcc]
  · rw [t6, hf.vCnt]
  · rw [t6, hf.vNz]
  · rw [t6, hf.vScn]
  · rw [t6, hf.vF]
  · rw [t6, hf.vR]
  · rw [t6, hf.vgR]
  · rw [t6, hf.vgL]

/-! ## The corners -/

theorem corner_step (u v : Bool) (σ : WState GS GR) (ELc ERc : List Bool) (L R : ℕ) (out : List Bool) (gR gL : ℕ)
    (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) (hcap : 2 * (h * b + h * b + tl) + 2 ≤ cap) :
    ∃ τ, WExec cap (cornerW u v gOUT sOFF sEL sER rAcc rCnt) σ τ (cornerCost (h * b + h * b + tl)) ∧
      FS s b h tl σ0 τ OFFw ELc ERc L R (out ++ frame (xw u v OFFw ELc ERc)) gR gL := by
  obtain ⟨τ, e, c⟩ := cornerW_spec (O := gOUT) (A := sOFF) (B := sEL) (C := sER) (acc := rAcc) (cnt := rCnt) cap
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) u v OFFw ELc ERc [] [] [] σ hf.stOF hf.stEL hf.stER (h * b + h * b + tl) hf.lOF hf.lEL hf.lER hf.shOF
    hf.shEL hf.shER (by rw [hf.hO, hf.sO]) hf.vAcc hf.vCnt hcap
  have fr := c.frS
  have rr := c.frR
  refine ⟨τ, e, ⟨hf.lOF, hf.lEL, hf.lER, by rw [c.sA, hf.stOF], c.hA, by rw [c.sB, hf.stEL], c.hB,
    by rw [c.sC, hf.stER], c.hC, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by rw [c.sO, hf.sO], by rw [c.hO, c.sO, hf.sO],
    ?_, ?_, ?_, ?_, ?_, ?_, c.vacc, c.vcnt, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [(fr sCL (by decide) (by decide) (by decide) (by decide)).1, hf.nL.1]
  · rw [(fr sCL (by decide) (by decide) (by decide) (by decide)).2, hf.nL.2]
  · rw [(fr sCR (by decide) (by decide) (by decide) (by decide)).1, hf.nR.1]
  · rw [(fr sCR (by decide) (by decide) (by decide) (by decide)).2, hf.nR.2]
  · rw [(fr sTOT (by decide) (by decide) (by decide) (by decide)).1, hf.nT.1]
  · rw [(fr sTOT (by decide) (by decide) (by decide) (by decide)).2, hf.nT.2]
  · rw [(fr gIN (by decide) (by decide) (by decide) (by decide)).1, hf.sIN]
  · rw [rr _ (by decide) (by decide), hf.vS]
  · rw [rr _ (by decide) (by decide), hf.vB]
  · rw [rr _ (by decide) (by decide), hf.vH]
  · rw [rr _ (by decide) (by decide), hf.vT]
  · intro i hi
    rw [rr _ (RD_acc i) (RD_cnt i), hf.vZ i hi]
  · rw [rr _ (by decide) (by decide), hf.vNz]
  · rw [rr _ (by decide) (by decide), hf.vScn]
  · rw [rr _ (by decide) (by decide), hf.vF]
  · rw [rr _ (by decide) (by decide), hf.vR]
  · rw [rr _ (by decide) (by decide), hf.vgR]
  · rw [rr _ (by decide) (by decide), hf.vgL]

/-- The cell's four corners. -/
def cornersW : WM GS GR :=
  .seq (cornerW true true gOUT sOFF sEL sER rAcc rCnt) (.seq (cornerW true false gOUT sOFF sEL sER rAcc rCnt)
    (.seq (cornerW false true gOUT sOFF sEL sER rAcc rCnt) (cornerW false false gOUT sOFF sEL sER rAcc rCnt)))

/-- The four corners' cost. -/
def cornersCost (n : ℕ) : ℕ := cornerCost n + 1 + (cornerCost n + 1 + (cornerCost n + 1 + cornerCost n))

theorem corners_step (σ : WState GS GR) (ELc ERc : List Bool) (L R : ℕ) (out : List Bool) (gR gL : ℕ)
    (hf : FS s b h tl σ0 σ OFFw ELc ERc L R out gR gL) (hcap : 2 * (h * b + h * b + tl) + 2 ≤ cap) :
    ∃ τ, WExec cap cornersW σ τ (cornersCost (h * b + h * b + tl)) ∧
      FS s b h tl σ0 τ OFFw ELc ERc L R (out ++ blk OFFw ELc ERc) gR gL := by
  obtain ⟨τ1, e1, f1⟩ := corner_step cap s b h tl σ0 OFFw true true σ ELc ERc L R out gR gL hf hcap
  obtain ⟨τ2, e2, f2⟩ := corner_step cap s b h tl σ0 OFFw true false τ1 ELc ERc L R _ gR gL f1 hcap
  obtain ⟨τ3, e3, f3⟩ := corner_step cap s b h tl σ0 OFFw false true τ2 ELc ERc L R _ gR gL f2 hcap
  obtain ⟨τ4, e4, f4⟩ := corner_step cap s b h tl σ0 OFFw false false τ3 ELc ERc L R _ gR gL f3 hcap
  refine ⟨τ4, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_⟩
  simpa [blk, List.append_assoc] using f4

end Steps

end NearCubicWires.WireExponent3_5.PrimT.Flips
