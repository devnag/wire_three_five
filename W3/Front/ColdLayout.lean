import W3.Front.ColdPrims
import Proof.CaseAnalysis.WitnessOracleCap
import Proof.CaseAnalysis.WitnessOracleRun
import Proof.PCP.PCPPNativeOracle
import Setup.PhaseA
import Close.Amplifier
import OuterM.Width

/-!
# The cold front end, part 1: the cold prefix's layout and program

The near-cubic-wires paper ("It rejects without guessing unless n = N_ν … guesses … B_src … B_pf … deterministically rejects a
branch if any description is malformed or noncanonical … fails the fixed general-circuit size bound q^G or, for B_src,
the description-length bound λ_ν"), (C.10.0), C.10 (`H_B`) (`N^{d_chk} + q^{O(1)}`, `d_chk = 2`).

One `WMX` program `coldP` (gates register file): `FL := [false]`; `rN := n`, `LEN := 1^n`, `ORIG := frame x`; on
`n ≥ 1`: `powP` (`n = 2^ν`), `ν ≥ c*`; then the guess word `WT` (gates `phA1`, padded so both fields are physical), the
native width (gates `OuterM.widthDonor`, binary and unary), the code bound `L(q) = 8192((q+1)^{E₀}+q+5)^{10}` and the
padding length `M = 16 L + q + 4`; per field: `fieldRW`, `truncField` (bits past `L` must be `0`), `framedOnes`, proof 1's
cold decoder on `(frame 1^M, frame (prefixBits b L), frame q.bits, 1^q)` (cost poly(`M`), not `n^25`); on both decodes:
proof 1's `PCPPNativeOracleCold` (`1^{|B|}`, `1^q`) and `OracleCap` (`|B| ≤ q^G`) per circuit; then JF's `F.M` on
`frame x, ⟨B_src⟩, ⟨B_pf⟩`; `FL := [true]` iff its guard flag holds.
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-! ## Layout -/

/-- The stream count minus one: 33 fixed streams, then the private blocks of the width donors (`tB`, `tU`), the two
cold decoders (1381 each), the two native-oracle counters (40 each), the two caps (`tC` each) and `F` (`tF`). -/
def nsC (tB tU tC tF : ℕ) : ℕ := 32 + tB + tU + 2842 + 2 * tC + tF

section L
variable (tB tU tC tF : ℕ)

/-- Fixed stream `k < 33`. -/
def cs (k : ℕ) (hk : k < 33) : Fin (nsC tB tU tC tF + 1) := ⟨k, by unfold nsC; omega⟩
@[simp] theorem cs_val (k : ℕ) (hk : k < 33) : (cs tB tU tC tF k hk).val = k := rfl

abbrev cX := cs tB tU tC tF 1 (by decide)
abbrev cRAW := cs tB tU tC tF 2 (by decide)
abbrev cLEN := cs tB tU tC tF 3 (by decide)
abbrev cFL := cs tB tU tC tF 4 (by decide)
abbrev cFT := cs tB tU tC tF 5 (by decide)
abbrev cORIG := cs tB tU tC tF 6 (by decide)
abbrev cWT := cs tB tU tC tF 7 (by decide)
abbrev cXW1 := cs tB tU tC tF 8 (by decide)
abbrev cXW2 := cs tB tU tC tF 9 (by decide)
abbrev cXF := cs tB tU tC tF 10 (by decide)

/-- Field stream `i < 11` of field `k < 2`: `0 FB, 1 TMP, 2 FBP, 3 XP, 4 QB, 5 QU, 6 DD, 7 DF, 8 SZ, 9 QC, 10 CF`. -/
def fs (k : Fin 2) (i : ℕ) (hi : i < 11) : Fin (nsC tB tU tC tF + 1) :=
  cs tB tU tC tF (11 + 11 * k.val + i) (by have := k.isLt; omega)
@[simp] theorem fs_val (k : Fin 2) (i : ℕ) (hi : i < 11) : (fs tB tU tC tF k i hi).val = 11 + 11 * k.val + i := rfl

def bWB : ℕ := 33
def bWU : ℕ := 33 + tB
def bDEC (k : Fin 2) : ℕ := 33 + tB + tU + 1381 * k.val
def bOC (k : Fin 2) : ℕ := 33 + tB + tU + 2762 + 40 * k.val
def bCAP (k : Fin 2) : ℕ := 33 + tB + tU + 2842 + tC * k.val
def bF : ℕ := 33 + tB + tU + 2842 + 2 * tC

/-- Stream `b + j` of a private block. -/
def blk (b j : ℕ) (h : b + j < nsC tB tU tC tF + 1) : Fin (nsC tB tU tC tF + 1) := ⟨b + j, h⟩

end L

/-! ## Registers (gates register file; `0 … 39` are free outside the term loop) -/

def rK2 : Fin nrW := ⟨1, by decide⟩
def rOP : Fin nrW := ⟨2, by decide⟩
def rT : Fin nrW := ⟨3, by decide⟩
def rD : Fin nrW := ⟨4, by decide⟩
def rC : Fin nrW := ⟨5, by decide⟩
def rQ : Fin nrW := ⟨6, by decide⟩
def rL : Fin nrW := ⟨7, by decide⟩
def rM : Fin nrW := ⟨8, by decide⟩
def rLC : Fin nrW := ⟨9, by decide⟩
def rZ (k : Fin 2) : Fin nrW := ⟨10 + k.val, by have := k.isLt; show 10 + k.val < 128; omega⟩
def rK : Fin nrW := ⟨12, by decide⟩
def rU : Fin nrW := ⟨13, by decide⟩
def rA : Fin nrW := ⟨14, by decide⟩
def rQ1 : Fin nrW := ⟨15, by decide⟩
def rW : Fin nrW := ⟨16, by decide⟩

/-! ## Tape maps of the docked machines -/

section Maps
variable (pB pU : Program) (tC : ℕ) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  {mw : Outer.MWSource} {SV : Outer.SuccinctVerifier H0 G0} (F : FrontSpecD mw SV)

abbrev NS := nsC pB.tapeCount pU.tapeCount tC F.t

/-- Width donor (binary): input tape on `XW1`, every other tape private. -/
def mWB (j : Fin pB.tapeCount) : Fin (NS pB pU tC F + 1) :=
  if j.val = 0 then cXW1 _ _ _ _ else blk _ _ _ _ (bWB) j.val (by unfold nsC bWB; have := j.isLt; omega)
/-- Width donor (unary): input tape on `XW2`. -/
def mWU (j : Fin pU.tapeCount) : Fin (NS pB pU tC F + 1) :=
  if j.val = 0 then cXW2 _ _ _ _ else blk _ _ _ _ (bWU pB.tapeCount) j.val (by unfold nsC bWU; have := j.isLt; omega)
/-- Cold decoder `k`: tapes `0 … 3` on `XP, FBP, QB, QU`, flag `1379` on `DF`, descriptor `1299` on `DD`. -/
def mDEC (k : Fin 2) (j : Fin (CloseoutWitness.Oracle.tapes + 1)) : Fin (NS pB pU tC F + 1) :=
  if j.val = 0 then fs _ _ _ _ k 3 (by decide) else if j.val = 1 then fs _ _ _ _ k 2 (by decide)
  else if j.val = 2 then fs _ _ _ _ k 4 (by decide) else if j.val = 3 then fs _ _ _ _ k 5 (by decide)
  else if j.val = 1379 then fs _ _ _ _ k 7 (by decide) else if j.val = 1299 then fs _ _ _ _ k 6 (by decide)
  else blk _ _ _ _ (bDEC pB.tapeCount pU.tapeCount k) j.val (by
    unfold nsC bDEC; have hj : j.val < 1381 := j.isLt; have := k.isLt; omega)
/-- Native-oracle counter `k`: descriptor tape `0` on `DD`, `1^{|B|}` (`32`) on `SZ`, `1^q` (`36`) on `QC`. -/
def mOC (k : Fin 2) (j : Fin 40) : Fin (NS pB pU tC F + 1) :=
  if j.val = 0 then fs _ _ _ _ k 6 (by decide) else if j.val = 32 then fs _ _ _ _ k 8 (by decide)
  else if j.val = 36 then fs _ _ _ _ k 9 (by decide)
  else blk _ _ _ _ (bOC pB.tapeCount pU.tapeCount k) j.val (by
    unfold nsC bOC; have := j.isLt; have := k.isLt; omega)

end Maps

section Maps2
variable (pB pU : Program) (Dc : ℕ) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  {mw : Outer.MWSource} {SV : Outer.SuccinctVerifier H0 G0} (F : FrontSpecD mw SV)

/-- The cap's tape count. -/
abbrev tCap (Dc : ℕ) : ℕ := CloseoutWitness.OracleCap.Core.tapes Dc

/-- Cap `k`: `1^q` (tape `0`) on `QC`, `1^{|B|}` (`1`) on `SZ`, the flag (`P+4`) on `CF`. -/
def mCAP (k : Fin 2) (j : Fin (tCap Dc)) : Fin (NS pB pU (tCap Dc) F + 1) :=
  if j.val = 0 then fs _ _ _ _ k 9 (by decide) else if j.val = 1 then fs _ _ _ _ k 8 (by decide)
  else if j.val = CloseoutWitness.OracleCap.Core.P Dc + 4 then fs _ _ _ _ k 10 (by decide)
  else blk _ _ _ _ (bCAP pB.tapeCount pU.tapeCount (tCap Dc) k) j.val (by
    unfold nsC bCAP; have := j.isLt; have := k.isLt
    have hm : (tCap Dc) * k.val ≤ (tCap Dc) * 1 := Nat.mul_le_mul_left _ (by omega)
    omega)

/-- `F`: `zIn` on `XF`, `sIn` on `DD₀`, `pIn` on `DD₁`, every other tape private. -/
def mF (j : Fin F.t) : Fin (NS pB pU (tCap Dc) F + 1) :=
  if j = F.zIn then cXF _ _ _ _ else if j = F.sIn then fs _ _ _ _ 0 6 (by decide)
  else if j = F.pIn then fs _ _ _ _ 1 6 (by decide)
  else blk _ _ _ _ (bF pB.tapeCount pU.tapeCount (tCap Dc)) j.val (by unfold nsC bF; have := j.isLt; omega)

end Maps2

/-! ## The program -/

section Program
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree cstar : ℕ)

noncomputable abbrev progB := Rewind.program (OuterM.widthDonor mw SV).word.program
noncomputable abbrev progU := Rewind.program (OuterM.widthDonor mw SV).unary.program
abbrev Dc (degree : ℕ) := CloseoutWitness.OracleCap.degree degree
/-- `E₀ = 2^{depth}`: `q^G`-gate circuits have at most `(q+1)^{E₀} - 1` gates (`oracleSizeBound_succ`). -/
abbrev E0 (degree : ℕ) := 2 ^ RecoveryScheduleEnvelope.oracleDepth degree

noncomputable abbrev NSC := NS (progB mw SV) (progU mw SV) (tCap (Dc degree)) F

/-- One field: read, truncate to `L` bits, build the padding word, `q` in binary and unary, decode. -/
noncomputable def fieldP (k : Fin 2) : WMX (NSC mw SV F degree) nrW :=
  let s := fun (i : ℕ) (h : i < 11) => fs (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) F.t k i h
  .seq (.wm (Codec.fieldRW (cWT _ _ _ _) (s 0 (by decide)) rOP rK))
  (.seq (truncField (s 0 (by decide)) (s 1 (by decide)) (s 2 (by decide)) rOP rL rLC (rZ k) rD)
  (.seq (framedOnes (s 3 (by decide)) rM rU rOP)
  (.seq (.wm (Codec.copyRW (mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F (progB mw SV).outputTape)
    (s 4 (by decide)) rOP rT rD))
  (.seq (TabMachine.writeOnes (s 5 (by decide)) rQ rK2)
  (.mach CloseoutWitness.Oracle.machine (mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k))))))

/-- The code bound `rL := 8192((q+1)^{E₀}+q+5)^{10}` and the padding length `rM := 16 rL + q + 4`. -/
noncomputable def boundP : WMX (NSC mw SV F degree) nrW :=
  .seq (.wm (Codec.dupR rQ rQ1 dS)) (.seq (WMX.inc rQ1)
  (.seq (WMX.inc rA) (.seq (CheckedPCPP.EncSetup.powW rQ1 rA pX3 pH pB (E0 degree))
  (.seq (.wm (Codec.dupR rQ rA dS)) (.seq (.wm (CheckedPCPP.NodeEmit.incN rA 5))
  (.seq (.wm (CheckedPCPP.NodeEmit.incN rL 8192)) (.seq (CheckedPCPP.EncSetup.powW rA rL pX3 pH pB 10)
  (.seq (.wm (CheckedPCPP.NodeEmit.incN rM 16)) (.seq (CheckedPCPP.EncSetup.powW rL rM pX3 pH pB 1)
  (.seq (.wm (Codec.dupR rQ rM dS)) (.wm (CheckedPCPP.NodeEmit.incN rM 4))))))))))))

/-- The guess word: `WT := prefixBits raw (4⌊n/16⌋ + 5)` (gates `phA1` with its phase-B padding). -/
noncomputable def wtP : WMX (NSC mw SV F degree) nrW :=
  .seq (.wm (Codec.dupR rN kQ dS)) (.seq (div16 kQ hH hBr)
  (.seq (.wm (Codec.dupR kQ rW dS)) (.seq (.wm (Codec.dupR kQ rW dS)) (.seq (.wm (Codec.dupR kQ rW dS))
  (.seq (.wm (Codec.dupR kQ rW dS)) (.seq (.wm (CheckedPCPP.NodeEmit.incN rW 5))
  (.seq (.wm (Codec.unframeW (cRAW _ _ _ _) (cWT _ _ _ _) oW rW)) (.wm (WM.rewind (cWT _ _ _ _) oW)))))))))

/-- The native width: `q` in binary (the binary donor's output tape) and `rQ := q`. -/
noncomputable def widthP : WMX (NSC mw SV F degree) nrW :=
  .seq (.wm (Codec.copyRW (cX _ _ _ _) (cXW1 _ _ _ _) rOP rT rD))
  (.seq (.mach (progB mw SV).machine (mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F))
  (.seq (.wm (Codec.copyRW (cX _ _ _ _) (cXW2 _ _ _ _) rOP rT rD))
  (.seq (.mach (progU mw SV).machine (mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F))
  (.wm (Codec.unaryQ (mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F (progU mw SV).outputTape) rQ rT rD)))))

/-- The front end: `XF := frame x`, `F.M` on `frame x, ⟨B_src⟩, ⟨B_pf⟩`, `FL := [true]` on its guard. -/
noncomputable def frontPart : WMX (NSC mw SV F degree) nrW :=
  .seq (.wm (Codec.copyRW (cX _ _ _ _) (cXF _ _ _ _) rOP rT rD))
  (.seq (.mach F.M (mF (progB mw SV) (progU mw SV) (Dc degree) F))
  (.ifs (mF (progB mw SV) (progU mw SV) (Dc degree) F F.flag) (WMX.wr (cFL _ _ _ _) true) WMX.skip))

/-- One circuit's native-oracle counter and cap. -/
noncomputable def capOneP (k : Fin 2) : WMX (NSC mw SV F degree) nrW :=
  .seq (.mach PCPPNativeOracleCold.machine (mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k))
    (.mach (CloseoutWitness.OracleCap.machine degree) (mCAP (progB mw SV) (progU mw SV) (Dc degree) F k))

/-- The caps and the front end, on both decodes. -/
noncomputable def capsP : WMX (NSC mw SV F degree) nrW :=
  let A := fun (k : Fin 2) (i : ℕ) (h : i < 11) =>
    fs (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) F.t k i h
  .seq (capOneP mw SV F degree 0)
  (.ifs (A 0 10 (by decide))
    (.seq (capOneP mw SV F degree 1) (.ifs (A 1 10 (by decide)) (frontPart mw SV F degree) WMX.skip))
    WMX.skip)

/-- Width, bound, both fields. -/
noncomputable def prepP : WMX (NSC mw SV F degree) nrW :=
  .seq (wtP mw SV F degree) (.seq (widthP mw SV F degree) (.seq (boundP mw SV F degree)
  (.seq (fieldP mw SV F degree 0) (fieldP mw SV F degree 1))))

/-- Reject on a `1` past `L(q)` or a failed decode; otherwise the caps and the front end. -/
noncomputable def tailP : WMX (NSC mw SV F degree) nrW :=
  .ifr (rZ 0) WMX.skip (.ifr (rZ 1) WMX.skip
    (.ifs (fs _ _ _ _ 0 7 (by decide)) (.ifs (fs _ _ _ _ 1 7 (by decide)) (capsP mw SV F degree) WMX.skip)
      WMX.skip))

noncomputable def deepP : WMX (NSC mw SV F degree) nrW := .seq (prepP mw SV F degree) (tailP mw SV F degree)

/-- The index guard `ν ≥ c*`, then the deep part. -/
noncomputable def guardP : WMX (NSC mw SV F degree) nrW :=
  .seq (.wm (CheckedPCPP.NodeEmit.incN rC cstar))
  (.seq (Recovery.HTParts.leW rC rNu pU pK pT pF) (.ifr pF (deepP mw SV F degree) WMX.skip))

/-- **The cold prefix.** -/
noncomputable def coldP : WMX (NSC mw SV F degree) nrW :=
  .seq (WMX.wr (cFL _ _ _ _) false)
  (.seq (BinW.width (cX _ _ _ _) rN tW)
  (.seq (TabMachine.writeOnes (cLEN _ _ _ _) rN rK2)
  (.seq (.wm (Codec.copyRW (cX _ _ _ _) (cORIG _ _ _ _) rOP rT rD))
  (.ifr rN
    (.seq (powP (cFT _ _ _ _)) (.ifs (cFT _ _ _ _) (guardP mw SV F degree cstar) WMX.skip))
    WMX.skip))))

end Program

end W3.NearCubicWires.RepairSource.Outer3.Front
