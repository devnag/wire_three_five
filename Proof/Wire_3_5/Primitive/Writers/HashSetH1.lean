import Proof.Wire_3_5.Primitive.Writers.HashCellK
import Proof.Wire_3_5.Primitive.Writers.HashFront
import Proof.Wire_3_5.Primitive.SeedFix.C4KWTypes

/-! # HASH setup (C), P3 part 1: the HASH setup's machine `M0` on one bank (layout and stages)

P3:3011-3016 (the HASH stage's setup before the loop) and P3:2253-2290 (the Hb printer's static words): the HASH
setup `M0` runs on one bank `3 + XH` (`setupH`/`hashLay_run` take it as a parameter), in seven stages, each on
its own region above the previous one:

1. `mSet`: the THR setup chain `ThrSet.setupT3` (with the HASH numbers machine), lifted onto the bank's first
   `3 + thrXb` tapes (`hash_setup_run`: the SymBank part of `HBank2`);
2. `mF1`, `mF2`: two copies of the front (`HashSet.frontCopyM`) on `[oF1, oF1 + L.N)`, `[oF2, oF2 + L.N)`:
   `1^n, 1^{C_L(n+1)^D}, 1^{C_d(n+1)^D}, 1^{2^m}`;
3. `mD`: the data-stage rerun and copy-in (T-a, `C4KW.drM`) on `[oD, oD + drN)`, from the first copy's counts:
   the call's data word `unaryList (hashNums ++ thrCounts)`;
4. `mC`: the HASH cell (`HashCell.cellM`) on `[oC, oC + BX + 1)`, its request, data word, `1^V` and `1^W`
   read from the request tape, T-a's output and the second copy's `gUD`, `gUW`;
5. `mK`: the kept words writer docked (T-b, `C4KW.kwDockM`) on `[oK, oK + 94 + W.x)`, its twelve inputs the HASH
   tape (`gP1`), the cell's ten streams and `gW 3` (`1^{fr 1}`);
6. `mQ`: the copy of `1^{Q'}` (T-c, `C4KW.qDockM`) from `gW 34` onto `oQ`.

* the offsets `xb`, `oF1`, `oF2`, `oD`, `oC`, `oK`, `oQ`, `hOff`, `XH`; the tapes `g0`, `tNt`, `tLt`, `tDt`, `uT`,
  `vT`, `wT`, `extC`, `kInH`, `srcQ`, `hkTH`, `hqTH`; the stages and **`M0H`**.

Paper quantity of the main type: the HASH stage's setup machine (its bank carries `HBank2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires.WireExponent3_5.PrimT.C4Set

section Lay
variable (L : Lay) {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
  (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg)
  (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (Wk : PrimT.C4KW.KWW) (fT : ℕ)

/-- The THR setup chain's scratch count. -/
abbrev xb : ℕ := ThrSet.thrXb L S4.x3
/-- The first front copy's region. -/
abbrev oF1 : ℕ := 3 + xb L S4
/-- The second front copy's region. -/
abbrev oF2 : ℕ := oF1 L S4 + L.N
/-- T-a's region. -/
abbrev oD : ℕ := oF2 L S4 + L.N
/-- The HASH cell's region. -/
abbrev oC : ℕ := oD L S4 + PrimT.C4KW.drN S4
/-- T-b's region. -/
abbrev oK : ℕ := oC L S4 + (BX (cX T N) + 1)
/-- T-c's region. -/
abbrev oQ : ℕ := oK L S4 T N + 94 + Wk.x
/-- **The setup's end**: the bank is blank from here up. -/
abbrev hOff : ℕ := oQ L S4 T N Wk + 3
/-- The bank's scratch count (room for the pre-loop stage, the loop, the finisher: `fT` the loop family's tapes). -/
abbrev XH : ℕ := hOff L S4 T N Wk + fT + 17

theorem LN_le : L.N ≤ 3 + xb L S4 := by
  show 3 + L.X ≤ 3 + ThrSet.thrXb L S4.x3
  unfold ThrSet.thrXb; omega

theorem hxX : 3 + xb L S4 ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ oK oC oD oF2 oF1; omega

/-- The request tape. -/
def g0 : Fin (3 + XH L S4 T N Wk fT) := ⟨0, by omega⟩

theorem hF1 : oF1 L S4 + L.N ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ oK oC oD oF2; omega
theorem hF2 : oF2 L S4 + L.N ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ oK oC oD; omega
theorem hDD : oD L S4 + PrimT.C4KW.drN S4 ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ oK oC; omega
theorem hCC : oC L S4 + (BX (cX T N) + 1) ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ oK; omega
theorem hKK : oK L S4 T N + 94 + Wk.x ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff oQ; omega
theorem hQQ : oQ L S4 T N Wk + 3 ≤ 3 + XH L S4 T N Wk fT := by unfold XH hOff; omega

/-- The first copy's `1^n`, `1^{C_L(n+1)^D}`, `1^{C_d(n+1)^D}` (T-a's counts). -/
def tNt : Fin (3 + XH L S4 T N Wk fT) := HashSet.fcT L (oF1 L S4) (hF1 L S4 T N Wk fT) L.gN1
def tLt : Fin (3 + XH L S4 T N Wk fT) := HashSet.fcT L (oF1 L S4) (hF1 L S4 T N Wk fT) L.gUL
def tDt : Fin (3 + XH L S4 T N Wk fT) := HashSet.fcT L (oF1 L S4) (hF1 L S4 T N Wk fT) L.gUD

/-- T-a's counts' tape (the call's data word). -/
def uT : Fin (3 + XH L S4 T N Wk fT) :=
  ⟨oD L S4 + PrimT.C4KW.drTU S4, by
    have := hDD L S4 T N Wk fT
    have : PrimT.C4KW.drN S4 = PrimT.C4KW.drM3 S4 + 3 := rfl
    have : PrimT.C4KW.drTU S4 = PrimT.C4KW.drM3 S4 + 1 := rfl
    omega⟩

/-- The second copy's `1^{C_d(n+1)^D}` (the cell's `1^V`) and `1^{2^m}` (the cell's fill count). -/
def vT : Fin (3 + XH L S4 T N Wk fT) := HashSet.fcT L (oF2 L S4) (hF2 L S4 T N Wk fT) L.gUD
def wT : Fin (3 + XH L S4 T N Wk fT) := HashSet.fcT L (oF2 L S4) (hF2 L S4 T N Wk fT) L.gUW

/-- The cell's four inputs on the bank. -/
def extC (j : Fin (BX (cX T N) + 1)) : Option (Fin (3 + XH L S4 T N Wk fT)) :=
  if j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 0))) then some (g0 L S4 T N Wk fT)
  else if j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 113))) then some (uT L S4 T N Wk fT)
  else if j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 2))) then some (vT L S4 T N Wk fT)
  else if j = Fin.castAdd 1 (bCnt (cX T N)) then some (wT L S4 T N Wk fT) else none

/-- The kept words writer's inputs: the HASH tape (`gP1`), the cell's streams `kS i`, `gW 3`. -/
def kInH (i : Fin 12) : Fin (3 + XH L S4 T N Wk fT) :=
  if i.val = 0 then ⟨1, by omega⟩
  else if i.val = 10 then ⟨(L.gW 3).val, by have := (L.gW 3).isLt; have := LN_le L S4; unfold XH hOff oQ oK oC oD oF2 oF1; omega⟩
  else ⟨oC L S4 + (kS i).val + 1, by
    have := (kS i).isLt; have := hCC L S4 T N Wk fT
    have : BX (cX T N) = LNS (cX T N) + 2 + LNR + 2 := rfl
    unfold LNS at this; omega⟩

/-- T-c's source: `gW 34` (`1^{fr 2}`). -/
def srcQ : Fin (3 + XH L S4 T N Wk fT) :=
  ⟨(L.gW 34).val, by have := (L.gW 34).isLt; have := LN_le L S4; unfold XH hOff oQ oK oC oD oF2 oF1; omega⟩

/-- `HBank2`'s kept words' tapes (T-b's outputs) and `1^{Q'}`'s tape (T-c's output). -/
def hkTH (j : Fin 94) : Fin (3 + XH L S4 T N Wk fT) := ⟨oK L S4 T N + j.val, by have := hKK L S4 T N Wk fT; omega⟩
def hqTH : Fin (3 + XH L S4 T N Wk fT) := ⟨oQ L S4 T N Wk, by have := hQQ L S4 T N Wk fT; omega⟩

variable (CL Cd Cc cr : ℕ) (P : WM (LNS 0) LNR)

/-- 1: the THR setup chain, lifted. -/
noncomputable def mSet :=
  RecoveryFocus.machine (BigBank.liftE (hxX L S4 T N Wk fT)) (ThrSet.setupT3 L CL Cd Cc S4.x3 S4.s3 S4.M3 P)
/-- 2: the two front copies. -/
noncomputable def mF1 := HashSet.frontCopyM L CL Cd Cc (oF1 L S4) (hF1 L S4 T N Wk fT) (g0 L S4 T N Wk fT)
noncomputable def mF2 := HashSet.frontCopyM L CL Cd Cc (oF2 L S4) (hF2 L S4 T N Wk fT) (g0 L S4 T N Wk fT)
/-- 3: T-a. -/
noncomputable def mD := PrimT.C4KW.drM S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT)
  (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT)
/-- 4: the HASH cell. -/
noncomputable def mC := RecoveryFocus.machine (slx (oC L S4) (hCC L S4 T N Wk fT) (extC L S4 T N Wk fT)) (cellM T N cr)
/-- 5: T-b. -/
noncomputable def mK := PrimT.C4KW.kwDockM Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT)
/-- 6: T-c. -/
noncomputable def mQ := PrimT.C4KW.qDockM (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT)

/-- **The HASH setup's machine** (`setupH`/`hashStageU` parameter `M0`). -/
noncomputable def M0H :=
  Composition.machine (mSet L S4 T N Wk fT CL Cd Cc P) (Composition.machine (mF1 L S4 T N Wk fT CL Cd Cc)
    (Composition.machine (mF2 L S4 T N Wk fT CL Cd Cc) (Composition.machine (mD L S4 T N Wk fT)
      (Composition.machine (mC L S4 T N Wk fT cr) (Composition.machine (mK L S4 T N Wk fT) (mQ L S4 T N Wk fT))))))

end Lay

end NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
