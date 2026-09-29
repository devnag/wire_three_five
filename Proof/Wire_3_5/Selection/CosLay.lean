import Proof.Wire_3_5.Selection.CosPT
import Proof.Wire_3_5.Primitive.Writers.StarNums

/-! # C1.5: the machine's layout and program (P3:1324-1362, 3673)

Paper: star:selection's algorithm (P3:1337-1360: enumerate, count, "Sum its exact count with the rational population
weights, over gates and rows. There are 2^k candidate cosets [...] Select a minimum objective") and the union machine's
use of it (P3:3673). This module fixes ONE concrete register machine `Pw` (50 streams, 112 registers):
* streams `Sm k = k + 2 (mod 50)`: the input `IN = Sm 48` is stream `0` (the word function's input tape), the output
  `OUT = Sm 49` is stream `1`; the coset loop's streams `Sm 0 … Sm 47`;
* registers `Qm j = j` (`j < 64`, the coset loop's), PA's star-number block `Pm i = 64 + i`, the round counter `rC = 84`,
  the parse's registers `85 … 99`, the output block `Rout i = 100 + i`;
* `Pw := parseP ; cosetL ; setOut ; outW ; cleanP`.
Main declarations: `Sm`, `Qm`, `Pm`, `Rout`, `zPT`, `parseP`, `setOut`, `cleanP`, **`Pw`**. Paper quantity: the coset
selection machine. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.PrimT (emitW)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM dbl)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (halveM)
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith (mulAddW pow2W)
open NearCubicWires.WireExponent3_5.PrimAsm.StarNums (phaseB phaseC phaseD)
open NearCubicWires.WireExponent3_5.SelectionMachine.Gate (zw)

/-! ## The layout -/

/-- The coset loop's streams: `Sm k = k + 2 (mod 50)`. -/
def Sm (k : Fin 50) : Fin (49 + 1) := ⟨(k.val + 2) % 50, Nat.mod_lt _ (by norm_num)⟩

/-- The coset loop's registers. -/
def Qm (j : Fin 64) : Fin 112 := ⟨j.val, by omega⟩

theorem Sm_inj : Function.Injective Sm := by decide

theorem Qm_inj : Function.Injective Qm := fun a b h => Fin.ext (by simpa [Qm] using congrArg Fin.val h)

theorem Sm_surj (i : Fin 50) : ∃ k, Sm k = i := by
  refine ⟨⟨(i.val + 48) % 50, Nat.mod_lt _ (by norm_num)⟩, Fin.ext ?_⟩
  simp only [Sm]
  omega

/-- PA's star-number block. -/
def Pm : Fin 20 ↪ Fin 112 := ⟨fun i => ⟨64 + i.val, by omega⟩, fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp at this; omega)⟩

/-- The output block. -/
def Rout : Fin 12 ↪ Fin 112 := ⟨fun i => ⟨100 + i.val, by omega⟩, fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp at this; omega)⟩

/-- The population table's registers `(c, f, K, M, t, p, K2, PTL = Q 58)`. -/
def zPT : Fin 8 ↪ Fin 112 := ⟨fun i => ![90, 91, 92, 93, 89, 94, 95, 58] i, by decide⟩

/-- The stream-power block of `pow2W`: `(k, C, _, _)`. -/
def zPow : Fin 4 ↪ Fin 112 := ⟨fun i => ![73, 84, 92, 89] i, by decide⟩

/-- The product block of `mulAddW`: `Big += W·W'`. -/
def zMul : Fin 5 ↪ Fin 112 := ⟨fun i => ![86, 92, 87, 89, 93] i, by decide⟩

/-! ## The parse -/

/-- The input's length `L` (in `85`) and `2L` (in `89`); the input head back to `0`. -/
def lenP : WM 49 112 :=
  .seq (.whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.inc 85) (.seq (.inc 89) (.inc 89))))))
    (.seq (rewS 0 89 98) (WM.clear 89))

/-- `n`, `r` into PA's block; PA's phases B–D: `s`, `b`, `r/2`, `n − rb`, `s·(r/2)`, `k`. -/
def numsP : WM 49 112 :=
  .seq (readNatM true 0 91 90 64 94 89) (.seq (readNatM true 0 91 90 67 94 89)
    (.seq (phaseB Pm) (.seq (phaseC Pm) (phaseD 0 Pm))))

/-- The standing shape registers `Q 0 … Q 5`, `Q 60 = n + 1`. -/
def shapeP : WM 49 112 :=
  .seq (FinalPass.Hash4.wcopyR 70 0 89) (.seq (FinalPass.Hash4.wcopyR 69 1 89) (.seq (FinalPass.Hash4.wcopyR 68 2 89)
    (.seq (FinalPass.Hash4.wcopyR 71 3 89) (.seq (.inc 3) (.seq (halveM 3 91 90) (.seq (WM.clear 90)
      (.seq (FinalPass.Hash4.wcopyR 71 4 89) (.seq (halveM 4 91 90) (.seq (WM.clear 90)
        (.seq (FinalPass.Hash4.wcopyR 85 5 89) (.seq (.inc 5) (.seq (FinalPass.Hash4.wcopyR 64 60 89) (.inc 60)))))))))))))

/-- The widths: `W = 8(L + n + 2)` in `86`, `2W + 1` in `95`, `Big = 8W²` in `87`. -/
def widthP : WM 49 112 :=
  .seq (FinalPass.Hash4.wcopyR 85 86 89) (.seq (addR 64 89 86) (.seq (.inc 86) (.seq (.inc 86) (.seq (dbl 86 89)
    (.seq (dbl 86 89) (.seq (dbl 86 89) (.seq (FinalPass.Hash4.wcopyR 86 95 89) (.seq (dbl 95 89) (.seq (.inc 95)
      (.seq (FinalPass.Hash4.wcopyR 86 92 89) (.seq (mulAddW zMul) (.seq (WM.clear 92) (.seq (dbl 87 89)
        (.seq (dbl 87 89) (dbl 87 89)))))))))))))))

/-- The ruler `false :: 1^W` on `Sm 45`, its head home. -/
def rulerP : WM 49 112 :=
  .seq (emitW (Sm 45) false) (.seq (FinalPass.Hash4.wcopyR 86 92 89) (.seq (onesW (Sm 45) 92) (rewS (Sm 45) 87 89)))

/-- A zero word of width `N` (register) on `Z` (the helper stream `Sm 47`). -/
def zwP (Z : Fin 50) (N : Fin 112) : WM 49 112 := zw Z 98 N 89

/-- The loop's words: zero words, `BN = 1`, `OF = 2^V`, the counter words. -/
def wordsP : WM 49 112 :=
  .seq (zwP (Sm 3) 86) (.seq (zwP (Sm 33) 86) (.seq (zwP (Sm 34) 86) (.seq (zwP (Sm 35) 86) (.seq (zwP (Sm 36) 86)
    (.seq (zwP (Sm 37) 86) (.seq (zwP (Sm 38) 86) (.seq (zwP (Sm 39) 86) (.seq (zwP (Sm 40) 86) (.seq (zwP (Sm 42) 86)
      (.seq (zwP (Sm 44) 86) (.seq (zwP (Sm 46) 86) (.seq (zwP (Sm 41) 86) (.seq (oneB (Sm 41) (Sm 3) 90 91)
        (.seq (zwP (Sm 2) 86) (.seq (oneB (Sm 2) (Sm 3) 90 91) (.seq (FinalPass.Hash4.wcopyR 85 92 89)
          (.seq (.whr 92 (.seq (.dec 92) (shlB (Sm 2) (Sm 3) 90 91))) (.seq (zwP (Sm 32) 86)
            (.seq (zwP (Sm 0) 73) (zwP (Sm 43) 73))))))))))))))))))))

/-- The gate count, `NG`, and the gate table. -/
def gatesP : WM 49 112 :=
  .seq (readNatM true 0 91 90 88 94 89) (.seq (FinalPass.Hash4.wcopyR 88 92 89)
    (.seq (.whr 92 (.seq (.dec 92) (incB (Sm 32) (Sm 3) 90 91))) (.seq (FinalPass.Hash4.wcopyR 88 92 89)
      (.seq (.whr 92 (.seq (.dec 92) (addR 60 89 97))) (.seq (recL 0 (Sm 30) (Sm 45) 90 91 97) (rewS (Sm 30) 87 89))))))

/-- The population count and the population table. -/
def popsP : WM 49 112 :=
  .seq (readNatM true 0 91 90 59 94 89) (.seq (FinalPass.Hash4.wcopyR 59 96 89)
    (.seq (popsT 0 (Sm 31) (Sm 45) zPT 96) (rewS (Sm 31) 87 89)))

/-- **The parse**: from the framed request word to the coset loop's entry state. -/
def parseP : WM 49 112 :=
  .seq lenP (.seq numsP (.seq shapeP (.seq widthP (.seq rulerP (.seq wordsP (.seq gatesP (.seq popsP (pow2W zPow))))))))

/-! ## After the loop -/

/-- `r`, `s` into the output block. -/
def setOut : WM 49 112 := .seq (FinalPass.Hash4.wcopyR 67 110 89) (FinalPass.Hash4.wcopyR 68 111 89)

/-- The registers left nonzero after the output. -/
def dirty : List (Fin 112) := [0, 1, 2, 3, 4, 5, 58, 59, 60, 64, 67, 68, 69, 70, 71, 72, 73, 85, 86, 87, 88, 95, 110, 111]

/-- Clear a list of registers. -/
def clearAll : List (Fin 112) → WM 49 112
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clearAll rs)

/-- **The cleanup**: the input and output heads home, every register `0`. -/
def cleanP : WM 49 112 := .seq (rewS 0 87 89) (.seq (rewS 1 87 89) (clearAll dirty))

/-- **The coset-selection machine.** -/
def Pw : WM 49 112 :=
  .seq parseP (.seq (cosetL Sm Sm_inj Qm Qm_inj 84) (.seq setOut (.seq (outW (Sm 43) (Sm 49) Rout) cleanP)))

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
