import Proof.Wire_3_5.UnionMachine.NumsC1

/-! # NW phase (c), part 2: the program `cProg` (n, the mode bit, `e = n − k`, `T_f`)

From the writer's entry (`NumsPh2.Entry`: `frame fpIn` on `sIn`, `fpIn = natWord n ++ (mode bit :: …)`): PA's
`ParseNat.readNatM` reads `n` into `rN`; one step and a test read the mode bit into `rM`; PA's star numbers
`StarNums.starNumsM c_r 0` on `starBlk` (from a copy of `n`) give `k = r·s` (`starBlk 9`); `UnaryArith.subW` gives
`e = n − k` in `rE`; `T_f = KT·(n+2)^{ZT}` in `rT` (`incN`, `powN`); `clearL` zeroes the block and the scratch
`g 0 … g 9`; the input is rewound by a copy of `T_f` (`WM.rewind`).

* `g`, `R6`, `RS`, `rsC`, **`cProg`**; `mode_bit`, `fpIn_split`.

Paper quantities of the main type: the call's length `n`, its mode, the shift `n − k` of `Den = 2^{n−k}·V`, the width
`T_f` (P3:3044-3048, `star:partition` P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- Scratch registers `470 … 479`. -/
def g (j : Fin 10) : Fin LNR := ⟨470 + j.val, by have := j.isLt; show 470 + j.val < 512; omega⟩

/-- The power's registers `(a, m, t, u, w, v) = (rT, g 6, g 7, g 4, g 5, g 9)`. -/
def R6 : Fin 6 ↪ Fin LNR := ⟨![rT, g 6, g 7, g 4, g 5, g 9], by decide⟩

/-- The subtraction's registers `(a, b, t, w) = (rE, k, g 4, g 5)`. -/
def RS : Fin 4 ↪ Fin LNR := ⟨![rE, starBlk 9, g 4, g 5], by decide⟩

/-- The registers (c) clears: the star block and the scratch. -/
def rsC : List (Fin LNR) := (List.finRange 20).map starBlk ++ (List.finRange 10).map g

/-- **Phase (c)'s program** at the gate's `c_r`, `KT`, `ZT`. -/
def cProg (x cr KT ZT : ℕ) : WM (LNS x) LNR :=
  .seq (ParseNat.readNatM true (sIn x) (g 0) (g 1) rN (g 2) (g 3))
  (.seq (.fwd (sIn x)) (.seq (.ifs (sIn x) (.inc rM) .skip)
  (.seq (FinalPass.Hash4.wcopyR rN (starBlk 0) (g 4))
  (.seq (StarNums.starNumsM cr 0 starBlk)
  (.seq (FinalPass.Hash4.wcopyR rN rE (g 4))
  (.seq (UnaryArith.subW RS)
  (.seq (StarNums.incN rT KT)
  (.seq (FinalPass.Hash4.wcopyR rN (g 6) (g 4))
  (.seq (StarNums.incN (g 6) 2)
  (.seq (powN R6 ZT)
  (.seq (clearL rsC)
  (.seq (FinalPass.Hash4.wcopyR rT (g 8) (g 4))
  (WM.rewind (sIn x) (g 8))))))))))))))

/-- The mode bit is the framed input's cell after `natWord n` and its marker. -/
theorem mode_bit (w tl : List Bool) (b : Bool) :
    readTapeBit ([] ++ ParseNat.enc true w ++ (marks (b :: tl) ++ [false])) (2 * w.length + 1) = b := by
  have hl : (ParseNat.enc true w).length = 2 * w.length := by rw [ParseNat.enc_length]; rfl
  rw [List.nil_append, show 2 * w.length + 1 = (ParseNat.enc true w).length + 1 by omega, ParseNat.read_pre]
  rfl

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
