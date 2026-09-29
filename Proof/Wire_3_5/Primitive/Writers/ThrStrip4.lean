import Proof.Wire_3_5.Primitive.Writers.ThrStrip3

/-! # c4 THR block, the request's strip, part 4: the program and its run

**`stripW`**: from the THR writer's input `reqW n true codes cc (natListWord tr ++ hbF)` on stream `0`, the output
stream `sY` holds `frame (reqW n true codes cc (natListWord tr))`, the request's own word (the hash suffix stripped),
stream `0` unchanged. The request's parse is `hbXW`'s, verbatim (`parseW`); the prefix's length is the word's pair
count minus the suffix's.

Paper quantity of the main type: the THR request's word (the compiler's input, P3:1886-1906) read off the THR input. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The strip's count registers. -/
def rA : Fin LNR := ⟨470, by decide⟩
def rE : Fin LNR := ⟨471, by decide⟩
def rD : Fin LNR := ⟨472, by decide⟩
/-- **The stripped request's stream.** -/
abbrev sY : Fin (LNS 0 + 1) := sk 0 122

/-- The request's parse (`hbXW`'s first eight steps). -/
def parseW : WM (LNS 0) LNR :=
  .seq (skipNatM true (sk 0 0) dF dC) (.seq (.fwd (sk 0 0)) (.seq (.fwd (sk 0 0))
  (.seq (readNatM true (sk 0 0) dF dC dK dP dT) (.seq (skipCodesW 0)
  (.seq (readNatM true (sk 0 0) dF dC dK dP dT) (.seq (skipCodesW 0)
  (CopyNat.copyNatListM true (sk 0 0) sD hQ)))))))

/-- **The strip program.** -/
def stripW : WM (LNS 0) LNR :=
  .seq (cnt3W (sk 0 0) rA rE rD) (.seq (rew2W (sk 0 0) rD) (.seq parseW (.seq (suf1W (sk 0 0) rA)
    (.seq (rew2W (sk 0 0) rE) (.seq (cpyW (sk 0 0) sY rA) (.wr sY false))))))

theorem frame_m (w : List Bool) : frame w = marks w ++ [false] := Modulus.frame_eq_marks w

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
