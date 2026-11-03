import Proof.Wire_3_5.FinalPass.Core7

/-! # S5Core, part 9: the request's head and the SYM slots at a THR request (P3:3083-3086, 3170-3181)

* `reqW_shape`, **`fpIn_shape`** (the final pass's input starts `1^L 0 bits mb`, `L = natBitLength n`, `|bits| = L`, `mb`
  the THR flag), `fixed_len`, **`fpIn_len`** (`2L + 2 ≤ |fpIn|`);
* **`sym_blank_thr`** (at a THR request the SYM slots of `frontWordsW2` are blank).

Paper quantities: the request's head and mode (P3:3083-3086); the front's words (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- The request word's head: `natWord n = 1^L 0 bits`, then the mode bit. -/
theorem reqW_shape (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    PrimAsm.Data.reqW n mb codes cc tl = List.replicate (natBitLength n) true ++ false ::
      (WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n ++ mb :: (RepairRepresentation.natWord codes.length ++
        codes.flatMap RepairRepresentation.natWord ++ RepairRepresentation.natListWord cc ++ tl)) := by
  simp [PrimAsm.Data.reqW, RepairRepresentation.natWord, WilliamsPublishedForm.framedNatBits]

/-- The THR flag of a mode. -/
def thrFlag : Mode → Bool
  | .thr => true
  | .sym => false

section Family
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem fixed_len (L v : ℕ) : (WilliamsPublishedForm.fixedWidthNatBits L v).length = L := by
  simp [WilliamsPublishedForm.fixedWidthNatBits]

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Core
