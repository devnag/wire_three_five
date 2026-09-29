import Proof.Wire_3_5.FinalPass.Core8

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
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The final pass's input starts with the request's head**: `1^L 0 bits mb`, `L = natBitLength n`, `mb` the THR
flag. -/
theorem fpIn_shape (r : FReq l F kclk coef A a ha) : ∃ rest : List Bool,
    fpIn l F kclk coef A a ha r = List.replicate (natBitLength r.1.n) true ++ false ::
      (WilliamsPublishedForm.fixedWidthNatBits (natBitLength r.1.n) r.1.n ++ thrFlag r.1.mode :: rest) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  cases mode with
  | thr =>
    rw [S5T.fpIn_thr l F kclk coef A a ha n a' ha' carriers translation Cs hc, reqW_shape]
    exact ⟨_, rfl⟩
  | sym =>
    rw [S5T.fpIn_sym l F kclk coef A a ha n a' ha' carriers translation Cs hc, reqW_shape]
    exact ⟨_, rfl⟩

theorem fixed_len (L v : ℕ) : (WilliamsPublishedForm.fixedWidthNatBits L v).length = L := by
  simp [WilliamsPublishedForm.fixedWidthNatBits]

/-- The input is at least the request's head long. -/
theorem fpIn_len (r : FReq l F kclk coef A a ha) :
    2 * natBitLength r.1.n + 2 ≤ (fpIn l F kclk coef A a ha r).length := by
  obtain ⟨rest, h⟩ := fpIn_shape l F kclk coef A a ha r
  rw [h]
  simp [fixed_len]
  omega

/-- **At a THR request the SYM slots are blank.** -/
theorem sym_blank_thr (r : FReq l F kclk coef A a ha) (hm : r.1.mode = .thr) (k : Fin 17) :
    frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k) = [] := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  cases mode with
  | sym => simp at hm
  | thr =>
    have hv : (symSlot k).val = 16 + k.val := rfl
    simp only [frontWordsW2, frontWordsOfW2]
    split_ifs with h1 h2 h3 h4 <;> first | rfl | omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Core
