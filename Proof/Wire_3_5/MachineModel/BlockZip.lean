import Proof.Wire_3_5.MachineModel.BlockCost
import Proof.Wire_3_5.MachineModel.BlockOfRun

/-! # Block v3 (S5): one-pass bit scans over two framed words (fold and map)

Paper: the regular filters and the pullback use bit-level primitives on `ℓ`-bit and `n`-bit words.
- P3:1664-1671: a center bit "may be a parity of many message bits", a masked parity.
- The field arithmetic of `GF(2^ℓ)` is shifts and XORs (P3:2932-2941), with the trace a masked parity.
- The binary elimination XORs rows (P3:2950-2957).

The paper quantities are the scanned word functions: the fold `ZipFold.fold f σ left right`, e.g. the
masked parity `⟨a, mask⟩ mod 2` and word equality, and the map `ZipMap.map out nxt σ left right`,
e.g. the bitwise XOR and AND of two words.

The machines generalize the Theorem 2.5 comparison machine (`OrdinaryCompare`: a 1-bit-state fold,
`Compare.next`) and the adder (`OrdinaryAdd`: a 1-bit-state map with carry) to an ARBITRARY 1-bit
transducer. Each is proved once (`ZipFold.scan_prefix`, `ZipMap.scan_prefix`) and instantiated as a
block with its exact output in `2|left|+1` steps. The instances are `xorBlock`, `andBlock`,
`parityBlock` and `eqBlock`. The twins are the reference folds and maps, checked by `decide`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-! ## The fold: a 1-bit state over two framed words, the final state appended to the output -/

namespace ZipFold

/-- The reference fold: low bit first. -/
def fold (f : Bool → Bool → Bool → Bool) : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | a :: as, b :: bs, old => fold f as bs (f a b old)
  | _ :: _, [], old => old


end ZipFold

/-! ## The map: a 1-bit state over two framed words, a framed output word -/

namespace ZipMap

/-- The reference map: the output bit of each position, low bit first. -/
def map (out nxt : Bool → Bool → Bool → Bool) : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, b :: bs, old => out a b old :: map out nxt as bs (nxt a b old)
  | _ :: _, [], _ => []

@[simp] theorem map_length (out nxt : Bool → Bool → Bool → Bool) (left right : List Bool) (old : Bool)
    (hw : left.length = right.length) : (map out nxt left right old).length = left.length := by
  induction left generalizing right old with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [map, ih right _ (by simpa using hw)]

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (state : Fin 5) (inputMove : HeadMove) (output : Bool) : Action 3 5 :=
  ⟨state, fun i => if i.val = 2 then some output else none,
    fun i => if i.val = 2 then .right else inputMove⟩

/-- The map machine: tape 0 and tape 1 are the framed words, tape 2 receives the framed output. -/
def machine (out nxt : Bool → Bool → Bool → Bool) (init : Bool) : Machine 3 5 where
  descriptionBits := 0
  start := scanState init
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val < 2 then
      if scanned 0 then some (action (bitState (state.val == 1)) .right true)
      else some (action 4 .stay false)
    else if state.val < 4 then
      some (action (scanState (nxt (scanned 0) (scanned 1) (state.val == 3))) .right
        (out (scanned 0) (scanned 1) (state.val == 3)))
    else none

end ZipMap

/-! ## Instances: XOR, AND, masked parity, equality -/

/-- Bitwise XOR of two words. -/
def xorOut (a b _ : Bool) : Bool := xor a b
/-- Bitwise AND (masking). -/
def andOut (a b _ : Bool) : Bool := a && b
/-- The state is unused by the pointwise maps. -/
def keep (_ _ old : Bool) : Bool := old
/-- The masked parity `⊕ᵢ aᵢ·bᵢ` (the trace `⟨τ, a⟩` and the pullback's center-bit parities). -/
def parityStep (a b old : Bool) : Bool := xor old (a && b)

theorem map_xor (left right : List Bool) (hw : left.length = right.length) (old : Bool) :
    ZipMap.map xorOut keep left right old = List.zipWith xor left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right => simp [ZipMap.map, xorOut, keep, ih right (by simpa using hw)]

/-- The masked parity is the XOR of the positionwise ANDs, `⊕ᵢ aᵢ·bᵢ` (from `old`). -/
theorem fold_parity (left right : List Bool) (old : Bool) :
    ZipFold.fold parityStep left right old = (List.zipWith (· && ·) left right).foldl xor old := by
  induction left generalizing right old with
  | nil => cases right <;> rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right => simp only [ZipFold.fold, List.zipWith_cons_cons, List.foldl_cons, parityStep, ih]

/-! ## Costs -/

/-! ## Executable twins -/


end NearCubicWires.WireExponent3_5.Block
