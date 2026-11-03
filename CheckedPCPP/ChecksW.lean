import CheckedPCPP.NodeEmit
import Gadget.CheckedNodes
import Proof.PCP.PCPPNativeRequestSchema
import CheckedPCPP.Harness
import CheckedPCPP.WMXReady
import Gadget.ThreeQuery
import Mathlib.Computability.TuringMachine.Computable
import Platform.Hoare
import Platform.RegArith
import Proof.CaseAnalysis.CaseTwoRequestInput
import Proof.Foundations.OrdinaryMachine
import Proof.Foundations.SourceCore

/-!
# H3b, part 2: the check nodes of the checked circuit, row by row from the support matrix

The near-cubic-gates paper: `checkedCircuit Enc D` adds, for each code position `j`, a check that the systematic
coordinate `q + j` equals the parity of the input coordinates in the support of row `j` (closed form
`Gadget/CheckedNodes.checkNodes`: a constant, a parity chain over `canonList (support j)`, the code bit, an XOR and a
negation), conjoined onto the running output by an `and` node (`checksNodes`). The machine reads the support matrix
(H3a, `MatSem.matBit`: cell `j·q + i` is `[i ∈ support j]`) row by row and writes each node's native bytes
(`NodeEmit`). This part: one matrix row's parity chain (`colLoop`, `colLoop_runs`).

Registers `G : Fin 18 ↪ Fin nr`: `G 0 … G 7` the node writer (`G 7` the output position), `G 8` scratch, `G 9 = q`,
`G 10 = K` (next node index), `G 11` the parity accumulator, `G 12` the running conjunction, `G 13` the column,
`G 14` the row, `G 15`, `G 17` loop scratch, `G 16 = L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.ChecksW

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.SourceInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Platform
open NearCubicGates.Close.CheckedPCPP.NodeEmit

/-! ## The parity chain of one row, column by column -/

section Sem

end Sem

/-! ## Byte bounds -/

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append, List.length_replicate,
    List.length_cons, WilliamsPublishedForm.fixedWidthNatBits, List.length_ofFn]
  omega

theorem native_len_le {n : ℕ} (nd : BooleanNode n) (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) :
    (PCPPRequestNodeSchema.native nd).length ≤ 6 * V + 9 := by
  rw [native_len, natWord_len, natWord_len, natWord_len]
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 0)
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 1)
  have := natBitLength_le (PCPPRequestNodeSchema.fields nd 2)
  have := hV 0; have := hV 1; have := hV 2
  omega

theorem flatMap_native_le {n : ℕ} (V : ℕ) :
    ∀ nds : List (BooleanNode n), (∀ nd ∈ nds, ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) →
      (nds.flatMap PCPPRequestNodeSchema.native).length ≤ nds.length * (6 * V + 9)
  | [], _ => by simp
  | nd :: nds, h => by
    have h1 := native_len_le nd V (h nd (by simp))
    have h2 := flatMap_native_le V nds (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-! ## Registers and templates -/

variable {ns nr : ℕ} (cap : ℕ) (G : Fin 18 ↪ Fin nr)

/-- The node writer's registers `G 0 … G 7`. -/
def Rw : Fin 8 ↪ Fin nr :=
  ⟨fun i => G (Fin.castLE (by decide) i), fun a b h => by
    have := G.injective h
    exact Fin.ext (by simpa [Fin.ext_iff] using this)⟩

theorem Rw_apply (i : Fin 8) : Rw G i = G (Fin.castLE (by decide) i) := rfl

theorem G_ne {a b : Fin 18} (h : a ≠ b) : G a ≠ G b := G.injective.ne h

theorem Rw_ne (i : Fin 8) (b : Fin 18) (hb : 8 ≤ b.val) : Rw G i ≠ G b := by
  rw [Rw_apply]; apply G_ne; intro e; have := congrArg Fin.val e; simp at this; omega


/-! ## One row's parity chain -/

section Col

end Col

/-! ## One row: the constant, the parity chain, the code bit, the XOR, the negation, the conjunction -/


/-! ## The rows -/

section Rows

end Rows

section RowInvS

end RowInvS

end NearCubicGates.Close.CheckedPCPP.ChecksW
