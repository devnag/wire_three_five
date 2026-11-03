import Lean
import Proof.Wire_3_5.Foundations.OutMachineSAShell
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineSlot1WBase


noncomputable section
set_option maxRecDepth 4096


/-! # SA's slot 1, part 1: the sample word is a copy of the seed's frames

"The final pass reads the fixed seeds from its input" (P3:3165-3175): the final pass's input is `fpIn r = r.word ++
seedWord r`, and the seed word is the greedy sample in the final pass's format, `sampleWord kh S` (per pair two framed
`kh`-bit halves), followed at a THR call by the framed hash bits. S4's word 1 (`sampWord P smp`, P3:3044-3048) is the
same frames with a closing `false`:

* `flatMap_eq`, `sampleWord_frames` (a sample word is the flattened frames of its halves), **`sampWord_eq`** (the
  bridge);
* **`seed_split`**: at every request, `seedWord = flatten (map frame (fs ++ ex))` with `ex` the hash frame at THR and
  empty at SYM, and S4's word 1 `= flatten (map frame fs) ++ [false]`.

Paper quantity of the main type: S4's sample word and the input's seed word (P3:3044-3048, 3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **The seed's frames**: at every request, the input's seed word is the frames `fs` (and at THR the hash frame),
and S4's word 1 is the frames `fs` with a closing `false`. -/
theorem seed_split (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    ∃ fs ex : List (List Bool),
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1 = ((fs ++ ex).map frame).flatten ∧
      ex.length = (if PrimAsm.Codec.modeBit r.1.mode then 1 else 0) ∧
      SA.slot1Ws l F kclk coef A a ha r 0 = (fs.map frame).flatten ++ [false] := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  cases mode
  · refine ⟨?fs, [?h], ?e1, rfl, ?e2⟩
    case e2 =>
      simp only [SA.slot1Ws, frontWordsW2, frontWordsOfW2, dif_pos hs]
      show sampWord _ _ = _
      rw [sampWord_eq, sampleWord_frames]
    case e1 =>
      simp only [seedWord, dif_pos hs]
      rw [sampleWord_frames, List.map_append, List.flatten_append]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rfl
  · refine ⟨?fs2, [], ?f1, rfl, ?f2⟩
    case f2 =>
      simp only [SA.slot1Ws, frontWordsW2, frontWordsOfW2, dif_pos hs]
      show sampWord _ _ = _
      rw [sampWord_eq, sampleWord_frames]
    case f1 =>
      simp only [seedWord, dif_pos hs, List.append_nil]
      exact sampleWord_frames _ _

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1

end
