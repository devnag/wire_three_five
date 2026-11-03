import Proof.Wire_3_5.Stage35.AfterGlue
import Recovery.CaseOneRuns
import Proof.Wire_3_5.Stage35.Kit
import ENP.TSpec
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/AfterKit.lean with the copies schedule (Stage35.WQ).

/-!
# The recovery after the refuter: the producers it docks

The near-cubic-gates paper's uniform recovery (sec:all-lengths): stage 2 ("a formula with one variable per oracle address … finds the first oracle
`O*`", `ENP.TStage`), "Run the general amplifier on `X_z` or `Ô*`" (the Case 1 machine, `Recovery.CaseOneRuns`) and
"In the small-oracle branch, the honest PCPP proof and each AND helper are computable in polynomial time once the pair
is known" (the Case 2 producer, `Recovery.HardTableRuns`). `Kit s P g` holds one machine of each, as data, for one
source bundle `s`, PCPP `P` and parameter record `g`; `kit_of` extracts it from the three producer statements.
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.After

open Stage35 _root_.NearCubicGates.Close

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- The Case 1 machine for the selected amplifier (data of `Recovery.CaseOneRuns`; the near-cubic-gates paper's extraction of the hard table Case 1 (i)/(iii),
§11.6 "run the general amplifier"). -/
structure C1Kit (s : WS35) (g : WQ) where
  t : ℕ
  st : ℕ
  M : Machine t st
  output : Fin t
  large : 3 ≤ output.val
  C : ℕ
  E : ℕ
  run : ∀ (a q : ℕ) (w : BitInput (2 ^ a)) (rest : List Bool) (n : ℕ) (point : BitInput n),
    1 ≤ q → q ≤ n → (g.amp.output q (cycFn a w q)).arity ≤ n →
    ∃ out, ClockJoin.ReadyRun M (C * (2 ^ n + 1) ^ E)
      (oneInput t (RepairOrdinary.frame (List.ofFn w) ++ rest) (RepairOrdinary.frame (List.ofFn point)) q) out ∧
      out output = RepairOrdinary.frame
        (Transfer.GateParams.amplified g.amp q (cycFn a w q) n point).toNat.bits

/-- The Case 2 producer: the Case-2 kit (`Stage35.CaseTwoKit` at `mw SV`, the PCPP algorithm `P`, the selected
amplifier, the copy schedule, `d_G`); paper v2 §H.5 Case 2 and §H.6. -/
abbrev HTKit (s : WS35) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) (g : WQ) :=
  Stage35.CaseTwoKit s.mw s.SV P g.amp g.copies g.clauseDegree g.sel

/-- The three docked producers for one `(s, P, g)`. -/
structure Kit (s : WS35) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) (g : WQ) where
  ts : ENP.TStage
  c1 : C1Kit s g
  ht : HTKit s P g

theorem c1Kit_of (h : CaseOneRuns) (s : WS35) (g : WQ) : Nonempty (C1Kit s g) := by
  obtain ⟨t, st, M, output, large, C, E, run⟩ := h g.amp
  exact ⟨⟨t, st, M, output, large, C, E, run⟩⟩

theorem kit_of (hT : ENP.TStageRuns) (h1 : CaseOneRuns) (s : WS35)
    (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) (g : WQ) (ht : HTKit s P g) :
    Nonempty (Kit s P g) := by
  obtain ⟨ts⟩ := hT
  obtain ⟨c1⟩ := c1Kit_of h1 s g
  exact ⟨⟨ts, c1, ht⟩⟩

end NearCubicGates.Close.Recovery3.After

