import Proof.Foundations.AsymptoticAdapters
import Proof.Foundations.CanonicalEncodedListLengthProgram
import Proof.Foundations.ExecutableProgramTightRefuterSource
import Proof.Foundations.OperationalWilliamsSourceCore
import Proof.Foundations.RecoveryPipeline
import Proof.Foundations.TseitinCNF

/-!
# Closed-form adapters from recovered per-class facts to the exact headlines

The recovery layer naturally proves a non-strict agreement bound with a
strictly smaller reserved advantage.  This module performs only the final
logical conversions: it combines the two modes at one onset, spends the
inverse-polynomial exponent reserve, and contraposes the fixed-advantage cap.
No source theorem or manuscript-composition premise is introduced here.
-/

namespace NearCubicWires.HeadlineClosure

open AppendixC RecoveryPipeline

end NearCubicWires.HeadlineClosure
