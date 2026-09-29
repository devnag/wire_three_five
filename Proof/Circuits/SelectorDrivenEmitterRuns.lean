import Proof.Circuits.SelectorDrivenAtomContextRuns

/-!
# The emitter runs at the selector-driven frame

Site 2a of the body-chain replay.  `BankEmittedAtomLoop.inverseEmitterRuns_ofCompiler`
assembles `InverseEmitterRuns` (the atom emitter run on the bank frame) from the
frame adapter runs and the compiler.  This module produces the same emitter — an
`encodeTaggedList` of the schedule's selector atoms beside the retained frame —
at the **selector-driven frame**, consuming `SelectorDrivenAtomContextRuns`'s
`InverseSelectorFrameAdapterRuns` (site 1, `hdiagonal`-free).

Only the emitter bits are frame-dependent; the fuel
(`inverseBankEmitterFuel`) is frame-independent and reused verbatim.
-/

namespace NearCubicWires.SelectorDrivenEmitterRuns

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank

end NearCubicWires.SelectorDrivenEmitterRuns
