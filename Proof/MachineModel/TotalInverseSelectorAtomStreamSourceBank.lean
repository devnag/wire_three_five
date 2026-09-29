import Proof.Circuits.InverseSelectorAtomStreamClosure

/-!
# Frozen source-bank setup for the guarded selector atom stream

This module isolates the unchanged fixed-target source-driven bank.  The
guarded selector proof can consume its exact frame without reopening the
source schedule normalization.
-/

namespace NearCubicWires.TotalInverseSelectorAtomStreamSourceBank

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.UniformTargetLanguageBank

end NearCubicWires.TotalInverseSelectorAtomStreamSourceBank
