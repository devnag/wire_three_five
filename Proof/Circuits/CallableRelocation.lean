import Proof.Foundations.VerifiedLinker

/-!
# Canonical callable-program relocation

A fixed callee can be embedded in a larger controller while preserving its
interpreter trace, isolating its register bank, and replacing its halt with one
accumulating return.  This module is independent of any sequence encoding or
controller, so the balanced public ABI and other fixed callers share one
relocation proof.
-/

namespace NearCubicWires.CallableRelocation

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker




end NearCubicWires.CallableRelocation
