import W3.Aliases
import Proof.Foundations.HierarchySourceContract
import Outer.Source
import Proof.Foundations.RepresentationSourceContracts

w3_alias_base

namespace W3


/-! The repaired eight source groups, containing ten literature constituents.
No U, ordinary simulator, rational bound, codec or local running-time supplier
is an imported field. The final target records ordinary E^NP explicitly. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure PCPSourceGroup : Prop where
  shortPCP : NearCubicGates.Close.Outer.MWSource
  proximity : PointwisePCPPSource

end NearCubicWires.RepairSource

end W3
