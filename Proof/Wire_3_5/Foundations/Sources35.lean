import Lean
import W3.Proof.Foundations.SourceRegistry
import Proof.Foundations.HierarchySourceContract
import Proof.Foundations.RecoverySourceContracts


/-! # The source bundle at the range the proof reads (inputs 8 and 9 narrowed)

The Theorem 2.5 source bundle with its refuter and amplifier fields at exactly the arguments this proof reads:
* the refuter (CLW20 Theorem 1.13, §H.1 item 3) at the polynomial clocks `T(n) = n^(k+2)` (`refuter k`; the hierarchy
  clock `N^{C_clk}` of "Clock, hierarchy verifier, and source lengths", `C_clk = kclk + 2`);
* the amplifier (CLW20 Lemma 3.9, §H.1 item 4) at the one oracle degree `17·c_STV` of Case 1's simulation margin
  (`AmplifierAt35`);
* the other fields as in the Theorem 2.5 bundle (`normalization`, `decomposition`, `williams`, `expander`, `prime`, the
  short PCP and the pointwise PCPP, the XOR source).

Paper quantity of the main type: the imported results of §H.1 at the parameters the proof instantiates. -/

set_option autoImplicit false


namespace NearCubicWires.RepairSource
open NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation

/-- The amplifier at the one oracle degree `17·c_STV` the proof reads (CLW20 Lemma 3.9 at `S = oracleSizeBound`). -/
structure AmplifierAt35 where
  stvExponent : ℕ
  stvExponentPositive : 1 ≤ stvExponent
  schedule : _root_.NearCubicWires.RepairSource.OrdinaryScheduleAmplifier stvExponent (17 * stvExponent)

/-- **The source bundle** with the refuter at the clocks `n^(k+2)` and the amplifier at the degree `17·c_STV`. -/
structure Sources35 : Prop where
  normalization : ThresholdNormalizationContract
  decomposition : DecompositionSource
  williams : WilliamsSource
  expander : ExpanderSpectrumContract
  prime : PrimeThetaBoundContract
  pcp : W3.NearCubicWires.RepairSource.PCPSourceGroup
  refuter : ∀ k : ℕ, Nonempty
    (_root_.NearCubicWires.RepairSource.HierarchyRefuterAlgorithm (fun n => n ^ (k + 2)))
  xor : XorSource
  amplifier : Nonempty AmplifierAt35

/-- The hierarchy and its refuter at the clock `n^(k+2)`. -/
noncomputable def Sources35.hierarchy (S : Sources35) (k : ℕ) :
    _root_.NearCubicWires.RepairSource.HierarchyRefuterAlgorithm (fun n => n ^ (k + 2)) :=
  Classical.choice (S.refuter k)

/-- The amplifier at the degree `17·c_STV`. -/
noncomputable def Sources35.amplification (S : Sources35) : AmplifierAt35 :=
  Classical.choice S.amplifier

end NearCubicWires.RepairSource

