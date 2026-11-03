import Joins.Transfer
import Recovery.CaseOneRuns
import Proof.CaseAnalysis.HardnessPremises

/-!
# Joins for the three-way case split

Parametric in the gates objects `mw : Outer.MWSource` and `SV : Outer.SuccinctVerifier H L` (like the gates `Outer.*`),
and in `CaseSources` (the fields of `EightSources′` the split reads besides the carrier), so nothing here waits for
the anchor. At the freeze the anchor's `language` is meant to be the one-liner
`languageC (toCase sources) k clock (shortPCP sources) (svOf …) machine degree copies clauseDegree sourceOnset`.

Paper, "Three cases at the conflicting word":
* source circuit: "a fan-in-two circuit with q inputs and at most q^G gates whose description has at
  most λ_ν bits … if it satisfies (C.10.0). Descriptions are ordered lexicographically, and ``first'' refers to this
  order." Lean reading (as in the near-cubic-gates development): `SrcExists`/`firstSrc` = `RecoveryChoice.oracleSelector` on the
  listed-pairs PCP `ENP.unitOuter` (CHECK), canonical order `canonicalBoundedCircuitDescription (oracleSizeBound d q)`.
  The `λ_ν` clause is dropped from the definition and recovered from `LenFitC` where it is used.
* Hard word: `¬ SrcExists`; Case-1 table `srcFn` = `X_z`.
* first accepted outer oracle: `firstOracle` = false-first least `HonestTable` (gates `FirstTable`).
* Hard oracle: `¬ IsCaseTwo` with `B*_src`, `O*`; Case-1 table `Ô*` = `Transfer.GateParams.pfFn O*`.
* Hard proof table: `IsCaseTwo`; `B* = selectedPair`; "H_{B*} is a tautology" = `selected_taut`.
* Case 2 table: "f(i,j,u) = T̂_ij(u) on q_0 = q+r+1 bits" = `paddedUnsigned` of the PCPP of
  `Outer.Dat … B*` (this proof's pointwise PCPP; request `PCPPRequestBoundary.request` at `Outer.Dat`).
* exceptional initial lengths: "If none exists at an exceptional initial length, the slice is set to zero."
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalBinary NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.CircuitRestriction
open NearCubicGates.Close

namespace W3.NearCubicWires.RepairSource.Outer3

section Choices

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L)

/-- `ν < q(N_ν)`. -/
theorem nu_lt_width (ν : ℕ) : ν < Outer.width mw SV (2 ^ ν) := by
  have := Outer.succ_le_widthOf k (Outer.apad mw SV) ν (by unfold Outer.apad; omega)
  unfold Outer.width
  omega

/-- CHECK (C.10.0) as the listed-pairs PCP: its accepted oracles of `q^G` gates are the source circuits for `z`. -/
noncomputable def checkPCP (ν : ℕ) (z : BitInput (2 ^ ν)) :=
  ENP.unitOuter ν (Outer.width mw SV (2 ^ ν)) (List.ofFn z) (nu_lt_width mw SV ν).le

/-- "The word z has" a source circuit (l.5671–5674, stage 1 l.5990–5995). -/
def SrcExists (d ν : ℕ) (z : BitInput (2 ^ ν)) : Prop := RecoveryChoice.SmallOracle (checkPCP mw SV ν z) d z

/-- `B*_src`, "the first source circuit for z" (l.5690). -/
noncomputable def firstSrc (d ν : ℕ) (z : BitInput (2 ^ ν)) (h : SrcExists mw SV d ν z) :
    BooleanCircuit (Outer.width mw SV (2 ^ ν)) :=
  (RecoveryChoice.oracleSelector (checkPCP mw SV ν z) d z h).circuit

/-- `C^O_{⟨B*_src⟩_ν}` has an accepted (honest) oracle (l.5694–5697; stage 2 l.5997–6005). -/
def AcceptedOracle (d ν : ℕ) (z : BitInput (2 ^ ν)) (h1 : SrcExists mw SV d ν z) : Prop :=
  ∃ t, Transfer.HonestTable (Outer.outC mw SV ν (firstSrc mw SV d ν z h1)).circuit t

/-- `O*`, "the first accepted outer oracle", as a truth table (l.5697–5699). -/
noncomputable def firstOracle (d ν : ℕ) (z : BitInput (2 ^ ν)) (h1 : SrcExists mw SV d ν z)
    (h2 : AcceptedOracle mw SV d ν z h1) :
    BitInput (2 ^ (Outer.outC mw SV ν (firstSrc mw SV d ν z h1)).ell) :=
  (Classical.choice (Transfer.existsFirstTable _ h2)).table

/-- Stage 3's PCP: "B_pf(a0^{q−ℓ_out}) = O*(a)" for every `a` (l.6007–6010). -/
noncomputable def matchPCP (ν : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ Outer.width mw SV (2 ^ ν)) (t : BitInput (2 ^ ℓ)) :=
  ENP.unitOuter ℓ (Outer.width mw SV (2 ^ ν)) (boolFunctionTable (Transfer.tableOracle t)) hℓ

/-- `X_z(u) = z_i` where `bin_ν(i)` is the first `ν` coordinates of `u` (l.5681–5684). -/
noncomputable def srcFn (ν : ℕ) (z : BitInput (2 ^ ν)) : BoolFunction (Outer.width mw SV (2 ^ ν)) := fun r =>
  z (binaryAddress fun j : Fin ν => r (Fin.castLE (nu_lt_width mw SV ν).le j))

/-- Case **Hard proof table** (l.5710–5713): `B*_src` and `O*` exist and some circuit with `q` inputs and at most `q^G`
gates satisfies `O_{B_pf} = O*`. -/
def IsCaseTwo (d ν : ℕ) (z : BitInput (2 ^ ν)) : Prop :=
  ∃ h1 : SrcExists mw SV d ν z, ∃ h2 : AcceptedOracle mw SV d ν z h1,
    ∃ hℓ : (Outer.outC mw SV ν (firstSrc mw SV d ν z h1)).ell ≤ Outer.width mw SV (2 ^ ν),
      RecoveryChoice.SmallOracle (matchPCP mw SV ν hℓ (firstOracle mw SV d ν z h1 h2)) d z

/-- `B* = (B*_src, B*_pf)`, `B*_pf` "the first circuit … such that O_{B*_pf} = O*" (l.5711–5713). -/
noncomputable def selectedPair (d ν : ℕ) (z : BitInput (2 ^ ν)) (h : IsCaseTwo mw SV d ν z) :
    Outer.OuterGuess (Outer.width mw SV (2 ^ ν)) :=
  ⟨firstSrc mw SV d ν z h.1, (RecoveryChoice.oracleSelector _ d z h.2.2.2).circuit⟩

/-- "Then H_{B*} is a tautology, because C^{O*}_{⟨B*_src⟩_ν} is unsatisfiable" (l.5713–5715). -/
theorem selected_taut (d ν : ℕ) (z : BitInput (2 ^ ν)) (h : IsCaseTwo mw SV d ν z) :
    ∀ x, (Outer.D mw SV ν (selectedPair mw SV d ν z h)).D.eval x = true := by
  intro x
  have hmatch := (ENP.unitOuter_match _ _ h.2.2.1
    (Transfer.tableOracle (firstOracle mw SV d ν z h.1 h.2.1)) z _ (fun _ => false)).mp
    ((RecoveryChoice.oracleSelector _ d z h.2.2.2).accepts (fun _ => false))
  exact Outer.D_eval_true mw SV ν (selectedPair mw SV d ν z h) _ hmatch
    (Classical.choice (Transfer.existsFirstTable _ h.2.1)).honest x

/-- The PCPP request whose circuit is `H_B = (Outer.Dat … B).D` itself, of arity `q` (
the H2′ output `frame (descriptor H_B)` docks definitionally; the near-cubic-wires paper "Add isolated gates if necessary to meet
Fact C.2's size-at-least-input premise; this does not change the computed function"). -/
noncomputable def requestOf (a : PointwisePCPPAlgorithm) (ν : ℕ) {N : ℕ}
    (B : Outer.OuterGuess (Outer.width mw SV N)) (hq : a.minimumArity ≤ Outer.width mw SV N) :
    PCPPRequest a.minimumArity where
  arity := Outer.width mw SV N
  circuit := (Outer.Dat mw SV ν B).D
  large := hq
  sizeLarge := (Outer.Dat mw SV ν B).sizeAtLeast

/-- The PCPP request at the substituted outer verifier `H_B = Outer.Dat … B` (`req`):
`requestOf` once `q ≥` the PCPP's minimum arity (all large `N`), the arity-lifted request below that (D7). -/
noncomputable def requestAt (a : PointwisePCPPAlgorithm) (ν : ℕ) {N : ℕ}
    (B : Outer.OuterGuess (Outer.width mw SV N)) : PCPPRequest a.minimumArity :=
  if hq : a.minimumArity ≤ Outer.width mw SV N then requestOf mw SV a ν B hq
  else PCPPRequestBoundary.request a (Outer.Dat mw SV ν B).D

theorem requestAt_of (a : PointwisePCPPAlgorithm) (ν : ℕ) {N : ℕ}
    (B : Outer.OuterGuess (Outer.width mw SV N)) (hq : a.minimumArity ≤ Outer.width mw SV N) :
    requestAt mw SV a ν B = requestOf mw SV a ν B hq := by
  unfold requestAt; rw [dif_pos hq]

/-- **core′**: the hard slice at source index `ν` on the conflicting word `z` (l.5668–5733): Case 2's XOR power of
the padded proof-table function `f` (l.5725–5733), Case 1's amplified `X_z` (Hard word) or `Ô*` (Hard oracle)
(§7 l.2263–2275, Fact C.4 l.4994), all padded to `target`; `false` at an exceptional length without `O*`
(l.6003–6005) and off the guards (as the old `core`). -/
noncomputable def coreC (a : PointwisePCPPAlgorithm) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (ν : ℕ) (z : BitInput (2 ^ ν)) (copies clauseBits target : ℕ) : BoolFunction target := by
  classical
  exact
    if h1 : SrcExists mw SV d ν z then
      if h2 : AcceptedOracle mw SV d ν z h1 then
        if h : IsCaseTwo mw SV d ν z then
          let request := requestAt mw SV a ν (selectedPair mw SV d ν z h)
          let pcpp := a.output request
          if hc : pcpp.clauseBits ≤ clauseBits then
            if ht : copies * (request.arity + clauseBits + 1) ≤ target then
              padCore (xorPower (paddedUnsigned pcpp hc) copies) ht
            else fun _ => false
          else fun _ => false
        else Transfer.GateParams.amplified amplifier (Outer.width mw SV (2 ^ ν))
          (Transfer.GateParams.pfFn (firstOracle mw SV d ν z h1 h2)) target
      else fun _ => false
    else Transfer.GateParams.amplified amplifier (Outer.width mw SV (2 ^ ν)) (srcFn mw SV ν z) target

/-- Case **Hard word** value. -/
theorem coreC_hardWord (a : PointwisePCPPAlgorithm) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (ν : ℕ) (z : BitInput (2 ^ ν)) (copies clauseBits target : ℕ) (h : ¬ SrcExists mw SV d ν z) :
    coreC mw SV a amplifier ν z copies clauseBits target =
      Transfer.GateParams.amplified amplifier (Outer.width mw SV (2 ^ ν)) (srcFn mw SV ν z) target := by
  unfold coreC
  rw [dif_neg h]

/-- Case **Hard oracle** value. -/
theorem coreC_hardOracle (a : PointwisePCPPAlgorithm) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (ν : ℕ) (z : BitInput (2 ^ ν)) (copies clauseBits target : ℕ) (h1 : SrcExists mw SV d ν z)
    (h2 : AcceptedOracle mw SV d ν z h1) (h : ¬ IsCaseTwo mw SV d ν z) :
    coreC mw SV a amplifier ν z copies clauseBits target =
      Transfer.GateParams.amplified amplifier (Outer.width mw SV (2 ^ ν))
        (Transfer.GateParams.pfFn (firstOracle mw SV d ν z h1 h2)) target := by
  unfold coreC
  rw [dif_pos h1, dif_pos h2, dif_neg h]

/-- Case **Hard proof table** value (Case 2). -/
theorem coreC_hardTable (a : PointwisePCPPAlgorithm) {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d)
    (ν : ℕ) (z : BitInput (2 ^ ν)) (copies clauseBits target : ℕ) (h : IsCaseTwo mw SV d ν z)
    (hc : (a.output (requestAt mw SV a ν (selectedPair mw SV d ν z h))).clauseBits ≤ clauseBits)
    (ht : copies * ((requestAt mw SV a ν (selectedPair mw SV d ν z h)).arity + clauseBits + 1) ≤ target) :
    coreC mw SV a amplifier ν z copies clauseBits target =
      padCore (xorPower (paddedUnsigned (a.output (requestAt mw SV a ν (selectedPair mw SV d ν z h))) hc) copies)
        ht := by
  unfold coreC
  rw [dif_pos h.1, dif_pos h.2.1, dif_pos h]
  simp only []
  rw [dif_pos hc, dif_pos ht]

end Choices

/-! ## Statement types (bodies after the freeze) -/

section Statements

end Statements

end W3.NearCubicWires.RepairSource.Outer3
