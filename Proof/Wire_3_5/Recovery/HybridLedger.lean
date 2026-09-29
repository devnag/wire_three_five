import Proof.Wire_3_5.Recovery.HybridCore

/-! # The recovery ledger at the re-pinned setup `S₂` (P3:3399-3430, 3616-3626, 3657-3697, 3699-3702; D1.6)

Realizes, at the setup `S₂` (the refuter hierarchy's own PCP padded to `q(N)`), the per-length
conditions that M12 proved at `S₁`: the request's size for an oracle within `q^G` ("Every guess has `q^{O(1)} = o(N)`
bits", P3:3675-3677), the guess-length envelope as a fixed polynomial of `q`, the record `CaseTwoLedger` at one source
length (P3:3399-3430, 3616-3626), the request's arity `q(N)` eventually, and the refuter's rejected yes-instances for
the union machine at `S₂` (P3:3699-3702). The proofs are the with `S₁` replaced by `S₂`; the files are unchanged.

Paper quantities: `recKs2` (the request size coefficient at `S₂`), `requestSize2_le`, **`recBudget2`** with
`recBudget2_poly`, **`ledger_at2`**, `eventually_request_arity2`, `recMachine2`, **`rejected_yes_eventually2`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open Filter

section Sizes
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The size coefficient of the substituted request at `S₂`. -/
noncomputable def recKs2 : ℕ :=
  3 * (recPCP l kclk).coefficient + 24 * (recPCP l kclk).coefficient ^ 3 + (gatePCPP l).minimumArity + 3

theorem recQueryCount2_le (N : ℕ) :
    (recSetup2 l G kclk coef A a ha).pcp.queryCount N ≤
      (recPCP l kclk).coefficient * ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N + 1) ^
        (gateSource l).degrees.queries := by
  have hq := (recPCP l kclk).queryBound N
  have hw : (recPCP l kclk).pcp.nativeWidth N ≤ (recSetup2 l G kclk coef A a ha).pcp.nativeWidth N := le_max_left _ _
  refine hq.trans (Nat.mul_le_mul_left _ ?_)
  exact Nat.pow_le_pow_left (by omega) _

/-- The substituted request's size at `S₂` for an oracle within `q^G`. -/
theorem requestSize2_le {N : ℕ} (z : BitInput N)
    (oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N))
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
      ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N)) :
    ((recSetup2 l G kclk coef A a ha).request z oracle).circuit.size + 1 ≤
      recKs2 l kclk * ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N + 1) ^ recSigma l := by
  obtain ⟨h1, h3, h0⟩ := recSigma_ge l
  have hreq := PCPPRequestBoundary.request_size (gatePCPP l)
    (PCPPSubstitution.compactSubstituted oracle ((recSetup2 l G kclk coef A a ha).pcp.queryAddressBits z)
      ((recSetup2 l G kclk coef A a ha).pcp.decision z fun _ => false))
  have hdom : PCPPRequestBoundary.domain (gatePCPP l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) ≤
      (recSetup2 l G kclk coef A a ha).pcp.nativeWidth N + (gatePCPP l).minimumArity := by
    unfold PCPPRequestBoundary.domain; omega
  have key := size_arith _ _ _ _ _ _ _ _ _ _ (recQueryCount2_le l G kclk coef A a ha N)
    (oracleSize_le (recOracleDeg l) _ oracle.size hsize)
    (PCPPSubstitution.compactSubstituted_size oracle ((recSetup2 l G kclk coef A a ha).pcp.queryAddressBits z)
      ((recSetup2 l G kclk coef A a ha).pcp.decision z fun _ => false)) hdom h1 h3 h0
  show (PCPPRequestBoundary.request (gatePCPP l) _).circuit.size + 1 ≤ _
  rw [hreq]
  exact key

end Sizes

section BudgetPoly
variable (l : Literals)

/-- The PCPP variable count bound at `S₂`. -/
noncomputable def recNv2 (kclk q : ℕ) : ℕ :=
  (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree +
    (gatePCPP l).coefficient * (recKs2 l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree

/-- **The guess-length envelope at `S₂`** `1 + K_O + n_v·q·(4 + K_c)`. -/
noncomputable def recBudget2 (kclk q : ℕ) : ℕ := 1 + recKo l q + recNv2 l kclk q * (q * (4 + recKc q))

theorem recBudget2_poly (kclk : ℕ) : PolynomiallyBounded (recBudget2 l kclk) := by
  have hO : PolynomiallyBounded (recKo l) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_comp PCPPQueryBounds.circuit_polynomial (pb_succ_pow (recOracleExp l) 4)))
      (polynomiallyBounded_constant 1)
  have hS : PolynomiallyBounded (fun q => canonicalSymmetricCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.symWidth_poly (pb_succ_pow 26 4)
  have hT : PolynomiallyBounded (fun q => canonicalThresholdCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.thrWidth_poly (pb_succ_pow 26 4)
  have hKc : PolynomiallyBounded recKc :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add hS hT)) (polynomiallyBounded_constant 1)
  have hA : PolynomiallyBounded (fun q => (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)
  have hB : PolynomiallyBounded
      (fun q => (gatePCPP l).coefficient * (recKs2 l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _)
      (polynomiallyBounded_pow (polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)) _)
  have hNv : PolynomiallyBounded (recNv2 l kclk) := polynomiallyBounded_add hA hB
  have hQ : PolynomiallyBounded (fun q => q * (4 + recKc q)) :=
    polynomiallyBounded_mul polynomiallyBounded_id (polynomiallyBounded_add (polynomiallyBounded_constant 4) hKc)
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_constant 1) hO)
    (polynomiallyBounded_mul hNv hQ)

end BudgetPoly

section LedgerAt
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

include hG in
/-- **The Case-2 ledger at one source length at `S₂`** from the per-length facts at `q = q(N)`. -/
noncomputable def ledger_at2 (P : FusedPrimitive (G.inputs kclk coef A a ha)) (m : Mode) {N : ℕ} (z : BitInput N)
    (oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N))
    (q : ℕ) (hq : ((recSetup2 l G kclk coef A a ha).request z oracle).arity = q) (hq1 : 1 ≤ q)
    (hstar : Even (rowBr G.row.cr q) ∧ 2 ≤ rowBr G.row.cr q ∧ 4 * rowBr G.row.cr q ≤ q ∧
      Lq q ≤ starWidth (rowBr G.row.cr q) q ∧ starWidth (rowBr G.row.cr q) q ≤ Lq q ^ G.kDeg)
    (hfit : (G.budget kclk coef A a ha).FitsAt q)
    (W : ℕ) (hW : (W : ℝ) ≤ wireCap G.row.cap m q) (hW4 : W + 1 ≤ 2 * (q + 1) ^ 4) (hWq : q ≤ W)
    (hsp : G.row.sp q ≤ q)
    (Ldesc : ℕ) (hLd : Ldesc ≤ (q + 1) ^ 26) (hLd1 : 1 ≤ Ldesc)
    (hξ : 1 / (2 : ℝ) ^ (G.filterErrDeg * Nat.clog 2 (q + 2)) ≤ ((gateCParams1 l).ξ : ℝ))
    (hD : (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(G.D : ℝ)) ≤
      ((gateParams1 l).eps0 : ℝ))
    (Ko Kc : ℕ) (hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko)
    (hcodeC : ∀ C : m.Circuit q, m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc)
    (hbudget : 1 + Ko + (((recSetup2 l G kclk coef A a ha).pcppOf z oracle).systematicBits +
      ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits) * (G.row.sp q * (4 + Kc)) ≤ N / 16) :
    CaseTwoLedger (recSetup2 l G kclk coef A a ha) z oracle m P (gateCParams1 l)
      (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) W Ldesc := by
  have hδ := gateDelta_pos l
  have hCδ := gateCδ1_pos l
  have hStar : (G.inputs kclk coef A a ha).StarAt ((recSetup2 l G kclk coef A a ha).request z oracle).arity := by
    rw [hq]; exact hstar
  have hcarr : (q + 1) ^ 26 ≤ (q + 1) ^ G.carrierDeg := Nat.pow_le_pow_right (by omega) hG.carrier
  have hdescd : (q + 1) ^ 26 ≤ (q + 1) ^ G.descDeg := Nat.pow_le_pow_right (by omega) hG.desc
  have h4 : (q + 1) ^ 4 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc' : ∀ C : m.Circuit ((recSetup2 l G kclk coef A a ha).request z oracle).arity,
      m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc := by
    rw [hq]; exact hcodeC
  exact
  { hA := by
      show _ ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup2 l G kclk coef A a ha).request z oracle).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact massCap_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hΛ := by
      show 1 ≤ ((gridMassOf (gateCδ1 l) G.row.sp ((recSetup2 l G kclk coef A a ha).request z oracle).arity : ℚ) : ℝ)
      rw [hq, hG.sp]
      exact one_le_gridMass (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hs := by
      show 1 ≤ G.row.sp ((recSetup2 l G kclk coef A a ha).request z oracle).arity
      rw [hq, hG.sp]
      exact one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q
    hsδ := gridMass_hsδ (gateCδ1 l) G.row.sp _ hδ.le (gateCδ1_spec l) _
    hStar := hStar
    hFit := by rw [hq]; exact hfit
    hname := hG.name
    hdesc := by rw [hq]; exact hLd.trans hdescd
    hdescK := by
      show m.descriptionBits (unionConstAtom m _) ≤ _
      rw [unionConstAtom_descriptionBits]
      exact Nat.one_le_pow _ _ (by omega)
    hdescP := fun Sp => by
      show m.descriptionBits (unionParityAtom m _ Sp) ≤ _
      refine (unionParityAtom_descriptionBits_le m _ Sp).trans ?_
      rw [hq]; exact h4.trans hdescd
    hKP := fun Sp => by
      show (m.gates (unionParityAtom m _ Sp)).length ≤ W
      refine (unionParityAtom_gates_length m _ Sp).trans ?_
      rw [hq]; exact hWq
    hlen := by
      rw [hq]
      have h1 : (G.row.sp q + 1) * W ≤ (q + 1) * (2 * (q + 1) ^ 4) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (q + 1) * (2 * (q + 1) ^ 4) ≤ (q + 1) ^ 26 := by
        have e : (q + 1) * (2 * (q + 1) ^ 4) = 2 * (q + 1) ^ 5 := by ring
        have h5 : 2 * (q + 1) ^ 5 ≤ (q + 1) ^ 6 := by
          calc 2 * (q + 1) ^ 5 ≤ (q + 1) * (q + 1) ^ 5 := Nat.mul_le_mul_right _ (by omega)
            _ = (q + 1) ^ 6 := by ring
        have h6 : (q + 1) ^ 6 ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      exact (h1.trans h2).trans hcarr
    hbC := by rw [hq]; exact hLd.trans hcarr
    hbP := fun Sp gt hgt => by
      have h1 := unionParityAtom_encodingBits_le m _ Sp gt hgt
      have key : ∀ n : ℕ, 2 * n + 1 ≤ (n + 1) ^ G.carrierDeg := fun n => by
        have h2 : 2 * n + 1 ≤ (n + 1) ^ 2 := by
          calc 2 * n + 1 ≤ n * n + 2 * n + 1 := by omega
            _ = (n + 1) ^ 2 := by ring
        exact h2.trans (Nat.pow_le_pow_right (by omega) (by have := hG.carrier; omega))
      exact h1.trans (key _)
    Cpar := 2
    hCpar := by norm_num
    hwP := fun Sp => by
      have h1 := unionParityAtom_wires_le m ((recSetup2 l G kclk coef A a ha).request z oracle).arity Sp
      have h2 : (((m.gates (unionParityAtom m _ Sp)).wires : ℕ) : ℝ) ≤
          ((2 * ((recSetup2 l G kclk coef A a ha).request z oracle).arity ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2
    hcap := by
      have hq1' : 1 ≤ ((recSetup2 l G kclk coef A a ha).request z oracle).arity := by rw [hq]; exact hq1
      have hW' : (W : ℝ) ≤ wireCap G.row.cap m ((recSetup2 l G kclk coef A a ha).request z oracle).arity := by
        rw [hq]; exact hW
      have hc := hcap_of G.row.cap m ((G.inputs kclk coef A a ha).starParams _ hStar)
        (G.row.sp ((recSetup2 l G kclk coef A a ha).request z oracle).arity) W _ hq1' rfl
        hG.betaInv ((gateCParams1 l).β : ℝ) hG.beta hW'
      rw [hG.cpar] at hc
      push_cast at hc
      exact hc
    hξ := by rw [hq]; exact hξ
    hD := by
      show (1 + ((gridMassOf (gateCδ1 l) G.row.sp _ : ℚ) : ℝ)) ^ 4 * _ ≤ _
      rw [hq, hG.sp, gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) hCδ q]
      exact_mod_cast hD
    Ko := Ko
    Ks := 4
    Kc := Kc
    hO := hO
    hKs := intWord_grid_le
    hcodeC := hc'
    hcodeK := hc' _ (by
      show m.descriptionBits (unionConstAtom m _) ≤ Ldesc
      rw [unionConstAtom_descriptionBits]; exact hLd1)
    hbudget := by
      have e : (recSetup2 l G kclk coef A a ha).gridSize ((recSetup2 l G kclk coef A a ha).request z oracle).arity =
          G.row.sp q := by
        show G.row.sp _ = _
        rw [hq]
      rw [e]; exact hbudget }

end LedgerAt

section Facts
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The request's arity at `S₂` is `q(N)`** eventually. -/
theorem eventually_request_arity2 (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∀ᶠ N in atTop, (recSetup2 l G kclk coef A a ha).pcp.nativeWidth N = nativeWidth kclk G.Apad N ∧
      ∀ (z : BitInput N) (oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N)),
        ((recSetup2 l G kclk coef A a ha).request z oracle).arity = nativeWidth kclk G.Apad N := by
  obtain ⟨N₀, hw⟩ := recSetup2_width l G kclk coef A a ha hApad
  filter_upwards [eventually_atTop.2 ⟨N₀, hw⟩,
    (tendsto_nativeWidth kclk G.Apad).eventually (eventually_ge_atTop (gatePCPP l).minimumArity)] with N hw hm
  refine ⟨hw, fun z oracle => ?_⟩
  show max _ _ = _
  rw [hw]
  exact max_eq_left hm

end Facts

section Refuter

end Refuter

end NearCubicWires.WireExponent3_5.Transfer
