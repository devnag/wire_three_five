import Proof.Packets.SrcStartBankInst

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding P1Closure SupplierPipeline SupplierEstimator
open RepairSource RepairSource.CloseoutFinal PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- The bank's cost coefficient (degree 4 in `|nativeWord| + q + 1`). -/
def bankK : ℕ :=
  3 * BlockPlatform.UnaryCalc.polyCoefficient 3 16777216 + 3 * BlockPlatform.UnaryCalc.polyCoefficient 2 262144 + 2^30

theorem frames_length (xs : List (List Bool)) (q : ℕ) (h : ∀ x ∈ xs, x.length = q) :
    (PacketsGlue.CountFrames.frames xs).length = xs.length * (2*q+1) := by
  induction xs with
  | nil => simp [PacketsGlue.CountFrames.frames]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [PacketsGlue.CountFrames.frames, List.map_cons, List.flatten_cons, List.length_append,
      RepairOrdinary.frame_length, List.length_cons] at ht ⊢
    rw [ht, hx]
    ring

theorem supF_frames_length (a : DecompositionAlgorithm) (r : Request) :
    (PacketsGlue.CountFrames.frames (supF a r)).length = (r.family a).occurrences.length * (2*r.q+1) := by
  rw [frames_length (supF a r) r.q, supF_length]
  intro x hx
  unfold supF at hx
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
  simp

theorem members_length {q : ℕ} (live : Finset (Fin q)) : (CloseoutRowsGateSupport.gateMembers live).length = q := by
  rw [CloseoutRowsGateSupport.gateMembers, List.length_ofFn]

/-- **The start bank's cost is `≤ bankK·(|nativeWord| + q + 1)^4`.** -/
theorem bankCost_le (a : DecompositionAlgorithm) (r : Request) :
    bankCost a r ≤ bankK * (r.nativeWord.length + r.q + 1)^4 := by
  have hN : (r.family a).occurrences.length ≤ r.nativeWord.length := occ_le_nw a r
  have hsup := supF_frames_length a r
  have hsl := supF_length a r
  have hmem := members_length (Packets.live (r.family a))
  unfold bankCost wordsCost PCJ6e421fabe2aa4155_SourcePoolProduced.budget PCJ6e421fabe2aa4155_SourcePoolMasters.budget
    PCJ6e421fabe2aa4155_SourcePoolPreparation.budget PCJ6e421fabe2aa4155_SourcePoolDrivers.budget
    PCJ6e421fabe2aa4155_SourcePoolScalars.budget PCJ6e421fabe2aa4155_SourcePoolHeader.budget
    PCJ6e421fabe2aa4155_SourcePoolInitialize.budget Stream.xBound
  rw [RepairOrdinary.frame_length, hsup, hsl, hmem, List.length_replicate]
  generalize (r.family a).occurrences.length = N at hN ⊢
  generalize r.nativeWord.length = B at hN ⊢
  have p3 := BlockPlatform.UnaryCalc.poly_cost_polyBounded 3 16777216 (B+r.q)
  have p2 := BlockPlatform.UnaryCalc.poly_cost_polyBounded 2 262144 (B+r.q)
  unfold ValidatorPolynomialDomination.PolyBounded at p3 p2
  have hval : PCJ6e421fabe2aa4155_SourcePoolCapacity.value B r.q = 16777216*(B+r.q+1)^3 := rfl
  rw [hval]
  have hdp := RepairSource.ProjectionNormalization.DimensionPower.cost_bound 1 8 (B+r.q+1) 1 le_rfl
  generalize hMd : B + r.q + 1 = M at p3 p2 hdp ⊢
  have hM : 1 ≤ M := by omega
  have e4 : M^(3+1) = M^4 := rfl
  have e3 : M^(2+1) = M^3 := rfl
  rw [e4] at p3
  rw [e3] at p2
  have x12 : M ≤ M^2 := by nlinarith
  have x23 : M^2 ≤ M^3 := Nat.pow_le_pow_right hM (by omega)
  have x34 : M^3 ≤ M^4 := Nat.pow_le_pow_right hM (by omega)
  have p2' : BlockPlatform.UnaryCalc.polyCoefficient 2 262144 * M^3 ≤ BlockPlatform.UnaryCalc.polyCoefficient 2 262144 * M^4 :=
    Nat.mul_le_mul_left _ x34
  have hdp2 : (M+1)^(1+1) ≤ 4*M^2 := by
    have : (M+1)^(1+1) ≤ (2*M)^2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hbit : natBitLength (2*N) ≤ 2*N+1 := Nat.add_le_add_right (Nat.log_le_self 2 (2*N)) 1
  have hhdr : NearCubicWires.RepairOrdinary.EquationNaturalHeader.budget (2*N) ≤ 300*M^2 := by
    unfold NearCubicWires.RepairOrdinary.EquationNaturalHeader.budget
    have h1 : N ≤ M := by omega
    have h2 : (2*N)^2 ≤ 4*M^2 := by
      have := Nat.pow_le_pow_left (show 2*N ≤ 2*M by omega) 2
      nlinarith
    omega
  have hx : (B + 30)^2 ≤ 900*M^2 := by
    have := Nat.pow_le_pow_left (show B + 30 ≤ 30*M by omega) 2
    nlinarith
  have hsq : N*(2*r.q+1) ≤ 2*M^2 := by
    have := Nat.mul_le_mul (show N ≤ M by omega) (show 2*r.q+1 ≤ 2*M by omega)
    nlinarith
  have hK : bankK * M^4 = 3*(BlockPlatform.UnaryCalc.polyCoefficient 3 16777216 * M^4) +
      3*(BlockPlatform.UnaryCalc.polyCoefficient 2 262144 * M^4) + 2^30 * M^4 := by unfold bankK; ring
  rw [hK]
  have hq : r.q ≤ M := by omega
  have hB : B ≤ M := by omega
  have e1 : 16777216*M^3 ≤ 16777216*M^4 := Nat.mul_le_mul_left _ x34
  omega

end
end NearCubicWires.SourceStart.Bank

