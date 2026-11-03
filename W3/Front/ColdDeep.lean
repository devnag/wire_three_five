import W3.Front.ColdCaps
import W3.Front.ColdSem

/-!
# The cold front end, part 6: the deep part of the cold prefix (`prepP`, `tailP`)

Paper: the two guessed descriptions are read off the oracle field (D6), each is decoded by proof 1's cold
decoder on its first `L(q)` bits after checking that no `1` follows (malformed/noncanonical ⇒ reject), each is held to
`q^G` gates, and JF's `F.M` decides the λ_ν guard and (C.10.0) and builds `H_B`. `prep_exec` runs the reads and decodes;
`pass_iff` is the semantic bridge from the machine's decisions to `Passes`' core.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.Close.Worker.Format (readField countWord)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- The two fields of the oracle word (D6). -/
abbrev fld1 (raw : List Bool) : List Bool := (readField raw).1
abbrev fld2 (raw : List Bool) : List Bool := (readField (readField raw).2).1

section Sem
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (degree : ℕ)

/-- `Passes`' core at `N = 2^ν`: the oracle field decodes to a pair within the caps passing JF's guard. -/
def PassCore (ν : ℕ) (z : BitInput (2 ^ ν)) (raw : List Bool) : Prop :=
  ∃ B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν)), Worker.Decodes (Outer.width mw SV (2 ^ ν)) raw B ∧
    B.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree (Outer.width mw SV (2 ^ ν)) ∧
    B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree (Outer.width mw SV (2 ^ ν)) ∧ Guard G0 ν z B

/-- **The machine's decisions are `PassCore`.** -/
theorem pass_iff (ν : ℕ) (z : BitInput (2 ^ ν)) (raw : List Bool) :
    PassCore mw SV degree ν z raw ↔
      ((fld1 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true = 0 ∧
      ((fld2 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true = 0 ∧
      ∃ c0 c1 : BooleanCircuit (Outer.width mw SV (2 ^ ν)),
        decodeBooleanCircuit _ (value (Codec.prefixBits (fld1 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) =
          some c0 ∧
        decodeBooleanCircuit _ (value (Codec.prefixBits (fld2 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) =
          some c1 ∧
        c0.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree (Outer.width mw SV (2 ^ ν)) ∧
        c1.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree (Outer.width mw SV (2 ^ ν)) ∧
        Guard G0 ν z (⟨c0, c1⟩ : Outer.OuterGuess (Outer.width mw SV (2 ^ ν))) := by
  constructor
  · rintro ⟨B, hd, hs, hp, hg⟩
    obtain ⟨z0, d0⟩ := trunc_of_decodes degree _ _ B.src hd.1 hs
    obtain ⟨z1, d1⟩ := trunc_of_decodes degree _ _ B.pf hd.2 hp
    exact ⟨z0, z1, B.src, B.pf, d0, d1, hs, hp, hg⟩
  · rintro ⟨z0, z1, c0, c1, d0, d1, hs, hp, hg⟩
    rw [value_prefix_of_zero _ _ z0] at d0
    rw [value_prefix_of_zero _ _ z1] at d1
    exact ⟨⟨c0, c1⟩, ⟨d0, d1⟩, hs, hp, hg⟩

/-- Decoding is deterministic: the decoded pair is unique. -/
theorem decodes_unique {q : ℕ} (raw : List Bool) (B B' : Outer.OuterGuess q) (h : Worker.Decodes q raw B)
    (h' : Worker.Decodes q raw B') : B = B' := by
  obtain ⟨a1, a2⟩ := h
  obtain ⟨b1, b2⟩ := h'
  rw [a1] at b1; rw [a2] at b2
  cases B; cases B'
  simp only [Option.some.injEq] at b1 b2
  subst b1; subst b2; rfl

end Sem

section Prep
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

/-- The cost of `prepP`. -/
noncomputable def prepCost (n q K E : ℕ) (b1 b2 : List Bool) : ℕ :=
  (200 * (n + 1) + 18 * (4 * (n / 16) + 5) + 100) + 1 + (widthCost n q K + 1 + (boundCost E q + 1 +
    (fieldCost b1 (Lq E q) (16 * Lq E q + q + 4) q + 1 + fieldCost b2 (Lq E q) (16 * Lq E q + q + 4) q)))

/-- The register capacity of the cold prefix. -/
def capD (E n q c : ℕ) : ℕ := 3 * (Mq E q * Mq E q) + 10 * n + 4 * q + c + 200

theorem capD_facts (E n q c : ℕ) :
    8 * n + 100 ≤ capD E n q c ∧ 8 * n + 4 * q + 20 ≤ capD E n q c ∧
      3 * (Mq E q * Mq E q) + 100 ≤ capD E n q c ∧
      4 * Lq E q + 2 * (n / 16) + 2 * (16 * Lq E q + q + 4) + 4 * q + 100 ≤ capD E n q c ∧
      4 * n + 4 ≤ capD E n q c ∧ c ≤ capD E n q c := by
  have hM : Mq E q = 16 * Lq E q + q + 4 := rfl
  have h2 : 2 * Mq E q ≤ Mq E q * Mq E q := Nat.mul_le_mul_right _ (by omega)
  unfold capD
  refine ⟨by omega, by omega, by omega, ?_, by omega, by omega⟩
  have : 2 * (n / 16) ≤ 10 * n := by omega
  omega

theorem prep_exec (ν : ℕ) (z : BitInput (2 ^ ν)) (raw : List Bool) (h16 : 16 * raw.length ≤ 2 ^ ν) (cap c : ℕ)
    (hcap : capD (E0 degree) (2 ^ ν) (Outer.width mw SV (2 ^ ν)) c ≤ cap)
    (σ : WState (NSC mw SV F degree) nrW)
    (hX : σ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn z)) (hXh : σ.sh (cX _ _ _ _) = 0)
    (hRAW : σ.st (cRAW _ _ _ _) = RepairOrdinary.frame raw) (hRAWh : σ.sh (cRAW _ _ _ _) = 0)
    (hfr : ∀ i : Fin (NSC mw SV F degree + 1), 7 ≤ i.val → σ.st i = [] ∧ σ.sh i = 0)
    (hN : σ.val rN = 2 ^ ν)
    (hz : ∀ r ∈ [kQ, hH, hBr, rW, dS, oW, rOP, rT, rD, rQ, rQ1, rA, rL, rM, pX3, pH, pB, rK, rU, rLC, rK2, rZ 0,
      rZ 1], σ.val r = 0) :
    ∃ τ, WXExec cap (prepP mw SV F degree) σ τ (prepCost (2 ^ ν) (Outer.width mw SV (2 ^ ν))
        (OuterM.widthDonor mw SV).K (E0 degree) (fld1 raw) (fld2 raw)) ∧
      τ.val (rZ 0) = ((fld1 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true ∧
      τ.val (rZ 1) = ((fld2 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true ∧
      τ.st (fsC mw SV F degree 0 7 (by decide)) = [(decodeBooleanCircuit (Outer.width mw SV (2 ^ ν))
        (value (Codec.prefixBits (fld1 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))))).isSome] ∧
      τ.sh (fsC mw SV F degree 0 7 (by decide)) = 0 ∧
      τ.st (fsC mw SV F degree 1 7 (by decide)) = [(decodeBooleanCircuit (Outer.width mw SV (2 ^ ν))
        (value (Codec.prefixBits (fld2 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))))).isSome] ∧
      τ.sh (fsC mw SV F degree 1 7 (by decide)) = 0 ∧
      (∀ c0 : BooleanCircuit (Outer.width mw SV (2 ^ ν)), decodeBooleanCircuit _
        (value (Codec.prefixBits (fld1 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) = some c0 →
        τ.st (fsC mw SV F degree 0 6 (by decide)) = PCPPNative.descriptor c0) ∧
      τ.sh (fsC mw SV F degree 0 6 (by decide)) = 0 ∧
      (∀ c1 : BooleanCircuit (Outer.width mw SV (2 ^ ν)), decodeBooleanCircuit _
        (value (Codec.prefixBits (fld2 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) = some c1 →
        τ.st (fsC mw SV F degree 1 6 (by decide)) = PCPPNative.descriptor c1) ∧
      τ.sh (fsC mw SV F degree 1 6 (by decide)) = 0 ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val < 11 → i.val ≠ 2 → i.val ≠ 7 → i.val ≠ 8 → i.val ≠ 9 →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ (k : Fin 2) (i : ℕ) (h : i < 11), 8 ≤ i → τ.st (fsC mw SV F degree k i h) = [] ∧
        τ.sh (fsC mw SV F degree k i h) = 0) ∧
      (∀ i : Fin (NSC mw SV F degree + 1), bOC (progB mw SV).tapeCount (progU mw SV).tapeCount 0 ≤ i.val →
        τ.st i = [] ∧ τ.sh i = 0) ∧
      (∀ r ∈ [rOP, rT, rD], τ.val r = 0) := by
  classical
  set q := Outer.width mw SV (2 ^ ν) with hqd
  have hq : OuterM.qOf mw SV (2 ^ ν) = q := OuterM.qOf_two_pow mw SV ν
  obtain ⟨C1, C2, C3, C4, C5, C6⟩ := capD_facts (E0 degree) (2 ^ ν) q c
  set ℓ := Lq (E0 degree) q with hℓ
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zkQ, zH, zBr, zW, zS, zO, zOP, zT, zD, zQ, zQ1, zA, zL, zM, zX3, zpH, zpB, zK, zU, zLC, zK2, zZ0,
    zZ1⟩ := hz
  set tB := (progB mw SV).tapeCount with htB
  set tU := (progU mw SV).tapeCount with htU
  have hD0 : bDEC tB tU 0 = 33 + tB + tU := by simp [bDEC]
  have hD1 : bDEC tB tU 1 = 33 + tB + tU + 1381 := by simp [bDEC]
  have hO0 : bOC tB tU 0 = 33 + tB + tU + 2762 := by simp [bOC]
  have hwb : (wbOut mw SV F degree).val = 33 + (progB mw SV).outputTape.val := by
    have := (progB mw SV).outputFresh
    simp only [wbOut, mWB, if_neg this]; rfl
  have hwb' : (progB mw SV).outputTape.val < tB := (progB mw SV).outputTape.isLt
  -- W. the guess word
  obtain ⟨σ1, e1, w1, w1h, f1, v1, -⟩ := wtP_exec mw SV F degree (2 ^ ν) raw cap σ hRAW hRAWh
    (hfr _ (by simp <;> omega)).1 (hfr _ (by simp <;> omega)).2 hN (by simp [zkQ, zH, zBr, zW, zS, zO]) (by omega)
  have v1' : ∀ r, r ≠ kQ → σ1.val r = σ.val r := fun r hr => by rw [v1, Function.update_of_ne hr]
  have s1 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 7 → i.val ≠ 2 → σ1.st i = σ.st i ∧ σ1.sh i = σ.sh i :=
    fun i h7 h2 => f1 i (fun e => h7 (by rw [e]; rfl)) (fun e => h2 (by rw [e]; rfl))
  -- Wd. the width
  have hX1 := s1 (cX _ _ _ _) (by simp <;> omega) (by simp <;> omega)
  have hW1 := s1 (cXW1 _ _ _ _) (by simp <;> omega) (by simp <;> omega)
  have hW2 := s1 (cXW2 _ _ _ _) (by simp <;> omega) (by simp <;> omega)
  obtain ⟨σ2, e2, wb2, wb2h, q2, f2, v2, -⟩ := widthP_exec mw SV F degree z cap σ1
    (hX1.1.trans hX) (hX1.2.trans hXh)
    (hW1.1.trans (hfr _ (by simp <;> omega)).1) (hW1.2.trans (hfr _ (by simp <;> omega)).2)
    (hW2.1.trans (hfr _ (by simp <;> omega)).1) (hW2.2.trans (hfr _ (by simp <;> omega)).2)
    (fun i h1 h2 => by
      have := s1 i (by omega) (by omega); rw [this.1, this.2]; exact hfr i (by omega))
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [v1' _ (by decide)] <;> assumption)
    (by rw [hq]; omega)
  rw [hq] at e2 wb2 q2
  -- B. the code bound and the padding length
  have e3 := boundP_exec mw SV F degree q cap σ2 q2
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [v2 _ (by decide), v1' _ (by decide)] <;>
          assumption)
    (by omega)
  set σ3 := (((σ2.setv rQ1 (q + 1)).setv rA ((q + 1) ^ E0 degree + q + 5)).setv rL (Lq (E0 degree) q)).setv rM
    (Mq (E0 degree) q) with hσ3
  have v3 : ∀ r, r ≠ rQ1 → r ≠ rA → r ≠ rL → r ≠ rM → σ3.val r = σ2.val r := fun r h1 h2 h3 h4 => by
    rw [hσ3]; simp only [WState.setv_val]
    rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have v3L : σ3.val rL = ℓ := by
    rw [hσ3]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_self]
  have v3M : σ3.val rM = 16 * ℓ + q + 4 := by
    rw [hσ3]; simp only [WState.setv_val]; rw [Function.update_self]; rfl
  have v3Q : σ3.val rQ = q := by rw [v3 _ (by decide) (by decide) (by decide) (by decide)]; exact q2
  have v3z : ∀ r, r ≠ rQ1 → r ≠ rA → r ≠ rL → r ≠ rM → r ≠ rQ → r ≠ kQ → σ3.val r = σ.val r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [v3 r h1 h2 h3 h4, v2 r h5, v1' r h6]
  -- the fields of the guess word
  obtain ⟨R1, R2, hg1, hg2, hl1, hl2⟩ := fields_of_raw (2 ^ ν) raw h16
  have hl1' : (fld1 raw).length ≤ 2 ^ ν / 16 := hl1
  have hl2' : (fld2 raw).length ≤ 2 ^ ν / 16 := hl2
  have hWT3 : σ3.st (cWT _ _ _ _) = countWord (fld1 raw).length ++ (fld1 raw) ++ R1 := by
    show σ2.st _ = _
    rw [(f2 (cWT _ _ _ _) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)).1, w1, prefixBits_guess (2 ^ ν) raw h16, hg1]
  have hWT3h : σ3.sh (cWT _ _ _ _) = 0 := by
    show σ2.sh _ = _
    rw [(f2 (cWT _ _ _ _) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)).2, w1h]
  -- keep: σ3 agrees with σ off `RAW, WT, XW1, XW2` and the width blocks
  have k3 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 2 → i.val ≠ 7 → i.val ≠ 8 → i.val ≠ 9 →
      (i.val < 33 ∨ 33 + tB + tU ≤ i.val) → σ3.st i = σ.st i ∧ σ3.sh i = σ.sh i := by
    intro i h2 h7 h8 h9 hb
    have a := f2 i h8 h9 hb
    have b := s1 i h7 h2
    exact ⟨a.1.trans b.1, a.2.trans b.2⟩
  -- F0
  obtain ⟨σ4, e4, wt4, wt4h, z4, df4, df4h, dd4, dd4h, f4, v4, -⟩ := fieldP_exec mw SV F degree 0 [] (fld1 raw) R1 ℓ q
    cap σ3 (by rw [hWT3]; simp [List.append_assoc]) hWT3h
    (fun i h => by
      have := k3 (fsC mw SV F degree 0 i (by omega)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
      rw [this.1, this.2]; exact hfr _ (by simp <;> omega))
    (fun i h1 h2 => by
      rw [hD0] at h1 h2
      have := k3 i (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [this.1, this.2]; exact hfr _ (by omega))
    (by show σ2.st _ = _; exact wb2) (by show σ2.sh _ = _; exact wb2h)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [v3z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;> assumption)
    v3L v3M v3Q (by omega)
  -- F1
  have hc1 : (countWord (fld1 raw).length ++ fld1 raw).length = (fld1 raw).length + 1 + (fld1 raw).length := by
    simp [countWord]; omega
  have k4 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 7 → (i.val < 11 ∨ 19 ≤ i.val) →
      (i.val < 33 + tB + tU ∨ 33 + tB + tU + 1381 ≤ i.val) → σ4.st i = σ3.st i ∧ σ4.sh i = σ3.sh i := by
    intro i h7 h1 h2
    exact f4 i (fun e => h7 (by rw [e]; rfl)) (by simpa using h1) (by rw [hD0]; exact h2)
  obtain ⟨σ5, e5, wt5, wt5h, z5, df5, df5h, dd5, dd5h, f5, v5, -⟩ := fieldP_exec mw SV F degree 1
    (countWord (fld1 raw).length ++ fld1 raw) (fld2 raw) R2 ℓ q cap σ4
    (by rw [wt4, hWT3, hg2]; simp [List.append_assoc])
    (by rw [wt4h, hc1]; simp)
    (fun i h => by
      have a := k4 (fsC mw SV F degree 1 i (by omega)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
      have b := k3 (fsC mw SV F degree 1 i (by omega)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
      rw [a.1, a.2, b.1, b.2]; exact hfr _ (by simp <;> omega))
    (fun i h1 h2 => by
      rw [hD1] at h1 h2
      have a := k4 i (by omega) (by omega) (by omega)
      have b := k3 i (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [a.1, a.2, b.1, b.2]; exact hfr _ (by omega))
    (by
      have a := k4 (wbOut mw SV F degree) (by omega) (by omega) (by omega)
      rw [a.1]; show σ2.st _ = _; exact wb2)
    (by
      have a := k4 (wbOut mw SV F degree) (by omega) (by omega) (by omega)
      rw [a.2]; show σ2.sh _ = _; exact wb2h)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [v4 _ (by decide), v3z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
            assumption)
    (by rw [v4 _ (by decide)]; exact v3L) (by rw [v4 _ (by decide)]; exact v3M) (by rw [v4 _ (by decide)]; exact v3Q)
    (by omega)
  have k5 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 7 → (i.val < 22 ∨ 30 ≤ i.val) →
      (i.val < 33 + tB + tU + 1381 ∨ 33 + tB + tU + 2762 ≤ i.val) → σ5.st i = σ4.st i ∧ σ5.sh i = σ4.sh i := by
    intro i h7 h1 h2
    exact f5 i (fun e => h7 (by rw [e]; rfl)) (by simpa using h1) (by rw [hD1]; omega)
  have keep : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 2 → i.val ≠ 7 → i.val ≠ 8 → i.val ≠ 9 →
      (i.val < 11 ∨ (19 ≤ i.val ∧ i.val < 22) ∨ (30 ≤ i.val ∧ i.val < 33) ∨ 33 + tB + tU + 2762 ≤ i.val) →
      σ5.st i = σ.st i ∧ σ5.sh i = σ.sh i := by
    intro i h2 h7 h8 h9 hr
    have a := k5 i h7 (by omega) (by omega)
    have b := k4 i h7 (by omega) (by omega)
    have c := k3 i h2 h7 h8 h9 (by omega)
    exact ⟨a.1.trans (b.1.trans c.1), a.2.trans (b.2.trans c.2)⟩
  have v5z : ∀ r, r ≠ rZ 0 → r ≠ rZ 1 → r ≠ rQ1 → r ≠ rA → r ≠ rL → r ≠ rM → r ≠ rQ → r ≠ kQ →
      σ5.val r = σ.val r := fun r a b c d e f g h => by rw [v5 r b, v4 r a, v3z r c d e f g h]
  refine ⟨σ5, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))), ?_, z5, ?_, ?_, df5, df5h, ?_, ?_,
    dd5, dd5h, ?_, ?_, ?_, ?_⟩
  · rw [v5 _ (by decide)]; exact z4
  · have a := k5 (fsC mw SV F degree 0 7 (by decide)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
    rw [a.1]; exact df4
  · have a := k5 (fsC mw SV F degree 0 7 (by decide)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
    rw [a.2]; exact df4h
  · intro c0 hc0
    have a := k5 (fsC mw SV F degree 0 6 (by decide)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
    rw [a.1]; exact dd4 c0 hc0
  · have a := k5 (fsC mw SV F degree 0 6 (by decide)) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
    rw [a.2]; exact dd4h
  · intro i h11 h2 h7 h8 h9
    exact keep i h2 h7 h8 h9 (by omega)
  · intro k i h h8
    have hk := k.isLt
    have := keep (fsC mw SV F degree k i h) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
      (by simp <;> omega)
    rw [this.1, this.2]; exact hfr _ (by simp <;> omega)
  · intro i hi
    rw [hO0] at hi
    have := keep i (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [this.1, this.2]; exact hfr _ (by omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [v5z _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
        assumption

end Prep

section Bounds

open NearCubicWires.RepairSource.ProjectionNormalization in
/-- One circuit's cap step, uniformly over circuits of at most `S` gates. -/
noncomputable def capU (degree q S : ℕ) : ℕ :=
  2 * (80 * (q + 1) ^ 2 + 1 + 80 * (S + 1) ^ 2) + 4 * S + 4 * q + 29 +
    (DimensionPolynomial.budget (CloseoutWitness.OracleCap.degree degree) 1 q + 4 * S + 20)

open NearCubicWires.RepairSource.ProjectionNormalization in
theorem capOne_le (degree q s S : ℕ) (hs : s ≤ S) :
    PCPPNativeOracleCold.budget q s + 1 + CloseoutWitness.OracleCap.budget degree q s ≤ capU degree q S := by
  have h1 := PCPPQueryCost.natural_le q q le_rfl
  have h2 := PCPPQueryCost.natural_le s S hs
  have h3 := Nat.min_le_left (s + 1) (DimensionPolynomial.value (CloseoutWitness.OracleCap.degree degree) 1 q)
  unfold PCPPNativeOracleCold.budget PCPPNativeQueryHeader.budget CloseoutWitness.OracleCap.budget
    CloseoutWitness.OracleCap.Core.budget capU
  omega

/-- The front end's step, uniformly over circuits of at most `S` gates. -/
def frontU (K e n q S : ℕ) : ℕ := 100 * n + 100 + K * (n + 1) ^ 2 * (78 * (q + S + 5) ^ 2 + q + 1) ^ e

theorem front_le (K e n q S : ℕ) (c0 c1 : BooleanCircuit q) (h0 : c0.size ≤ S) (h1 : c1.size ≤ S) :
    (22 * n + 1 + 1 + 7 + 1 + (18 * (2 * n + 1) + 3 + 1 + (5 * (2 * n + 1) + 1 + 1 + (5 * (2 * n + 1) + 1)))) + 1 +
      (K * (n + 1) ^ 2 * ((PCPPNative.descriptor c0).length + (PCPPNative.descriptor c1).length + q + 1) ^ e + 1 + 2)
      ≤ frontU K e n q S := by
  have d0 := PCPPNative.descriptor_length_bound c0
  have d1 := PCPPNative.descriptor_length_bound c1
  have m0 : (q + c0.size + 5) ^ 2 ≤ (q + S + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have m1 : (q + c1.size + 5) ^ 2 ≤ (q + S + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hb : (PCPPNative.descriptor c0).length + (PCPPNative.descriptor c1).length + q + 1 ≤
      78 * (q + S + 5) ^ 2 + q + 1 := by omega
  have hk := Nat.mul_le_mul_left (K * (n + 1) ^ 2) (Nat.pow_le_pow_left hb e)
  unfold frontU
  omega

/-- The tail's uniform cost. -/
noncomputable def tailU (degree K e n q S : ℕ) : ℕ := 2 * capU degree q S + frontU K e n q S + 20

/-- A decoded field of `ℓ` bits has at most `16 ℓ` gates (proof 1's `decoded_size`). -/
theorem decoded_le {q : ℕ} (b : List Bool) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (c : BooleanCircuit q)
    (h : decodeBooleanCircuit q (value (Codec.prefixBits b ℓ)) = some c) : c.size ≤ 16 * ℓ :=
  CloseoutWitness.Oracle.decoded_size q (16 * ℓ) _ c (by omega) (by simp [Codec.prefixBits]) h

theorem one_le_Lq (E q : ℕ) : 1 ≤ Lq E q := by
  unfold Lq
  have : 1 ≤ ((q + 1) ^ E + q + 5) ^ 10 := Nat.one_le_pow _ _ (by omega)
  omega

end Bounds

section Tail
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

theorem wbit_single {ns nr : ℕ} (σ : WState ns nr) (i : Fin (ns + 1)) (b : Bool) (h : σ.st i = [b])
    (hh : σ.sh i = 0) : wbit σ i = b := by
  unfold wbit; rw [h, hh]; rfl

theorem tail_exec (ν : ℕ) (hν : 1 ≤ ν) (hon : F.onset ≤ ν) (z : BitInput (2 ^ ν)) (raw : List Bool) (cap : ℕ)
    (hcap : 4 * 2 ^ ν + 4 ≤ cap) (σ : WState (NSC mw SV F degree) nrW)
    (hX : σ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn z)) (hXh : σ.sh (cX _ _ _ _) = 0)
    (hXF : σ.st (cXF _ _ _ _) = []) (hXFh : σ.sh (cXF _ _ _ _) = 0)
    (hFL : σ.st (cFL _ _ _ _) = [false]) (hFLh : σ.sh (cFL _ _ _ _) = 0)
    (hZ0 : σ.val (rZ 0) = ((fld1 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true)
    (hZ1 : σ.val (rZ 1) = ((fld2 raw).drop (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))).count true)
    (hDF0 : σ.st (fsC mw SV F degree 0 7 (by decide)) = [(decodeBooleanCircuit (Outer.width mw SV (2 ^ ν))
        (value (Codec.prefixBits (fld1 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))))).isSome])
    (hDF0h : σ.sh (fsC mw SV F degree 0 7 (by decide)) = 0)
    (hDF1 : σ.st (fsC mw SV F degree 1 7 (by decide)) = [(decodeBooleanCircuit (Outer.width mw SV (2 ^ ν))
        (value (Codec.prefixBits (fld2 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))))).isSome])
    (hDF1h : σ.sh (fsC mw SV F degree 1 7 (by decide)) = 0)
    (hDD0 : ∀ c0 : BooleanCircuit (Outer.width mw SV (2 ^ ν)), decodeBooleanCircuit _
        (value (Codec.prefixBits (fld1 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) = some c0 →
        σ.st (fsC mw SV F degree 0 6 (by decide)) = PCPPNative.descriptor c0)
    (hDD0h : σ.sh (fsC mw SV F degree 0 6 (by decide)) = 0)
    (hDD1 : ∀ c1 : BooleanCircuit (Outer.width mw SV (2 ^ ν)), decodeBooleanCircuit _
        (value (Codec.prefixBits (fld2 raw) (Lq (E0 degree) (Outer.width mw SV (2 ^ ν))))) = some c1 →
        σ.st (fsC mw SV F degree 1 6 (by decide)) = PCPPNative.descriptor c1)
    (hDD1h : σ.sh (fsC mw SV F degree 1 6 (by decide)) = 0)
    (hfresh : ∀ (k : Fin 2) (i : ℕ) (h : i < 11), 8 ≤ i → σ.st (fsC mw SV F degree k i h) = [] ∧
      σ.sh (fsC mw SV F degree k i h) = 0)
    (hblk : ∀ i : Fin (NSC mw SV F degree + 1), bOC (progB mw SV).tapeCount (progU mw SV).tapeCount 0 ≤ i.val →
      σ.st i = [] ∧ σ.sh i = 0)
    (hz : ∀ r ∈ [rOP, rT, rD], σ.val r = 0) :
    ∃ τ, WXExec cap (tailP mw SV F degree) σ τ (tailU degree F.K F.e (2 ^ ν) (Outer.width mw SV (2 ^ ν))
        (16 * Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))) ∧
      (∃ b : Bool, τ.st (cFL _ _ _ _) = [b] ∧ (b = true ↔ PassCore mw SV degree ν z raw)) ∧
      (∀ B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν)), Worker.Decodes _ raw B → PassCore mw SV degree ν z raw →
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.field) =
          RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.sizeSlot) =
          List.replicate (Outer.Dat mw SV ν B).D.size true ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.aritySlot) =
          List.replicate (Outer.width mw SV (2 ^ ν)) true) ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val < 11 → i.val ≠ 4 → i.val ≠ 10 → τ.st i = σ.st i) := by
  classical
  set q := Outer.width mw SV (2 ^ ν) with hqd
  set ℓ := Lq (E0 degree) q with hℓd
  have hℓ1 : 1 ≤ ℓ := one_le_Lq _ _
  have hpi := pass_iff mw SV degree ν z raw
  rw [← hqd, ← hℓd] at hpi
  set tB := (progB mw SV).tapeCount with htB
  set tU := (progU mw SV).tapeCount with htU
  have hO0 : bOC tB tU 0 = 33 + tB + tU + 2762 := by simp [bOC]
  have hO1 : bOC tB tU 1 = 33 + tB + tU + 2802 := by simp [bOC]
  have hC0 : bCAP tB tU (tCap (Dc degree)) 0 = 33 + tB + tU + 2842 := by simp [bCAP]
  have hC1 : bCAP tB tU (tCap (Dc degree)) 1 = 33 + tB + tU + 2842 + tCap (Dc degree) := by simp [bCAP]
  have hF0 : bF tB tU (tCap (Dc degree)) = 33 + tB + tU + 2842 + 2 * tCap (Dc degree) := by simp [bF]
  have hT : tailU degree F.K F.e (2 ^ ν) q (16 * ℓ) =
      2 * capU degree q (16 * ℓ) + frontU F.K F.e (2 ^ ν) q (16 * ℓ) + 20 := rfl
  have hT' : tailU degree F.K F.e (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (16 * ℓ) =
      tailU degree F.K F.e (2 ^ ν) q (16 * ℓ) := rfl
  -- reject branches: `τ = σ`
  have rej : ∀ m, m ≤ 20 → ¬ PassCore mw SV degree ν z raw → WXExec cap (tailP mw SV F degree) σ σ m →
      ∃ τ, WXExec cap (tailP mw SV F degree) σ τ (tailU degree F.K F.e (2 ^ ν) q (16 * ℓ)) ∧
        (∃ b : Bool, τ.st (cFL _ _ _ _) = [b] ∧ (b = true ↔ PassCore mw SV degree ν z raw)) ∧
        (∀ B : Outer.OuterGuess q, Worker.Decodes _ raw B → PassCore mw SV degree ν z raw →
          τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.field) =
            RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
          τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.sizeSlot) =
            List.replicate (Outer.Dat mw SV ν B).D.size true ∧
          τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.aritySlot) = List.replicate q true) ∧
        (∀ i : Fin (NSC mw SV F degree + 1), i.val < 11 → i.val ≠ 4 → i.val ≠ 10 → τ.st i = σ.st i) := by
    intro m hm hP e
    refine ⟨σ, WXExec.mono e (by omega), ⟨false, hFL, ⟨fun h => absurd h (by decide), fun h => absurd h hP⟩⟩,
      fun B _ h => absurd h hP,
      fun _ _ _ _ => rfl⟩
  by_cases h0 : ((fld1 raw).drop ℓ).count true = 0
  swap
  · exact rej 1 (by omega) (fun h => h0 (hpi.1 h).1)
      (WXExec.ifrT (by rw [hZ0]; exact h0) (WXExec.skip cap σ))
  by_cases h1 : ((fld2 raw).drop ℓ).count true = 0
  swap
  · exact rej 2 (by omega) (fun h => h1 (hpi.1 h).2.1)
      (WXExec.ifrF (by rw [hZ0]; exact h0) (WXExec.ifrT (by rw [hZ1]; exact h1) (WXExec.skip cap σ)))
  cases hd0 : decodeBooleanCircuit q (value (Codec.prefixBits (fld1 raw) ℓ)) with
  | none =>
    refine rej 3 (by omega) (fun h => by obtain ⟨-, -, c0, -, d0, -⟩ := hpi.1 h; rw [hd0] at d0; cases d0)
      (WXExec.ifrF (by rw [hZ0]; exact h0) (WXExec.ifrF (by rw [hZ1]; exact h1)
        (WXExec.ifsF (by rw [wbit_single σ _ _ hDF0 hDF0h, hd0]; rfl) (WXExec.skip cap σ))))
  | some c0 =>
  cases hd1 : decodeBooleanCircuit q (value (Codec.prefixBits (fld2 raw) ℓ)) with
  | none =>
    refine rej 4 (by omega) (fun h => by obtain ⟨-, -, -, c1, -, d1, -⟩ := hpi.1 h; rw [hd1] at d1; cases d1)
      (WXExec.ifrF (by rw [hZ0]; exact h0) (WXExec.ifrF (by rw [hZ1]; exact h1)
        (WXExec.ifsT (by rw [wbit_single σ _ _ hDF0 hDF0h, hd0]; rfl)
          (WXExec.ifsF (by rw [wbit_single σ _ _ hDF1 hDF1h, hd1]; rfl) (WXExec.skip cap σ)))))
  | some c1 =>
  have hs0 := decoded_le _ ℓ hℓ1 c0 hd0
  have hs1 := decoded_le _ ℓ hℓ1 c1 hd1
  have hdec : Worker.Decodes q raw ⟨c0, c1⟩ :=
    ⟨by rw [← value_prefix_of_zero _ _ h0]; exact hd0, by rw [← value_prefix_of_zero _ _ h1]; exact hd1⟩
  have tZ0 : σ.val (rZ 0) = 0 := by rw [hZ0]; exact h0
  have tZ1 : σ.val (rZ 1) = 0 := by rw [hZ1]; exact h1
  have tD0 : wbit σ (fsC mw SV F degree 0 7 (by decide)) = true := by rw [wbit_single σ _ _ hDF0 hDF0h, hd0]; rfl
  have tD1 : wbit σ (fsC mw SV F degree 1 7 (by decide)) = true := by rw [wbit_single σ _ _ hDF1 hDF1h, hd1]; rfl
  -- the first cap
  obtain ⟨σ6, e6, cf6, cf6h, dd6, dd6h, f6, v6, -⟩ := capOne_exec mw SV F degree 0 c0 cap σ (hDD0 c0 hd0) hDD0h
    (fun i h h8 => hfresh 0 i h h8) (fun i h1 _ => hblk i h1)
    (fun i h1 _ => hblk i (by rw [hC0] at h1; rw [hO0]; omega))
  have k6 : ∀ i : Fin (NSC mw SV F degree + 1), (i.val < 17 ∨ 22 ≤ i.val) →
      (i.val < 33 + tB + tU + 2762 ∨ 33 + tB + tU + 2802 ≤ i.val) →
      (i.val < 33 + tB + tU + 2842 ∨ 33 + tB + tU + 2842 + tCap (Dc degree) ≤ i.val) →
      σ6.st i = σ.st i ∧ σ6.sh i = σ.sh i := fun i a b c =>
    f6 i (by simpa using a) (by rw [hO0]; omega) (by rw [hC0]; omega)
  have hc0 := capOne_le degree q c0.size (16 * ℓ) hs0
  by_cases hz0 : c0.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q
  swap
  · have tC0 : wbit σ6 (fsC mw SV F degree 0 10 (by decide)) = false := by
      rw [wbit_single σ6 _ _ cf6 cf6h, decide_eq_false hz0]
    have hnP : ¬ PassCore mw SV degree ν z raw := fun h => by
      obtain ⟨-, -, c0', -, d0', -, hs', -⟩ := hpi.1 h
      rw [hd0] at d0'; cases d0'; exact hz0 hs'
    have hFL6 := k6 (cFL _ _ _ _) (by simp) (by simp <;> omega) (by simp <;> omega)
    refine ⟨σ6, WXExec.mono (WXExec.ifrF tZ0 (WXExec.ifrF tZ1 (WXExec.ifsT tD0 (WXExec.ifsT tD1
      (WXExec.seq e6 (WXExec.ifsF tC0 (WXExec.skip cap σ6))))))) (by omega),
      ⟨false, by rw [hFL6.1, hFL], ⟨fun h => absurd h (by decide), fun h => absurd h hnP⟩⟩,
      fun B _ h => absurd h hnP, fun i hi _ _ => (k6 i (by omega) (by omega) (by omega)).1⟩
  have tC0 : wbit σ6 (fsC mw SV F degree 0 10 (by decide)) = true := by
    rw [wbit_single σ6 _ _ cf6 cf6h, decide_eq_true hz0]
  -- the second cap
  have hDD1' := k6 (fsC mw SV F degree 1 6 (by decide)) (by simp) (by simp <;> omega) (by simp <;> omega)
  obtain ⟨σ7, e7, cf7, cf7h, dd7, dd7h, f7, v7, -⟩ := capOne_exec mw SV F degree 1 c1 cap σ6
    (by rw [hDD1'.1]; exact hDD1 c1 hd1) (by rw [hDD1'.2]; exact hDD1h)
    (fun i h h8 => by
      have := k6 (fsC mw SV F degree 1 i h) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
      rw [this.1, this.2]; exact hfresh 1 i h h8)
    (fun i h1 h2 => by
      rw [hO1] at h1 h2
      have := k6 i (by omega) (by omega) (by omega)
      rw [this.1, this.2]; exact hblk i (by rw [hO0]; omega))
    (fun i h1 h2 => by
      rw [hC1] at h1 h2
      have := k6 i (by omega) (by omega) (by omega)
      rw [this.1, this.2]; exact hblk i (by rw [hO0]; omega))
  have k7 : ∀ i : Fin (NSC mw SV F degree + 1), (i.val < 28 ∨ 33 ≤ i.val) →
      (i.val < 33 + tB + tU + 2802 ∨ 33 + tB + tU + 2842 ≤ i.val) →
      (i.val < 33 + tB + tU + 2842 + tCap (Dc degree) ∨ 33 + tB + tU + 2842 + 2 * tCap (Dc degree) ≤ i.val) →
      σ7.st i = σ6.st i ∧ σ7.sh i = σ6.sh i := fun i a b c =>
    f7 i (by simp <;> omega) (by rw [hO1]; omega) (by rw [hC1]; omega)
  have hc1 := capOne_le degree q c1.size (16 * ℓ) hs1
  by_cases hz1 : c1.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q
  swap
  · have tC1 : wbit σ7 (fsC mw SV F degree 1 10 (by decide)) = false := by
      rw [wbit_single σ7 _ _ cf7 cf7h, decide_eq_false hz1]
    have hnP : ¬ PassCore mw SV degree ν z raw := fun h => by
      obtain ⟨-, -, -, c1', -, d1', -, hs', -⟩ := hpi.1 h
      rw [hd1] at d1'; cases d1'; exact hz1 hs'
    have hFL7 := k7 (cFL _ _ _ _) (by simp) (by simp <;> omega) (by simp <;> omega)
    have hFL6 := k6 (cFL _ _ _ _) (by simp) (by simp <;> omega) (by simp <;> omega)
    refine ⟨σ7, WXExec.mono (WXExec.ifrF tZ0 (WXExec.ifrF tZ1 (WXExec.ifsT tD0 (WXExec.ifsT tD1
      (WXExec.seq e6 (WXExec.ifsT tC0 (WXExec.seq e7 (WXExec.ifsF tC1 (WXExec.skip cap σ7))))))))) (by omega),
      ⟨false, by rw [hFL7.1, hFL6.1, hFL], ⟨fun h => absurd h (by decide), fun h => absurd h hnP⟩⟩,
      fun B _ h => absurd h hnP, fun i hi _ _ => ((k7 i (by omega) (by omega) (by omega)).1.trans
        (k6 i (by omega) (by omega) (by omega)).1)⟩
  have tC1 : wbit σ7 (fsC mw SV F degree 1 10 (by decide)) = true := by
    rw [wbit_single σ7 _ _ cf7 cf7h, decide_eq_true hz1]
  -- the front end
  have kk : ∀ i : Fin (NSC mw SV F degree + 1), i.val < 17 → σ7.st i = σ.st i ∧ σ7.sh i = σ.sh i := fun i hi =>
    ⟨(k7 i (by omega) (by omega) (by omega)).1.trans (k6 i (by omega) (by omega) (by omega)).1,
     (k7 i (by omega) (by omega) (by omega)).2.trans (k6 i (by omega) (by omega) (by omega)).2⟩
  have hD0' := k7 (fsC mw SV F degree 0 6 (by decide)) (by simp) (by simp <;> omega) (by simp <;> omega)
  obtain ⟨σ8, e8, fl8, facts8, -, f8, -, -, -⟩ := frontPart_exec mw SV F degree ν hν hon z ⟨c0, c1⟩ cap σ7
    (by rw [(kk _ (by simp)).1]; exact hX) (by rw [(kk _ (by simp)).2]; exact hXh)
    (by rw [(kk _ (by simp)).1]; exact hXF) (by rw [(kk _ (by simp)).2]; exact hXFh)
    (by rw [hD0'.1]; exact dd6) (by rw [hD0'.2]; exact dd6h) dd7 dd7h
    (by rw [(kk _ (by simp)).1]; exact hFL) (by rw [(kk _ (by simp)).2]; exact hFLh)
    (fun i hi => by
      rw [hF0] at hi
      have a := k7 i (by omega) (by omega) (by omega)
      have b := k6 i (by omega) (by omega) (by omega)
      rw [a.1, a.2, b.1, b.2]; exact hblk i (by rw [hO0]; omega))
    (by intro r hr; rw [v7, v6]; exact hz r hr) hcap
  dsimp only at e8
  have hiff : Guard G0 ν z (⟨c0, c1⟩ : Outer.OuterGuess q) ↔ PassCore mw SV degree ν z raw := by
    constructor
    · intro hg; exact hpi.2 ⟨h0, h1, c0, c1, hd0, hd1, hz0, hz1, hg⟩
    · intro h
      obtain ⟨-, -, c0', c1', d0', d1', -, -, hg⟩ := hpi.1 h
      rw [hd0] at d0'; rw [hd1] at d1'; cases d0'; cases d1'; exact hg
  have hf := front_le F.K F.e (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (16 * ℓ) c0 c1 hs0 hs1
  have hFU : frontU F.K F.e (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (16 * ℓ) = frontU F.K F.e (2 ^ ν) q (16 * ℓ) := rfl
  refine ⟨σ8, WXExec.mono (WXExec.ifrF tZ0 (WXExec.ifrF tZ1 (WXExec.ifsT tD0 (WXExec.ifsT tD1
      (WXExec.seq e6 (WXExec.ifsT tC0 (WXExec.seq e7 (WXExec.ifsT tC1 e8)))))))) (by omega),
    ⟨_, fl8, by rw [decide_eq_true_iff]; exact hiff⟩, ?_, ?_⟩
  · intro B hB hP
    have e := decodes_unique raw B ⟨c0, c1⟩ hB hdec
    subst e
    exact facts8 (hiff.2 hP)
  · intro i hi h4 h10
    rw [(f8 i h4 h10 (by omega) (by omega) (by rw [hF0]; omega)).1]
    exact (kk i (by omega)).1

end Tail

section DeepAll
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

/-- **The deep part** (`prepP; tailP`) at `N = 2^ν`: the flag is `PassCore`, and on a pass `F`'s outputs are the
request fields of `H_B` at the decoded pair. -/
theorem deep_exec (ν : ℕ) (hν : 1 ≤ ν) (hon : F.onset ≤ ν) (z : BitInput (2 ^ ν)) (raw : List Bool)
    (h16 : 16 * raw.length ≤ 2 ^ ν) (cap c : ℕ)
    (hcap : capD (E0 degree) (2 ^ ν) (Outer.width mw SV (2 ^ ν)) c ≤ cap)
    (σ : WState (NSC mw SV F degree) nrW)
    (hX : σ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn z)) (hXh : σ.sh (cX _ _ _ _) = 0)
    (hRAW : σ.st (cRAW _ _ _ _) = RepairOrdinary.frame raw) (hRAWh : σ.sh (cRAW _ _ _ _) = 0)
    (hFL : σ.st (cFL _ _ _ _) = [false]) (hFLh : σ.sh (cFL _ _ _ _) = 0)
    (hfr : ∀ i : Fin (NSC mw SV F degree + 1), 7 ≤ i.val → σ.st i = [] ∧ σ.sh i = 0)
    (hN : σ.val rN = 2 ^ ν)
    (hz : ∀ r ∈ [kQ, hH, hBr, rW, dS, oW, rOP, rT, rD, rQ, rQ1, rA, rL, rM, pX3, pH, pB, rK, rU, rLC, rK2, rZ 0,
      rZ 1], σ.val r = 0) :
    ∃ τ, WXExec cap (deepP mw SV F degree) σ τ (prepCost (2 ^ ν) (Outer.width mw SV (2 ^ ν))
        (OuterM.widthDonor mw SV).K (E0 degree) (fld1 raw) (fld2 raw) + 1 +
        tailU degree F.K F.e (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (16 * Lq (E0 degree) (Outer.width mw SV (2 ^ ν)))) ∧
      (∃ b : Bool, τ.st (cFL _ _ _ _) = [b] ∧ (b = true ↔ PassCore mw SV degree ν z raw)) ∧
      (∀ B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν)), Worker.Decodes _ raw B → PassCore mw SV degree ν z raw →
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.field) =
          RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.sizeSlot) =
          List.replicate (Outer.Dat mw SV ν B).D.size true ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.aritySlot) =
          List.replicate (Outer.width mw SV (2 ^ ν)) true) ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val < 11 → i.val ≠ 2 → i.val ≠ 4 → i.val ≠ 7 → i.val ≠ 8 →
        i.val ≠ 9 → i.val ≠ 10 → τ.st i = σ.st i) := by
  obtain ⟨σ1, e1, z0, z1, df0, df0h, df1, df1h, dd0, dd0h, dd1, dd1h, kp, fr, bl, rz⟩ :=
    prep_exec mw SV F degree ν z raw h16 cap c hcap σ hX hXh hRAW hRAWh hfr hN hz
  obtain ⟨_, _, C3, _, C5, _⟩ := capD_facts (E0 degree) (2 ^ ν) (Outer.width mw SV (2 ^ ν)) c
  have kX := kp (cX _ _ _ _) (by simp) (by simp) (by simp) (by simp) (by simp)
  have kXF := kp (cXF _ _ _ _) (by simp) (by simp) (by simp) (by simp) (by simp)
  have kFL := kp (cFL _ _ _ _) (by simp) (by simp) (by simp) (by simp) (by simp)
  have fXF := hfr (cXF _ _ _ _) (by simp)
  obtain ⟨σ2, e2, fl2, facts2, k2⟩ := tail_exec mw SV F degree ν hν hon z raw cap (by omega) σ1
    (kX.1.trans hX) (kX.2.trans hXh) (kXF.1.trans fXF.1) (kXF.2.trans fXF.2) (kFL.1.trans hFL) (kFL.2.trans hFLh)
    z0 z1 df0 df0h df1 df1h dd0 dd0h dd1 dd1h fr bl rz
  exact ⟨σ2, WXExec.seq e1 e2, fl2, facts2, fun i a b c d e f g =>
    (k2 i a c g).trans (kp i a b d e f).1⟩

end DeepAll

end W3.NearCubicWires.RepairSource.Outer3.Front
