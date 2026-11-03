import Proof.Wire_3_5.Stage35.ExecCostSpec
import Proof.Wire_3_5.Stage35.Kit
import Proof.Wire_3_5.Stage35.Lang

/-!
# The Case-2 kit with the growing XOR schedule

Paper v2, §H.6 stage 2 ("In the yes case (Case 2, Hard proof table), prefix self-reduction recovers `Γ*_pf`. Each
honest proof bit is then computed by the deterministic PCPP algorithm") and §H.5 Case 2 (`f^{⊕t(q)}`): the Case-2
producer of the after-prefix program (`Stage35.CaseTwoKit`), at the copy schedule `t(q)+1` and the selector `a(n)`
this proof's scan computes. The machine is the Case-2 execution `Stage35.Exec.htwo` at the near-cubic-wires Case-2
source block `blockV h2 a` (H2′ on the word of `C_{⟨B*_src⟩_ν}` and the descriptor of `B*_pf`, the request at
`H_{B*}`): on the five port words it recomputes `a(n)` and `t(q(2^{a(n)}))` from the address, and its output is the
slice's Case-2 bit `coreC … ν z (t(q)+1) … n point` (`coreC_hardTable`), since `ν = a(n)` and `t(q) ≤ n + 1` past an
onset.

Inputs: the clause bound at `d_G` (`hcl`, paper (58)), and the execution's cost class (`ExecCost.FoldNeedCap`,
`ExecCost.HtwoCostPoly`).
-/

set_option autoImplicit false

namespace Stage35.KitMain
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth coreWidth paddedUnsigned)
open NearCubicWires.RecoveryPipeline (padCore)
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open W3.NearCubicWires.RepairSource.Outer3 W3.NearCubicWires.RepairSource.Outer3.Case2
open Stage35.Fold Stage35.Exec
open _root_.NearCubicGates.Close

section Sched
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The schedule counter is `t(q)`** once `t(q) ≤ c + 1`. -/
theorem candT_sched (k A a c : ℕ) (hc : sched ζ h0 h1 (Lq (widthAt k A a)) ≤ c + 1) :
    candT k A (zu ζ) (zv ζ) a ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) c = sched ζ h0 h1 (Lq (widthAt k A a)) := by
  unfold candT
  have e1 : candA0 k A (zu ζ) (zv ζ) a = schedA ζ (Lq (widthAt k A a)) 0 := by
    unfold candA0 candL0 schedA; ring
  have e2 : candB0 (zv ζ) = schedB ζ 0 := by unfold candB0 schedB; ring
  rw [e1, e2, roundCount_sched h0 h1 _ c hc]

end Sched

/-- The execution's input bank is the recovery's Case-2 port bank. -/
theorem htwoIn_port {a : PointwisePCPPAlgorithm} (S : SBlock a) (D : ℕ) (w description address : List Bool)
    (R B : ℕ) : htwoIn S D w description address R B = Recovery.portInput (G S D) w description address R B := by
  funext j
  obtain ⟨v, hv⟩ := j
  unfold htwoIn Recovery.portInput
  by_cases h5 : v < 5
  · rw [dif_pos (show v < 135 by omega), dif_pos h5]
    interval_cases v <;> rfl
  · rw [dif_neg h5]
    by_cases h135 : v < 135
    · rw [dif_pos h135]
      unfold Cold.input
      rw [if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega),
        if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega),
        if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega),
        if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega),
        if_neg (by intro e; have := congrArg Fin.val e; simp at this; omega)]
    · rw [dif_neg h135]

theorem pad_congr (a : PointwisePCPPAlgorithm) {r₁ r₂ : PCPPRequest a.minimumArity} (e : r₁ = r₂) {cb c₁ c₂ target : ℕ}
    (ec : c₁ = c₂) (h₁ : (a.output r₁).clauseBits ≤ cb) (h₂ : (a.output r₂).clauseBits ≤ cb)
    (t₁ : c₁ * (r₁.arity + cb + 1) ≤ target) (t₂ : c₂ * (r₂.arity + cb + 1) ≤ target) :
    padCore (xorPower (paddedUnsigned (a.output r₁) h₁) c₁) t₁ =
      padCore (xorPower (paddedUnsigned (a.output r₂) h₂) c₂) t₂ := by
  subst e; subst ec; rfl

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) {c d : ℕ}
  (amplifier : OrdinaryScheduleAmplifier c d) (D : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The selector: this proof's scan index `a(n) = prefixS … n`. -/
noncomputable def selOf (n : ℕ) : ℕ := CertPrefix.prefixS k (Outer.apad mw SV) (zu ζ) (zv ζ) D n

/-- **The Case-2 kit** at the copy schedule `t(q)+1` and the selector `a(n)`, from the clause bound at `d_G` and the
execution's cost class. -/
theorem kit_of (hD : 1 ≤ D)
    (hcl : ∃ q₀ : ℕ, ∀ (ν N : ℕ) (B : Outer.OuterGuess (Outer.width mw SV N)), 1 ≤ ν → ν ≤ Outer.width mw SV N →
      q₀ ≤ Outer.width mw SV N → B.pf.size ≤ oracleSizeBound d (Outer.width mw SV N) →
      (a.output (requestAt mw SV a ν B)).clauseBits ≤ clauseWidth D (Outer.width mw SV N))
    (hN : ExecCost.FoldNeedCap mw SV a d D)
    (hC : ∀ e1 e2 e3 e4, ExecCost.HtwoCostPoly mw SV a d D k (Outer.apad mw SV) (zu ζ) (zv ζ) e1 e2 e3 e4) :
    Nonempty (CaseTwoKit mw SV a amplifier (copies h0 h1) D (selOf mw SV D (ζ := ζ))) := by
  classical
  set A := Outer.apad mw SV with hA
  obtain ⟨e1, e2, e3, hcaps⟩ := prefix_caps k A (zu ζ) (zv ζ) D (two_u_lt_v h0 h1)
  obtain ⟨e4, hneed⟩ := hN
  obtain ⟨C, E, hcost⟩ := hC e1 e2 e3 e4
  obtain ⟨q₀, hq₀⟩ := hcl
  obtain ⟨n₁, hn₁⟩ := eventually_sched_le h0 h1 k A
  let S := blockV h2 a
  refine ⟨{
    t := G S D
    st := _
    M := htwo S k D A (zu ζ) (zv ζ) e1 e2 e3 e4
    output := outSlot S D 1
    large := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D
      have e : (outSlot S D 1).val = b6 S D + 2 + 1 := rfl
      omega
    cutoff := 2 ^ (SV.onset + 1 + n₁ + q₀ + a.minimumArity)
    C := C
    E := E
    run := ?_ }⟩
  intro n point ν z hνn hcut hsel hfit h
  have hν : SV.onset + 1 + n₁ + q₀ + a.minimumArity ≤ ν := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcut
  have hνw := nu_lt_width mw SV ν
  have hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν) := by omega
  let x : KI mw SV a d := ⟨ν, z, h, hq, by omega, by omega⟩
  have hcl' := hq₀ ν (2 ^ ν) x.B (by omega) hνw.le (by omega) (pf_le_cap x)
  have hreq : S.req x.i = requestAt mw SV a ν x.B := kitInst_req mw SV a d ν z h hq
  have hcb : (a.output (S.req x.i)).clauseBits ≤ capOf S D x.i := by
    show _ ≤ clauseWidth D x.q
    rw [hreq]; exact hcl'
  have hS : CertPrefix.prefixS k A (zu ζ) (zv ζ) D n = ν := hsel.symm
  have hqS : x.q = widthAt k A (CertPrefix.prefixS k A (zu ζ) (zv ζ) D n) := by
    rw [hS, widthAt_eq]; rfl
  have hsch := hn₁ n (by omega) ν hνn
  have hcand : candT k A (zu ζ) (zv ζ) (CertPrefix.prefixS k A (zu ζ) (zv ζ) D n) ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) n + 1
      = copies h0 h1 x.q := by
    rw [hS, candT_sched h0 h1 k A ν n hsch]
    show sched ζ h0 h1 (Lq (widthAt k A ν)) + 1 = rowBt h0 h1 x.q + 1
    rw [widthAt_eq]; rfl
  have hfitE : (candT k A (zu ζ) (zv ζ) (CertPrefix.prefixS k A (zu ζ) (zv ζ) D n) ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) n
      + 1) * widthOf S D x.i ≤ n := by
    rw [hcand]
    have : coreWidth (copies h0 h1 x.q) D x.q ≤ n / 2 := hfit
    unfold coreWidth at this
    show copies h0 h1 x.q * (x.q + clauseWidth D x.q + 1) ≤ n
    omega
  have htotal := hneed x point _ hcb hfitE hνn
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcaps n
  obtain ⟨out, hrun, hout⟩ := htwo_run S k D x.i A (zu ζ) (zv ζ) e1 e2 e3 e4 hD x.B.pf (pf_le_cap x) rfl point rfl
    hqS hcb hfitE htotal c1 c2 c3 c4 c5 c6
  have hc := hcost x point hcb hqS hfitE hνn c6
  refine ⟨out, ?_, ?_⟩
  · rw [← htwoIn_port]
    exact ClockJoin.enlarge _ _ _ _ _ hrun hc
  · have ht : copies h0 h1 x.q * ((requestAt mw SV a ν x.B).arity + clauseWidth D x.q + 1) ≤ n := by
      rw [← hreq]
      have : coreWidth (copies h0 h1 x.q) D x.q ≤ n / 2 := hfit
      unfold coreWidth at this
      show copies h0 h1 x.q * (x.q + clauseWidth D x.q + 1) ≤ n
      omega
    rw [hout]
    show _ = RepairOrdinary.frame (coreC mw SV a amplifier ν z (copies h0 h1 x.q) (clauseWidth D x.q) n point).toNat.bits
    rw [coreC_hardTable mw SV a amplifier ν z (copies h0 h1 x.q) (clauseWidth D x.q) n h hcl' ht]
    rw [pad_congr a hreq hcand hcb hcl' hfitE ht]
    rfl

end Stage35.KitMain
