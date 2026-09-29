import Proof.Wire_3_5.Recovery.CaseTwoPadBlock

/-! # One whole padded block: source and occurrence (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes one copy's honest proof bit of the padded Case 2 ("each honest proof bit is computed by the deterministic
PCPP algorithm", P3:3762-3763), restating base's `CloseoutCaseTwo.WholeBlock` on the padded source block
(`Proof.Wire_3_5.Recovery.CaseTwoPadBlock`): base's `Occurrence` machine, generic in the request, reads the padded request's
clause cache, its framed input and the retained address, and writes the unsigned honest assignment bit of the padded
request at the addressed block; a paid rewind (`wresetMachine`) restores all heads.

Paper quantity: one honest proof bit of the padded request; **`wmachine`** / **`wblock_run`** and
**`wresetMachine`** / **`wreset_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## The padded source block's interface -/

def scommonSlots (k : ℕ) (j : Fin (SourceCache.tapes a)) := ssourceSlots source a k
  (oslots source a k (RequestSource.cacheSlots a j))
theorem scommon_injective (k : ℕ) : Function.Injective (scommonSlots source a k) := by
  exact (ssource_injective source a k).comp
    ((NativeSourceDock.slots_injective a (pframeSlot source k) (psizeSlot source k) (parity source k)
      (slots_distinct source k).1 (slots_distinct source k).2.1 (slots_distinct source k).2.2).comp
      (RequestSource.cache_injective a))
theorem scache_injective (k : ℕ) : Function.Injective (scacheSlots source a k) := by
  intro i j he
  have hc := scommon_injective source a k he
  have hb := SourceCache.cold_injective a hc
  have hi := PCPPQueryCold.bank_injective (SourceCache.degree a) hb
  exact Fin.ext (congrArg (fun x : Fin 21 => x.val) hi)
theorem scache_request (k : ℕ) (j : Fin 19) : scacheSlots source a k j ≠ srequestSlot source a k := by
  intro he
  exact SourceCache.cold_away a _ (scommon_injective source a k he)
theorem scache_away (k : ℕ) (i : Fin 3) (j : Fin 19) :
    scacheSlots source a k j ≠ sold source a k (i.castAdd 6) :=
  ssource_away source a k i _
theorem srequest_away (k : ℕ) (i : Fin 3) : srequestSlot source a k ≠ sold source a k (i.castAdd 6) :=
  ssource_away source a k i _

/-! ## The whole block's layout -/

def wtapes (k D : ℕ) := stapes source a k + Occurrence.tapes D a
def wold (k D : ℕ) (j : Fin (stapes source a k)) : Fin (wtapes source a k D) := j.castAdd (Occurrence.tapes D a)
def wport (k : ℕ) : Fin 21 → Fin (stapes source a k) :=
  Fin.append (scacheSlots source a k) ![srequestSlot source a k, sold source a k 2]
theorem wport_injective (k : ℕ) : Function.Injective (wport source a k) := by
  apply Fin.append_injective_iff.mpr
  refine ⟨scache_injective source a k, ?_, ?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    · exact ((srequest_away source a k 2) he).elim
    · exact ((srequest_away source a k 2) he.symm).elim
  · intro i j
    fin_cases j
    · exact scache_request source a k i
    · exact scache_away source a k 2 i
def wslots (k D : ℕ) (j : Fin (Occurrence.tapes D a)) : Fin (wtapes source a k D) :=
  if WholeBlock.shared j then wold source a k D (wport source a k (WholeBlock.key j))
  else j.natAdd (stapes source a k)
theorem wold_injective (k D : ℕ) : Function.Injective (wold source a k D) := by
  intro i j he; apply Fin.ext; exact congrArg (fun x : Fin (wtapes source a k D) => x.val) he
theorem wslots_injective (k D : ℕ) : Function.Injective (wslots source a k D) := by
  intro i j he
  by_cases hi : WholeBlock.shared i <;> by_cases hj : WholeBlock.shared j
  · exact WholeBlock.key_injective i j hi hj (wport_injective source a k
      (wold_injective source a k D (by simpa only [wslots, if_pos hi, if_pos hj] using he)))
  · have hv := congrArg Fin.val he
    have bound := (wport source a k (WholeBlock.key i)).isLt
    simp only [wslots, if_pos hi, if_neg hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · have hv := congrArg Fin.val he
    have bound := (wport source a k (WholeBlock.key j)).isLt
    simp only [wslots, if_neg hi, if_pos hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [wslots, if_neg hi, if_neg hj, Fin.val_natAdd] at hv
    omega
def wfirst (k D CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (wold source a k D) (smachine source a k CH Cpad code)
def wlast (k D block : ℕ) := RecoveryFocus.machine (wslots source a k D) (Occurrence.machine D block a)
/-- **The whole padded block.** -/
def wmachine (k D block CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (wfirst source a k D CH Cpad code) (wlast source a k D block)
def winput (k D : ℕ) (hierarchy descriptor address : List Bool) (q : ℕ) : Fin (wtapes source a k D) → List Bool :=
  Fin.addCases (sinput source a k hierarchy descriptor address q) (fun _ => [])
def woutputSlot (k D : ℕ) := wslots source a k D (Occurrence.outputSlot D a)

theorem wport_away (k : ℕ) (i : Fin 2) (j : Fin 21) : wport source a k j ≠ sold source a k (i.castAdd 7) := by
  refine Fin.addCases (motive := fun j => wport source a k j ≠ sold source a k (i.castAdd 7))
    (fun j : Fin 19 => ?_) (fun j : Fin 2 => ?_) j
  · rw [wport, Fin.append_left]
    exact scache_away source a k (i.castAdd 1) j
  · fin_cases j
    · exact srequest_away source a k (i.castAdd 1)
    · intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change 2 = i.val at hv
      omega
theorem wslots_away (k D : ℕ) (i : Fin 2) :
    ∀ j, wslots source a k D j ≠ wold source a k D (sold source a k (i.castAdd 7)) := by
  intro j he
  by_cases hj : WholeBlock.shared j
  · exact wport_away source a k i (WholeBlock.key j)
      (wold_injective source a k D (by simpa only [wslots, if_pos hj] using he))
  · have hv := congrArg Fin.val he
    have bound := (sold source a k (i.castAdd 7)).isLt
    simp only [wslots, if_neg hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
theorem waddress_slot (k D : ℕ) :
    wslots source a k D (Occurrence.old D a (OccurrenceAddress.base D 57)) =
      wold source a k D (sold source a k 2) := rfl
theorem wcache_slot (k D : ℕ) (j : Fin 19) :
    wslots source a k D (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) =
      wold source a k D (scacheSlots source a k j) := by
  have hshared : WholeBlock.shared (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) := Or.inl j.isLt
  rw [wslots, if_pos hshared]
  have hk : WholeBlock.key (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) = j.castAdd 2 := by
    apply Fin.ext
    rw [WholeBlock.key_value]
    change (if j.val < 19 then j.val else if j.val = 56 then 19 else 20) = j.val
    rw [if_pos j.isLt]
  rw [hk]
  exact congrArg (wold source a k D) (Fin.append_left _ _ j)
theorem wrequest_slot (k D : ℕ) :
    wslots source a k D (Occurrence.old D a (OccurrenceAddress.base D 56)) =
      wold source a k D (srequestSlot source a k) := rfl

private theorem wcache_heads (i : Fin 19) :
    PCPPQueryClauseReuse.heads i = if i.val = 13 ∨ i.val = 14 then 1 else 0 := by
  fin_cases i <;> rfl
private theorem wcache_entry_heads (D : ℕ) (a : PointwisePCPPAlgorithm) (i : Fin 19) :
    Occurrence.heads D a (Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39))) =
      PCPPQueryClauseReuse.heads i := by
  simp only [Occurrence.heads, Occurrence.old, Fin.addCases_left, OccurrenceAddress.heads,
    OccurrenceAddress.base, Fin.val_castAdd]
  exact (wcache_heads i).symm

/-- The padded request of the block. -/
def wrequest {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :=
  PCPPRequestBoundary.request a (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) r.2 hpad oracle))

def wbudget {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (D block : ℕ) (u : BitInput (wrequest source a H Cpad hpad r oracle q hq).arity)
    (clause : BitInput (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (position : Bool) (padding : ℕ) :=
  sbudget source a H Cpad hpad r oracle q hq + 1 +
    Occurrence.budget D block a (wrequest source a H Cpad hpad r oracle q hq) u clause position padding

/-- **The whole padded block is ready**: the honest assignment bit of the padded request's PCPP output at the
addressed block; the three retained frames are kept. -/
theorem wblock_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (D block : ℕ) (hD : 1 ≤ D)
    (u : BitInput (wrequest source a H Cpad hpad r oracle q hq).arity)
    (clause : BitInput (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits + pad.length =
      CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity)
    (hpre : pre.length = block * ((wrequest source a H Cpad hpad r oracle q hq).arity +
      CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity + 1)) :
    let address := pre ++ AddressFields.word u clause pad position ++ tail
    let req := wrequest source a H Cpad hpad r oracle q hq
    ∃ out, run (wmachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (wbudget source a H Cpad hpad r oracle q hq D block u clause position pad.length)
      (winput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address q) =
        some out ∧
      out.steps ≤ wbudget source a H Cpad hpad r oracle q hq D block u clause position pad.length ∧
      out.final.tapes (woutputSlot source a k D) =
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ i : Fin 3, out.final.tapes (wold source a k D (sold source a k (i.castAdd 6))) =
        ![RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r),
          RepairOrdinary.frame (PCPPNative.descriptor oracle), RepairOrdinary.frame address] i := by
  dsimp only
  let req := wrequest source a H Cpad hpad r oracle q hq
  let address := pre ++ AddressFields.word u clause pad position ++ tail
  obtain ⟨sr, hsr, ss, sc, sh, srq, srqh, ret, retH⟩ := sblock_run source a H Cpad hcoeff hpad r oracle q hq address
  obtain ⟨p, hp, _, ps, ph, pt, pkeep⟩ := RecoveryFocus.dock (wold source a k D) (wold_injective source a k D)
    (smachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    (fun _ => 0) (winput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)
      address q) _
    (by intro j; rfl) (by intro j; exact Fin.addCases_left j) sr hsr
  have fresh (j : Fin (Occurrence.tapes D a)) :
      p.final.heads (j.natAdd (stapes source a k)) = 0 ∧
      p.final.tapes (j.natAdd (stapes source a k)) = [] := by
    have outside : ∀ i, wold source a k D i ≠ j.natAdd (stapes source a k) := by
      intro i he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      simp only [wold, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simpa only [winput, Fin.addCases_right] using pkeep _ outside
  obtain ⟨occ, ho, os, obit, oa⟩ := Occurrence.run D block hD a req u clause pad pre tail position hcap hpre
  obtain ⟨lastReceipt, hl, _, ls, _, lt, keep⟩ := RecoveryFocus.dock (wslots source a k D)
    (wslots_injective source a k D) (Occurrence.machine D block a) _ p.final.heads p.final.tapes _
    (by intro j
        change p.final.heads (wslots source a k D j) = Occurrence.heads D a j
        by_cases h19 : j.val < 19
        · let i : Fin 19 := ⟨j.val, h19⟩
          have he : j = Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)) := Fin.ext rfl
          rw [he, wcache_slot, wcache_entry_heads]
          exact (ph _).trans (sh i)
        by_cases h56 : j.val = 56
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 56) := Fin.ext h56
          rw [he, wrequest_slot]
          exact (ph _).trans srqh
        by_cases h57 : j.val = 57
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 57) := Fin.ext h57
          rw [he, waddress_slot]
          exact (ph _).trans (retH 2)
        · have hn : ¬WholeBlock.shared j := by unfold WholeBlock.shared; omega
          rw [wslots, if_neg hn, (fresh j).1]
          exact (WholeBlock.fresh_input a D req address j hn).2.symm)
    (by intro j
        change p.final.tapes (wslots source a k D j) = Occurrence.input D a req address j
        by_cases h19 : j.val < 19
        · let i : Fin 19 := ⟨j.val, h19⟩
          have he : j = Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)) := Fin.ext rfl
          rw [he, wcache_slot, WholeBlock.input_flat]
          simp only [Occurrence.old, OccurrenceAddress.base, Fin.val_castAdd]
          rw [dif_pos i.isLt]
          exact (pt _).trans (sc i)
        by_cases h56 : j.val = 56
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 56) := Fin.ext h56
          rw [he, wrequest_slot]
          exact (pt _).trans srq
        by_cases h57 : j.val = 57
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 57) := Fin.ext h57
          rw [he, waddress_slot]
          exact (pt _).trans (ret 2)
        · have hn : ¬WholeBlock.shared j := by unfold WholeBlock.shared; omega
          rw [wslots, if_neg hn, (fresh j).2]
          exact (WholeBlock.fresh_input a D req address j hn).1.symm) occ ho
  have whole := Composition.run_join (wfirst source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (wlast source a k D block) _ _ _ p lastReceipt hp hl
  refine ⟨_, whole, ?_, (lt (Occurrence.outputSlot D a)).trans obit, ?_⟩
  · change p.steps + 1 + lastReceipt.steps ≤ _
    rw [ps, ls]
    change sr.steps + 1 + occ.steps ≤ sbudget source a H Cpad hpad r oracle q hq + 1 +
      Occurrence.budget D block a req u clause position pad.length
    exact Nat.add_le_add (Nat.add_le_add_right ss 1) os
  · intro i
    by_cases hi : i.val < 2
    · let j : Fin 2 := ⟨i.val, hi⟩
      exact (keep _ (wslots_away source a k D j)).2.trans ((pt _).trans (ret i))
    · have he : i = 2 := Fin.ext (by have hb := i.isLt; omega)
      subst i
      change lastReceipt.final.tapes (wold source a k D (sold source a k 2)) = RepairOrdinary.frame address
      rw [← waddress_slot]
      exact (lt _).trans oa

/-! ## With a paid head reset -/

def wresetMachine (k D block CH Cpad : ℕ) (code : List Bool) :=
  Rewind.machine (wmachine source a k D block CH Cpad code)
def wresetInput (k D : ℕ) (hierarchy descriptor address : List Bool) (q : ℕ) :
    Fin (wtapes source a k D + 1) → List Bool :=
  Fin.addCases (winput source a k D hierarchy descriptor address q) (fun _ : Fin 1 => [])

/-- **The whole padded block with its head reset is ready.** -/
theorem wreset_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (D block : ℕ) (hD : 1 ≤ D)
    (u : BitInput (wrequest source a H Cpad hpad r oracle q hq).arity)
    (clause : BitInput (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits + pad.length =
      CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity)
    (hpre : pre.length = block * ((wrequest source a H Cpad hpad r oracle q hq).arity +
      CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity + 1)) :
    let address := pre ++ AddressFields.word u clause pad position ++ tail
    let req := wrequest source a H Cpad hpad r oracle q hq
    ∃ out, ClockJoin.ReadyRun
      (wresetMachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2 * wbudget source a H Cpad hpad r oracle q hq D block u clause position pad.length + 2)
      (wresetInput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address q)
        out ∧
      out ((woutputSlot source a k D).castAdd 1) =
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ i : Fin 3, out ((wold source a k D (sold source a k (i.castAdd 6))).castAdd 1) =
        ![RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r),
          RepairOrdinary.frame (PCPPNative.descriptor oracle), RepairOrdinary.frame address] i := by
  dsimp only
  obtain ⟨p, hp, ps, pb, pr⟩ := wblock_run source a H Cpad hcoeff hpad r oracle q hq D block hD
    u clause pad pre tail position hcap hpre
  obtain ⟨out, hr, ht, hh, hs, _⟩ := Rewind.reset_run
    (wmachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier)) _ _ p hp
  have ready : ClockJoin.ReadyRun
      (wresetMachine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (2 * p.steps + 2)
      (wresetInput source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)
        (pre ++ AddressFields.word u clause pad position ++ tail) q) out.final.tapes := ⟨out, hr, rfl, hh, hs.le⟩
  refine ⟨out.final.tapes, ClockJoin.enlarge _ _ _ _ _ ready ?_, (ht _).trans pb, ?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ps) 2
  · intro i
    exact (ht _).trans (pr i)

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole
