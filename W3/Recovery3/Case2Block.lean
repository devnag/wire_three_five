import Proof.CaseAnalysis.CaseTwoExecution

/-!
# The Case-2 chain, part 1: proof 1's Case-2 chain, generic in the source block

The near-cubic-wires paper (Case 2 table `f(i,j,u) = T̂_ij(u)` on `q_0 = q+r+1` bits, XOR-powered and padded) and Lemma C.10
("In Case 2, apply the deterministic honest-assignment algorithm in Fact C.2 to H_{B*}"). Proof 1 computes
the bit `padCore (xorPower (paddedUnsigned (a.output req) hc) copies) ht point` by the chain
`Execution ⊃ XorFamily ⊃ FixedFold ⊃ WholeBlock ⊃ SourceBlock` (base `Proof/CaseAnalysis/CaseTwo*.lean`); everything
below `SourceBlock` (`Occurrence*`, …) is independent of the request's origin, and the wrappers use `SourceBlock` only
through its interface. `SBlock a` is that interface (a machine on three word tapes producing the PCPP source cache
and the framed request of `req i`, leaving its three words in place); `WholeBlock`/`XorFamily` below are proof 1's,
restated over any `SBlock` (proofs copied, `SourceBlock.* source a k` ↦ `S.*`). The v3 instance (H2′ front on
`H_B`, request `requestOf`) is in `Case2Front.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo NearCubicWires.RecoveryPipeline

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

/-- **A Case-2 source block** for the PCPP algorithm `a`: one machine, started on three word tapes `0, 1, 2`
(`w0 i`, `RepairOrdinary.frame (d i)`, `RepairOrdinary.frame address`), producing proof 1's source cache (19 slots) and the framed PCPP input of
`req i`, leaving the three words (heads `0`). -/
structure SBlock (a : PointwisePCPPAlgorithm) where
  ι : Type
  req : ι → PCPPRequest a.minimumArity
  w0 : ι → List Bool
  d : ι → List Bool
  budget : ι → ℕ
  t : ℕ
  st : ℕ
  M : Machine t st
  three : 3 ≤ t
  cacheSlots : Fin 19 → Fin t
  requestSlot : Fin t
  cache_injective : Function.Injective cacheSlots
  cache_request : ∀ j, cacheSlots j ≠ requestSlot
  cache_low : ∀ j, 3 ≤ (cacheSlots j).val
  request_low : 3 ≤ requestSlot.val
  run : ∀ (i : ι) (address : List Bool), ∃ result,
    LocalBitMultitape.run M (budget i)
      (XorFamily.wordInput (t := t) ![w0 i, RepairOrdinary.frame (d i), RepairOrdinary.frame address]) = some result ∧
    result.steps ≤ budget i ∧
    (∀ j, result.final.tapes (cacheSlots j) =
      PCPPQueryIndexPadding.clauseData (pcppOutput (req i) (a.output (req i))) (req i).arity 0
        (PCPPQueryCachedBounds.capacity a ((req i).circuit.size + (req i).arity)) [] j) ∧
    (∀ j, result.final.heads (cacheSlots j) = PCPPQueryClauseReuse.heads j) ∧
    result.final.tapes requestSlot = RepairOrdinary.frame (pcppInput (req i)) ∧ result.final.heads requestSlot = 0 ∧
    (∀ k : Fin 3, result.final.tapes ⟨k.val, by have := k.isLt; omega⟩ = ![w0 i, RepairOrdinary.frame (d i), RepairOrdinary.frame address] k) ∧
    (∀ k : Fin 3, result.final.heads ⟨k.val, by have := k.isLt; omega⟩ = 0)

namespace SBlock

noncomputable section

variable {a : PointwisePCPPAlgorithm} (S : SBlock a)

/-- Word tape `k < 3`. -/
def lo (k : Fin 3) : Fin S.t := ⟨k.val, by have := k.isLt; have := S.three; omega⟩

/-- The three words of an instance. -/
def words (i : S.ι) (address : List Bool) : Fin 3 → List Bool := ![S.w0 i, RepairOrdinary.frame (S.d i), RepairOrdinary.frame address]

theorem cache_away (k : Fin 3) (j : Fin 19) : S.cacheSlots j ≠ S.lo k := fun e => by
  have := congrArg Fin.val e; have := S.cache_low j; have := k.isLt; simp [lo] at *; omega

theorem request_away (k : Fin 3) : S.requestSlot ≠ S.lo k := fun e => by
  have := congrArg Fin.val e; have := S.request_low; have := k.isLt; simp [lo] at *; omega

/-! ## WholeBlock over `S` (base `CaseTwoWholeBlockLayout/Input/Run/Reset`) -/

def wtapes (D : ℕ) := S.t + Occurrence.tapes D a
def wold (D : ℕ) (j : Fin S.t) : Fin (S.wtapes D) := j.castAdd (Occurrence.tapes D a)
def port : Fin 21 → Fin S.t := Fin.append S.cacheSlots ![S.requestSlot, S.lo 2]

theorem port_injective : Function.Injective S.port := by
  apply Fin.append_injective_iff.mpr
  refine ⟨S.cache_injective, ?_, ?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> try rfl
    · exact ((S.request_away 2) he).elim
    · exact ((S.request_away 2) he.symm).elim
  · intro i j
    fin_cases j
    · exact S.cache_request i
    · exact S.cache_away 2 i

def wslots (D : ℕ) (j : Fin (Occurrence.tapes D a)) : Fin (S.wtapes D) :=
  if WholeBlock.shared j then S.wold D (S.port (WholeBlock.key j)) else j.natAdd S.t

theorem wold_injective (D : ℕ) : Function.Injective (S.wold D) := by
  intro i j he; apply Fin.ext; exact congrArg (fun x : Fin (S.wtapes D) => x.val) he

theorem wslots_injective (D : ℕ) : Function.Injective (S.wslots D) := by
  intro i j he
  by_cases hi : WholeBlock.shared i <;> by_cases hj : WholeBlock.shared j
  · exact WholeBlock.key_injective i j hi hj (S.port_injective
      (S.wold_injective D (by simpa only [wslots, if_pos hi, if_pos hj] using he)))
  · have hv := congrArg Fin.val he
    have bound := (S.port (WholeBlock.key i)).isLt
    simp only [wslots, if_pos hi, if_neg hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · have hv := congrArg Fin.val he
    have bound := (S.port (WholeBlock.key j)).isLt
    simp only [wslots, if_neg hi, if_pos hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [wslots, if_neg hi, if_neg hj, Fin.val_natAdd] at hv
    omega

def wfirst (D : ℕ) := RecoveryFocus.machine (S.wold D) S.M
def wlast (D block : ℕ) := RecoveryFocus.machine (S.wslots D) (Occurrence.machine D block a)
def wmachine (D block : ℕ) := Composition.machine (S.wfirst D) (S.wlast D block)
def winput (D : ℕ) (i : S.ι) (address : List Bool) : Fin (S.wtapes D) → List Bool :=
  Fin.addCases (XorFamily.wordInput (t := S.t) (S.words i address)) (fun _ => [])
def woutputSlot (D : ℕ) := S.wslots D (Occurrence.outputSlot D a)

theorem port_away (k : Fin 2) (j : Fin 21) : S.port j ≠ S.lo (k.castAdd 1) := by
  refine Fin.addCases (motive := fun j => S.port j ≠ S.lo (k.castAdd 1)) (fun j : Fin 19 => ?_) (fun j : Fin 2 => ?_) j
  · rw [port, Fin.append_left]
    exact S.cache_away (k.castAdd 1) j
  · fin_cases j
    · exact S.request_away (k.castAdd 1)
    · intro he
      have hv := congrArg Fin.val he
      have hi := k.isLt
      change 2 = k.val at hv
      omega

theorem wslots_away (D : ℕ) (k : Fin 2) : ∀ j, S.wslots D j ≠ S.wold D (S.lo (k.castAdd 1)) := by
  intro j he
  by_cases hj : WholeBlock.shared j
  · exact S.port_away k (WholeBlock.key j)
      (S.wold_injective D (by simpa only [wslots, if_pos hj] using he))
  · have hv := congrArg Fin.val he
    have bound := (S.lo (k.castAdd 1)).isLt
    simp only [wslots, if_neg hj, wold, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

theorem address_slot (D : ℕ) :
    S.wslots D (Occurrence.old D a (OccurrenceAddress.base D 57)) = S.wold D (S.lo 2) := rfl

theorem cache_slot (D : ℕ) (j : Fin 19) :
    S.wslots D (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) = S.wold D (S.cacheSlots j) := by
  have hshared : WholeBlock.shared (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) := Or.inl j.isLt
  rw [wslots, if_pos hshared]
  have hk : WholeBlock.key (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))) = j.castAdd 2 := by
    apply Fin.ext
    rw [WholeBlock.key_value]
    change (if j.val < 19 then j.val else if j.val = 56 then 19 else 20) = j.val
    rw [if_pos j.isLt]
  rw [hk]
  exact congrArg (S.wold D) (Fin.append_left _ _ j)

theorem request_slot (D : ℕ) :
    S.wslots D (Occurrence.old D a (OccurrenceAddress.base D 56)) = S.wold D S.requestSlot := rfl

private theorem cache_heads (i : Fin 19) :
    PCPPQueryClauseReuse.heads i = if i.val = 13 ∨ i.val = 14 then 1 else 0 := by
  fin_cases i <;> rfl

private theorem cache_entry_heads (D : ℕ) (a : PointwisePCPPAlgorithm) (i : Fin 19) :
    Occurrence.heads D a (Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39))) =
      PCPPQueryClauseReuse.heads i := by
  simp only [Occurrence.heads, Occurrence.old, Fin.addCases_left, OccurrenceAddress.heads,
    OccurrenceAddress.base, Fin.val_castAdd]
  exact (cache_heads i).symm

def wbudget (i : S.ι) (D block : ℕ) (u : BitInput (S.req i).arity)
    (clause : BitInput (a.output (S.req i)).clauseBits) (position : Bool) (padding : ℕ) :=
  S.budget i + 1 + Occurrence.budget D block a (S.req i) u clause position padding

theorem wblock_run (i : S.ι) (D block : ℕ) (hD : 1 ≤ D)
    (u : BitInput (S.req i).arity) (clause : BitInput (a.output (S.req i)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (S.req i)).clauseBits + pad.length = CloseoutLanguage.clauseWidth D (S.req i).arity)
    (hpre : pre.length = block * ((S.req i).arity + CloseoutLanguage.clauseWidth D (S.req i).arity + 1)) :
    let address := pre ++ AddressFields.word u clause pad position ++ tail
    let req := S.req i
    ∃ out, LocalBitMultitape.run (S.wmachine D block) (S.wbudget i D block u clause position pad.length)
      (S.winput D i address) = some out ∧
      out.steps ≤ S.wbudget i D block u clause position pad.length ∧
      out.final.tapes (S.woutputSlot D) =
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ k : Fin 3, out.final.tapes (S.wold D (S.lo k)) = S.words i address k := by
  dsimp only
  let req := S.req i
  let address := pre ++ AddressFields.word u clause pad position ++ tail
  obtain ⟨sr, hsr, ss, sc, sh, srq, srqh, ret, retH⟩ := S.run i address
  obtain ⟨p, hp, _, ps, ph, pt, pkeep⟩ := RecoveryFocus.dock (S.wold D) (S.wold_injective D)
    S.M _ (fun _ => 0) (S.winput D i address) _
    (by intro j; rfl) (by intro j; exact Fin.addCases_left j) sr hsr
  have fresh (j : Fin (Occurrence.tapes D a)) :
      p.final.heads (j.natAdd S.t) = 0 ∧ p.final.tapes (j.natAdd S.t) = [] := by
    have outside : ∀ i, S.wold D i ≠ j.natAdd S.t := by
      intro i he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      simp only [wold, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simpa only [winput, Fin.addCases_right] using pkeep _ outside
  obtain ⟨occ, ho, os, obit, oa⟩ := Occurrence.run D block hD a req u clause pad pre tail position hcap hpre
  obtain ⟨lastReceipt, hl, _, ls, _, lt, keep⟩ := RecoveryFocus.dock (S.wslots D)
    (S.wslots_injective D) (Occurrence.machine D block a) _ p.final.heads p.final.tapes _
    (by intro j
        change p.final.heads (S.wslots D j) = Occurrence.heads D a j
        by_cases h19 : j.val < 19
        · let i : Fin 19 := ⟨j.val, h19⟩
          have he : j = Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)) := Fin.ext rfl
          rw [he, S.cache_slot, cache_entry_heads]
          exact (ph _).trans (sh i)
        by_cases h56 : j.val = 56
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 56) := Fin.ext h56
          rw [he, S.request_slot]
          exact (ph _).trans srqh
        by_cases h57 : j.val = 57
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 57) := Fin.ext h57
          rw [he, S.address_slot]
          exact (ph _).trans (retH 2)
        · have hn : ¬WholeBlock.shared j := by unfold WholeBlock.shared; omega
          rw [wslots, if_neg hn, (fresh j).1]
          exact (WholeBlock.fresh_input a D req address j hn).2.symm)
    (by intro j
        change p.final.tapes (S.wslots D j) = Occurrence.input D a req address j
        by_cases h19 : j.val < 19
        · let i : Fin 19 := ⟨j.val, h19⟩
          have he : j = Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)) := Fin.ext rfl
          rw [he, S.cache_slot, WholeBlock.input_flat]
          simp only [Occurrence.old, OccurrenceAddress.base, Fin.val_castAdd]
          rw [dif_pos i.isLt]
          exact (pt _).trans (sc i)
        by_cases h56 : j.val = 56
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 56) := Fin.ext h56
          rw [he, S.request_slot]
          exact (pt _).trans srq
        by_cases h57 : j.val = 57
        · have he : j = Occurrence.old D a (OccurrenceAddress.base D 57) := Fin.ext h57
          rw [he, S.address_slot]
          exact (pt _).trans (ret 2)
        · have hn : ¬WholeBlock.shared j := by unfold WholeBlock.shared; omega
          rw [wslots, if_neg hn, (fresh j).2]
          exact (WholeBlock.fresh_input a D req address j hn).1.symm) occ ho
  have whole := Composition.run_join (S.wfirst D) (S.wlast D block) _ _ _ p lastReceipt hp hl
  refine ⟨_, whole, ?_, (lt (Occurrence.outputSlot D a)).trans obit, ?_⟩
  · change p.steps + 1 + lastReceipt.steps ≤ _
    rw [ps, ls]
    change sr.steps + 1 + occ.steps ≤ S.budget i + 1 + Occurrence.budget D block a req u clause position pad.length
    exact Nat.add_le_add (Nat.add_le_add_right ss 1) os
  · intro k
    by_cases hk : k.val < 2
    · let j : Fin 2 := ⟨k.val, hk⟩
      have hkj : k = j.castAdd 1 := Fin.ext rfl
      rw [hkj]
      exact (keep _ (S.wslots_away D j)).2.trans ((pt _).trans (ret (j.castAdd 1)))
    · have he : k = 2 := Fin.ext (by have hb := k.isLt; omega)
      subst k
      change lastReceipt.final.tapes (S.wold D (S.lo 2)) = RepairOrdinary.frame address
      rw [← S.address_slot]
      exact (lt _).trans oa

def wresetMachine (D block : ℕ) := Rewind.machine (S.wmachine D block)
def wresetInput (D : ℕ) (i : S.ι) (address : List Bool) : Fin (S.wtapes D + 1) → List Bool :=
  Fin.addCases (S.winput D i address) (fun _ : Fin 1 => [])

theorem wreset_run (i : S.ι) (D block : ℕ) (hD : 1 ≤ D)
    (u : BitInput (S.req i).arity) (clause : BitInput (a.output (S.req i)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (S.req i)).clauseBits + pad.length = CloseoutLanguage.clauseWidth D (S.req i).arity)
    (hpre : pre.length = block * ((S.req i).arity + CloseoutLanguage.clauseWidth D (S.req i).arity + 1)) :
    let address := pre ++ AddressFields.word u clause pad position ++ tail
    let req := S.req i
    ∃ out, ClockJoin.ReadyRun (S.wresetMachine D block)
      (2 * S.wbudget i D block u clause position pad.length + 2) (S.wresetInput D i address) out ∧
      out ((S.woutputSlot D).castAdd 1) =
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ k : Fin 3, out ((S.wold D (S.lo k)).castAdd 1) = S.words i address k := by
  dsimp only
  obtain ⟨p, hp, ps, pb, pr⟩ := S.wblock_run i D block hD u clause pad pre tail position hcap hpre
  obtain ⟨out, hr, ht, hh, hs, _⟩ := Rewind.reset_run (S.wmachine D block) _ _ p hp
  have ready : ClockJoin.ReadyRun (S.wresetMachine D block) (2 * p.steps + 2)
      (S.wresetInput D i (pre ++ AddressFields.word u clause pad position ++ tail)) out.final.tapes :=
    ⟨out, hr, rfl, hh, hs.le⟩
  refine ⟨out.final.tapes, ClockJoin.enlarge _ _ _ _ _ ready ?_, (ht _).trans pb, ?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ps) 2
  · intro k
    exact (ht _).trans (pr k)

/-! ## XorFamily over `S` (base `CaseTwoXorFamilyInput/XorFamily/XorRun`) -/

theorem winput_words (D : ℕ) (i : S.ι) (address : List Bool) :
    S.winput D i address = XorFamily.wordInput (t := S.wtapes D) (S.words i address) := by
  unfold winput
  exact XorFamily.extend_words S.three _

theorem wreset_input (D : ℕ) (i : S.ι) (address : List Bool) :
    S.wresetInput D i address = XorFamily.wordInput (S.words i address) := by
  have hw : 3 ≤ S.wtapes D := by unfold wtapes; have := S.three; omega
  unfold wresetInput
  rw [S.winput_words]
  exact XorFamily.extend_words hw _

def xtapes (D : ℕ) := S.wtapes D + 1 + 1
def accumulator (D : ℕ) : Fin (S.xtapes D) := Fin.last (S.wtapes D + 1)

theorem accumulator_lower (D : ℕ) : 3 ≤ (S.accumulator D).val := by
  have := S.three
  change 3 ≤ S.wtapes D + 1
  unfold wtapes
  omega

theorem body_input (D : ℕ) (i : S.ι) (address : List Bool) (parity : Bool) :
    XorBody.input (S.wresetInput D i address) parity =
      FixedFold.bodyInput (S.accumulator D) (S.words i address) parity := by
  rw [S.wreset_input]
  exact XorFamily.extend_accumulator (S.accumulator_lower D) _ parity

def workers (D block : ℕ) : Σ s, Machine (S.xtapes D) s :=
  ⟨_, XorBody.machine (S.wresetMachine D block) ((S.woutputSlot D).castAdd 1)⟩
def sizes (D block : ℕ) := (S.workers D block).1
def programs (D block : ℕ) : Machine (S.xtapes D) (S.sizes D block) := (S.workers D block).2

end

end SBlock

end W3.NearCubicWires.RepairSource.Outer3.Case2
