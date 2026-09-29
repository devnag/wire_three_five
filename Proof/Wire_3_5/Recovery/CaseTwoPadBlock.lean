import Proof.Wire_3_5.Recovery.CaseTwoPadSource

/-! # One padded source block (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes the per-copy source step of the padded Case 2 ("each honest proof bit is computed by the deterministic PCPP
algorithm", P3:3762-3763), restating base's `CloseoutCaseTwo.SourceBlock` with the padded source of
`Proof.Wire_3_5.Recovery.CaseTwoPadSource`: base's `CompoundInput` pairs the retained hierarchy and oracle frames, and the padded
source runs on the pair and on `1^q` (one extra input tape, `sold 8`), leaving the clause data and framed input of the
padded request and keeping the three retained frames.

Paper quantity: the padded request's PCPP output per block; **`smachine`** and **`sblock_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

def stapes (k : ℕ) := 9 + otapes source a k
def sold (k : ℕ) (i : Fin 9) : Fin (stapes source a k) := i.castAdd (otapes source a k)
def spairSlots (k : ℕ) (i : Fin 6) := sold source a k ((![0, 1, 3, 4, 5, 6] : Fin 6 → Fin 9) i)
/-- The padded source's tapes: the paired word at `sold 3`, `1^q` at `sold 8`, the rest after the nine. -/
def ssourceSlots (k : ℕ) (j : Fin (otapes source a k)) : Fin (stapes source a k) :=
  if j.val = 0 then sold source a k 3
  else if j.val = PCPPNativeHierarchyNodes.tapes source k then sold source a k 8 else j.natAdd 9

theorem spair_injective (k : ℕ) : Function.Injective (spairSlots source a k) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hmap : (![0, 1, 3, 4, 5, 6] : Fin 6 → Fin 9) i = ![0, 1, 3, 4, 5, 6] j := Fin.ext hv
  exact (by decide : Function.Injective (![0, 1, 3, 4, 5, 6] : Fin 6 → Fin 9)) hmap
theorem ssource_injective (k : ℕ) : Function.Injective (ssourceSlots source a k) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [ssourceSlots, sold] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hv <;> omega
theorem ssource_away (k : ℕ) (i : Fin 3) : ∀ j, ssourceSlots source a k j ≠ sold source a k (i.castAdd 6) := by
  intro j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  dsimp only [ssourceSlots, sold] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hv <;> omega

/-- The block's input: the three retained frames and `1^q`. -/
def sinput (k : ℕ) (hierarchy oracle address : List Bool) (q : ℕ) : Fin (stapes source a k) → List Bool := fun i =>
  if i.val = 0 then RepairOrdinary.frame hierarchy else if i.val = 1 then RepairOrdinary.frame oracle else if i.val = 2 then RepairOrdinary.frame address
  else if i.val = 8 then List.replicate q true else []
def spair (k : ℕ) := RecoveryFocus.machine (spairSlots source a k) CompoundInput.machine
def ssourceProgram (k CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (ssourceSlots source a k) (omachine source a k CH Cpad code)
/-- **The padded source block.** -/
def smachine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (spair source a k) (ssourceProgram source a k CH Cpad code)
def scacheSlots (k : ℕ) (j : Fin 19) := ssourceSlots source a k
  (oslots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))
def srequestSlot (k : ℕ) := ssourceSlots source a k
  (oslots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))
def sbudget {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :=
  CompoundInput.budget (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) + 1 +
    obudget source a H Cpad hpad r oracle q hq

theorem spair_input (k : ℕ) (hierarchy oracle address : List Bool) (q : ℕ) (j : Fin 6) :
    sinput source a k hierarchy oracle address q (spairSlots source a k j) = CompoundInput.input hierarchy oracle j := by
  fin_cases j <;> rfl

theorem ssource_input (k : ℕ) (hierarchy oracle address : List Bool) (q : ℕ) (A : Fin 6 → List Bool)
    (hword : A 2 = RepairOrdinary.frame hierarchy ++ RepairOrdinary.frame oracle) (j : Fin (otapes source a k)) :
    install (spairSlots source a k) (sinput source a k hierarchy oracle address q) A (ssourceSlots source a k j) =
      oinput source a k hierarchy oracle q j := by
  rw [oinput_val]
  have ht : 438 ≤ PCPPNativeHierarchyNodes.tapes source k := by unfold PCPPNativeHierarchyNodes.tapes; omega
  by_cases h0 : j.val = 0
  · have he : ssourceSlots source a k j = spairSlots source a k 2 := by simp [ssourceSlots, h0]; rfl
    rw [he, install_slot (spairSlots source a k) (spair_injective source a k), hword, if_pos h0]
    rfl
  · have away : ∀ i, spairSlots source a k i ≠ ssourceSlots source a k j := by
      intro i he
      have hv := congrArg Fin.val he
      have hp : (spairSlots source a k i).val ≤ 6 := by fin_cases i <;> simp [spairSlots, sold]
      have hp' : (spairSlots source a k i).val ≠ 8 := by fin_cases i <;> simp [spairSlots, sold]
      simp only [ssourceSlots, if_neg h0] at hv
      split_ifs at hv <;> simp only [sold, Fin.val_castAdd, Fin.val_natAdd] at hv <;> omega
    rw [install_other (spairSlots source a k) _ _ _ away, if_neg h0]
    by_cases hQ : j.val = PCPPNativeHierarchyNodes.tapes source k
    · rw [if_pos hQ]
      have htz : PCPPNativeHierarchyNodes.tapes source k ≠ 0 := by omega
      simp [sinput, ssourceSlots, hQ, sold, htz]
    · rw [if_neg hQ]
      simp only [sinput, ssourceSlots, h0, hQ, if_false, Fin.val_natAdd]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The padded source block is ready**: the clause data and framed input of the padded request's PCPP output on
the cache and request slots; the three retained frames are kept. -/
theorem sblock_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (address : List Bool) :
    let request := PCPPRequestBoundary.request a (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k
      H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))
    ∃ result, run (smachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (sbudget source a H Cpad hpad r oracle q hq)
      (sinput source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address q) =
        some result ∧
      result.steps ≤ sbudget source a H Cpad hpad r oracle q hq ∧
      (∀ j, result.final.tapes (scacheSlots source a k j) =
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size + request.arity)) [] j) ∧
      (∀ j, result.final.heads (scacheSlots source a k j) = PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (srequestSlot source a k) = RepairOrdinary.frame (pcppInput request) ∧
      result.final.heads (srequestSlot source a k) = 0 ∧
      (∀ i : Fin 3, result.final.tapes (sold source a k (i.castAdd 6)) =
        ![RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r), RepairOrdinary.frame (PCPPNative.descriptor oracle), RepairOrdinary.frame address] i) ∧
      (∀ i : Fin 3, result.final.heads (sold source a k (i.castAdd 6)) = 0) := by
  obtain ⟨paired, pairReady, hword, hH, hD⟩ := CompoundInput.pair_ready
    (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)
  have firstReady := pairReady.focus (spairSlots source a k) (spair_injective source a k)
    (sinput source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address q)
    (spair_input source a k _ _ _ _)
  obtain ⟨firstReceipt, hfirst, ft, fh, fs⟩ := firstReady
  obtain ⟨base, hb, bs, bt, bh, hrq, hrqh⟩ := osource_run source a H Cpad hcoeff hpad r oracle q hq
  obtain ⟨lastReceipt, hl, _, ls, lh, lt, keep⟩ := RecoveryFocus.dock (t := otapes source a k)
    (ssourceSlots source a k) (ssource_injective source a k)
    (omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration (omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (oinput source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) q))
    (by intro j; exact fh _) (by intro j; rw [ft]; exact ssource_input source a k _ _ address q paired hword j) base hb
  have he : (⟨(omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)).start,
      firstReceipt.final.heads, firstReceipt.final.tapes⟩ : Configuration (stapes source a k) _) =
      Composition.restart firstReceipt.final
        (ssourceProgram source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)).start := rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole := Composition.run_join (spair source a k)
    (ssourceProgram source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ _ firstReceipt lastReceipt hfirst hl
  refine ⟨Composition.joinedReceipt firstReceipt lastReceipt, whole, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change firstReceipt.steps + 1 + lastReceipt.steps ≤ _
    rw [ls]
    unfold sbudget
    omega
  · intro j
    change lastReceipt.final.tapes (ssourceSlots source a k
      (oslots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))) = _
    exact (lt _).trans (bt j)
  · intro j
    change lastReceipt.final.heads (ssourceSlots source a k
      (oslots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))) = _
    exact (lh _).trans (bh j)
  · change lastReceipt.final.tapes (ssourceSlots source a k
      (oslots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))) = _
    exact (lt _).trans hrq
  · change lastReceipt.final.heads (ssourceSlots source a k
      (oslots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a)))) = _
    exact (lh _).trans hrqh
  · intro i
    change lastReceipt.final.tapes (sold source a k (i.castAdd 6)) = _
    rw [(keep _ (ssource_away source a k i)).2, ft]
    fin_cases i
    · exact (install_slot (spairSlots source a k) (spair_injective source a k) _ _ 0).trans hH
    · exact (install_slot (spairSlots source a k) (spair_injective source a k) _ _ 1).trans hD
    · rw [install_other (spairSlots source a k) _ _ _ (by
        intro j he
        have hv := congrArg Fin.val he
        fin_cases j <;> simp [spairSlots, sold] at hv)]
      rfl
  · intro i
    change lastReceipt.final.heads (sold source a k (i.castAdd 6)) = 0
    exact ((keep _ (ssource_away source a k i)).1).trans (fh _)

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock
