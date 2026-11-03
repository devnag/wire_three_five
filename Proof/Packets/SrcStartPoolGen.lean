import Proof.SourceAssembly.SourcePoolProduced

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.PoolGen
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline RepairSource RepairSource.VerifierDecoding
noncomputable section

/-- `SourcePoolCapacity.arithmetic` at `N ≤ B`. -/
theorem arithmetic (N B q : Nat) (hn : N ≤ B) :
    4*N+4+PoolEntryLoop.budget N B q (B+q+1) ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  let w := B+q+1
  have hw : 1 ≤ w := by omega
  have hn' : N ≤ w := by omega
  have hb : B ≤ w := by omega
  have hw2 : w ≤ w^2 := by nlinarith
  have hw3 : w^2 ≤ w^3 := by
    have h := Nat.mul_le_mul_right (w^2) hw
    simpa only [one_mul, pow_succ, Nat.mul_comm] using h
  rw [PCJ6e421fabe2aa4155_SourceCacheBudget.loop_eq]
  have he : B+q+(B+q+1)+1 = 2*w := by omega
  rw [he]
  have hm := Nat.mul_le_mul hn' (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hb) (409600*(2*w)^2)) 25)
  unfold PCJ6e421fabe2aa4155_SourcePoolCapacity.value
  change 4*N+4+(N*(409600*(2*w)^2+4*B+25)+3) ≤ 16777216*w^3
  nlinarith

/-- `SourcePoolBank.prefix_bound` at `N ≤ B`. -/
theorem prefix_bound (B q N : Nat) (hn : N ≤ B) :
    (natWord (2*N)).length+1 ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  have hp := arithmetic N B q hn
  have hb : natBitLength (2*N) ≤ 2*N+1 := Nat.add_le_add_right (Nat.log_le_self 2 (2*N)) 1
  rw [DecompositionSource.natWord_length]
  omega

/-- `SourcePoolBank.actual_start_padded` at `N ≤ B`. -/
theorem actual_start_padded {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (hn : N ≤ B) (i : Fin 132) :
    ZeroPadding.pad (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) (PCJ6e421fabe2aa4155_SourcePoolBank.startBank live B N source i) =
    ZeroPadding.pad (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q)
      (NativeFanout.word PCJ6e421fabe2aa4155_SourcePoolBank.select (PCJ6e421fabe2aa4155_SourcePoolBank.data live B N source) i) :=
  PCJ6e421fabe2aa4155_SourcePoolBank.start_padded live B N _ source (PCJ6e421fabe2aa4155_SourcePoolCapacity.small_bounds B q).2.1
    (prefix_bound B q N hn) (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.scalar_bounds B q).1
    (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.scalar_bounds B q).2.1
    (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.scalar_bounds B q).2.2 i

/-- `SourcePoolAllocate.fits` at `N ≤ B`. -/
theorem fits {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (hn : N ≤ B)
    (hs : source.length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) :
    ∀ i, (PCJ6e421fabe2aa4155_SourcePoolBank.data live B N source i).length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  have small := PCJ6e421fabe2aa4155_SourcePoolCapacity.small_bounds B q
  have scalars := PCJ6e421fabe2aa4155_SourcePoolSeedFanout.scalar_bounds B q
  have hC : ConstantGateReusable.C (B+q+1) = 8*(B+q+1)+12 := rfl
  intro i
  refine Fin.addCases (m := 5) (n := 4) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · change (List.replicate (B+q+1) true).length ≤ _
      rw [List.length_replicate]; omega
    · change (RepairOrdinary.frame (SignedSortKey.binary (B+q+1) 0)).length ≤ _
      rw [frame_length, SignedSortKey.binary_length]; omega
    · change (CloseoutRowsGateSupport.gateMembers live).length ≤ _
      rw [CloseoutRowsGateSupport.gateMembers, List.length_ofFn]; omega
    · change (List.replicate (ConstantGateReusable.C (B+q+1)) true).length ≤ _
      rw [List.length_replicate]; omega
    · change (CompareMachine.word q).length ≤ _
      simp only [CompareMachine.word, List.length_cons, List.length_replicate]; omega
  · fin_cases j
    · change (List.replicate (PoolEntry.reserve B q (B+q+1)) true).length ≤ _
      rw [List.length_replicate]; omega
    · exact hs
    · have h := prefix_bound B q N hn
      change (natWord (2*N)).length ≤ _
      omega
    · change (CompareMachine.word N).length ≤ _
      have h := prefix_bound B q N hn
      have hb : N+1 ≤ (natWord (2*N)).length+1+N := by omega
      simp only [CompareMachine.word, List.length_cons, List.length_replicate]
      have h2 := arithmetic N B q hn
      omega

/-- `SourcePoolInitialize.run` at `N ≤ B`. -/
theorem initialize_run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (hn : N ≤ B)
    (hs : source.length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) :
    ∃ H A, Step PCJ6e421fabe2aa4155_SourcePoolInitialize.machine (PCJ6e421fabe2aa4155_SourcePoolInitialize.budget B q N) (fun _ => 0)
      (PCJ6e421fabe2aa4155_SourcePoolInitialize.input live B N source) H A ∧
      (∀ i, H (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i) = PCJ6e421fabe2aa4155_SourcePoolInitialize.head N i) ∧
      (∀ i, A (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i) = ZeroPadding.pad (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q)
        (PCJ6e421fabe2aa4155_SourcePoolBank.startBank live B N source i)) := by
  let P := PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q
  let D := PCJ6e421fabe2aa4155_SourcePoolBank.data live B N source
  let V := NativeFanout.output PCJ6e421fabe2aa4155_SourcePoolBank.select D P
  have hV := Step.of_ready (NativeFanout.ready PCJ6e421fabe2aa4155_SourcePoolBank.select D P (fits live B N source hn hs))
  let A0 : Fin 145 → List Bool := Fin.addCases (motive := fun _ => List Bool) V (fun _ : Fin 2 => [])
  have hz : (Fin.addCases (motive := fun _ : Fin 145 => Nat) (fun _ : Fin 143 => 0) (fun _ : Fin 2 => 0)) = (fun _ => 0) := by
    funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right]
  have hf : Step PCJ6e421fabe2aa4155_SourcePoolInitialize.first (2*P+4) (fun _ => 0)
      (PCJ6e421fabe2aa4155_SourcePoolInitialize.input live B N source) (fun _ => 0) A0 :=
    ((hV.embed (fun _ : Fin 2 => 0) (fun _ => [])).congr_in hz rfl).congr hz rfl
  let localBank := fun i => A0 (PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots i)
  have h61 : localBank 61 = ZeroPadding.pad P (natWord (2*N)) := rfl
  have h132 : localBank 132 = [] := rfl
  have h133 : localBank 133 = [] := rfl
  obtain ⟨F, hb, keep⟩ := PCJ6e421fabe2aa4155_SourcePoolBoot.run N P localBank h61 h132 h133
  have hb' := hb.dock PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots PCJ6e421fabe2aa4155_SourcePoolInitialize.boot_inj
    (fun _ => 0) A0 (by intro i; rfl) (by intro i; rfl)
  refine ⟨_, _, hf.seq hb', ?_, ?_⟩
  · intro i
    have h : PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots (i.castAdd 2) = PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i := by
      simp only [PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots, Fin.addCases_left]
    rw [← h, dockH_slot PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots PCJ6e421fabe2aa4155_SourcePoolInitialize.boot_inj]
    unfold PCJ6e421fabe2aa4155_SourcePoolBoot.heads PCJ6e421fabe2aa4155_SourcePoolInitialize.head
    have h61' : (i.castAdd 2 : Fin 134) = 61 ↔ i = 61 := by
      constructor <;> intro h <;> have hv := congrArg Fin.val h <;> exact Fin.ext hv
    have h131' : (i.castAdd 2 : Fin 134) = 131 ↔ i = 131 := by
      constructor <;> intro h <;> have hv := congrArg Fin.val h <;> exact Fin.ext hv
    simp only [h61', h131']
    by_cases hi : i = 61
    · rw [if_pos hi, if_pos hi]; simp [PCJ6e421fabe2aa4155_SourcePoolBank.prefixWord, frame_length]
    · rw [if_neg hi, if_neg hi]
  · intro i
    have h : PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots (i.castAdd 2) = PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i := by
      simp only [PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots, Fin.addCases_left]
    have hk : F (i.castAdd 2) = localBank (i.castAdd 2) := keep (i.castAdd 2) (by
      intro he
      have hv : i.val = 132 := congrArg Fin.val he
      have hi := i.isLt
      omega)
    have heq : install PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots A0 F (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i) =
        F (i.castAdd 2) := by
      rw [← h]; exact install_slot PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots PCJ6e421fabe2aa4155_SourcePoolInitialize.boot_inj A0 F (i.castAdd 2)
    rw [heq, hk]
    change A0 (PCJ6e421fabe2aa4155_SourcePoolInitialize.bootSlots (i.castAdd 2)) = _
    rw [h]
    simp only [A0, PCJ6e421fabe2aa4155_SourcePoolInitialize.worker, Fin.addCases_left, V, NativeFanout.output,
      PCJ6e421fabe2aa4155_SourcePoolAllocate.worker, Fin.addCases_right]
    exact (actual_start_padded live B N source hn i).symm

/-- **`SourcePoolProduced.run` at `N ≤ B`**: the accepted producer machine, from its five words (`word q`, `1^B`, `word N`, the live
mask, the occurrence stream), writes the pool writer's start bank on its 132 worker slots. -/
theorem produced_run {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (hn : N ≤ B)
    (hs : source.length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) :
    ∃ H A, Step PCJ6e421fabe2aa4155_SourcePoolProduced.machine (PCJ6e421fabe2aa4155_SourcePoolProduced.budget B q N) (fun _ => 0)
      (PCJ6e421fabe2aa4155_SourcePoolProduced.input live B N source) H A ∧
      (∀ i, H (PCJ6e421fabe2aa4155_SourcePoolProduced.slots (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i)) =
        PCJ6e421fabe2aa4155_SourcePoolInitialize.head N i) ∧
      (∀ i, A (PCJ6e421fabe2aa4155_SourcePoolProduced.slots (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i)) =
        ZeroPadding.pad (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) (PCJ6e421fabe2aa4155_SourcePoolBank.startBank live B N source i)) := by
  obtain ⟨D, hd, fields, hP⟩ := PCJ6e421fabe2aa4155_SourcePoolMasters.run live B N source
  let A0 : Fin 229 → List Bool := Fin.addCases (motive := fun _ => List Bool) D (fun _ : Fin 145 => [])
  have hz : (Fin.addCases (motive := fun _ : Fin 229 => Nat) (fun _ : Fin 84 => 0) (fun _ : Fin 145 => 0)) = (fun _ => 0) := by
    funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right]
  have hf : Step PCJ6e421fabe2aa4155_SourcePoolProduced.first _ (fun _ => 0) (PCJ6e421fabe2aa4155_SourcePoolProduced.input live B N source)
      (fun _ => 0) A0 :=
    ((hd.embed (fun _ : Fin 145 => 0) (fun _ => [])).congr_in hz rfl).congr hz rfl
  obtain ⟨H, F, hi, fh, fw⟩ := initialize_run live B N source hn hs
  have selected : ∀ i, A0 (PCJ6e421fabe2aa4155_SourcePoolProduced.slots i) = PCJ6e421fabe2aa4155_SourcePoolInitialize.input live B N source i := by
    intro i
    rw [PCJ6e421fabe2aa4155_SourcePoolInitialize.input, PCJ6e421fabe2aa4155_SourcePoolProduced.input_shape]
    by_cases h : i.val < 9
    · rw [PCJ6e421fabe2aa4155_SourcePoolProduced.slots, dif_pos h, dif_pos h]
      simp only [A0, Fin.addCases_left]
      exact fields ⟨i.val, h⟩
    rw [PCJ6e421fabe2aa4155_SourcePoolProduced.slots, dif_neg h, dif_neg h]
    by_cases hi : i = 141
    · subst i; rw [if_pos rfl, if_pos rfl]; exact hP
    rw [if_neg hi, if_neg hi]
    simp only [A0, Fin.addCases_right]
  have hl := hi.dock PCJ6e421fabe2aa4155_SourcePoolProduced.slots PCJ6e421fabe2aa4155_SourcePoolProduced.slots_inj (fun _ => 0) A0
    (by intro i; rfl) selected
  refine ⟨_, _, hf.seq hl, ?_, ?_⟩
  · intro i
    exact (dockH_slot PCJ6e421fabe2aa4155_SourcePoolProduced.slots PCJ6e421fabe2aa4155_SourcePoolProduced.slots_inj _ _ _).trans (fh i)
  · intro i
    exact (install_slot PCJ6e421fabe2aa4155_SourcePoolProduced.slots PCJ6e421fabe2aa4155_SourcePoolProduced.slots_inj _ _ _).trans (fw i)

/-- `SourcePoolCapacity.segment_bound` at `|occ| ≤ B`. -/
theorem segment_bound {q : Nat} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (B : Nat) (hn : occ.length ≤ B)
    (hb : ∀ g ∈ occ, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ B) :
    (segment (CloseoutRowsUniversal.pool live occ) []).length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  obtain ⟨r, hr, hf, hs⟩ := PoolEntryLoop.segment_run live occ B (B+q+1) []
    (by omega) (by omega) hb (fun g hg => PCJ6e421fabe2aa4155_SourcePoolAdmissions.magnitude g (hb g hg))
  have hh := SelectiveReset.prefix_head (prefix_of_run _ _ _ r hr).1 (61 : Fin 132)
  rw [hf] at hh
  change (segment (CloseoutRowsUniversal.pool live occ) []).length ≤
    (natWord (2*occ.length) ++ RepairOrdinary.frame []).length + r.steps at hh
  have hnw : natBitLength (2*occ.length) ≤ 2*occ.length+1 := Nat.add_le_add_right (Nat.log_le_self 2 (2*occ.length)) 1
  have hp : (natWord (2*occ.length) ++ RepairOrdinary.frame []).length ≤ 4*occ.length+4 := by
    simp only [List.length_append, DecompositionSource.natWord_length, frame_length, List.length_nil] at *
    omega
  exact hh.trans ((Nat.add_le_add hp hs).trans (arithmetic occ.length B q hn))

end
end NearCubicWires.SourceStart.PoolGen

