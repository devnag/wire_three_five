import Proof.Rows.FinalThresholdChildMagnitude
import Proof.MachineModel.ClockScalarFields
import Proof.CaseAnalysis.RawRowsThresholdSize

/-! One actual canonical-base update: widen the physically produced native
magnitude using the existing B+2 copy driver, then add it to the retained
prefix accumulator. Source guards prove the common width for at most four
selected children. Initial accumulator/caller inputs, iteration and shared
bank cleanup remain separate physical duties. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdMagnitudeBase
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding SignedSortKey ThresholdAlignedEnvelope SupplierPipeline SupplierEstimator
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000

theorem widen (B C x : ℕ) (hC : 8*B+12≤C) (hx : x<2^B) :
    Step ClockNormalize.machine (4*(B+2)+4) (fun _ : Fin 5=>0)
      ![List.replicate (B+2) true,MatrixScoreWeight.scalar C B x,
        List.replicate C false,List.replicate C false,List.replicate (C+1) false]
      (fun _ : Fin 5=>0)
      ![List.replicate (B+2) true,MatrixScoreWeight.scalar C B x,
        MatrixScoreWeight.scalar C (B+2) x,ZeroPadding.pad C [true],List.replicate (C+1) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,_⟩ := ClockScalarFields.scalar_run (B+2) (binary B x)
    (by simp only [binary_length];omega)
  have hv := SignedSortKey.binary_value B x hx
  rw [hv] at h2
  have ht : r.final.tapes=![List.replicate (B+2) true,RepairOrdinary.frame (binary B x),
      RepairOrdinary.frame (binary (B+2) x),[true],List.replicate (2*(B+2)+1) false] := by
    funext i;fin_cases i <;>assumption
  have step := (Step.of_run hr (funext hh) ht).pad (![0,C,C,C,C+1] : Fin 5 → ℕ)
  refine (step.congr_in rfl ?_).congr rfl ?_
  · funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad C []=List.replicate C false
      simp [ZeroPadding.pad]
    · change ZeroPadding.pad C []=List.replicate C false
      simp [ZeroPadding.pad]
    · change ZeroPadding.pad (C+1) []=List.replicate (C+1) false
      simp [ZeroPadding.pad]
  · funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · rfl
    · rfl
    · change ZeroPadding.pad (C+1) (List.replicate (2*(B+2)+1) false)=_
      rw [Rewind.Workspace.pad_zeros,max_eq_left (show 2*(B+2)+1≤C+1 by omega)]
      rfl

def input (B C x a : ℕ) : Fin 9 → List Bool :=
  ![List.replicate (B+2) true,MatrixScoreWeight.scalar C B x,
    MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,List.replicate (C+1) false,
    MatrixScoreWeight.scalar C (B+2) a,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C]
def widened (B C x a : ℕ) : Fin 9 → List Bool :=
  ![List.replicate (B+2) true,MatrixScoreWeight.scalar C B x,
    MatrixScoreWeight.scalar C (B+2) x,ZeroPadding.pad C [true],List.replicate (C+1) false,
    MatrixScoreWeight.scalar C (B+2) a,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C]
def output (B C x a : ℕ) : Fin 9 → List Bool :=
  ![List.replicate (B+2) true,MatrixScoreWeight.scalar C B x,
    MatrixScoreWeight.scalar C (B+2) x,ZeroPadding.pad C [true],List.replicate (C+1) false,
    MatrixScoreWeight.scalar C (B+2) (x+a),MatrixScoreWeight.scalar C (B+2) (x+a),
    MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C]
def addSlots : Fin 5 → Fin 9 := ![2,5,6,7,8]
noncomputable def machine := Composition.machine (TapeEmbedding.machine 4 ClockNormalize.machine)
  (RecoveryFocus.machine addSlots MatrixScoreAccumulate.machine)

theorem run (B C x a : ℕ) (hC : 8*B+12≤C) (hx : x<2^B) (ha : x+a<2^(B+2)) :
    Step machine (16*(B+2)+18) (fun _ : Fin 9=>0) (input B C x a)
      (fun _ : Fin 9=>0) (output B C x a) := by
  have first := (widen B C x hC hx).embed (fun _ : Fin 4=>0)
    (![MatrixScoreWeight.scalar C (B+2) a,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C,MatrixScoreWeight.zeros C] : Fin 4 → List Bool)
  have first' : Step (TapeEmbedding.machine 4 ClockNormalize.machine) (4*(B+2)+4)
      (fun _ : Fin 9=>0) (input B C x a) (fun _ : Fin 9=>0) (widened B C x a) := by
    refine (first.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;>rfl
  have add := (Step.of_ready (MatrixScoreWeight.padded_accumulate C (B+2) x a (by omega) ha)).dock
    addSlots (by decide) (fun _ : Fin 9=>0) (widened B C x a)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  have add' : Step (RecoveryFocus.machine addSlots MatrixScoreAccumulate.machine) (12*(B+2)+13)
      (fun _ : Fin 9=>0) (widened B C x a) (fun _ : Fin 9=>0) (output B C x a) := by
    refine add.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) ?_
    apply HierarchyAllocation.install_eq addSlots (by decide)
    · intro i;fin_cases i <;>rfl
    · intro i hi;fin_cases i
      · simp only [output,widened,Matrix.cons_val_zero']
      · simp only [output,widened,Matrix.cons_val_succ',Matrix.cons_val_zero']
      · exact False.elim (hi 0 rfl)
      · simp only [output,widened,Matrix.cons_val_succ',Matrix.cons_val_zero']
      · simp only [output,widened,Matrix.cons_val_succ',Matrix.cons_val_zero']
      · exact False.elim (hi 1 rfl)
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 3 rfl)
      · exact False.elim (hi 4 rfl)
  have whole := first'.seq add'
  simpa only [machine,show 4*(B+2)+4+1+(12*(B+2)+13)=16*(B+2)+18 by omega] using whole



theorem magnitude_spares {n : ℕ} (g : ExactThresholdGate n)
    (tail mtail out : List Bool) (w C D : ℕ)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items g,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude g<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items g) w C≤D) :
    ∃ result : Fin 44 → List Bool,
      Step C10ThresholdChildMagnitude.machine (C10ThresholdChildMagnitude.budget g w C)
        (C10NaturalHardwireScoreInputs.heads out 0 0)
        (C10NaturalHardwireScoreInputs.data (exactWord g++tail)
          (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g)++mtail)
          out w C D (C10ThresholdChildMagnitude.items g).length 0 0)
        (C10NaturalHardwireScoreInputs.heads out (exactWord g).length (C10ThresholdChildMagnitude.items g).length) result ∧
      result 0=exactWord g++tail ∧ result 14=MatrixScoreWeight.scalar C w (childMagnitude g) ∧
      (∀ j : Fin 5,result (![18,19,20,21,22] j)=List.replicate C false) ∧
      result 41=List.replicate (C+1) false := by
  have halves := C10ThresholdChildMagnitude.items_magnitude g
  have hp : C10NaturalHardwireScore.positiveSum (C10ThresholdChildMagnitude.items g)=
      C10NaturalHardwireScore.selectedSum (C10ThresholdChildMagnitude.items g) := by
    simp [C10NaturalHardwireScore.positiveSum,C10NaturalHardwireScore.selectedSum,
      C10ThresholdChildMagnitude.items,Function.comp_def]
  have hn : CloseoutRowsPoolMinimum.negSum (C10ThresholdChildMagnitude.items g)=
      CloseoutRowsPoolMinimum.liveSum (C10ThresholdChildMagnitude.items g) := by
    simp [CloseoutRowsPoolMinimum.negSum,CloseoutRowsPoolMinimum.liveSum,
      C10ThresholdChildMagnitude.items,Function.comp_def]
  have first := C10NaturalHardwireScoreInputs.run (C10ThresholdChildMagnitude.items g) tail mtail out w C D hw hc
    (by rw[hp];omega) (by rw[hn];omega) hD
  rw [C10ThresholdChildMagnitude.items_word] at first
  let H := C10NaturalHardwireScoreInputs.heads out (exactWord g).length (C10ThresholdChildMagnitude.items g).length
  let A := C10NaturalHardwireScoreInputs.data (exactWord g++tail)
    (CloseoutRowsPoolWeight.mask (C10ThresholdChildMagnitude.items g)++mtail) out w C D
    (C10ThresholdChildMagnitude.items g).length (C10NaturalHardwireScore.selectedSum (C10ThresholdChildMagnitude.items g))
    (CloseoutRowsPoolMinimum.liveSum (C10ThresholdChildMagnitude.items g))
  have second := (Step.of_ready (MatrixScoreWeight.padded_accumulate C w
    (C10NaturalHardwireScore.selectedSum (C10ThresholdChildMagnitude.items g))
    (CloseoutRowsPoolMinimum.liveSum (C10ThresholdChildMagnitude.items g))
    (by omega) (by rw[halves];exact hm))).dock (![13,14,15,16,17] : Fin 5 → Fin 44)
      (by decide) H A (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  have whole := first.seq (second.congr (dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)) rfl)
  rw [show C10NaturalHardwireScoreInputs.budget (C10ThresholdChildMagnitude.items g) w C+1+(12*w+13)=
    C10ThresholdChildMagnitude.budget g w C by unfold C10ThresholdChildMagnitude.budget;omega] at whole
  refine ⟨_,whole,install_other _ _ _ _ (by decide),?_,?_,install_other _ _ _ _ (by decide)⟩
  · exact (install_slot (![13,14,15,16,17] : Fin 5 → Fin 44) (by decide) _ _ 1).trans
      (congrArg (MatrixScoreWeight.scalar C w) halves)
  · intro j;fin_cases j <;>exact install_other (![13,14,15,16,17] : Fin 5 → Fin 44) _ _ _ (by decide)


end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdMagnitudeBase
