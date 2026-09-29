import Proof.PCP.VerifierDecodingReadyCalls

/-! Whole decoder with its actual runtime-entry preparation. The code and
input-limit word are the only nonblank inputs; rejected codes never run the
successful restoration or tag-width loops. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Ready
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem endpoint_bit (word fields : List Bool) (limit t s x y : ℕ) (out : State) :
    (endpoint word fields limit t s x y out).scanned 19=
      (Whole.endpoint word fields limit t s x y out).scanned 19 := by
  simp [endpoint,ReadyLayout.output,ReadyCounters.output,RecoveryCalls.stopped,Fin.addCases,Configuration.scanned]

theorem ready_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤budget word.length ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨n,base,hn,hwhole,hh,hout⟩ := Whole.whole_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hwhole.run hh
  have he := TapeEmbedding.run_embed Whole.machine (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 19=Whole.valid word limit := by
    change readTapeBit (r.final.tapes 19) (r.final.heads 19)=_
    rw [hf]
    exact hout.1
  cases hv : Whole.valid word limit with
  | false =>
    have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit.trans hv)
    refine ⟨_,_,?_,hp,?_,?_,by simp [hv]⟩
    · rw [htime]
      dsimp [budget,Whole.budget] at *
      have hpos : 0 < (word.length+1)^2 := by positivity
      omega
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simpa [RecoveryCalls.stopped,Configuration.scanned] using hbit
  | true =>
    obtain ⟨t,s,fields,x,y,hparts,ht,hspos,hgood⟩ := hout.2 hv
    obtain ⟨out,houtcome,hsource,hbits,_⟩ := hgood
    have hfirst : first.final=TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
        (Whole.endpoint word fields limit t s x y out) := by
      change TapeEmbedding.config _ _ r.final=_
      rw [hf,houtcome]
    have hp := call_prefix 0 1 n _ first he (by simp [next]; exact hbit.trans hv)
    rw [hfirst] at hp
    have hseq := (Whole.valid_parts_iff word fields limit t s hparts).mp hv
    have hfit := sequential_countsFit t s fields hseq.2
    have hbound : 2^t*s ≤ word.length := by
      rw [HeaderMachine.parts_decomposition hparts,Nat.mul_comm]
      exact hfit.2.2.2.1
    obtain ⟨m,hm,htail⟩ := success_tail word fields limit t s x y out hparts hbound
    have hall := hp.trans htail
    refine ⟨_,_,?_,hall,?_,?_,?_⟩
    · dsimp [budget,Whole.budget] at *
      nlinarith
    · simp [machine,RecoveryCalls.machine,endpoint,RecoveryCalls.stopped]
    · rw [endpoint_bit]
      rw [←houtcome]
      exact hout.1
    · intro _
      exact ⟨t,s,fields,x,y,out,hparts,ht,hspos,rfl,hbits,hsource⟩

def inputCapacity (word : List Bool) : Fin 21 → ℕ :=
  fun i => Fin.addCases (Whole.inputCapacity word) (fun _ : Fin 1 => 0) i
noncomputable def blankEntry (word : List Bool) (limit : ℕ) :
    Configuration 21 (Fintype.card (RecoveryCalls.Control sizes)) :=
  ⟨machine.start,
    fun i => Fin.addCases (Whole.blankEntry word limit).heads (fun _ : Fin 1 => 0) i,
    fun i => Fin.addCases (Whole.blankEntry word limit).tapes (fun _ : Fin 1 => []) i⟩

theorem whole_blank_padding (word : List Bool) (limit : ℕ) :
    ZeroPadding.config (Whole.inputCapacity word) (Whole.blankEntry word limit)=Whole.initial word limit := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,Whole.inputCapacity,Whole.blankEntry,Whole.initial,
      controlConfig,TapeEmbedding.config,FrontTable.extras,Front.inputCapacity,Front.blankEntry,Front.initial,
      Dimensions.inputCapacity,Dimensions.blankEntry,Dimensions.initial,
      GuardedPreparation.inputCapacity,GuardedPreparation.blankEntry,GuardedPreparation.initial,
      GuardedPreparation.extend,Preparation.initial,Preparation.zeros,Fin.addCases,ZeroPadding.pad]

theorem blank_padding (word : List Bool) (limit : ℕ) :
    ZeroPadding.config (inputCapacity word) (blankEntry word limit)=initial word limit := by
  have hw := whole_blank_padding word limit
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (motive := fun i =>
      (ZeroPadding.config (inputCapacity word) (blankEntry word limit)).heads i=
      (initial word limit).heads i) (fun j : Fin 20 => ?_) (fun j : Fin 1 => ?_) i
    · simpa only [ZeroPadding.config,inputCapacity,blankEntry,initial,controlConfig,
        TapeEmbedding.config,Fin.addCases_left] using congrFun (congrArg Configuration.heads hw) j
    · simp only [ZeroPadding.config,blankEntry,initial,controlConfig,TapeEmbedding.config,Fin.addCases_right]
  · funext i
    refine Fin.addCases (motive := fun i =>
      (ZeroPadding.config (inputCapacity word) (blankEntry word limit)).tapes i=
      (initial word limit).tapes i) (fun j : Fin 20 => ?_) (fun j : Fin 1 => ?_) i
    · simpa only [ZeroPadding.config,inputCapacity,blankEntry,initial,controlConfig,
        TapeEmbedding.config,Fin.addCases_left] using congrFun (congrArg Configuration.tapes hw) j
    · simp [ZeroPadding.config,inputCapacity,blankEntry,initial,controlConfig,TapeEmbedding.config,Fin.addCases]

end NearCubicWires.RepairSource.VerifierDecoding.Ready
