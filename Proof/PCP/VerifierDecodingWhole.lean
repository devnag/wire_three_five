import Proof.PCP.VerifierDecodingWholeTable

/-! Whole all-input guarded decoder from the physical code/limit inputs and
blank work tapes. Each dependent loop follows its actual successful guard. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Whole
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Outcome (word : List Bool) (limit : ℕ)
    (final : Configuration 20 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 19=valid word limit ∧
    (valid word limit=true → ∃ t s fields x y,
      HeaderMachine.parts word=some (t,s,fields) ∧ 2≤t ∧ 0<s ∧
      Success word fields limit t s x y final)

theorem whole_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤budget word.length ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨n,base,hn,hfront,hh,hout⟩ := Front.front_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hfront.run hh
  have he := TapeEmbedding.run_embed Front.machine (fun _ : Fin 6 => 0)
    (FrontTable.extras word.length) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 6 => 0) (FrontTable.extras word.length) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 12=Front.valid word limit := by
    change readTapeBit (r.final.tapes 12) (r.final.heads 12)=_
    rw [hf]
    exact hout.1
  cases hv : Front.valid word limit with
  | false =>
    have hp := call_prefix 0 4 n _ first he (by simp [next]; exact hbit.trans hv)
    have hall := hp.trans (reject_tail first.final.heads first.final.tapes)
    refine ⟨_,_,?_,hall,?_,?_,by simp [valid,hv]⟩
    · dsimp [budget,Front.budget] at *
      nlinarith
    · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
    · simpa [valid,hv] using rejected_bit first.final.heads first.final.tapes
  | true =>
    obtain ⟨t,s,fields,x,y,hparts,ht,hspos,hendpoint⟩ := hout.2 hv
    have hlen := GuardedPreparation.parts_lengths hparts
    have hfirst : first.final=FrontTable.front word fields limit t s x y := by
      change TapeEmbedding.config _ _ r.final=_
      rw [hf,hendpoint]
      rfl
    have hp := call_prefix 0 1 n _ first he (by simp [next]; exact hbit.trans hv)
    rw [hfirst] at hp
    have hc : GuardedPreparation.valid word limit=true ∧ StartFlags.valid fields (Front.bound s) s=true := by
      simpa [Front.valid,hparts] using hv
    obtain ⟨m,final,hm,htail,hhalt,hfinal,hgood⟩ := guard_tail word fields limit t s x y hparts ht hspos hc.2
    have hall := hp.trans htail
    refine ⟨_,final,?_,hall,hhalt,?_,?_⟩
    · dsimp [budget,Front.budget] at *
      nlinarith
    · simpa [valid,hv,hparts] using hfinal
    · intro hvalid
      exact ⟨t,s,fields,x,y,hparts,ht,hspos,hgood (by simpa [valid,hv,hparts] using hvalid)⟩

def inputCapacity (word : List Bool) : Fin 20 → ℕ :=
  fun i => Fin.addCases (Front.inputCapacity word) ![word.length+2,word.length+2,word.length+2,1,0,1] i
noncomputable def blankEntry (word : List Bool) (limit : ℕ) :
    Configuration 20 (Fintype.card (RecoveryCalls.Control sizes)) :=
  ⟨machine.start,
    fun i => Fin.addCases (Front.blankEntry word limit).heads (fun _ : Fin 6 => 0) i,
    fun i => Fin.addCases (Front.blankEntry word limit).tapes (fun _ : Fin 6 => []) i⟩

end NearCubicWires.RepairSource.VerifierDecoding.Whole
