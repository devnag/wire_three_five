import Proof.CaseAnalysis.RowsRawPolynomialSkip

/-! A raw variable block drives selection in the already-produced atom
cache. The actual prefix polynomials are scanned once, with no numeric
index conversion, count prepass, or discarded output. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (ip cp : ℕ) : Fin 2→ℕ:=![ip,cp]
def data (index cache : List Bool) : Fin 2→List Bool:=![index,cache]
def slots : Fin 1→Fin 2:=fun _=>1
noncomputable def skip:=RecoveryFocus.machine slots CloseoutRowsRawPolynomialSkip.machine
def advance : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.right,.stay]⟩ else none
noncomputable def body:=Composition.machine skip advance
def idle : Machine 2 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,6]
noncomputable def programs : (i : Fin 2)→Machine 2 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>body
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 2→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def loop:=RecoveryCalls.machine sizes programs 0 next
def cacheWord (ps : List (List (List ℕ))):=ps.flatMap ExtIncidence.stream
noncomputable def machine:=Composition.machine (Composition.machine advance loop) advance

theorem advance_run (ip cp : ℕ) (index cache : List Bool) :
    Step advance 1 (heads ip cp) (data index cache) (heads (ip+1) cp) (data index cache) := by
  have hs:step advance ⟨0,heads ip cp,data index cache⟩=
      some ⟨1,heads (ip+1) cp,data index cache⟩:=by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem skip_run (ip : ℕ) (index pre tail : List Bool) (p : List (List ℕ)) :
    Step skip (ExtIncidence.stream p).length (heads ip pre.length)
      (data index (pre++ExtIncidence.stream p++tail))
      (heads ip (pre.length+(ExtIncidence.stream p).length))
      (data index (pre++ExtIncidence.stream p++tail)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawPolynomialSkip.skip_run p pre tail
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock slots (by decide)
    CloseoutRowsRawPolynomialSkip.machine _ (heads ip pre.length)
    (data index (pre++ExtIncidence.stream p++tail)) _
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl) raw hr
  have other:=keep 0 (by intro i;fin_cases i;decide)
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact other.1
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
  · funext i;fin_cases i
    · exact other.2
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
