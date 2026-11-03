import Proof.MachineModel.Round
import Proof.PCP.PCPPQueryNatural

/-! Parse the actual occurrence header in the existing natural reader.
Only its nine private tapes have C backing; source and produced template are exact. -/
namespace PCJ45bee56da9f34d5a_PreludeNatural
open NearCubicWires NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 11) := if i=0 ∨ i=10 then 0 else C
def input (C : ℕ) (source : List Bool) (i : Fin 11) : List Bool :=
  if i=0 then source else if i=10 then [] else List.replicate C false
def heads (n : ℕ) (i : Fin 11) := if i=0 then (natWord n).length else if i=10 then 1 else 0
def selected (i : Fin 11) : Bool := decide (i≠0 ∧ i≠10)
noncomputable def machine := MaskedReset.machine PCPPQueryNatural.machine selected

theorem padded_run (C n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    ∃ (H : Fin 11 → ℕ) (A : Fin 11 → List Bool),
      Step PCPPQueryNatural.machine (PCPPQueryNatural.budget n) (fun _ => 0)
        (input C (natWord n++tail)) H A ∧
      H 0=(natWord n).length ∧ A 0=natWord n++tail ∧ H 10=1 ∧ A 10=UnaryTemplate.tape n ∧
      ∀ i,i≠0 → i≠10 → (A i).length=C := by
  obtain ⟨r,hr,hs,src,pos,drv,dh⟩ := PCPPQueryNatural.natural_run [] tail n
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr src pos
  have hi : PCPPQueryNatural.entry (natWord n++tail) 0 =
      (⟨PCPPQueryNatural.machine.start,fun _ => 0,fun i => if i=0 then natWord n++tail else []⟩ :
        Configuration 11 PCPPQueryNatural.states) := by
    apply configuration_ext
    · rfl
    · funext i;simp [PCPPQueryNatural.entry]
    · rfl
  rw [hi] at hr
  have raw : Step PCPPQueryNatural.machine (PCPPQueryNatural.budget n) (fun _ => 0)
      (fun i => if i=0 then natWord n++tail else []) r.final.heads r.final.tapes :=
    ⟨r,hr,rfl,rfl,hs⟩
  let A := fun i => ZeroPadding.pad (caps C i) (r.final.tapes i)
  have run := raw.pad (caps C)
  have initial : (fun i => ZeroPadding.pad (caps C i) (if i=0 then natWord n++tail else [])) =
      input C (natWord n++tail) := by
    funext i
    by_cases h0 : i=0
    · subst i;simp [caps,input,ZeroPadding.pad_zero]
    by_cases h10 : i=10
    · subst i;simp [caps,input,ZeroPadding.pad_zero]
    · simp [caps,input,h0,h10,ZeroPadding.pad]
  rw [initial] at run
  refine ⟨r.final.heads,A,run,?_,?_,dh,?_,?_⟩
  · rw [DecompositionSource.natWord_length];exact pos
  · change ZeroPadding.pad 0 (r.final.tapes 0) = _
    rw [ZeroPadding.pad_zero,src]
  · change ZeroPadding.pad 0 (r.final.tapes 10) = _
    rw [ZeroPadding.pad_zero,drv]
  · intro i h0 h10
    obtain ⟨p,pr,_ph,pt,_ps⟩ := run
    have hfit : (⟨PCPPQueryNatural.machine.start,fun _ => 0,input C (natWord n++tail)⟩ :
        Configuration 11 PCPPQueryNatural.states).heads i+PCPPQueryNatural.budget n <
        (input C (natWord n++tail) i).length := by
      simpa only [input,if_neg h0,if_neg h10,List.length_replicate,Nat.zero_add] using hC
    have bound := length_preserved PCPPQueryNatural.machine _ _ p i pr hfit
    rw [pt] at bound
    change (A i).length=(input C (natWord n++tail) i).length at bound
    simpa only [input,if_neg h0,if_neg h10,List.length_replicate] using bound

theorem masked_run (C n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    ∃ A : Fin 11 → List Bool,
      Step machine (2*PCPPQueryNatural.budget n+2)
        (Fin.addCases (fun _ : Fin 11 => 0) (fun _ : Fin 1 => 0))
        (Fin.addCases (input C (natWord n++tail)) (fun _ : Fin 1 => List.replicate C false))
        (Fin.addCases (heads n) (fun _ : Fin 1 => 0))
        (Fin.addCases A (fun _ : Fin 1 => List.replicate C false)) ∧
      A 0=natWord n++tail ∧ A 10=UnaryTemplate.tape n ∧
      ∀ i,i≠0 → i≠10 → (A i).length=C := by
  obtain ⟨H,A,run,h0,a0,h10,a10,hlen⟩ := padded_run C n tail hC
  have masked := run.mask selected (by intros;rfl) hC.le
  refine ⟨A,?_,a0,a10,hlen⟩
  apply masked.congr _ rfl
  have he : (fun i => if selected i then 0 else H i) = heads n := by
    funext i
    by_cases hi : i=0
    · subst i;simp [selected,heads,h0]
    by_cases hj : i=10
    · subst i;simp [selected,heads,h10]
    · simp [selected,heads,hi,hj]
  rw [he]

end PCJ45bee56da9f34d5a_PreludeNatural
