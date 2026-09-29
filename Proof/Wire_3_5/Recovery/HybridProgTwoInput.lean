import Proof.Wire_3_5.Recovery.HybridProgTwoAliases

/-! # The hybrid `E^NP` program: TwoInput (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramTwoInput`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: Match the five literal Case2 input words and empty work at its actual shared-bank boundary. The sixth shared port is its initially empty result.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose CloseoutLanguage
set_option autoImplicit false
noncomputable section

def twoInput (p : Parameters) (word description address : List Bool) (R B : ℕ) : Fin (tn p)→List Bool:=
  HDirect.input (WireExponent3_5.Transfer.gateSource p.l) (WireExponent3_5.Transfer.gatePCPP p.l) p.kclk (WireExponent3_5.Transfer.recDG p.l)
    word description address R B

theorem two_local_first (p : Parameters) (j : Fin 5) :
    twoLocal p (j.castAdd 1)=HDirect.ports (WireExponent3_5.Transfer.gateSource p.l) (WireExponent3_5.Transfer.gatePCPP p.l) p.kclk (WireExponent3_5.Transfer.recDG p.l) j:=Fin.addCases_left j

theorem two_input_fields (p : Parameters) (word description address : List Bool) (R B : ℕ) (j : Fin 5) :
    twoInput p word description address R B (twoLocal p (j.castAdd 1))=
      CloseoutCaseTwo.DirectInput.words word description address R B j:=by
  exact (congrArg (twoInput p word description address R B) (two_local_first p j)).trans
    (HDirect.input_port (WireExponent3_5.Transfer.gateSource p.l) (WireExponent3_5.Transfer.gatePCPP p.l) p.kclk (WireExponent3_5.Transfer.recDG p.l)
      word description address R B j)

theorem two_input_empty (p : Parameters) (word description address : List Bool) (R B : ℕ)
    (i : Fin (tn p)) (hi : ∀ j,twoLocal p j≠i) : twoInput p word description address R B i=[]:=by
  have hb : 5 ≤ i.val:=by
    by_contra! hb
    exact hi ((⟨i.val,hb⟩ : Fin 5).castAdd 1)
      ((two_local_first p ⟨i.val,hb⟩).trans (Fin.ext rfl))
  exact HDirect.input_empty (WireExponent3_5.Transfer.gateSource p.l) (WireExponent3_5.Transfer.gatePCPP p.l) p.kclk (WireExponent3_5.Transfer.recDG p.l)
    word description address R B i hb

theorem two_input_output (p : Parameters) (word description address : List Bool) (R B : ℕ) :
    twoInput p word description address R B (twoLocal p 5)=[]:=by
  exact HDirect.input_empty (WireExponent3_5.Transfer.gateSource p.l) (WireExponent3_5.Transfer.gatePCPP p.l) p.kclk (WireExponent3_5.Transfer.recDG p.l) word description address R B _
    (HDirect.output_large _ _ _ _)

theorem two_entry (p : Parameters) (word description address : List Bool) (R B : ℕ)
    (A : Fin (tapes p)→List Bool)
    (fields : ∀ j,A (((twoShared p j).castAdd (tn p)).castAdd 2)=
      twoInput p word description address R B (twoLocal p j))
    (fresh : ∀ i : Fin (tn p),A ((i.natAdd (n3 p)).castAdd 2)=[]) (i : Fin (tn p)) :
    A (twoSlot p i)=twoInput p word description address R B i:=by
  exact CloseoutCommonPortBank.input_at (twoLocal p) (twoShared p)
    (fun z=>A (z.castAdd 2)) (twoInput p word description address R B) fields fresh
    (two_input_empty p word description address R B) i

theorem two_entry_heads (p : Parameters) (H : Fin (tapes p)→ℕ)
    (fields : ∀ j,H (((twoShared p j).castAdd (tn p)).castAdd 2)=0)
    (fresh : ∀ i : Fin (tn p),H ((i.natAdd (n3 p)).castAdd 2)=0) (i : Fin (tn p)) :
    H (twoSlot p i)=0:=by
  cases hp : RecoveryFocus.pick (twoLocal p) i with
  | none =>simp only [twoSlot,twoBank,CloseoutCommonPortBank.slot,hp,fresh]
  | some j =>simpa only [twoSlot,twoBank,CloseoutCommonPortBank.slot,hp] using fields j

end
end NearCubicWires.RepairSource.HybridProgram
