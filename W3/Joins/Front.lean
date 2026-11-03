import W3.Joins.Cases
import Proof.CaseAnalysis.CaseTwoNativeSourceDock

set_option autoImplicit false
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close.Outer

namespace W3.NearCubicWires.RepairSource.Outer3

/-- The front end's entry bank: `frame z` on `zIn`, the native descriptors of `B_src` and `B_pf` on `sIn`, `pIn`,
every other tape empty. -/
def frontBank (t : ℕ) (zIn sIn pIn : Fin t) (z s p : List Bool) : Fin t → List Bool :=
  fun i => if i = zIn then RepairOrdinary.frame z else if i = sIn then s else if i = pIn then p else []

/-- The guard decided on the flag tape: the description-length bound `λ_ν` (`SrcFits`) and the check (C.10.0). -/
def Guard (G ν : ℕ) (z : BitInput (2 ^ ν)) {q : ℕ} (B : OuterGuess q) : Prop :=
  SrcFits G ν B.src ∧ Check ν z B.src

instance (G ν : ℕ) (z : BitInput (2 ^ ν)) {q : ℕ} (B : OuterGuess q) : Decidable (Guard G ν z B) := by
  unfold Guard SrcFits; infer_instance

/-- **JF `FrontSpecD`.** One machine; from `frame z`, `⟨B_src⟩`, `⟨B_pf⟩` it reaches a ready run within
`K·(N+1)^2·(|⟨B_src⟩| + |⟨B_pf⟩| + q + 1)^e` steps (`N = 2^ν`; d_chk = 2), its flag reads `[decide (Guard …)]`, and when
the guard holds the `field` port holds `frame (descriptor H_B)` and the `size`/`arity` ports hold `|H_B|` and `q` in
unary. -/
structure FrontSpecD (mw : MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
    (SV : SuccinctVerifier H G) where
  t : ℕ
  st : ℕ
  M : Machine t st
  zIn : Fin t
  sIn : Fin t
  pIn : Fin t
  field : Fin t
  sizeSlot : Fin t
  aritySlot : Fin t
  flag : Fin t
  inputs_nodup : [zIn, sIn, pIn].Nodup
  fs : field ≠ sizeSlot
  fa : field ≠ aritySlot
  sa : sizeSlot ≠ aritySlot
  K : ℕ
  e : ℕ
  onset : ℕ
  run : ∀ (ν : ℕ) (z : BitInput (2 ^ ν)) (B : OuterGuess (width mw SV (2 ^ ν))), 1 ≤ ν → onset ≤ ν →
    let c := (Dat mw SV ν B).D
    ∃ out, ClockJoin.ReadyRun M (K * (2 ^ ν + 1) ^ 2 * ((PCPPNative.descriptor B.src).length +
        (PCPPNative.descriptor B.pf).length + width mw SV (2 ^ ν) + 1) ^ e)
        (frontBank t zIn sIn pIn (List.ofFn z) (PCPPNative.descriptor B.src) (PCPPNative.descriptor B.pf)) out ∧
      out flag = [decide (Guard G ν z B)] ∧
      (Guard G ν z B →
        out field = RepairOrdinary.frame (PCPPNative.descriptor c) ∧
        out sizeSlot = List.replicate c.size true ∧
        out aritySlot = List.replicate (width mw SV (2 ^ ν)) true)

end W3.NearCubicWires.RepairSource.Outer3
