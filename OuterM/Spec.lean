import Outer.Apply
import Proof.MachineModel.ClockJoin

/-!
# The shared outer-verifier machines: deliverable types

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer): the weak machine "first rejects unless `N = 2^ν`", computes the exact native
width `q(N) = ⌈log₂T_clk(N)⌉ + A_pad⌈log₂(log₂T_clk(N)+2)⌉ + A_pad`, checks that the description of `B_src` has at most
`L_ν` bits, and "constructs `C^O_{⟨B_src⟩_ν}`" with the imported constructor of imp:short-pcp applied to the succinct
verifier of lem:succinct-verifier (whose item (i): `T_G(L_ν)` is computable from `1^ν`). Two machines, shared by the
set-up, the E^NP recovery and the Case 2 producer:

* `WidthDonor`: ordinary word functions from `x` (stream `frame x`) to `frame q.bits` and to `1^q`, `q = q(2^{⌊log₂ N⌋})`
  (`qOf`; equal to `Outer.width` at every `N = 2^ν`, `qOf_two_pow`), within `K·(N+1)` steps (exponent `1`, independent
  of every parameter: the set-up's cost exponent is fixed before the clock, `Setup.SetupU`).
* `ARun`: one machine with input ports `dIn` (the RAW descriptor `PCPPNative.descriptor B`, as proof 1's cold decoder
  leaves it) and `nIn` (`1^ν`) and output ports `fOut` (`[decide (SrcFits G ν B)]`, the guarded length walk: it never
  reads past cell `L_ν` of the descriptor) and `wOut` (the RAW word of `C^O_{⟨B⟩_ν}`, i.e. `(Outer.outC mw SV ν B).word`,
  exactly as the composite's port `cIn` takes it), within `K·(ν+1)^e` steps for every `B` (independent of `|B|`).
  The A-run is: the guarded walk → `⟨B⟩_ν` (the first `L_ν` descriptor cells, zero padded) → `T_G(L_ν)` in binary by
  `SV.timeWord` → the imported constructor `(Outer.alg mw SV).constructor` on `frame ⟨B⟩_ν ++ frame T_G(L_ν).bits`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

instance srcFitsDecidable (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Decidable (Outer.SrcFits G ν B) := by
  unfold Outer.SrcFits
  infer_instance

section
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G)

/-- The native width at the largest power of two `2^{⌊log₂ N⌋} ≤ N` (the near-cubic-gates paper's fixed weak machine: the weak machine rejects unless
`N = 2^ν`, so only `N = 2^ν` matters; at every other length the donor is still total and exact for this value). -/
noncomputable def qOf (N : ℕ) : ℕ := Outer.width mw SV (2 ^ Nat.log 2 N)

/-- At `N = 2^ν`, `qOf` is the native width `q(N)`. -/
theorem qOf_two_pow (ν : ℕ) : qOf mw SV (2 ^ ν) = Outer.width mw SV (2 ^ ν) := by
  unfold qOf
  rw [Nat.log_pow (by norm_num)]

/-- **the width donor** (the near-cubic-gates paper's fixed weak machine, "the exact native width `q(N)`"): from `x` to `frame q.bits` and to
`1^q`, `q = qOf N`, within `K·(N+1)` steps. -/
structure WidthDonor where
  K : ℕ
  /-- `q` in binary, framed (the schedule's and the cold decoder's form). -/
  word : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => RepairOrdinary.frame (qOf mw SV r.1).bits) (fun r => K * (r.1 + 1) ^ 1)
  /-- `q` in unary (the ports `1^q` of the GR prefix and the Case 1/Case 2 machines). -/
  unary : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => List.replicate (qOf mw SV r.1) true) (fun r => K * (r.1 + 1) ^ 1)

/-- The A-run's input bank: the raw descriptor of `B` on `dIn`, `1^ν` on `nIn`, every other tape empty. -/
def aBank {t : ℕ} (dIn nIn : Fin t) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Fin t → List Bool :=
  fun j => if j = dIn then PCPPNative.descriptor B else if j = nIn then List.replicate ν true else []

/-- **the A-run** (the near-cubic-gates paper's fixed weak machine, "It constructs `C^O_{⟨B_src⟩_ν}`", the guard "description of at most
`L_ν` bits"; lem:succinct-verifier (i), "`T_G` is computable"): one machine, every `ν` and every circuit `B`; the
descriptor and `1^ν` are left intact. -/
structure ARun where
  t : ℕ
  st : ℕ
  M : Machine t st
  dIn : Fin t
  nIn : Fin t
  fOut : Fin t
  wOut : Fin t
  nodup : [dIn, nIn, fOut, wOut].Nodup
  K : ℕ
  e : ℕ
  run : ∀ (ν m : ℕ) (B : BooleanCircuit m), ∃ out,
    ClockJoin.ReadyRun M (K * (ν + 1) ^ e) (aBank dIn nIn ν B) out ∧
      out dIn = PCPPNative.descriptor B ∧ out nIn = List.replicate ν true ∧
      out fOut = [decide (Outer.SrcFits G ν B)] ∧
      out wOut = (Outer.outC mw SV ν B).word

end

end NearCubicGates.Close.OuterM
