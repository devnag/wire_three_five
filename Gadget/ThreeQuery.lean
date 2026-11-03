import Gadget.Checked

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

/-- The accepted input `(checkedCircuit code D, sysEnc code x)` when `D` accepts `x`. -/
noncomputable def acceptedInput (code : LinearCodeFamily) (D : Circuit) (x : BitInput D.n)
    (h : D.D.eval x = true) : AcceptedCircuitInput :=
  ⟨checkedCircuit code D, ⟨sysEnc code D.n x,
    (checkedCircuit_accepts_iff code D _).2 ⟨by rw [prefixOf_sysEnc]; exact h, by rw [prefixOf_sysEnc]⟩⟩⟩

structure ThreeQueryPCPP where
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_lt_one : gamma < 1
  code : LinearCodeFamily
  output : (C : Circuit) → RawThreeQueryPCPP C.n
  outputPoly : Nonempty (Turing.TM2ComputableInPolyTime (fun C : Circuit => C.word)
    (fun word : List Bool => word) (fun C => (output C).word))
  outputSize : ∃ K e : ℕ, ∀ C : Circuit,
    (output C).proofBits ≤ K * (C.m + 1) ^ e ∧ 2 ^ (output C).randomBits ≤ K * (C.m + 1) ^ e
  honest : (p : AcceptedCircuitInput) → BitInput (output p.1).proofBits
  honestPoly : Nonempty (Turing.TM2ComputableInPolyTime acceptedCircuitInputWord
    (fun word : List Bool => word) (fun p => List.ofFn (honest p)))
  codeLength : ∃ K : ℕ, ∀ n, 2 ≤ n → code.length n ≤ K * (n + 1)
  /-- "a polynomial-time computable linear encoding Enc" (the near-cubic-gates paper). -/
  encPoly : Nonempty (Turing.TM2ComputableInPolyTime messageWord (fun word : List Bool => word)
    (fun p => List.ofFn (code.enc p.1 p.2.val)))
  /-- "If D(x) = 1, an auxiliary assignment computable in polynomial time satisfies every clause." -/
  complete : ∀ (D : Circuit) (x : BitInput D.n) (h : D.D.eval x = true) coins,
    (output (checkedCircuit code D)).accepts (sysEnc code D.n x) (honest (acceptedInput code D x h)) coins = true

  sound : ∀ (D : Circuit) (x : BitInput D.n), 2 ≤ D.n → D.D.eval x = false →
    ∀ proof, (output (checkedCircuit code D)).fraction (sysEnc code D.n x) proof ≤ 1 - (gamma : ℝ)

end NearCubicGates.Close.Gadget
