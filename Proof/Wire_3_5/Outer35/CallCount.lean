import Lean
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.Transfer.TransferUnionSound
import Outer.Size
import Proof.Wire_3_5.UnionMachine.UnionCallCountBase


/-!
# The size of `H_Γ` and the number of primitive calls (paper v2, Lemma H.7(b), (58))

Paper v2, Lemma H.7(b): "Put `e_H = (G'+1)e_C + G + 1` [...] `H_Γ` is a circuit on `q` inputs of size at most `q^{e_H}`",
with the proof "Here `n = λ_a ≤ q^{G'}` and `log₂ T_G(λ_a) ≤ q` [...] so `C^O` has size at most `q^{(G'+1)e_C}`. Each oracle
gate becomes a copy of `Γ_pf`, with at most `q^G` gates"; and the clause count "the branch-independent integer `d_G = a_p
e_H` bounds all PCPP clause counts by `(q+2)^{d_G}`" ((58)).

* **`hsize_le`**: at any union setup whose size cap lies below `(w+1)^G`, every guess passing the outer step's guards
  (`UnionGuards`: `N = 2^a` past the onset, `Γ_pf` within `q^G` gates) has `|H_Γ| + 1 ≤ K (q+1)^{e_H}`, with
  `e_H = (lenG + 3)·e_C + G + 1` (`lenG + 2 = G'`, the instance length `λ_a = a^{lenG+2}`), `e_C` the short PCP's size
  exponent at `𝒱_G` (`Outer.alg`), from `Outer.Dat_size_le`, `Outer.outC_size_le` and `Outer.natBitLength_T_le`;
* **`calls_le_of`**: every such guess schedules at most `q(N)^{5 e_H d_a + 1}` primitive calls, eventually in `N`
  (`length_schedule_le`, `#calls ≤ 24K(1+2K(s+1))⁴`, `K = c_a(|H_Γ|+1)^{d_a}`; the grid law absorbs `(s+1)⁴`).

Paper quantity of the main types: `|H_Γ|` against `q^{e_H}`, and the number of scheduled primitive calls against
`q(N)^{unionCallDeg}`.
-/


set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicGates.Close
open Filter

section Generic
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- The exponent `e_H` of `|H_Γ|` at a setup whose size cap lies below `(w+1)^G`. -/
noncomputable def eHS (S : UnionSetup I) (Gc : ℕ) : ℕ := (S.lenG + 3) * (Outer.alg S.mw S.SV).sizeExp + Gc + 1

/-- **Lemma H.7(b)** at a pair: at `N = 2^a` past the onset, `Γ_pf` within the size cap, `|H_Γ| + 1 ≤ K (q+1)^{e_H}`. -/
theorem hsize_pair (S : UnionSetup I) (Gc : ℕ) (hcap : ∀ o w, o ≤ oracleSizeBound S.G w → o + 1 ≤ (w + 1) ^ Gc) :
    ∃ Ks : ℕ, ∀ N (z : BitInput N) (Γ : Outer.OuterGuess (S.width N)), N = 2 ^ Nat.log 2 N →
      S.onset ≤ Nat.log 2 N → Γ.pf.size ≤ oracleSizeBound S.G (S.width N) →
      (S.request z Γ).circuit.size + 1 ≤ Ks * (S.width N + 1) ^ eHS S Gc := by
  obtain ⟨M, hM⟩ := Outer.natBitLength_T_le S.SV
  set eC := (Outer.alg S.mw S.SV).sizeExp with heC
  set cA := (Outer.alg S.mw S.SV).coefficient with hcA
  refine ⟨cA * (M + kclk + 4) ^ eC + 3, fun N z g hN hon hpf => ?_⟩
  have hmin : S.pcppAlg.minimumArity ≤ Outer.width S.mw S.SV N := by
    have h := S.onset_arity (Nat.log 2 N) hon
    rwa [← hN] at h
  set ν := Nat.log 2 N with hν
  have hν1 : 1 ≤ ν := S.onset_pos.trans hon
  have hνq : ν ≤ S.width N := Outer.log_le_width S.mw S.SV N
  -- the circuit is `H_Γ`
  have hreq : (S.request z g).circuit.size = (Outer.Dat S.mw S.SV ν g).D.size := by
    unfold UnionSetup.request
    rw [W3.NearCubicWires.RepairSource.Outer3.requestAt_of S.mw S.SV S.pcppAlg ν g hmin]
    rfl
  rw [hreq]
  have hD := Outer.Dat_size_le S.mw S.SV ν g
  have hC := Outer.outC_size_le S.mw S.SV ν hν1 g.src
  have hpf1 := hcap _ _ hpf
  have hD0 : (Outer.Dat S.mw S.SV ν g).D.size ≤
      (Outer.outC S.mw S.SV ν g.src).circuit.size * (g.pf.size + 1) + S.width N + 2 := hD
  clear hD
  generalize (Outer.Dat S.mw S.SV ν g).D.size = Dsz at hD0 ⊢
  generalize (Outer.outC S.mw S.SV ν g.src).circuit.size = Cs at hD0 hC
  generalize g.pf.size = Pf at hD0 hpf1
  clear hpf
  clear_value ν
  generalize hqd : S.width N = q at hνq hpf1 hD0 ⊢
  have hT := hM ν
  -- the instance `⟨Γ_src⟩_a`, `log₂ T_G` and `C^O` in powers of `q + 1`
  have hq1 : 1 ≤ q + 1 := by omega
  have hX : 1 ≤ (q + 1) ^ (S.lenG + 2) := Nat.one_le_pow _ _ hq1
  have hlam : Outer.instLength S.lenG ν ≤ (q + 1) ^ (S.lenG + 2) := by
    unfold Outer.instLength; exact Nat.pow_le_pow_left (by omega) _
  have hlin : q + 1 ≤ (q + 1) ^ (S.lenG + 2) := Nat.le_self_pow (by omega) _
  have hin : Outer.instLength S.lenG ν + natBitLength (S.SV.T (Outer.instLength S.lenG ν)) + 1 ≤
      (M + kclk + 4) * (q + 1) ^ (S.lenG + 2) := by nlinarith
  have hC2 : Cs ≤ cA * ((M + kclk + 4) ^ eC * (q + 1) ^ ((S.lenG + 2) * eC)) := by
    refine hC.trans (Nat.mul_le_mul_left _ ?_)
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left hin _
  -- the substitution
  set Y := (q + 1) ^ ((S.lenG + 2) * eC) with hY
  set Z := (q + 1) ^ Gc with hZ
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ hq1
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ hq1
  have hYZ : Y * Z ≤ (q + 1) ^ eHS S Gc := by
    rw [hY, hZ, ← pow_add]; exact Nat.pow_le_pow_right hq1 (by unfold eHS; nlinarith)
  have hq3 : q + 3 ≤ 3 * (q + 1) ^ eHS S Gc := by
    have : q + 1 ≤ (q + 1) ^ eHS S Gc := Nat.le_self_pow (by unfold eHS; omega) _
    omega
  have hCpf : Cs * (Pf + 1) ≤ cA * (M + kclk + 4) ^ eC * (Y * Z) := by
    calc Cs * (Pf + 1)
        ≤ (cA * ((M + kclk + 4) ^ eC * Y)) * Z := Nat.mul_le_mul hC2 hpf1
      _ = cA * (M + kclk + 4) ^ eC * (Y * Z) := by ring
  have h5 : cA * (M + kclk + 4) ^ eC * (Y * Z) ≤ cA * (M + kclk + 4) ^ eC * (q + 1) ^ eHS S Gc :=
    Nat.mul_le_mul_left _ hYZ
  have e : (cA * (M + kclk + 4) ^ eC + 3) * (q + 1) ^ eHS S Gc =
      cA * (M + kclk + 4) ^ eC * (q + 1) ^ eHS S Gc + 3 * (q + 1) ^ eHS S Gc := by ring
  omega

/-- **Lemma H.7(b)**: `|H_Γ| + 1 ≤ K (q+1)^{e_H}` for every guess passing the outer step's guards. -/
theorem hsize_le (S : UnionSetup I) (Gc : ℕ) (hcap : ∀ o w, o ≤ oracleSizeBound S.G w → o + 1 ≤ (w + 1) ^ Gc) :
    ∃ Ks : ℕ, ∀ N (z : BitInput N) (g : UnionGuess S z), UnionGuards S z g →
      (S.request z g.pair).circuit.size + 1 ≤ Ks * (g.q + 1) ^ eHS S Gc := by
  obtain ⟨Ks, h⟩ := hsize_pair S Gc hcap
  refine ⟨Ks, fun N z g hg => ?_⟩
  obtain ⟨-, hN, hon, -, hpf, -, -⟩ := hg
  rw [q_eq_width S g hN hon]
  exact h N z g.pair hN hon hpf

/-- **The call count** (Lemma H.7(b) and (58)): eventually in `N`, every guess passing the outer step's guards
schedules at most `q(N)^{5 e_H d_a + 1}` primitive calls. -/
theorem calls_le_of (S : UnionSetup I) (Gc : ℕ) (hcap : ∀ o w, o ≤ oracleSizeBound S.G w → o + 1 ≤ (w + 1) ^ Gc)
    (qN : ℕ → ℕ) (hqN : Tendsto qN atTop atTop) (Csp : ℕ) (hsp : ∀ q, S.gridSize q ^ 8 ≤ Csp * Lq q ^ 3)
    (hw : ∀ᶠ N in atTop, S.width N = qN N) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess S z), UnionGuards S z g → ∀ tr : List ℕ,
      (g.checkData tr).schedule.length ≤ qN N ^ (5 * eHS S Gc * S.pcppAlg.degree + 1) := by
  obtain ⟨Ks, hKs⟩ := hsize_le S Gc hcap
  set σ := eHS S Gc with hσ
  set d := S.pcppAlg.degree with hd
  set K₀ := S.pcppAlg.coefficient * Ks ^ d with hK₀
  set C := 24 * K₀ * (1 + 2 * K₀) ^ 4 with hC
  filter_upwards [hw, hqN.eventually (eventually_calls C (σ * d * 5) Csp S.gridSize hsp)] with N hwN hbig
  intro z g hg tr
  have hq : g.q = qN N := by rw [q_eq_width S g hg.2.1 hg.2.2.1, hwN]
  have hsz := hKs N z g hg
  rw [hq] at hsz
  have hK : S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ d ≤ K₀ * ((qN N + 1) ^ (σ * d)) := by
    calc S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ d
        ≤ S.pcppAlg.coefficient * (Ks * (qN N + 1) ^ σ) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz d)
      _ = K₀ * (qN N + 1) ^ (σ * d) := by rw [hK₀, mul_pow, ← pow_mul]; ring
  have hX : 1 ≤ (qN N + 1) ^ (σ * d) := Nat.one_le_pow _ _ (by omega)
  have hs : g.s = S.gridSize (qN N) := by
    show S.gridSize g.q = S.gridSize (qN N)
    rw [hq]
  have hlen := length_schedule_le g tr
  have har := count_arith _ K₀ _ g.s hK hX
  rw [hs] at har
  calc (g.checkData tr).schedule.length ≤ _ := hlen
    _ ≤ C * ((qN N + 1) ^ (σ * d)) ^ 5 * (S.gridSize (qN N) + 1) ^ 4 := by rw [hs]; exact har
    _ = C * (qN N + 1) ^ (σ * d * 5) * (S.gridSize (qN N) + 1) ^ 4 := by rw [← pow_mul]
    _ ≤ qN N ^ (σ * d * 5 + 1) := hbig
    _ = qN N ^ (5 * σ * d + 1) := by ring_nf

end Generic

end NearCubicWires.WireExponent3_5.Transfer.UnionCallCount

