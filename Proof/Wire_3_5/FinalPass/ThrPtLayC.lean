import Proof.Wire_3_5.FinalPass.ThrPtLayB
import Proof.Wire_3_5.FinalPass.ThrPtPad

/-! # S2 (THR per point), part 11: the row word, lifted exactly (P3:2587-2630)

On the evaluator's layout: **`rowWL_spec`**: the RowW (`DigsBody.rowWImpl`, verified) writes row `(g, p)`'s word
`rowWord p r₀ as ws` on stream `13` from a stream of `k` blank cells (the previous row's word erased): RowW's spec at
`[]` transports exactly by `wexec_pad` (the stream ends as `pad (rowWord …) k`). The payloads are the call's words
`1 … 4` (streams `4 … 7`), RowW's registers `5 … 52` (`R 0 … R 4` = `a`, `g`'s index, `p`, `τ₀`, `0`; with no
carriers the occurrence offset is `0`). Paper quantities: the row's residue `r₀ = −target mod p`, the reduced
coefficients `a_i = w_i mod p`, the digit weights `2^d mod p` (row:radix, P3:2596-2618). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

/-- RowW's payload streams: `4 … 7`. -/
def payS : Fin 4 → Fin 17 := ![4, 5, 6, 7]

/-- RowW's registers: `5 … 52`. -/
def rowR : Fin Digs.digsK ↪ Fin 118 :=
  ⟨fun k => ⟨5 + k.val, by have := k.isLt; unfold Digs.digsK at this; omega⟩, fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only at this; omega)⟩

theorem payS_inj : Function.Injective payS := by decide

theorem payS_ne : ∀ i, payS i ≠ 13 := by decide

variable (cap : ℕ)

theorem padAll_sets_nil (ω : WState 16 118) (k : ℕ) (hk : ω.st 13 = List.replicate k false) :
    padAll (ω.sets 13 []) (fun j => if j = 13 then k else 0) = ω := by
  apply WState.eq
  · rfl
  · funext j
    by_cases h : j = 13
    · subst h; simp [pad_nil, hk]
    · simp [h, pad_zero]
  · rfl
  · rfl

theorem padAll_sets (ω : WState 16 118) (k : ℕ) (l : List Bool) :
    padAll (ω.sets 13 l) (fun j => if j = 13 then k else 0) = ω.sets 13 (pad l k) := by
  apply WState.eq
  · rfl
  · funext j
    by_cases h : j = 13
    · subst h; simp
    · simp [h, pad_zero]
  · rfl
  · rfl

theorem sets_sets' {ns nr : ℕ} (ω : WState ns nr) (i : Fin (ns + 1)) (l l' : List Bool) :
    (ω.sets i l).sets i l' = ω.sets i l' := by
  simp [WState.sets]

theorem rowWL_spec (P : Shared.StarParams) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (alg : RepairRepresentation.DecompositionAlgorithm)
    (den : ℕ) (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
    (k : ℕ) (ω : WState 16 118)
    (hpay : ∀ i : Fin 4, ω.st (payS i) = if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else [])
    (hpayH : ∀ i : Fin 4, ω.sh (payS i) = 0) (hdg : ω.st 13 = List.replicate k false) (hdgH : ω.sh 13 = 0)
    (hvA : ω.val 5 = a') (hvG : ω.val 6 = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)) (hvP : ω.val 7 = pr.val)
    (hvT : ω.val 8 = Primitive.thrDigits P Cs alg den) (hvO : ω.val 9 = 0)
    (hz : ∀ j : Fin Digs.digsK, 5 ≤ j.val → ω.val (rowR j) = 0)
    (hcap : DigsBody.rowWImpl.need (Digs.digsN P Cs [] alg den pr.val) ≤ cap) :
    WExec cap (DigsBody.rowWImpl.prog payS 13 rowR) ω
      (ω.sets 13 (pad (Term.rowWord pr.val (Term.thrR0 P Cs alg g pr.val) (Term.thrCoeffs P Cs alg g pr.val)
        (Term.thrWeights P Cs alg den pr.val)) k))
      (DigsBody.rowWImpl.bound (Digs.digsN P Cs [] alg den pr.val)) := by
  have hin : Digs.DigsIn payS 13 rowR P Cs [] alg den g pr (ω.sets 13 []) := by
    refine ⟨fun i => ?_, fun i => ?_, by simp, by simpa using hdgH, by show ω.val 5 = _; exact hvA,
      by show ω.val 6 = _; exact hvG, by show ω.val 7 = _; exact hvP, by show ω.val 8 = _; exact hvT, ?_, fun j hj => ?_⟩
    · have hne : payS i ≠ 13 := payS_ne i
      simp only [WState.sets_st, Function.update_of_ne hne]
      exact hpay i
    · simpa using hpayH i
    · simp only [WState.sets_val]
      rw [PrimAsm.Records.thrOff_eq]
      show ω.val 9 = _
      simpa using hvO
    · simpa using hz j hj
  have e := DigsBody.rowWImpl.run payS 13 rowR payS_inj payS_ne P ha' Cs [] alg den g pr cap (ω.sets 13 []) hin hcap
  have e2 := wexec_pad e (fun j => if j = 13 then k else 0)
  rw [padAll_sets_nil ω k hdg, sets_sets', padAll_sets] at e2
  exact e2

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
