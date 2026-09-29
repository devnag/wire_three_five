import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.FinalPass.DigsFinal

/-! # RADIX, stage 2: the digit populations on the setup's cell (P3:2596-2599)

C1's verified digit program `DigsBody.digsWImpl : Digs.DigsW` runs on the RADIX setup's entry `RsIn4`: its payload
streams are `133 … 136` (`sPayK`), its output is stream `137` (**`dgK`**), its register block **`dR`** puts `a'`
(`432`), the selection's index (`410`), `p` (`411`), `τ₀` (`422`) and `oOff` (`415`) in `0 … 4` and its scratch on
`445 … 487` (zero at the entry). **`digs_run`**: from `RsIn4` it writes `digsWord` of row `(g, p)`'s digit populations
on `137` and changes nothing else.

Paper quantity of the main type: the digit populations `v_{i,d}` of row `(g, p)` (P3:2598-2599). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadDigs
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass

/-- The digit program's register values. -/
def dRv (j : ℕ) : ℕ :=
  if j = 0 then 432 else if j = 1 then 410 else if j = 2 then 411 else if j = 3 then 422 else if j = 4 then 415
  else 440 + j

/-- **The digit program's register block**: `a'`, the index, `p`, `τ₀`, `oOff` in `0 … 4`; scratch `445 … 487`. -/
def dR : Fin 48 ↪ Fin LNR :=
  ⟨fun j => ⟨dRv j.val, by have := j.isLt; unfold dRv LNR; split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    apply Fin.ext
    unfold dRv at h
    split_ifs at h <;> omega⟩

theorem dR_val (j : Fin 48) : (dR j).val = dRv j.val := rfl

/-- The digit word's stream. -/
def dgK : Fin 161 := 137

/-- The payload streams on the cell. -/
def dPay (x : ℕ) : Fin 4 → Fin (LNS x + 1) := fun i => sk x (sPayK i)

/-- **The digit program on the setup's cell.** -/
noncomputable def digsP (x : ℕ) : WM (LNS x) LNR := DigsBody.digsWImpl.prog (dPay x) (sk x dgK) dR

theorem dPay_inj (x : ℕ) : Function.Injective (dPay x) := by
  intro a b h
  have h1 := congrArg Fin.val (sk_inj x h)
  simp only [sPayK] at h1
  exact Fin.ext (by omega)

theorem dPay_ne (x : ℕ) (i : Fin 4) : dPay x i ≠ sk x dgK := by
  intro h
  have h1 := congrArg Fin.val (sk_inj x h)
  simp only [sPayK, dgK] at h1
  have := i.isLt
  simp at h1
  omega

/-- **Stage 2, run**: from the setup's entry `RsIn4` (the payloads of `Cs`, `a'`, and in `410 …` the values `v` with the
index, `p`, `oOff` and `τ₀` in `v 0`, `v 1`, `v 5`, `v 12`), the digit program writes `digsWord` of row `(g, p)`'s
digit populations on `137` and changes nothing else. -/
theorem digs_run {x : ℕ} (P : StarParams) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (cap : ℕ)
    (σ : WState (LNS x) LNR) {w out : List Bool} {j : ℕ} {u : List Bool} {v : Fin 20 → ℕ} {prW winW modW : List Bool}
    {ncar capT : ℕ}
    (hin : RsIn4 x σ w out j u v prW winW modW ncar capT
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) a')
    (hv0 : v 0 = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)) (hv1 : v 1 = pr.val)
    (hv5 : v 5 = PrimAsm.Records.thrOff P Cs carriers) (hv12 : v 12 = Primitive.thrDigits P Cs alg den)
    (hneed : DigsBody.digsWImpl.need (Digs.digsN P Cs carriers alg den pr.val) ≤ cap) :
    WExec cap (digsP x) σ
      (σ.sets (sk x dgK) (Digs.digsWord (List.ofFn fun d => PrimAsm.Records.thrDigGis P Cs carriers alg den g pr d)))
      (DigsBody.digsWImpl.bound (Digs.digsN P Cs carriers alg den pr.val)) := by
  have hbl := hin.blank dgK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by decide))
  refine DigsBody.digsWImpl.run (dPay x) (sk x dgK) dR (dPay_inj x) (dPay_ne x) P ha' Cs carriers alg den g pr cap σ
    ⟨fun i => hin.sPay i, fun i => hin.hPay i, hbl.1, hbl.2, ?_, ?_, ?_, ?_, ?_, ?_⟩ hneed
  · exact hin.vA
  · have e := hin.vals 0; rw [hv0] at e; exact e
  · have e := hin.vals 1; rw [hv1] at e; exact e
  · have e := hin.vals 12; rw [hv12] at e; exact e
  · have e := hin.vals 5; rw [hv5] at e; exact e
  · intro k hk
    apply hin.zero
    right; right
    rw [dR_val]
    unfold dRv
    split_ifs <;> omega

end NearCubicWires.WireExponent3_5.UnionMachine.RadDigs
