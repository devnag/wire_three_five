import Proof.Wire_3_5.Foundations.OutMachineSlot1P

/-! # SA's slot 1, part 4: the writer, and SA from slot 0

* **`slot1W l : CoreWordsMJ l 1 (SA.slot1Ws l)`**: S4's word 1 (the sample word) at every request, one machine for
  every gate (capacity `28·(|fpIn|+1)`, steps and residues within `5000·(|fpIn|+1)^2`);
* **`saOf l slot0 : S4WordsMAJ l`**: SA from the offset's writer (slot 0), this writer and the carrier tables.

Paper quantity of the main type: S4's sample word (P3:3044-3048, 3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- The output stream as a one-word embedding. -/
def sOut1 : Fin 1 ↪ Fin 3 := ⟨fun _ => O, fun a b _ => Subsingleton.elim a b⟩

/-- **The sample word's writer** (S4's word 1). -/
noncomputable def slot1W (l : Literals) : CoreWordsMJ l 1 (SA.slot1Ws l) where
  ns := 2
  nr := 14
  s := fun _ => slot1P.toProg.size
  M := fun _ => slot1P.toProg.compile
  sIn := I
  sOut := sOut1
  out_ne := fun _ => by show O ≠ I; decide
  Kc := fun _ => 28
  Dk := fun _ => 1
  Cs := fun _ => 5000
  Ds := fun _ => 2
  run := fun F kclk coef A a ha r σ hin hsh hbl hv _ => by
    obtain ⟨fs, ex, hsw, hex, hsl⟩ := seed_split l F kclk coef A a ha r
    have hfp : fpIn l F kclk coef A a ha r = r.1.word ++ ((fs ++ ex).map frame).flatten := by
      show r.1.word ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1 = _
      rw [hsw]
    obtain ⟨τ, n, hx, hn, hO, hI, hS, hτs, hτv⟩ := slot1_spec
      (28 * ((fpIn l F kclk coef A a ha r).length + 1) ^ 1) r.1 fs ex hex σ (by rw [hin, hfp])
      (hbl O (by decide)) (hbl Sx (by decide)) hsh hv (by rw [hfp, pow_one])
    refine ⟨τ, n, by rw [hfp]; exact hn, Exec.step (WExec.exec _ hx), fun k => ?_, by rw [hI, hin], ?_, hτs, hτv⟩
    · show τ.st O = _
      rw [Subsingleton.elim k 0, hO, hsl]
    · intro i h1 h2
      have hi : i = Sx := by
        have h2' := h2 0
        fin_cases i
        · exact absurd rfl h1
        · exact absurd rfl h2'
        · rfl
      subst hi
      have hsq : (fpIn l F kclk coef A a ha r).length ≤ 5000 * ((fpIn l F kclk coef A a ha r).length + 1) ^ 2 := by
        have := Nat.le_self_pow (show 2 ≠ 0 by decide) ((fpIn l F kclk coef A a ha r).length + 1)
        omega
      rw [hfp] at hsq ⊢
      exact le_trans hS hsq

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- **SA from the offset's writer**: slot 0 given, slot 1 = `Slot1.slot1W`, slots 2–3 = the carrier tables. -/
noncomputable def saOf (l : Literals) (slot0 : CoreWordsMJ l 1 (slot0Ws l)) : S4WordsMAJ l :=
  saOf2 l slot0 (Slot1.slot1W l)

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA
