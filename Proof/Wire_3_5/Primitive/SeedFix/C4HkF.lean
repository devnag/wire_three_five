import Proof.Wire_3_5.Primitive.SeedFix.C4HkE

/-! # The HASH stage, part 6: the loop's dock is a dock

`C4Wrap.LoopEntry`'s dock conditions for `hashExt`: its targets are distinct (**`ext_inj`**: the layout's words by
their values, the kept words by `hkT`'s injectivity, `1^{Q'}` off them), below the loop's cells, off the ports, and the
prefix's target off port `1`.

* `preS_ne_postS`, `tgt_inj`, **`ext_inj`**, `ext_lt`, `ext_port`, `ext_pfx`.

Paper quantity: none (the dock's bookkeeping). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4H

theorem preS_ne_postS (S : C3ReqIface.C3Stage) : S.preS.val ≠ S.postS.val := by
  intro e
  have h := S.distinct
  have e' : S.preS = S.postS := Fin.ext e
  rw [e'] at h
  simp at h

section Ext
variable {x : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (A : C4Iface.AsmStage)
  (wa : RepairRepresentation.WilliamsAlgorithm) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ)
  (hr : off + 3 ≤ 3 + x)
  (hkN : ∀ j, L.N ≤ (hkT j).val ∧ (hkT j).val < off) (hkI : Function.Injective hkT)
  (hQ : L.N ≤ hqT.val ∧ hqT.val < off ∧ ∀ j, hkT j ≠ hqT)
include hkN hkI hQ

theorem tgt_inj (v1 v2 : ℕ) (hv1 : v1 < CTH A wa) (hk1 : hKeepN A wa v1 = true) (hv2 : v2 < CTH A wa)
    (hk2 : hKeepN A wa v2 = true)
    (h : hashTgt L hLx A wa hkT hqT off hr v1 = hashTgt L hLx A wa hkT hqT off hr v2) : v1 = v2 := by
  have hN := C4Set.Lay.N_eq L
  have hpre := L.S3.preS.isLt
  have hpost := L.S3.postS.isLt
  have hps := preS_ne_postS L.S3
  have hk0 := hkN ⟨0, by omega⟩
  have hU : HU = 253 := rfl
  have hQU : (C4Pipe.childQQ wa).val ≠ (C4Pipe.childUU wa).val := by simp [C4Pipe.childQQ, C4Pipe.childUU]
  have hAB : A.pA.val ≠ A.pB.val := fun e => A.hAB (Fin.ext e)
  rcases tgt_cases L hLx A wa hkT hqT off hr v1 hv1 hk1 with
    ⟨a1, e1⟩ | ⟨a1, e1⟩ | ⟨h1, b1, e1⟩ | ⟨a1, e1⟩ | ⟨b1, a1, e1⟩ | ⟨b1, a1, e1⟩ <;>
  rcases tgt_cases L hLx A wa hkT hqT off hr v2 hv2 hk2 with
    ⟨a2, e2⟩ | ⟨a2, e2⟩ | ⟨h2, b2, e2⟩ | ⟨a2, e2⟩ | ⟨b2, a2, e2⟩ | ⟨b2, a2, e2⟩ <;>
  rw [e1, e2] at h <;>
  first
    | omega
    | (have hv := congrArg Fin.val h
       simp only [gS_val, C4Set.Lay.gPRE, C4Set.Lay.gPOST, C4Set.Lay.gUU, Fin.val_mk] at hv
       omega)
    | (have := hkI h; simp only [Fin.mk.injEq] at this; omega)
    | (exact absurd h (hQ.2.2 _))
    | (exact absurd h.symm (hQ.2.2 _))
    | (have hv := congrArg Fin.val h
       have := hkN ⟨v1 - A.t, by assumption⟩
       simp only [gS_val, C4Set.Lay.gPRE, C4Set.Lay.gPOST, C4Set.Lay.gUU, Fin.val_mk] at hv
       omega)
    | (have hv := congrArg Fin.val h
       have := hkN ⟨v2 - A.t, by assumption⟩
       simp only [gS_val, C4Set.Lay.gPRE, C4Set.Lay.gPOST, C4Set.Lay.gUU, Fin.val_mk] at hv
       omega)

/-- **The loop's dock is injective.** -/
theorem ext_inj (FT : ℕ) :
    ∀ i j g, hashExt L hLx A wa hkT hqT off hr FT i = some g → hashExt L hLx A wa hkT hqT off hr FT j = some g →
      i = j := by
  intro i j g hi hj
  have hN := C4Set.Lay.N_eq L
  have hpre := L.S3.preS.isLt
  have hpost := L.S3.postS.isLt
  have hk0 := hkN ⟨0, by omega⟩
  apply Fin.ext
  rcases hashExt_some L hLx A wa hkT hqT off hr FT hi with ⟨a1, b1, e1⟩ | ⟨a1, e1⟩ | ⟨a1, e1⟩ | ⟨a1, e1⟩ <;>
  rcases hashExt_some L hLx A wa hkT hqT off hr FT hj with ⟨a2, b2, e2⟩ | ⟨a2, e2⟩ | ⟨a2, e2⟩ | ⟨a2, e2⟩
  · exact tgt_inj L hLx A wa hkT hqT off hr hkN hkI hQ _ _ a1 b1 a2 b2 (e1.symm.trans e2)
  all_goals first
    | omega
    | (have t1 := tgt_range L hLx A wa hkT hqT off hr hkN ⟨hQ.1, hQ.2.1⟩ i.val a1 b1
       rw [← e1] at t1
       omega)
    | (have t2 := tgt_range L hLx A wa hkT hqT off hr hkN ⟨hQ.1, hQ.2.1⟩ j.val a2 b2
       rw [← e2] at t2
       omega)
    | (have h1 := congrArg Fin.val e1
       simp only [gS_val, C4Set.Lay.gLG, C4Set.Lay.gRR, Fin.val_mk] at h1
       omega)
    | (have h2 := congrArg Fin.val e2
       simp only [gS_val, C4Set.Lay.gLG, C4Set.Lay.gRR, Fin.val_mk] at h2
       omega)
    | (have h1 := congrArg Fin.val e1
       have h2 := congrArg Fin.val e2
       simp only [gS_val, C4Set.Lay.gLG, C4Set.Lay.gRR, Fin.val_mk] at h1 h2
       omega)
    | (have t1 := tgt_range L hLx A wa hkT hqT off hr hkN ⟨hQ.1, hQ.2.1⟩ i.val a1 b1
       rw [← e1] at t1
       have hv := congrArg Fin.val e2
       simp only [gS_val, C4Set.Lay.gLG, C4Set.Lay.gRR, Fin.val_mk] at hv
       rcases tgt_cases L hLx A wa hkT hqT off hr i.val a1 b1 with
         ⟨_, e⟩ | ⟨_, e⟩ | ⟨h1, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [← e1] at e <;>
       first
         | (rw [e] at hv; simp only [gS_val, C4Set.Lay.gPRE, C4Set.Lay.gPOST, C4Set.Lay.gUU] at hv; omega)
         | (rw [e] at hv; have := hkN ⟨i.val - A.t, h1⟩; omega)
         | (rw [e] at hv; omega)
         | (rw [e] at hv; simp at hv; omega))
    | (have t1 := tgt_range L hLx A wa hkT hqT off hr hkN ⟨hQ.1, hQ.2.1⟩ j.val a2 b2
       rw [← e2] at t1
       have hv := congrArg Fin.val e1
       simp only [gS_val, C4Set.Lay.gLG, C4Set.Lay.gRR, Fin.val_mk] at hv
       rcases tgt_cases L hLx A wa hkT hqT off hr j.val a2 b2 with
         ⟨_, e⟩ | ⟨_, e⟩ | ⟨h1, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [← e2] at e <;>
       first
         | (rw [e] at hv; simp only [gS_val, C4Set.Lay.gPRE, C4Set.Lay.gPOST, C4Set.Lay.gUU] at hv; omega)
         | (rw [e] at hv; have := hkN ⟨j.val - A.t, h1⟩; omega)
         | (rw [e] at hv; omega)
         | (rw [e] at hv; simp at hv; omega))

end Ext

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
