import Proof.Wire_3_5.Primitive.Writers.C3WFill

/-! # C3 request writer, part 10: C3a′ docked between the phases

Paper quantity: none (the machine plumbing of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (dockZ)
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

namespace Lay
variable (L : Lay)

theorem hA : L.oA + L.Ua ≤ L.U := by have := L.offs; omega

/-- **A machine with one input tape, docked at the streams `sAIN` (input) and `sAOUT` (output)**, its other tapes in
C3a's region; the program's other tapes, the record and the rest's heads kept. -/
theorem c3_stage {s : ℕ} (p : Machine L.Ua s) (i o : Fin L.Ua) (hio : i ≠ o) (n : ℕ) (x : List Bool)
    (tout : Fin L.Ua → List Bool)
    (hp : Step p n (fun _ => 0) (fun j => if j = i then x else []) (fun _ => 0) tout) (cap : ℕ) (σ : WState CN CR)
    (hsh : ∀ s, σ.sh s = 0) (m : ℕ) (R : Fin L.X → List Bool) (hx : σ.st sAIN = x) (hy : σ.st sAOUT = [])
    (hR : ∀ k : Fin L.X, L.oA ≤ WT + 1 + k.val → R k = []) :
    ∃ R', Step (RecoveryFocus.machine (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA) p) n (L.gHead σ)
      (L.gBank cap σ m R) (L.gHead σ) (L.gBank cap ((σ.sets sAIN (tout i)).sets sAOUT (tout o)) m R') := by
  have hWT : WT = 64 := rfl
  have hb := L.offs
  have hvA : (L.ws sAIN).val = 19 := rfl
  have hvO : (L.ws sAOUT).val = 20 := rfl
  have hab : L.ws sAIN ≠ L.ws sAOUT := L.ws_ne (by decide)
  have ha : (L.ws sAIN).val < L.oA := by have := L.ws_lt sAIN; omega
  have hb' : (L.ws sAOUT).val < L.oA := by have := L.ws_lt sAOUT; omega
  have hinj := portSl_inj i o hio (L.ws sAIN) (L.ws sAOUT) hab L.oA L.hA ha hb'
  have hreg : ∀ j : Fin L.Ua, j ≠ i → j ≠ o → L.oA ≤ (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA j).val := by
    intro j h1 h2; rw [portSl_val _ _ _ _ _ _ _ h1 h2]; omega
  have d := dockZ hp (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA) hinj (L.gHead σ) (L.gBank cap σ m R)
    (by
      intro j
      by_cases h1 : j = i
      · rw [h1, portSl_i, gHead_ws, hsh]
      · by_cases h2 : j = o
        · rw [h2, portSl_o _ _ hio, gHead_ws, hsh]
        · exact L.gHead_x σ _ (by have := hreg j h1 h2; omega))
    (by
      intro j
      by_cases h1 : j = i
      · rw [h1, portSl_i, if_pos rfl]; unfold ws; rw [gBank_wm, wenc_A_s, hx]
      · rw [if_neg h1]
        by_cases h2 : j = o
        · rw [h2, portSl_o _ _ hio]; unfold ws; rw [gBank_wm, wenc_A_s, hy]
        · rw [L.gBank_x cap σ m R _ (by have := hreg j h1 h2; omega)]
          apply hR
          have := hreg j h1 h2
          simp only
          omega)
  have e := L.bank_split (install (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA) (L.gBank cap σ m R) tout) cap
    ((σ.sets sAIN (tout i)).sets sAOUT (tout o)) m
    (by
      intro j
      rcases tape_cases j with ⟨s', rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [WState.sets_st]
        by_cases s1 : s' = sAOUT
        · subst s1
          rw [Function.update_self]
          have e := install_slot (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA) hinj (L.gBank cap σ m R) tout o
          rw [portSl_o _ _ hio] at e
          exact e
        · rw [Function.update_of_ne s1]
          by_cases s2 : s' = sAIN
          · subst s2
            rw [Function.update_self]
            have e := install_slot (portSl i o (L.ws sAIN) (L.ws sAOUT) L.oA L.hA) hinj (L.gBank cap σ m R) tout i
            rw [portSl_i] at e
            exact e
          · rw [Function.update_of_ne s2]
            show install _ _ tout (L.ws s') = _
            rw [install_other _ _ _ _ (portSl_ne i o _ _ L.oA L.hA (L.ws s') (L.ws_ne s2) (L.ws_ne s1)
              (Or.inl (by have := L.ws_lt s'; omega)))]
            show L.gBank cap σ m R (L.wm (sTape s')) = _
            rw [gBank_wm, wenc_A_s]
      · have hv : (L.wm (cTape (ns := CN) (nr := CR))).val = 1 := rfl
        rw [install_other _ _ _ _ (portSl_ne i o _ _ L.oA L.hA _
          (fun e => by have := congrArg Fin.val e; rw [hv, hvA] at this; omega)
          (fun e => by have := congrArg Fin.val e; rw [hv, hvO] at this; omega)
          (Or.inl (by rw [hv]; omega))), gBank_wm, wenc_A_c, wenc_A_c]
        rfl
      · have hv : (L.wm (rTape (ns := CN) r)).val = CN + 2 + r.val := rfl
        have hCN : CN = 22 := rfl
        have hCR : CR = 40 := rfl
        have := r.isLt
        rw [install_other _ _ _ _ (portSl_ne i o _ _ L.oA L.hA _
          (fun e => by have := congrArg Fin.val e; rw [hv, hvA] at this; omega)
          (fun e => by have := congrArg Fin.val e; rw [hv, hvO] at this; omega)
          (Or.inl (by rw [hv]; omega))), gBank_wm, wenc_A_r, wenc_A_r]
        rfl)
    (by
      have hv : L.wrec.val = WT := rfl
      rw [install_other _ _ _ _ (portSl_ne i o _ _ L.oA L.hA _
        (fun e => by have := congrArg Fin.val e; have := L.ws_lt sAIN; omega)
        (fun e => by have := congrArg Fin.val e; have := L.ws_lt sAOUT; omega)
        (Or.inl (by omega))), gBank_rec])
  rw [e] at d
  exact ⟨_, d⟩

end Lay

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
