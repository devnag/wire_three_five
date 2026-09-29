import Proof.Wire_3_5.UnionMachine.RadAsm2

/-! # RADIX assembly (3): the table at `G`, the digit loop's registers, the record's end and the RADIX flag
(P3:2585-2623, P3:2604)

* `fsB`, `ph7` / **`ph7_spec`**: the fixed hash's table builder (`RadTab.buildL_spec`) on the cell: output `142`,
  window `143`, seed `144`, modulus `132`, scratch `145 … 148`, registers `rB`; the table word at `L` on `142`
  (head `0`); only those streams and `rB` change;
* `ph8` / **`ph8_spec`**: the block writer's fixed inputs `G`, `row`, `3·lb` into `rG 1, 2, 5`, `M` into `rZ 9`, the
  digit count `τ₀` into `rY 17`;
* `ph10` / **`ph10_spec`**: the record's closing `[true, false] ++ [false]` (`frame`'s end), the record stream
  rewound by its position `rY 0`, the RADIX flag `[true]` on `150` (head `0`).

Paper quantity of the main type: the RADIX row's framed record and flag (`RadSetupB3.RadReadyB2.s3`, `s150`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ) (x : ℕ)

/-! ## Stage 5a (4): the table at `G` -/

/-- The builder's streams on the cell: output `142`, window `143`, seed `144`, modulus `132`, scratch `145 … 148`. -/
def fsB : Fin 8 → Fin (LNS x + 1) :=
  ![sk x 142, sk x 143, sk x 144, sk x 132, sk x 145, sk x 146, sk x 147, sk x 148]

theorem fsB_val (k : Fin 8) : (fsB x k).val = (![142, 143, 144, 132, 145, 146, 147, 148] : Fin 8 → ℕ) k := by
  fin_cases k <;> rfl

theorem fsB_inj : Function.Injective (fsB x) := by
  intro a b h
  have e := congrArg Fin.val h
  rw [fsB_val, fsB_val] at e
  fin_cases a <;> fin_cases b <;> simp_all

def ph7 : WM (LNS x) LNR := FinalPass.Hash4.build.liftW (fsB x) rB

theorem ph7_spec (ω : WState (LNS x) LNR) (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ)
    (hcapS : (FinalPass.Hash4.seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap)
    (hcapW : (FinalPass.Hash4.winWord M L J Wf).length ≤ cap)
    (hcapO : (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF p ℓ M L all)).length + 1 ≤ cap)
    (hL : L ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap) (C : ℕ)
    (hC : ∀ j ≤ J, FinalPass.Hash4.levelCost ℓ L M all.length j (FinalPass.ListEval.pow (FinalPass.ListEval.topW J Wf j))
      (FinalPass.ListEval.topW J Wf j) ≤ C)
    (hW : ω.st (sk x 143) = FinalPass.Hash4.winWord M L J Wf) (hO : ω.st (sk x 142) = [])
    (hS : ω.st (sk x 144) = FinalPass.Hash4.seedWord ℓ all) (hP : ω.st (sk x 132) = frame (binary ℓ p))
    (hX : ∀ k : Fin 161, 145 ≤ k.val → k.val ≤ 148 → ∃ v, ω.st (sk x k) = frame (binary ℓ v))
    (hh : ∀ k : Fin 8, ω.sh (fsB x k) = 0) (hz : ∀ r : Fin 16, ω.val (rB r) = 0) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph7 x) ω τ'
        (FinalPass.Hash4.buildCost M L J C (FinalPass.Hash4.winWord M L J Wf).length
          (FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF p ℓ M L all)).length) ∧
      Keep ω τ' (fun i => i.val = 132 ∨ (142 ≤ i.val ∧ i.val ≤ 148)) (fun r => 138 ≤ r.val ∧ r.val < 154) ∧
      τ'.st (sk x 142) = FinalPass.ListEval.levelWord M J Wf (FinalPass.Hash4.rowF p ℓ M L all) ∧
      τ'.sh (sk x 142) = 0 := by
  obtain ⟨τ, hx, h0, h0h, -, -, -, -⟩ := RadTab.buildL_spec cap (fsB x) (fsB_inj x) rB ω p ℓ M L J Wf all hℓ hcapS
    hcapW hcapO hL hM hJ C hC hW hO hS hP (fun k hk => by
      fin_cases k
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact hX 145 (by decide) (by decide)
      · exact hX 146 (by decide) (by decide)
      · exact hX 147 (by decide) (by decide)
      · exact hX 148 (by decide) (by decide)) hh hz
  refine ⟨_, hx, ⟨fun i hi => ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · have hi' : ∀ k, fsB x k ≠ i := fun k e => by
      apply hi; subst e; rw [fsB_val]; fin_cases k <;> simp
    exact ⟨FinalPass.ThrPt.updW_st_out (fs := fsB x) (fr := rB) ω τ i hi',
      FinalPass.ThrPt.updW_sh_out (fs := fsB x) (fr := rB) ω τ i hi'⟩
  · have hr' : ∀ q, rB q ≠ r := fun q e => hr (by subst e; simp only [rB_val]; omega)
    exact FinalPass.ThrPt.updW_val_out (fs := fsB x) (fr := rB) ω τ r hr'
  · have e := FinalPass.ThrPt.updW_st_in (fs := fsB x) (fr := rB) (fsB_inj x) ω τ 0
    rw [show fsB x 0 = sk x 142 from rfl] at e
    rw [e, h0]
  · have e := FinalPass.ThrPt.updW_sh_in (fs := fsB x) (fr := rB) (fsB_inj x) ω τ 0
    rw [show fsB x 0 = sk x 142 from rfl] at e
    rw [e, h0h]

/-! ## The digit loop's registers -/

def ph8 : WM (LNS x) LNR :=
  .seq (wcopyR (rIn 4) (rG 1) (rY 4)) (.seq (wcopyR (rIn 3) (rG 2) (rY 4))
  (.seq (PrimAsm.ParseNat.addTo (rQ 8) (rG 5) (rY 4)) (.seq (PrimAsm.ParseNat.addTo (rQ 8) (rG 5) (rY 4))
  (.seq (PrimAsm.ParseNat.addTo (rQ 8) (rG 5) (rY 4)) (.seq (wcopyR (rIn 13) (rZ 9) (rY 4))
    (wcopyR (rIn 12) (rY 17) (rY 4)))))))

def ph8Cost (G row lb M τ : ℕ) : ℕ :=
  (18 * G + 3) + 1 + ((18 * row + 3) + 1 + ((18 * lb + 3) + 1 + ((18 * lb + 3) + 1 + ((18 * lb + 3) + 1 +
    ((18 * M + 3) + 1 + (18 * τ + 3))))))

theorem ph8_spec (σ : WState (LNS x) LNR) (G row lb M τ : ℕ) (hG : σ.val (rIn 4) = G) (hrow : σ.val (rIn 3) = row)
    (hlb : σ.val (rQ 8) = lb) (hM : σ.val (rIn 13) = M) (hτ : σ.val (rIn 12) = τ) (hg1 : σ.val (rG 1) = 0)
    (hg2 : σ.val (rG 2) = 0) (hg5 : σ.val (rG 5) = 0) (hz9 : σ.val (rZ 9) = 0) (hy17 : σ.val (rY 17) = 0)
    (hy4 : σ.val (rY 4) = 0) (hc : G + row + 3 * lb + M + τ ≤ cap) :
    WExec cap (ph8 x) σ (((((σ.setv (rG 1) G).setv (rG 2) row).setv (rG 5) (3 * lb)).setv (rZ 9) M).setv (rY 17) τ)
      (ph8Cost G row lb M τ) := by
  have hGY : ∀ i j, rG i ≠ rY j := fun i j e => YG j i e.symm
  have hYG : ∀ j i, rY j ≠ rG i := YG
  have hGI : ∀ i k h, rG i ≠ rIn k h := Gin
  have hIG : ∀ k h i, rIn k h ≠ rG i := fun k h i e => Gin i k h e.symm
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have hYI : ∀ i k h, rY i ≠ rIn k h := Yin
  have hQG : ∀ i j, rQ i ≠ rG j := QG
  have hGQ : ∀ j i, rG j ≠ rQ i := fun j i e => QG i j e.symm
  have hQY : ∀ i j, rQ i ≠ rY j := QY
  have hYQ : ∀ j i, rY j ≠ rQ i := fun j i e => QY i j e.symm
  have hZG : ∀ i j, rZ i ≠ rG j := ZG
  have hGZ : ∀ j i, rG j ≠ rZ i := fun j i e => ZG i j e.symm
  have hZY : ∀ i j, rZ i ≠ rY j := fun i j e => YZ j i e.symm
  have hYZ : ∀ j i, rY j ≠ rZ i := YZ
  have hZI : ∀ i k h, rZ i ≠ rIn k h := Zin
  have hIZ : ∀ k h i, rIn k h ≠ rZ i := fun k h i e => Zin i k h e.symm
  have hZQ : ∀ i j, rZ i ≠ rQ j := fun i j e => QZ j i e.symm
  have hQZ : ∀ j i, rQ j ≠ rZ i := QZ
  have s1 := wcopyR_spec cap (rIn 4) (rG 1) (rY 4) (hIG 4 _ 1) (hIY 4 _ 4) (hGY 1 4) σ hg1 hy4 (by omega)
  rw [hG] at s1
  have s2 := wcopyR_spec cap (rIn 3) (rG 2) (rY 4) (hIG 3 _ 2) (hIY 3 _ 4) (hGY 2 4) (σ.setv (rG 1) G)
    (by simp [hg2]) (by simp [hYG, hy4]) (by simp [hIG, hrow]; omega)
  have w2 : (σ.setv (rG 1) G).val (rIn 3) = row := by simp [hIG, hrow]
  rw [w2] at s2
  set σ2 := (σ.setv (rG 1) G).setv (rG 2) row with hσ2
  have v8 : ∀ y : ℕ, (σ2.setv (rG 5) y).val (rQ 8) = lb := fun y => by simp [σ2, hQG, hlb]
  have vt : ∀ y : ℕ, (σ2.setv (rG 5) y).val (rY 4) = 0 := fun y => by simp [σ2, hYG, hy4]
  have a1 := PrimAsm.ParseNat.addTo_spec cap (rQ 8) (rG 5) (rY 4) (hQG 8 5) (hQY 8 4) (hGY 5 4) (σ2.setv (rG 5) 0)
    (vt 0) (by rw [v8]; omega) (by rw [v8]; simp; omega)
  have e0 : σ2.setv (rG 5) 0 = σ2 := by
    rw [show (0 : ℕ) = σ2.val (rG 5) by simp [σ2, hg5], wsetv_same]
  rw [e0, show σ2.val (rG 5) = 0 by simp [σ2, hg5], show σ2.val (rQ 8) = lb by simp [σ2, hQG, hlb], Nat.zero_add] at a1
  have a2 := PrimAsm.ParseNat.addTo_spec cap (rQ 8) (rG 5) (rY 4) (hQG 8 5) (hQY 8 4) (hGY 5 4) (σ2.setv (rG 5) lb)
    (vt _) (by rw [v8]; omega) (by rw [v8]; simp; omega)
  rw [v8, WState.setv_val, Function.update_self, wsetv_setv] at a2
  have a3 := PrimAsm.ParseNat.addTo_spec cap (rQ 8) (rG 5) (rY 4) (hQG 8 5) (hQY 8 4) (hGY 5 4)
    (σ2.setv (rG 5) (lb + lb)) (vt _) (by rw [v8]; omega) (by rw [v8]; simp; omega)
  rw [v8, WState.setv_val, Function.update_self, wsetv_setv, show lb + lb + lb = 3 * lb by ring] at a3
  set σ5 := σ2.setv (rG 5) (3 * lb) with hσ5
  have s6 := wcopyR_spec cap (rIn 13) (rZ 9) (rY 4) (hIZ 13 _ 9) (hIY 13 _ 4) (hZY 9 4) σ5
    (by simp [σ5, σ2, hZG, hz9]) (by simp [σ5, σ2, hYG, hy4]) (by simp [σ5, σ2, hIG, hM]; omega)
  have w6 : σ5.val (rIn 13) = M := by simp [σ5, σ2, hIG, hM]
  rw [w6] at s6
  have s7 := wcopyR_spec cap (rIn 12) (rY 17) (rY 4) (hIY 12 _ 17) (hIY 12 _ 4) (rY.injective.ne (by decide))
    (σ5.setv (rZ 9) M) (by simp [σ5, σ2, hYZ, hYG, hy17]) (by simp [σ5, σ2, hYZ, hYG, hy4])
    (by simp [σ5, σ2, hIZ, hIG, hτ]; omega)
  have w7 : (σ5.setv (rZ 9) M).val (rIn 12) = τ := by simp [σ5, σ2, hIZ, hIG, hτ]
  rw [w7] at s7
  exact WExec.seq s1 (WExec.seq s2 (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq s6 s7)))))

/-! ## Stage 6: the record's end and the RADIX flag -/

def ph10 : WM (LNS x) LNR :=
  .seq (PrimAsm.Emit.emitW (sk x 3) (rY 0) [true, false, false]) (.seq (WM.rewind (sk x 3) (rY 0))
    (.seq (PrimAsm.Emit.emitW (sk x 150) (rY 18) [true]) (WM.rewind (sk x 150) (rY 18))))

theorem ph10_spec (σ : WState (LNS x) LNR) (u : List Bool) (h3 : σ.st (sk x 3) = u)
    (h3h : σ.sh (sk x 3) = u.length) (hOP : σ.val (rY 0) = u.length) (h150 : σ.st (sk x 150) = [])
    (h150h : σ.sh (sk x 150) = 0) (hy18 : σ.val (rY 18) = 0) (hc : u.length + 3 ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph10 x) σ τ' (8 * 3 + 1 + ((5 * (u.length + 3) + 1) + 1 + (8 + 1 + (5 + 1)))) ∧
      Keep σ τ' (fun i => i = sk x 3 ∨ i = sk x 150) (fun r => r = rY 0) ∧
      τ'.st (sk x 3) = u ++ [true, false, false] ∧ τ'.sh (sk x 3) = 0 ∧ τ'.st (sk x 150) = [true] ∧
      τ'.sh (sk x 150) = 0 := by
  have n3 : sk x 3 ≠ sk x 150 := fun e => by have := congrArg Fin.val (sk_inj x e); simp at this
  have n018 : rY 0 ≠ rY 18 := rY.injective.ne (by decide)
  have s1 := PrimAsm.Emit.emitW_spec cap (sk x 3) (rY 0) [true, false, false] σ (by rw [h3, h3h]) (by simp; omega)
  have s2 := wrewind_spec cap (sk x 3) (rY 0) (u.length + 3) (appendO σ (sk x 3) (rY 0) [true, false, false])
    (by simp [hOP]) (by simp [hOP]; omega)
  set σ2 := ((appendO σ (sk x 3) (rY 0) [true, false, false]).setv (rY 0) 0).seth (sk x 3)
    ((appendO σ (sk x 3) (rY 0) [true, false, false]).sh (sk x 3) - (u.length + 3)) with hσ2
  have s3 := PrimAsm.Emit.emitW_spec cap (sk x 150) (rY 18) [true] σ2 (by simp [σ2, Ne.symm n3, h150, h150h])
    (by simp [σ2, Ne.symm n018, hy18]; omega)
  have s4 := wrewind_spec cap (sk x 150) (rY 18) 1 (appendO σ2 (sk x 150) (rY 18) [true])
    (by simp [σ2, Ne.symm n018, hy18]) (by simp [σ2, Ne.symm n018, hy18]; omega)
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ⟨fun i hi => ?_, fun r hr => ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [not_or] at hi
    simp [σ2, Function.update_apply, hi.1, hi.2]
  · by_cases h18 : r = rY 18
    · subst h18; simp [σ2, n018, hy18]
    · simp [σ2, Function.update_apply, h18, hr]
  · simp [σ2, n3, h3]
  · simp [σ2, n3, h3h]
  · simp [σ2, Ne.symm n3, h150]
  · simp [σ2, Ne.symm n3, h150h]

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
