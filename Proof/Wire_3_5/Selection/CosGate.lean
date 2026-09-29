import Proof.Wire_3_5.Selection.CosBase

/-! # C1.5: one gate call inside the coset loop (P3:1356-1358)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357). From the
standing state `Base`, with gate `i`'s record in `GA`, the gate routine (C1.4's `gateW_spec`) adds the gate's
exact row count at the coset `N` to `TX`; the standing state holds after the call, every stream outside the gate
routine's scratch and `TX` keeps its contents, and the heads, registers and cell come back. Main declarations:
`mem_scR_inv`, **`gate_call`**. Paper quantity: a gate's exact row count at a candidate coset. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

theorem mem_scR_inv (G : Fin 28 → Fin (ns + 1)) (Rg : Fin 48 → Fin nr) (r : Fin nr)
    (hr : r ∈ (gateLayout G Rg).scR) : ∃ j : Fin 48, 6 ≤ j.val ∧ Rg j = r := by
  simp only [gateLayout, List.mem_map, List.mem_finRange, true_and] at hr
  obtain ⟨a, rfl⟩ := hr
  exact ⟨⟨a.val + 6, by omega⟩, by show 6 ≤ a.val + 6; omega, rfl⟩

/-- **One gate call**: `TX += gateRows` of gate `i` at the coset `N`; `Base` holds after it. -/
theorem gate_call (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ) (σ : WState ns nr)
    (b : Base S Q R h W V N σ) (i tx : ℕ) (hi : i < R.gates.length)
    (hGA : σ.st (S 1) = gateRec W (gateOf R.gates[i])) (hTX : NumOn σ (S 3) W tx) (hN : N < 2 ^ (R.r * R.s))
    (hKB : KeyBound (gateOf R.gates[i]) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hfit : tx + gateRows (starParamsOf R h) ((starParamsOf R h).translationOfCodes (codesOfIdx R.s R.r N))
      (gateOf R.gates[i]) < 2 ^ W)
    (hcap : gateNeed (starParamsOf R h) W V ≤ cap) :
    ∃ τ : WState ns nr, WExec cap (gateW (gG S) (gR Q)) σ τ (gateCost (starParamsOf R h) W V) ∧
      Base S Q R h W V N τ ∧
      NumOn τ (S 3) W (tx + gateRows (starParamsOf R h) ((starParamsOf R h).translationOfCodes
        (codesOfIdx R.s R.r N)) (gateOf R.gates[i])) ∧
      (∀ k : Fin 50, 28 ≤ k.val → τ.st (S k) = σ.st (S k)) ∧ τ.st (S 1) = σ.st (S 1) ∧
      τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have notsc : ∀ k : Fin 50, (28 ≤ k.val ∨ k.val < 4) → S k ∉ (gateLayout (gG S) (gR Q)).scS := by
    intro k hk hm
    obtain ⟨j, hj, e⟩ := mem_scS_inv (gG S) (gR Q) _ hm
    exact gG_ne hS hQ k hk j hj e
  have ntx : ∀ k : Fin 50, k ≠ 3 → S k ≠ (gateLayout (gG S) (gR Q)).TX := fun k hk => hS.ne hk
  have hready : GateReady (gateLayout (gG S) (gR Q)) (slW (gG S) (starParamsOf R h) W) σ (starParamsOf R h) N W V
      (gateOf R.gates[i]) := by
    refine ⟨b.nsw.1, b.nsw.2, hGA, b.gah, b.of, b.r0, b.r1, b.r2, b.r3, b.r4, b.r5, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_scS_inv (gG S) (gR Q) x hx
      rw [slW_G (gG S) (gG_inj S hS)]
      exact b.sc j hj
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_scR_inv (gG S) (gR Q) r hr
      exact b.zr j hj
  obtain ⟨τ, hx, hTXτ, hoth, hlen, hsh, hval, hcell⟩ := gateW_spec (gG S) (gG_inj S hS) (gR Q) (gR_inj Q hQ) cap
    σ (starParamsOf R h) N W V (gateOf R.gates[i]) tx hN hready hTX hKB hW hnk hfit hcap
  have keep : ∀ k : Fin 50, (28 ≤ k.val ∨ (k.val < 4 ∧ k ≠ 3)) → τ.st (S k) = σ.st (S k) := by
    intro k hk
    have hk3 : k ≠ 3 := by
      intro e
      subst e
      rcases hk with hk | ⟨-, hk⟩ <;> simp_all
    exact hoth (S k) (ntx k hk3) (notsc k (by omega))
  have k0 : τ.st (S 0) = σ.st (S 0) := keep 0 (Or.inr ⟨by decide, by decide⟩)
  have k1 : τ.st (S 1) = σ.st (S 1) := keep 1 (Or.inr ⟨by decide, by decide⟩)
  have k2 : τ.st (S 2) = σ.st (S 2) := keep 2 (Or.inr ⟨by decide, by decide⟩)
  refine ⟨τ, hx, ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ⟨hTXτ, ?_⟩, fun k hk => keep k (Or.inl hk), k1, hsh, hval, hcell⟩
  · rw [keep 30 (Or.inl (by decide)), b.gt]
  · rw [hsh, b.gth]
  · rw [keep 31 (Or.inl (by decide)), b.pt]
  · rw [keep 32 (Or.inl (by decide)), b.ng.1]
  · rw [hsh, b.ng.2]
  · rw [k2, b.of.1]
  · rw [hsh, b.of.2]
  · rw [k0, b.nsw.1]
  · rw [hsh, b.nsw.2]
  · rw [k1]; exact b.ga
  · rw [hsh, b.gah]
  · intro j hj
    refine ⟨Or.inr ?_, by rw [hsh]; exact (b.sc j hj).2⟩
    rw [hlen _ (mem_scS (gG S) (gR Q) j hj), slW_G (gG S) (gG_inj S hS)]
  · rw [hval, b.r0]
  · rw [hval, b.r1]
  · rw [hval, b.r2]
  · rw [hval, b.r3]
  · rw [hval, b.r4]
  · rw [hval, b.r5]
  · intro j hj; rw [hval]; exact b.zr j hj
  · rw [hval, b.nr1]
  · rw [hval, b.np]
  · rw [hval, b.ptl]
  · intro j hj; rw [hval]; exact b.tmp j hj
  · rw [hsh]; exact hTX.2

/-- **`Base` from agreement** on the standing state's streams, heads and registers (`GA` only by its length). -/
theorem Base.of_agree {S : Fin 50 → Fin (ns + 1)} {Q : Fin 64 → Fin nr} {R : SelectionReq} {h : ParamsOk R}
    {W V N : ℕ} {σ τ : WState ns nr} (b : Base S Q R h W V N σ)
    (hst : ∀ k : Fin 50, (k.val = 0 ∨ k.val = 2 ∨ (4 ≤ k.val ∧ k.val < 28) ∨ k.val = 30 ∨ k.val = 31 ∨ k.val = 32) →
      τ.st (S k) = σ.st (S k))
    (hga : (τ.st (S 1)).length ≤ (R.n + 1) * (2 * W + 2))
    (hsh : ∀ k : Fin 50, k ≠ 31 → τ.sh (S k) = σ.sh (S k))
    (hval : ∀ j : Fin 64, (j.val < 51 ∨ j.val = 54 ∨ j.val = 55 ∨ j.val = 56 ∨ 58 ≤ j.val) → τ.val (Q j) = σ.val (Q j)) :
    Base S Q R h W V N τ := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hga, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst 30 (by decide), b.gt]
  · rw [hsh 30 (by decide), b.gth]
  · rw [hst 31 (by decide), b.pt]
  · rw [hst 32 (by decide), b.ng.1]
  · rw [hsh 32 (by decide), b.ng.2]
  · rw [hst 2 (by decide), b.of.1]
  · rw [hsh 2 (by decide), b.of.2]
  · rw [hst 0 (by decide), b.nsw.1]
  · rw [hsh 0 (by decide), b.nsw.2]
  · rw [hsh 1 (by decide), b.gah]
  · intro j hj
    have e1 := hst ⟨j.val, by omega⟩ (by simp; omega)
    have e2 := hsh ⟨j.val, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this; omega)
    show (τ.st (S ⟨j.val, _⟩) = [] ∨ (τ.st (S ⟨j.val, _⟩)).length = _) ∧ τ.sh (S ⟨j.val, _⟩) = 0
    rw [e1, e2]
    exact b.sc j hj
  · rw [hval 0 (by decide), b.r0]
  · rw [hval 1 (by decide), b.r1]
  · rw [hval 2 (by decide), b.r2]
  · rw [hval 3 (by decide), b.r3]
  · rw [hval 4 (by decide), b.r4]
  · rw [hval 5 (by decide), b.r5]
  · intro j hj
    show τ.val (Q ⟨j.val, _⟩) = 0
    rw [hval ⟨j.val, by omega⟩ (by simp; omega)]
    exact b.zr j hj
  · rw [hval 60 (by decide), b.nr1]
  · rw [hval 59 (by decide), b.np]
  · rw [hval 58 (by decide), b.ptl]
  · intro j hj
    rw [hval j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact b.tmp j hj

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
