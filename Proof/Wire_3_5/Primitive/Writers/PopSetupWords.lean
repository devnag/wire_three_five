import Proof.Wire_3_5.UnionMachine.FsKit
import Proof.Wire_3_5.Primitive.Writers.SymLayout

/-! # PA POP setup, part 4: the POP setup's words

From the numbers in registers (`PopSetupNums`: the side bits `447`, `n` `441`, the rulers `459`, the index word's width
`461`, `3·rank − 1` `449`, `rank` `446`, `2·rank − 1` `458`, `J + 1` `462`; the seed index `f` in `403`), one program
(**`pwordsW`**) writes on blank streams, heads back at `0`, what `UnitReady.PopReady` reads from streams
(**`pwords_spec`**, exact contents), with the writers (`FsKit.unaryW`, `BinW.binW`) and **`fvW`** (`1^v 0`):
* the walk bank's inputs (`PopReady.hin`): the seed's index word `frame (binary (160n + 2·sb) f)` on `24`, the rulers
  `1^{sb}`, `1^n`, `1^{2sb+1}`, `1^{2sb+1}` on `25 … 28`;
* C5's builder words at the zero seed word (`PopReady.hC5`, `FinalPass.Flat.canonL`): `frame 0^{3·rank−1}` (`pmw`) on
  `8`, `1^{J+1} 0` (`fv`) on `9`, `frame (binary rank 0)` (`kw`, `bw`) on `14`, `15`, `frame 0^{2·rank−1}` (`ep`) on
  `16`;
* the POP flag `[true]` on `150`.

Paper quantity of the main type: the walk bank's inputs at the list seed (the walk sample's index word, P3:1505-1510) and
the table builder's entry words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine

variable (cap : ℕ)

theorem binCost_le (g k : ℕ) (hg : g ≤ cap) (hk : k ≤ cap) : BinW.binCost g k ≤ 60 * ((cap + 1) * (cap + 1)) := by
  unfold BinW.binCost
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul (by omega) (by omega))

section Fv
variable {ns nr : ℕ}

/-- **`1^v 0` on the blank `O`** (head back at `0`) from the register `V` (kept); scratch `A`, `T`, `P`: C5's level
count word `fv = 1^{J+1} ++ [false]` (`FinalPass.Flat.canonL`). -/
def fvW (O : Fin (ns + 1)) (V A T P : Fin nr) : WM ns nr :=
  .seq (BinW.dupR V A T) (.seq (.whr A (.seq (.dec A) (emitC O P true))) (.seq (emitC O P false) (WM.rewind O P)))

theorem fvW_spec (O : Fin (ns + 1)) (V A T P : Fin nr) (hVA : V ≠ A) (hVT : V ≠ T) (hAT : A ≠ T) (hAP : A ≠ P)
    (hVP : V ≠ P) (hTP : T ≠ P) (σ : WState ns nr) (v : ℕ) (hv : σ.val V = v) (ha : σ.val A = 0) (ht : σ.val T = 0)
    (hp : σ.val P = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hcap : v + 2 ≤ cap) :
    WExec cap (fvW O V A T P) σ (σ.sets O (List.replicate v true ++ [false]))
      (18 * v + 3 + 1 + (v * 11 + 1 + 1 + (7 + 1 + (5 * (v + 1) + 1)))) := by
  have d := BinW.dupR_spec cap V A T hVA hVT hAT σ v hv ha ht (by omega)
  have e0 : σ.setv A v = FsKit.stU σ O A P v 0 := by
    apply WState.eq
    · funext k
      by_cases hk : k = O
      · subst hk; simp [FsKit.stU, hOh]
      · simp [FsKit.stU, hk]
    · funext k
      by_cases hk : k = O
      · subst hk; simp [FsKit.stU, hO]
      · simp [FsKit.stU, hk]
    · funext k
      simp only [FsKit.stU, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      by_cases hkP : k = P
      · subst hkP; simp [Ne.symm hAP, hp]
      · simp [hkP]
    · rfl
  rw [e0] at d
  have lp := FsKit.unaryL_spec cap O A P hAP σ v (by omega) v 0 (by omega)
  have em := emitC_spec cap O P false (FsKit.stU σ O A P v v) (by simp [FsKit.stU]) (by simp [FsKit.stU]; omega)
  have rw7 := wrewind_spec cap O P (v + 1)
    ((((FsKit.stU σ O A P v v).sets O ((FsKit.stU σ O A P v v).st O ++ [false])).seth O
      ((FsKit.stU σ O A P v v).sh O + 1)).setv P ((FsKit.stU σ O A P v v).val P + 1))
    (by simp [FsKit.stU]) (by simp [FsKit.stU]; omega)
  refine WExec.cast cap (WExec.seq d (WExec.seq lp (WExec.seq em rw7))) ?_ le_rfl
  apply WState.eq
  · funext k
    by_cases hk : k = O
    · subst hk; simp [FsKit.stU, hOh]
    · simp [FsKit.stU, hk]
  · funext k
    by_cases hk : k = O
    · subst hk; simp [FsKit.stU]
    · simp [FsKit.stU, hk]
  · funext k
    simp only [FsKit.stU, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
    by_cases hkP : k = P
    · subst hkP; simp [hp]
    · by_cases hkA : k = A
      · subst hkA; simp [hkP, ha]
      · simp [hkP, hkA]
  · rfl

end Fv

/-- The streams the words stage writes. -/
def pwOut (x : ℕ) : List (Fin (LNS x + 1)) := [sk x 25, sk x 26, sk x 27, sk x 28, sk x 24, sk x 8, sk x 14, sk x 15, sk x 16, sk x 9, sk x 150]

/-- **The POP setup's words**: the walk bank's rulers and the seed's index word, C5's builder words at the zero seed
word, the level count `1^{J+1}0`, the POP flag (11 steps). -/
def pwordsW (x : ℕ) : WM (LNS x) LNR :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (FsKit.unaryW (sk x 25) (447 : Fin LNR) 477 478 479) (FsKit.unaryW (sk x 26) (441 : Fin LNR) 477 478 479)) (FsKit.unaryW (sk x 27) (459 : Fin LNR) 477 478 479)) (FsKit.unaryW (sk x 28) (459 : Fin LNR) 477 478 479)) (BinW.binW (sk x 24) ![403, 461, 471, 472, 473, 474, 475, 476])) (BinW.binW (sk x 8) ![470, 449, 471, 472, 473, 474, 475, 476])) (BinW.binW (sk x 14) ![470, 446, 471, 472, 473, 474, 475, 476])) (BinW.binW (sk x 15) ![470, 446, 471, 472, 473, 474, 475, 476])) (BinW.binW (sk x 16) ![470, 458, 471, 472, 473, 474, 475, 476])) (fvW (sk x 9) (462 : Fin LNR) 477 478 479)) (.wr (sk x 150) true)

theorem pwords_spec (x : ℕ) (σ : WState (LNS x) LNR) (sb n RW f k q3 r q2 J1 : ℕ)
    (h447 : σ.val 447 = sb) (h441 : σ.val 441 = n) (h459 : σ.val 459 = RW) (h403 : σ.val 403 = f) (h461 : σ.val 461 = k) (h449 : σ.val 449 = q3) (h446 : σ.val 446 = r) (h458 : σ.val 458 = q2) (h462 : σ.val 462 = J1)
    (z470 : σ.val 470 = 0) (z471 : σ.val 471 = 0) (z472 : σ.val 472 = 0) (z473 : σ.val 473 = 0) (z474 : σ.val 474 = 0) (z475 : σ.val 475 = 0) (z476 : σ.val 476 = 0) (z477 : σ.val 477 = 0) (z478 : σ.val 478 = 0) (z479 : σ.val 479 = 0)
    (hb : ∀ q : Fin 161, q.val ≠ 0 → q.val ≠ 1 → q.val ≠ 2 → q.val ≠ 113 → σ.st (sk x q) = [] ∧ σ.sh (sk x q) = 0)
    (hcap : sb + n + RW + f + 2 * k + 2 * q3 + 2 * r + 2 * q2 + J1 + 1000 ≤ cap) :
    ∃ τ : WState (LNS x) LNR, WExec cap (pwordsW x) σ τ (1000 * ((cap + 1) * (cap + 1))) ∧ τ.val = σ.val ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell ∧ (∀ i, i ∉ pwOut x → τ.st i = σ.st i) ∧
      τ.st (sk x 25) = List.replicate sb true ∧
      τ.st (sk x 26) = List.replicate n true ∧
      τ.st (sk x 27) = List.replicate RW true ∧
      τ.st (sk x 28) = List.replicate RW true ∧
      τ.st (sk x 24) = frame (binary k f) ∧
      τ.st (sk x 8) = frame (binary q3 0) ∧
      τ.st (sk x 14) = frame (binary r 0) ∧
      τ.st (sk x 15) = frame (binary r 0) ∧
      τ.st (sk x 16) = frame (binary q2 0) ∧
      τ.st (sk x 9) = List.replicate J1 true ++ [false] ∧
      τ.st (sk x 150) = [true] := by
  have b25 := hb 25 (by decide) (by decide) (by decide) (by decide)
  have b26 := hb 26 (by decide) (by decide) (by decide) (by decide)
  have b27 := hb 27 (by decide) (by decide) (by decide) (by decide)
  have b28 := hb 28 (by decide) (by decide) (by decide) (by decide)
  have b24 := hb 24 (by decide) (by decide) (by decide) (by decide)
  have b8 := hb 8 (by decide) (by decide) (by decide) (by decide)
  have b14 := hb 14 (by decide) (by decide) (by decide) (by decide)
  have b15 := hb 15 (by decide) (by decide) (by decide) (by decide)
  have b16 := hb 16 (by decide) (by decide) (by decide) (by decide)
  have b9 := hb 9 (by decide) (by decide) (by decide) (by decide)
  have b150 := hb 150 (by decide) (by decide) (by decide) (by decide)
  have c1 := FsKit.unaryW_spec cap (sk x 25) (447 : Fin LNR) 477 478 479 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σ sb (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega)
  have c2 := WExec.seq c1 (FsKit.unaryW_spec cap (sk x 26) (441 : Fin LNR) 477 478 479 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ n (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c3 := WExec.seq c2 (FsKit.unaryW_spec cap (sk x 27) (459 : Fin LNR) 477 478 479 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ RW (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c4 := WExec.seq c3 (FsKit.unaryW_spec cap (sk x 28) (459 : Fin LNR) 477 478 479 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ RW (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c5 := WExec.seq c4 (BinW.binW_spec cap (sk x 24) ![403, 461, 471, 472, 473, 474, 475, 476] (by decide) _ f k (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (fun j hj => by fin_cases j <;> simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2] at hj ⊢) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c6 := WExec.seq c5 (BinW.binW_spec cap (sk x 8) ![470, 449, 471, 472, 473, 474, 475, 476] (by decide) _ 0 q3 (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (fun j hj => by fin_cases j <;> simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2] at hj ⊢) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c7 := WExec.seq c6 (BinW.binW_spec cap (sk x 14) ![470, 446, 471, 472, 473, 474, 475, 476] (by decide) _ 0 r (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (fun j hj => by fin_cases j <;> simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2] at hj ⊢) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c8 := WExec.seq c7 (BinW.binW_spec cap (sk x 15) ![470, 446, 471, 472, 473, 474, 475, 476] (by decide) _ 0 r (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (fun j hj => by fin_cases j <;> simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2] at hj ⊢) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c9 := WExec.seq c8 (BinW.binW_spec cap (sk x 16) ![470, 458, 471, 472, 473, 474, 475, 476] (by decide) _ 0 q2 (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (fun j hj => by fin_cases j <;> simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2] at hj ⊢) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c10 := WExec.seq c9 (fvW_spec cap (sk x 9) (462 : Fin LNR) 477 478 479 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _ J1 (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2]) (by omega))
  have c11 := WExec.seq c10 (WExec.wr (sk x 150) true _)
  have p1 := binCost_le cap f k (by omega) (by omega)
  have p2 := binCost_le cap 0 q3 (by omega) (by omega)
  have p3 := binCost_le cap 0 r (by omega) (by omega)
  have p4 := binCost_le cap 0 q2 (by omega) (by omega)
  have pP : cap + 1 ≤ (cap + 1) * (cap + 1) := Nat.le_mul_self _
  refine ⟨_, WExec.mono c11 (by omega), by simp, by simp, by simp, ?_, ?_⟩
  · intro i hi
    simp only [pwOut, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp [Function.update_apply, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]
  · simp [Function.update_apply, (sk_inj x).eq_iff, h447, h441, h459, h403, h461, h449, h446, h458, h462, z470, z471, z472, z473, z474, z475, z476, z477, z478, z479, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b24.1, b24.2, b8.1, b8.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b9.1, b9.2, b150.1, b150.2, writeTapeBit]

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupWords
