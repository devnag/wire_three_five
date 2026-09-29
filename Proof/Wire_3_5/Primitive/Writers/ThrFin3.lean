import Proof.Wire_3_5.Primitive.Writers.ThrFin2

/-! # c4 THR block, the THR finisher's append, run (part 2): the copy and the whole program

`copyP` copies the payload of `marks u` to the end of `O` (**`copy_exec`**); **`fa_exec`** and, under the masked reset,
**`fa_step`**: from `sampleWord kh S` (`kh ≥ 1`), a blank tape, `marks hbF` (heads at `0`), the output
`sampleWord kh S ++ hbF`.

Paper quantity of the main type: the THR seed word `sampleWord kh S ++ frame hb` (P3:2932-2937, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem take_succ_getD (u : List Bool) (k : ℕ) (hk : k < u.length) :
    u.take (k + 1) = u.take k ++ [u.getD k false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem wrO_act (b : Bank 3) (v : Bool) :
    b.act (fun j => if j = 0 then some v else none) (mv 0) =
      ⟨Function.update b.H 0 (b.H 0 + 1), Function.update b.A 0 (writeTapeBit (b.A 0) (b.H 0) v)⟩ := by
  simp only [Bank.act, Bank.mk.injEq]
  constructor
  · funext j; by_cases hj : j = 0
    · subst hj; simp [mv, HeadMove.apply]
    · simp [mv, hj, HeadMove.apply]
  · funext j; by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]

/-- **The payload copy.** -/
theorem copy_exec (u O0 : List Bool) (k : ℕ) : ∀ (b : Bank 3), b.A 2 = marks u → b.H 2 = 2 * k →
    b.A 0 = O0 ++ u.take k → b.H 0 = O0.length + k → k ≤ u.length →
    Exec copyP b ⟨Function.update (Function.update b.H 0 (O0.length + u.length)) 2 (2 * u.length),
      Function.update b.A 0 (O0 ++ u)⟩ (8 * (u.length - k) + 1) := by
  induction h : u.length - k generalizing k with
  | zero =>
    intro b hA2 hH2 hA0 hH0 hk
    have hkx : k = u.length := by omega
    have hbit : b.bit 2 = false := by
      simp only [Bank.bit, hA2, hH2, hkx, readTapeBit]
      rw [List.getD_eq_default _ _ (by simp [marks]; omega)]
    have e : (⟨Function.update (Function.update b.H 0 (O0.length + u.length)) 2 (2 * u.length),
        Function.update b.A 0 (O0 ++ u)⟩ : Bank 3) = b := by
      cases b with
      | mk H A =>
        simp only [Bank.mk.injEq]
        constructor
        · funext j
          by_cases h2 : j = 2
          · subst h2; simp at hH2 ⊢; omega
          · by_cases h0 : j = 0
            · subst h0; simp at hH0 ⊢; omega
            · simp [h0, h2]
        · funext j
          by_cases h0 : j = 0
          · subst h0; simp at hA0 ⊢; rw [hA0, hkx, List.take_length]
          · simp [h0]
    rw [e]
    exact Exec.loopF hbit
  | succ r ih =>
    intro b hA2 hH2 hA0 hH0 hk
    have hkx : k < u.length := by omega
    have hrd := rd_marks [] u [] k hkx
    simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hrd
    have hbit : b.bit 2 = true := by simp only [Bank.bit, hA2, hH2]; exact hrd.1
    set b1 := b.act (fun _ => none) (mv 2) with hb1
    have e1 := Exec.act b (fun _ => none) (mv 2)
    have h1A : b1.A = b.A := rt_A b 2
    have h1H2 : b1.H 2 = 2 * k + 1 := by rw [hb1, rt_H]; simp [hH2]
    have h1H0 : b1.H 0 = O0.length + k := by rw [hb1, rt_H]; simp [hH0]
    have hbit1 : b1.bit 2 = u.getD k false := by simp only [Bank.bit, h1A, hA2, h1H2]; exact hrd.2
    have hlen : (O0 ++ u.take k).length = O0.length + k := by simp; omega
    have e2 : Exec (.ite 2 (wrO true) (wrO false)) b1
        ⟨Function.update b1.H 0 (b1.H 0 + 1), Function.update b1.A 0 (O0 ++ u.take (k + 1))⟩ 2 := by
      rw [take_succ_getD u k hkx]
      cases hv : u.getD k false with
      | true =>
        have ea := Exec.act b1 (fun j => if j = 0 then some true else none) (mv 0)
        have eq : b1.act (fun j => if j = 0 then some true else none) (mv 0) =
            ⟨Function.update b1.H 0 (b1.H 0 + 1), Function.update b1.A 0 (O0 ++ (u.take k ++ [true]))⟩ := by
          rw [wrO_act]
          have ew : writeTapeBit (b1.A 0) (b1.H 0) true = O0 ++ (u.take k ++ [true]) := by
            rw [h1A, hA0, h1H0, ← hlen, writeTapeBit_end']; simp
          rw [ew]
        rw [eq] at ea
        exact Exec.iteT (by rw [hbit1, hv]) ea
      | false =>
        have ea := Exec.act b1 (fun j => if j = 0 then some false else none) (mv 0)
        have eq : b1.act (fun j => if j = 0 then some false else none) (mv 0) =
            ⟨Function.update b1.H 0 (b1.H 0 + 1), Function.update b1.A 0 (O0 ++ (u.take k ++ [false]))⟩ := by
          rw [wrO_act]
          have ew : writeTapeBit (b1.A 0) (b1.H 0) false = O0 ++ (u.take k ++ [false]) := by
            rw [h1A, hA0, h1H0, ← hlen, writeTapeBit_end']; simp
          rw [ew]
        rw [eq] at ea
        exact Exec.iteF (by rw [hbit1, hv]) ea
    set b2 : Bank 3 := ⟨Function.update b1.H 0 (b1.H 0 + 1), Function.update b1.A 0 (O0 ++ u.take (k + 1))⟩ with hb2
    have e3 := Exec.act b2 (fun _ => none) (mv 2)
    set b3 := b2.act (fun _ => none) (mv 2) with hb3
    have hA23 : b3.A 2 = marks u := by rw [hb3, rt_A, hb2]; simp [h1A, hA2]
    have hH23 : b3.H 2 = 2 * (k + 1) := by rw [hb3, rt_H]; simp [hb2, h1H2]; omega
    have hA03 : b3.A 0 = O0 ++ u.take (k + 1) := by rw [hb3, rt_A, hb2]; simp
    have hH03 : b3.H 0 = O0.length + (k + 1) := by rw [hb3, rt_H]; simp [hb2, h1H0]; omega
    have e4 := ih (k + 1) (by omega) b3 hA23 hH23 hA03 hH03 (by omega)
    have heq : (⟨Function.update (Function.update b3.H 0 (O0.length + u.length)) 2 (2 * u.length),
        Function.update b3.A 0 (O0 ++ u)⟩ : Bank 3) =
        ⟨Function.update (Function.update b.H 0 (O0.length + u.length)) 2 (2 * u.length),
          Function.update b.A 0 (O0 ++ u)⟩ := by
      simp only [Bank.mk.injEq]
      constructor
      · funext j
        by_cases h2 : j = 2
        · subst h2; simp
        · by_cases h0 : j = 0
          · subst h0; simp
          · simp [h0, h2, hb3, rt_H, hb2, hb1]
      · funext j
        by_cases h0 : j = 0
        · subst h0; simp
        · simp [h0, hb3, rt_A, hb2, h1A]
    rw [heq] at e4
    exact Exec.mono (Exec.loopT hbit (Exec.seq e1 (Exec.seq e2 e3)) e4) (by omega)

/-- The append program's step bound. -/
def faCost (kh q hl : ℕ) : ℕ := 2 * q * (5 * kh + 5) + 1 + 1 + (8 * hl + 1)

/-- **The append program, run** (`kh ≥ 1`). -/
theorem fa_exec (kh : ℕ) (hkh : 1 ≤ kh) (S : List (ℕ × ℕ)) (hbF : List Bool) :
    ∃ H' : Fin 3 → ℕ, Exec faP ⟨fun _ => 0, ![FinalPass.Sample.sampleWord kh S, [], marks hbF]⟩
      ⟨H', ![FinalPass.Sample.sampleWord kh S ++ hbF, [], marks hbF]⟩ (faCost kh S.length hbF.length) := by
  set b0 : Bank 3 := ⟨fun _ => 0, ![FinalPass.Sample.sampleWord kh S, [], marks hbF]⟩ with hb0
  have e1 := frames_exec kh hkh (S.flatMap fun p => [binary kh p.1, binary kh p.2]) b0 []
    (sampleFrames_width kh S) (by simp [hb0, sampleWord_frames]) (by simp [hb0])
  set b1 : Bank 3 := ⟨Function.update b0.H 0 (([] : List Bool).length +
    ((S.flatMap fun p => [binary kh p.1, binary kh p.2]).flatMap frame).length), b0.A⟩ with hb1
  have e2 := copy_exec hbF (FinalPass.Sample.sampleWord kh S) 0 b1 (by simp [hb1, hb0]) (by simp [hb1, hb0])
    (by simp [hb1, hb0]) (by simp [hb1, hb0, sampleWord_frames]) (Nat.zero_le _)
  have hA : Function.update b1.A 0 (FinalPass.Sample.sampleWord kh S ++ hbF) =
      ![FinalPass.Sample.sampleWord kh S ++ hbF, [], marks hbF] := by
    funext j; fin_cases j <;> simp [hb1, hb0]
  rw [hA] at e2
  have hlen := sampleFrames_length kh S
  exact ⟨_, Exec.mono (Exec.seq e1 e2) (by unfold faCost; rw [hlen]; ring_nf; omega)⟩

/-- **The append machine** (every head back at `0`). -/
noncomputable def faM := MaskedReset.machine faP.compile (fun _ => true)

/-- **The append, as a step**: its log (tape `3`) blank at the start, `m` falses at the end. -/
theorem fa_step (kh : ℕ) (hkh : 1 ≤ kh) (S : List (ℕ × ℕ)) (hbF : List Bool) :
    ∃ m, Step faM (2 * faCost kh S.length hbF.length + 2) (fun _ => 0)
      (Fin.addCases ![FinalPass.Sample.sampleWord kh S, [], marks hbF] (fun _ : Fin 1 => []))
      (fun _ => 0)
      (Fin.addCases ![FinalPass.Sample.sampleWord kh S ++ hbF, [], marks hbF]
        (fun _ : Fin 1 => List.replicate m false)) := by
  obtain ⟨H', e⟩ := fa_exec kh hkh S hbF
  obtain ⟨m, hm⟩ := maskBlank e.step (fun _ => true) (fun _ _ => rfl) 0
  refine ⟨m, ?_⟩
  have hm' := Step.congr (hout' := fun _ => 0) (Step.congr_in (hin' := fun _ => 0) hm (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp) rfl) (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp) rfl
  exact hm'

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
