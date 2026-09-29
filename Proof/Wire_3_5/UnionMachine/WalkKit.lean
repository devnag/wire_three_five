import Proof.Wire_3_5.UnionMachine.SampKit

/-! # C6 tail, item 3 (part 2): word-program pieces for the walk bank

* `repG`: `k` copies of a program; **`unf_spec`**: the bits of a framed word's pairs appended unframed;
* **`fillP_spec`**: `n` copies of a bit appended along a ruler;
* **`padLoop_spec`**: zeros appended while a ruler's head, started at an offset, runs to its end (the padding of a
  coordinate word to the width `R`);
* **`wm_stepJ`**: a word program as a Step with its heads returned (`Rewind`, as `wm_step`), the log tape's
  residue `0^k`, `k` at most the program's cost (base's `Rewind.recorded_run`).

Paper quantity: none (the walk bank's bookkeeping). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.WalkKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (Cp Cp.refl Cp.tr cp_emit cp_fwd cp_rb rbW fp_cons fp_app fpl)
open NearCubicWires.WireExponent3_5.UnionMachine.SampKit

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- `k` copies of a program. -/
def repG (B : WM ns nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq B (repG B k)

/-- **Unframing**: the bits `w` of the next pairs of `X`, appended to `D`. -/
theorem unf_spec (X D : Fin (ns + 1)) (hXD : X ≠ D) : ∀ (w pre rest : List Bool) (σ : WState ns nr),
    σ.st X = pre ++ (frameP w ++ rest) → σ.sh X = pre.length → σ.sh D = (σ.st D).length →
    ∃ τ, WExec cap (repG (.seq (.fwd X) (rbW X D)) w.length) σ τ (w.length * 9) ∧ Cp X D σ τ (frameP w) w
  | [], _, _, σ, _, _, hD => ⟨σ, WExec.mono (WExec.skip σ) (by simp), Cp.refl X D σ hD⟩
  | b :: w, pre, rest, σ, hX, hh, hD => by
    obtain ⟨τ1, s1, c1⟩ := cp_fwd cap X D hXD true σ hD
    obtain ⟨τ2, s2, c2⟩ := cp_rb cap X D hXD b (pre ++ [true]) (frameP w ++ rest) τ1
      (by rw [c1.st, hX]; simp [fp_cons]) (by simp [c1.sh, hh]) c1.endO
    obtain ⟨τ, s3, c3⟩ := unf_spec X D hXD w (pre ++ [true, b]) rest τ2
      (by rw [c2.st, c1.st, hX]; simp [fp_cons]) (by simp [c2.sh, c1.sh, hh]) c2.endO
    refine ⟨τ, WExec.mono (WExec.seq (WExec.seq s1 s2) s3) (by simp only [List.length_cons]; omega),
      (c1.tr c2 rfl rfl).tr c3 (by simp [fp_cons]) (by simp)⟩

/-- **`n` copies of the bit `b`** appended to `D` along the ruler `R` (`Y` is not read). -/
theorem fillP_spec (R Y D : Fin (ns + 1)) (c : Fin nr) (hYR : Y ≠ R) (hDR : D ≠ R) (hYD : Y ≠ D) (b : Bool)
    (n : ℕ) (hn : n ≤ cap) (σ : WState ns nr) (hD : σ.sh D = (σ.st D).length)
    (hR : σ.st R = List.replicate n true) (hh : σ.sh R = 0) (hc : σ.val c = 0) :
    ∃ τ, WExec cap (rulerW R c (emitW D b)) σ τ (n * 16 + 3) ∧ Cp Y D σ τ [] (List.replicate n b) := by
  have hB : ∀ k, k < n → ∀ σ' : WState ns nr, Cp Y D σ (nrm R c σ') [] (List.replicate k b) →
      σ'.st R = List.replicate n true → σ'.sh R = k → σ'.val c = k →
      ∃ τ, WExec cap (emitW D b) σ' τ 3 ∧ Cp Y D σ (nrm R c τ) [] (List.replicate (k + 1) b) ∧
        τ.st R = σ'.st R ∧ τ.sh R = σ'.sh R ∧ τ.val c = σ'.val c := by
    intro k _ σ' hP' _ _ _
    have hD' : σ'.sh D = (σ'.st D).length := by
      have := hP'.endO
      simp only [nrm, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
        Function.update_of_ne hDR] at this
      exact this
    obtain ⟨τ, s1, c1⟩ := cp_emit cap Y D hYD b σ' hD'
    refine ⟨τ, s1, hP'.tr (cp_nrm R Y D c hYR hDR c1) rfl (by rw [List.replicate_succ']), ?_, ?_, ?_⟩
    · exact (c1.same R (Ne.symm hYR) (Ne.symm hDR)).1
    · exact (c1.same R (Ne.symm hYR) (Ne.symm hDR)).2
    · rw [c1.val]
  obtain ⟨τ, s, hP, -, -, -⟩ := ruler_spec cap R c (emitW D b) n 3
    (fun k τ => Cp Y D σ τ [] (List.replicate k b)) hn hB σ (Cp.refl Y D σ hD) hR hh hc
  exact ⟨τ, s, hP⟩

/-- **The padding loop**: zeros appended to `D` while the ruler's head runs from `h0 + k` to its end `N`, the counter
counting. -/
theorem padLoop_spec (R D : Fin (ns + 1)) (c : Fin nr) (hDR : D ≠ R) (N : ℕ) (hN : N ≤ cap) :
    ∀ (j k : ℕ) (σ : WState ns nr), k + j + (σ.sh R - k) = N → k ≤ σ.sh R →
      σ.st R = List.replicate N true → σ.val c = k → σ.sh D = (σ.st D).length → σ.sh R + j = N →
      ∃ τ, WExec cap (.whs R (.seq (emitW D false) (.seq (.fwd R) (.inc c)))) σ τ (j * 11 + 1) ∧
        τ.st D = σ.st D ++ List.replicate j false ∧ τ.sh D = (τ.st D).length ∧ τ.st R = σ.st R ∧ τ.sh R = N ∧
        τ.val c = k + j ∧ (∀ i, i ≠ D → i ≠ R → Same σ τ i) ∧ (∀ r, r ≠ c → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, k, σ, _, _, hR, hc, hD, hj => by
    have hz : wbit σ R = false := by
      unfold wbit; rw [hR, show σ.sh R = N by omega]; exact rd_rep_end N
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hD, rfl, by omega, by omega,
      fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  | j + 1, k, σ, hs, hk, hR, hc, hD, hj => by
    have hw : wbit σ R = true := by
      unfold wbit; rw [hR]; exact rd_rep N (σ.sh R) (by omega)
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap D false σ hD
    obtain ⟨σ2, s2, f2, f2h, o2, v2, c2⟩ := fwd_facts cap R σ1
    have hc2 : σ2.val c = k := by rw [v2, v1, hc]
    have s3 := WExec.inc (cap := cap) c σ2 (by omega)
    have hR2 : σ2.sh R = σ.sh R + 1 := by rw [f2h, (o1 R (Ne.symm hDR)).2]
    obtain ⟨τ, s4, e4, e4h, f4, f4h, v4, o4, r4, c4⟩ := padLoop_spec R D c hDR N hN j (k + 1)
      (σ2.setv c (σ2.val c + 1)) (by simp only [WState.setv_sh]; omega) (by simp only [WState.setv_sh]; omega)
      (by simp only [WState.setv_st]; rw [f2, (o1 R (Ne.symm hDR)).1, hR]) (by simp [hc2])
      (by simp only [WState.setv_sh, WState.setv_st]; rw [(o2 D hDR).1, (o2 D hDR).2]; exact e1h)
      (by simp only [WState.setv_sh]; omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) (by omega), ?_, e4h, ?_, f4h, ?_,
      fun i hiD hiR => ?_, fun r hr => ?_, ?_⟩
    · rw [e4]; simp only [WState.setv_st]; rw [(o2 D hDR).1, e1, List.replicate_succ, List.append_assoc]; rfl
    · rw [f4]; simp only [WState.setv_st]; rw [f2, (o1 R (Ne.symm hDR)).1]
    · rw [v4]; omega
    · exact (((o1 i hiD).trans' (o2 i hiR)).trans' ⟨rfl, rfl⟩).trans' (o4 i hiD hiR)
    · rw [r4 r hr]; simp only [WState.setv_val, Function.update_of_ne hr]; rw [v2, v1]
    · rw [c4]; simp only [WState.setv_cell]; rw [c2, c1]

/-! ## A word program as a Step, with its log -/

/-- **A word program as a Step**, with the log tape's residue `0^k`, `k ≤ n` (base's `Rewind.recorded_run`). -/
theorem wm_stepJ (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hH : (wenc cap σ).H = fun _ => 0) :
    ∃ (out : Fin (ns + 2 + nr + 1) → List Bool) (k : ℕ),
      Step (Rewind.machine P.toProg.compile) (2 * n + 2) (fun _ => 0) (Fin.addCases (wenc cap σ).A (fun _ => []))
        (fun _ => 0) out ∧ (∀ i, out (Fin.castAdd 1 i) = (wenc cap τ).A i) ∧
        out (Fin.natAdd (ns + 2 + nr) 0) = List.replicate k false ∧ k ≤ n := by
  have hs := (WExec.exec cap hw).step
  rw [hH] at hs
  obtain ⟨r, hr, -, ht, hsteps⟩ := hs
  have hr0 : runFrom P.toProg.compile n (initialConfiguration P.toProg.compile (wenc cap σ).A) = some r := hr
  obtain ⟨r', hr', hf, -, -⟩ := Rewind.recorded_run P.toProg.compile n
    (initialConfiguration P.toProg.compile (wenc cap σ).A) r hr0 0 (by simp [initialConfiguration])
  have hinit : Rewind.recording (initialConfiguration P.toProg.compile (wenc cap σ).A) 0 =
      initialConfiguration (Rewind.machine P.toProg.compile) (Fin.addCases (wenc cap σ).A (fun _ => [])) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [Rewind.recording, Rewind.config, initialConfiguration]
    · rfl
  rw [hinit, Nat.zero_add] at hr'
  refine ⟨r'.final.tapes, r.steps, (Step.of_run hr' ?_ rfl).enlarge (by omega), ?_, ?_, hsteps⟩
  · rw [hf]; funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Rewind.finished, Rewind.config]
  · intro i; rw [hf, ← ht]; simp [Rewind.finished, Rewind.config]
  · rw [hf]; simp [Rewind.finished, Rewind.config]

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.WalkKit
