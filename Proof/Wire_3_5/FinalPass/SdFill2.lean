import Proof.Wire_3_5.FinalPass.SdFill

/-! # S4 (the seeds phase), part 27: batches of fills, the width and the tables' lengths measured (P3:3170-3178)

* **`flJobs OP K t js`**: the fills `js` (stream, count register, bits, end bit) in order; **`flJobs_spec`**: from
  empty streams, the state `flApply σ js` (each job's stream holds `flOut σ j`, nothing else moves; `flApply_st_in`,
  `flApply_st_notin`, `flApply_val`, `flApply_sh`, `flApply_cell`).
* **`mH s K C`**: a gate list's weight width: if the word starts with a gate (`true`), `K += |w|` for its first framed
  field `w`; `mH_true`, `mH_false`.
* **`mT s K₀ K₁ C`**: the first two framed words' lengths into `K₀`, `K₁`; `mT_spec`.

Paper quantity of the main type: the seeds phase's formatted working streams and the lengths they are formatted to. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

/-- One fill: the stream, the count's register, the repeated bits, the end bit. -/
structure FlJob (ns nr : ℕ) where
  o : Fin (ns + 1)
  v : Fin nr
  bs : List Bool
  e : Bool

section Jobs
variable {ns nr : ℕ} (cap : ℕ)

/-- A job's word at the registers of `σ`. -/
def flOut (σ : WState ns nr) (j : FlJob ns nr) : List Bool := (List.replicate (σ.val j.v) j.bs).flatten ++ [j.e]

/-- The state after the jobs. -/
def flApply : WState ns nr → List (FlJob ns nr) → WState ns nr
  | σ, [] => σ
  | σ, j :: js => flApply (σ.sets j.o (flOut σ j)) js

/-- The jobs, in order. -/
def flJobs (OP K t : Fin nr) : List (FlJob ns nr) → WM ns nr
  | [] => .skip
  | j :: js => .seq (flFillC j.o OP K t j.v j.bs j.e) (flJobs OP K t js)

/-- The jobs' step count. -/
def flJobsCost (σ : WState ns nr) (js : List (FlJob ns nr)) : ℕ :=
  (js.map fun j => 18 * σ.val j.v + 3 + 1 + flCost (σ.val j.v) j.bs.length + 1).sum

theorem flApply_val : ∀ (σ : WState ns nr) (js : List (FlJob ns nr)), (flApply σ js).val = σ.val
  | _, [] => rfl
  | σ, j :: js => by rw [flApply, flApply_val]; rfl

theorem flApply_sh : ∀ (σ : WState ns nr) (js : List (FlJob ns nr)), (flApply σ js).sh = σ.sh
  | _, [] => rfl
  | σ, j :: js => by rw [flApply, flApply_sh]; rfl

theorem flApply_cell : ∀ (σ : WState ns nr) (js : List (FlJob ns nr)), (flApply σ js).cell = σ.cell
  | _, [] => rfl
  | σ, j :: js => by rw [flApply, flApply_cell]; rfl

theorem flApply_st_notin : ∀ (σ : WState ns nr) (js : List (FlJob ns nr)) (i : Fin (ns + 1)),
    i ∉ js.map FlJob.o → (flApply σ js).st i = σ.st i
  | _, [], _, _ => rfl
  | σ, j :: js, i, hi => by
    rw [List.map_cons, List.mem_cons, not_or] at hi
    rw [flApply, flApply_st_notin _ js i hi.2]
    simp [Function.update_of_ne hi.1]

theorem flApply_st_in : ∀ (σ : WState ns nr) (js : List (FlJob ns nr)), (js.map FlJob.o).Nodup →
    ∀ j ∈ js, (flApply σ js).st j.o = flOut σ j
  | _, [], _, j, hj => absurd hj (by simp)
  | σ, j0 :: js, hnd, j, hj => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [flApply]
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [flApply_st_notin _ js _ hnd.1]
      simp
    · rw [flApply_st_in _ js hnd.2 j hj']
      rfl

theorem flJobs_spec (OP K t : Fin nr) (hKO : K ≠ OP) (hKt : K ≠ t) :
    ∀ (js : List (FlJob ns nr)) (σ : WState ns nr), (js.map FlJob.o).Nodup →
      (∀ j ∈ js, σ.st j.o = [] ∧ σ.sh j.o = 0 ∧ j.v ≠ K ∧ j.v ≠ t ∧ σ.val j.v * j.bs.length + 1 ≤ cap ∧
        σ.val j.v ≤ cap) →
      σ.val K = 0 → σ.val t = 0 → σ.val OP = 0 →
      WExec cap (flJobs OP K t js) σ (flApply σ js) (flJobsCost σ js)
  | [], σ, _, _, _, _, _ => WExec.skip σ
  | j :: js, σ, hnd, hj, hK, ht, hO => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj j List.mem_cons_self
    have e1 := flFillC_spec cap j.o OP K t j.v hKO h3 h4 hKt j.bs j.e σ hK ht h1 h2 hO h5 h6
    have e2 := flJobs_spec OP K t hKO hKt js (σ.sets j.o (flOut σ j)) hnd.2
      (fun j' hj' => by
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hj j' (List.mem_cons_of_mem _ hj')
        have hne : j'.o ≠ j.o := fun h => hnd.1 (h ▸ List.mem_map_of_mem hj')
        exact ⟨by simp [Function.update_of_ne hne, g1], by simp [g2], g3, g4, by simpa using g5, by simpa using g6⟩)
      (by simpa using hK) (by simpa using ht) (by simpa using hO)
    refine WExec.cast cap (WExec.seq e1 e2) rfl ?_
    simp only [flJobsCost, List.map_cons, List.sum_cons, WState.sets_val]
    omega

end Jobs

section Meas
variable {ns nr : ℕ} (cap : ℕ) (s : Fin (ns + 1)) (K C : Fin nr)

/-- **A gate list's weight width**: past the gate marker, across the first framed field; the stream rewound. -/
def mH : WM ns nr :=
  .seq (.ifs s (.seq (.fwd s) (.seq (.inc C) (flMeas s K C))) .skip) (WM.rewind s C)

theorem mH_true (hKC : K ≠ C) (w rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = true :: (frameP w ++ false :: rest)) (hsh : σ.sh s = 0) (hC : σ.val C = 0)
    (hc : σ.val K + w.length + 2 * w.length + 2 ≤ cap) :
    WExec cap (mH s K C) σ (σ.setv K (σ.val K + w.length)) (30 * w.length + 20) := by
  have hb : wbit σ s = true := by unfold wbit; rw [hsh]; exact flRead _ 0 true _ (by rw [hst]; rfl)
  have e1 := WExec.fwd (cap := cap) s σ
  obtain ⟨σ1, h1⟩ : ∃ y : WState ns nr, y = σ.seth s (σ.sh s + 1) := ⟨_, rfl⟩
  rw [← h1] at e1
  have e2 := WExec.inc (cap := cap) C σ1 (by rw [h1]; simp [hC]; omega)
  obtain ⟨σ2, h2⟩ : ∃ y : WState ns nr, y = σ1.setv C (σ1.val C + 1) := ⟨_, rfl⟩
  rw [← h2] at e2
  have s2 : σ2.st s = σ.st s := by rw [h2, h1]; simp
  have p2 : σ2.sh s = 1 := by rw [h2, h1]; simp [hsh]
  have k2 : σ2.val K = σ.val K := by rw [h2, h1]; simp [Function.update_apply, hKC]
  have c2 : σ2.val C = 1 := by rw [h2, h1]; simp [hC]
  have e3 := flMeas_spec cap s K C hKC w rest σ2 1 (by rw [s2, hst]; rfl) p2 (by rw [k2]; omega)
    (by rw [c2]; omega)
  rw [k2, c2] at e3
  have e4 := wrewind_spec cap s C (1 + 2 * w.length)
    (((σ2.setv K (σ.val K + w.length)).setv C (1 + 2 * w.length)).seth s (1 + 2 * w.length)) (by simp)
    (by simp; omega)
  refine WExec.cast cap (WExec.seq (WExec.ifsT hb (WExec.seq e1 (WExec.seq e2 e3))) e4) ?_ (by omega)
  rw [h2, h1]
  wgen_eq [hKC, Ne.symm hKC, hC, hsh]

theorem mH_false (σ : WState ns nr) (hb : readTapeBit (σ.st s) 0 = false) (hsh : σ.sh s = 0) (hC : σ.val C = 0) :
    WExec cap (mH s K C) σ σ 3 := by
  have hw : wbit σ s = false := by unfold wbit; rw [hsh]; exact hb
  have e2 := wrewind_spec cap s C 0 σ hC (by rw [hC]; omega)
  have hσ : (σ.setv C 0).seth s (σ.sh s - 0) = σ := by
    rw [Nat.sub_zero, ← hC, wsetv_same]
    exact WState.eq (by simp) rfl rfl rfl
  rw [hσ] at e2
  exact WExec.cast cap (WExec.seq (WExec.ifsF hw (WExec.skip σ)) e2) rfl (by omega)

/-- **The first two framed words' lengths** into `K₀`, `K₁`; the stream rewound. -/
def mT (K1 : Fin nr) : WM ns nr :=
  .seq (flMeas s K C) (.seq (.fwd s) (.seq (.inc C) (.seq (flMeas s K1 C) (WM.rewind s C))))

theorem mT_spec (K1 : Fin nr) (hKC : K ≠ C) (hK1C : K1 ≠ C) (hKK : K ≠ K1) (w0 w1 rest : List Bool)
    (σ : WState ns nr) (hst : σ.st s = frameP w0 ++ false :: (frameP w1 ++ false :: rest)) (hsh : σ.sh s = 0)
    (hC : σ.val C = 0) (hc : σ.val K + σ.val K1 + 3 * w0.length + 3 * w1.length + 2 ≤ cap) :
    WExec cap (mT s K C K1) σ ((σ.setv K (σ.val K + w0.length)).setv K1 (σ.val K1 + w1.length))
      (30 * (w0.length + w1.length) + 20) := by
  have e1 := flMeas_spec cap s K C hKC w0 (frameP w1 ++ false :: rest) σ 0 (by rw [hst]; rfl) hsh (by omega)
    (by rw [hC]; omega)
  obtain ⟨σ1, h1⟩ : ∃ y : WState ns nr, y = ((σ.setv K (σ.val K + w0.length)).setv C (σ.val C + 2 * w0.length)).seth
      s (0 + 2 * w0.length) := ⟨_, rfl⟩
  rw [← h1] at e1
  have e2 := WExec.fwd (cap := cap) s σ1
  obtain ⟨σ2, h2⟩ : ∃ y : WState ns nr, y = σ1.seth s (σ1.sh s + 1) := ⟨_, rfl⟩
  rw [← h2] at e2
  have e3 := WExec.inc (cap := cap) C σ2 (by rw [h2, h1]; simp [hC]; omega)
  obtain ⟨σ3, h3⟩ : ∃ y : WState ns nr, y = σ2.setv C (σ2.val C + 1) := ⟨_, rfl⟩
  rw [← h3] at e3
  have s3 : σ3.st s = σ.st s := by rw [h3, h2, h1]; simp
  have p3 : σ3.sh s = 2 * w0.length + 1 := by rw [h3, h2, h1]; simp
  have k3 : σ3.val K1 = σ.val K1 := by rw [h3, h2, h1]; simp [Function.update_apply, hK1C, Ne.symm hKK]
  have c3 : σ3.val C = 2 * w0.length + 1 := by rw [h3, h2, h1]; simp [hC]
  have hdrop : (σ.st s).drop (2 * w0.length + 1) = frameP w1 ++ false :: rest := by
    rw [hst, show frameP w0 ++ false :: (frameP w1 ++ false :: rest) =
      (frameP w0 ++ [false]) ++ (frameP w1 ++ false :: rest) by simp]
    exact List.drop_left' (by simp)
  have e4 := flMeas_spec cap s K1 C hK1C w1 rest σ3 (2 * w0.length + 1) (by rw [s3, hdrop]) p3
    (by rw [k3]; omega) (by rw [c3]; omega)
  rw [k3, c3] at e4
  have e5 := wrewind_spec cap s C (2 * w0.length + 1 + 2 * w1.length)
    (((σ3.setv K1 (σ.val K1 + w1.length)).setv C (2 * w0.length + 1 + 2 * w1.length)).seth s
      (2 * w0.length + 1 + 2 * w1.length)) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  rw [h3, h2, h1]
  wgen_eq [hKC, Ne.symm hKC, hK1C, Ne.symm hK1C, hKK, Ne.symm hKK, hC, hsh]

end Meas

end NearCubicWires.WireExponent3_5.FinalPass.Sd
