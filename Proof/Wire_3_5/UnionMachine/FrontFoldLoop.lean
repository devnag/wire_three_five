import Proof.Wire_3_5.UnionMachine.CWEnvSem
import Proof.Wire_3_5.UnionMachine.FrontFoldRound

/-! # C6 front, U5, the writers' fold (b): every variable

The union front writes, per variable `X < nv`, the code of its encoding parity `unionParityAtom m q (supp X)`
(P3:3092-3094), the code of its carrier (the charged gates of its atoms and, if `X < sys`, of its parity:
P3:3409-3410, 3432-3433) and the carrier's envelope bit (P3:3083-3094). **`fold_run`**: the uniform fold of the round
(`FrontFoldRound.round_run`) over `X < nv`, with any parity writer and carrier writer of the class mode, ends with the
parity codes, the carrier codes and the envelope bits of every variable on the kept tapes `5`, `6`, `7`.

Paper quantity of the main type: the per-variable codes and envelope bits the table writer reads. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Transfer (unionParityAtom uniformFold_ready ready_lengths foldLoop foldBody
  roundTapes padScratch blankScratch)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldRound
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord carrierOf inBank)
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (ParityWriterJ CarrierWriterJ outBankJ)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeM envCodeIn envCodeCost atomsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound (foldCwE)
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA (idleA idleA_ready)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- **The fold's data**: the variable count, the systematic count, each variable's support and atoms. -/
structure FoldIn (m : Mode) (q : ℕ) where
  nv : ℕ
  sys : ℕ
  supp : ℕ → Finset (Fin q)
  atoms : ℕ → List (m.Circuit q)

namespace FoldIn
variable {m : Mode} {q : ℕ} (F : FoldIn m q)

/-- The encoding parity of `X`. -/
def par (X : ℕ) : m.Circuit q := unionParityAtom m q (F.supp X)
/-- The circuits whose gates form the carrier of `X`. -/
def cs (X : ℕ) : List (m.Circuit q) := F.atoms X ++ if X < F.sys then [F.par X] else []
/-- The carrier of `X`. -/
def car (X : ℕ) : Stars.Carrier q := carrierOf m (F.cs X)
/-- The parity's code, as written. -/
def pw (X : ℕ) : List Bool := natWord (m.code (F.par X))
/-- The carrier's code, as written. -/
def cw (X : ℕ) : List Bool := natWord (Stars.Carrier.code (F.car X))
/-- The carrier's envelope bit at degree `deg`. -/
def eb (deg X : ℕ) : Bool :=
  decide ((F.car X).length ≤ (q + 1) ^ deg ∧ ∀ g ∈ F.car X, g.encodingBits ≤ (q + 1) ^ deg)
/-- The bitmaps of the supports. -/
def ys : List (List Bool) := (List.range F.nv).map fun X => bitmap (F.supp X)
/-- The atoms' codes. -/
def as : List (List Bool) := (List.range F.nv).map fun X => codesWord m (F.atoms X)

/-- **The round state** after `X` variables (the counters with `Z0` cells). -/
def st (deg T Z0 X tP tC : ℕ) : Fin (1220 + tP + tC) → List Bool :=
  Qf [F.ys.flatMap frame, ctr X (Z0 - X), F.as.flatMap frame, ctr X (Z0 - X), List.replicate F.sys true,
    ((List.range X).map F.pw).flatMap frame, ((List.range X).map F.cw).flatMap frame, (List.range X).map (F.eb deg),
    List.replicate ((q + 1) ^ deg) true, List.replicate T true]

end FoldIn

/-- The envelope stage's capacity fits a carrier. -/
structure EnvFit {q : ℕ} (X : Stars.Carrier q) (deg T : ℕ) : Prop where
  c : (atomsOf (Stars.Carrier.code X)).length ≤ T
  s : ((atomsOf (Stars.Carrier.code X)).flatMap frame).length ≤ T
  l : (q + 1) ^ deg ≤ T
  w : foldCwE (natBitLength (Stars.Carrier.code X)) (atomsOf (Stars.Carrier.code X)).length + 1 ≤ T

theorem natWord_ne (x : ℕ) : natWord x ≠ [] := by
  intro h; have := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x; rw [h] at this; simp at this

theorem codesWord_append (m : Mode) {q : ℕ} (a b : List (m.Circuit q)) :
    codesWord m (a ++ b) = codesWord m a ++ codesWord m b := by
  simp [codesWord, List.map_append, List.flatten_append]

theorem codesWord_single (m : Mode) {q : ℕ} (c : m.Circuit q) : codesWord m [c] = natWord (m.code c) := by
  simp [codesWord]

/-! ## One variable -/

section Fold
variable {m : Mode} {q : ℕ}

/-- The round's fuel at variable `X`. -/
noncomputable def rcost (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (T Wa X : ℕ) : ℕ :=
  FrontFoldRound.roundCost q Wa X (Pw.K * ((bitmap (F.supp X)).length + q + 1) ^ Pw.d)
    (Cw.K * ((codesWord m (F.cs X)).length + q + 1) ^ Cw.d) (envCodeCost (Stars.Carrier.code (F.car X)) T)
    ((List.range X).map F.pw) ((List.range X).map F.cw) (codesWord m (F.atoms X)) (F.pw X) (F.cw X)

theorem ys_get (F : FoldIn m q) (X : ℕ) (h : X < F.ys.length) : F.ys[X] = bitmap (F.supp X) := by
  simp [FoldIn.ys]

theorem as_get (F : FoldIn m q) (X : ℕ) (h : X < F.as.length) : F.as[X] = codesWord m (F.atoms X) := by
  simp [FoldIn.as]

theorem cs_word' (F : FoldIn m q) (X : ℕ) :
    codesWord m (F.cs X) = codesWord m (F.atoms X) ++ if X < F.sys then F.pw X else [] := by
  simp only [FoldIn.cs, codesWord_append]
  split_ifs
  · rw [codesWord_single]; rfl
  · simp [codesWord]

theorem bitmap_len (S : Finset (Fin q)) : (bitmap S).length = q := by simp [bitmap]

theorem ys_len (F : FoldIn m q) : ∀ y ∈ F.ys, y.length ≤ q := by
  intro y hy
  obtain ⟨X, -, rfl⟩ := List.mem_map.mp hy
  rw [bitmap_len]

theorem kept_eq {tP tC : ℕ} (f g : Fin (1220 + tP + tC) → List Bool)
    (h : ∀ k : Fin 10, f (fx tP tC (k.castLE (by norm_num))) = g (fx tP tC (k.castLE (by norm_num)))) :
    ∀ t : Fin (1220 + tP + tC), t.val < 10 → f t = g t := by
  intro t ht
  have e : fx tP tC ((⟨t.val, ht⟩ : Fin 10).castLE (by norm_num)) = t := Fin.ext rfl
  rw [← e]; exact h _

/-- **One variable's round** in the fold: from the state after `X` variables to the state after `X + 1`. -/
theorem round_X (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (deg T Z0 Wa X : ℕ)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hX : X < F.nv) (hZ0 : F.nv + 1 ≤ Z0) (henv : EnvFit (F.car X) deg T) :
    ∃ out : Fin (1220 + Pw.t + Cw.t) → List Bool,
      ClockJoin.ReadyRun (FrontFoldRound.roundM Pw.M Pw.inS Pw.outS Cw.M Cw.inS Cw.outS) (rcost Pw Cw F T Wa X)
        (F.st deg T Z0 X Pw.t Cw.t) out ∧
      ∀ t : Fin (1220 + Pw.t + Cw.t), t.val < 10 → out t = F.st deg T Z0 (X + 1) Pw.t Cw.t t := by
  have hXy : X < F.ys.length := by simp [FoldIn.ys]; exact hX
  have hXa : X < F.as.length := by simp [FoldIn.as]; exact hX
  obtain ⟨JP, -, hP⟩ := Pw.parity_ready q (F.supp X)
  obtain ⟨JC, -, hC⟩ := Cw.carrier_ready q (F.cs X)
  obtain ⟨outE, hE, -, hE1, hE2, hE3⟩ := CWEnvSem.envelope_step (F.car X) deg T henv.c henv.s henv.l henv.w
  have hP' : ClockJoin.ReadyRun Pw.M (Pw.K * ((bitmap (F.supp X)).length + q + 1) ^ Pw.d)
      (inBank Pw.inS F.ys[X]) (outBankJ Pw.inS Pw.outS F.ys[X] (F.pw X) JP) := by
    rw [ys_get F X hXy]; exact hP
  obtain ⟨out, st, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := round_run Pw.M Pw.inS Pw.outS Pw.hio Cw.M Cw.inS
    Cw.outS Cw.hio F.ys F.as q Wa (ys_len F) hWa X (Z0 - X) F.sys hXy hXa (by omega)
    ((List.range X).map F.pw) ((List.range X).map F.cw)
    (fun g hg => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg; exact natWord_ne _)
    (fun g hg => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg; exact natWord_ne _)
    ((List.range X).map (F.eb deg)) (by simp) ((q + 1) ^ deg) T (F.pw X) JP _ hP' (codesWord m (F.atoms X))
    (as_get F X hXa) (codesWord m (F.cs X)) (cs_word' F X) (Stars.Carrier.code (F.car X)) JC _ hC (F.eb deg X) _
    outE hE hE1 hE2 hE3
  refine ⟨out, FrontKit.ready_of_step st, kept_eq _ _ ?_⟩
  have hZ : Z0 - X - 1 = Z0 - (X + 1) := by omega
  intro k
  fin_cases k
  · exact o0
  · show out (fx _ _ 1) = _; rw [o1, hZ]; rfl
  · exact o2
  · show out (fx _ _ 3) = _; rw [o3, hZ]; rfl
  · exact o4
  · show out (fx _ _ 5) = _; rw [o5]; show _ = ((List.range (X + 1)).map F.pw).flatMap frame
    rw [List.range_succ, List.map_append]; rfl
  · show out (fx _ _ 6) = _; rw [o6]; show _ = ((List.range (X + 1)).map F.cw).flatMap frame
    rw [List.range_succ, List.map_append]; rfl
  · show out (fx _ _ 7) = _; rw [o7]; show _ = (List.range (X + 1)).map (F.eb deg)
    rw [List.range_succ, List.map_append]; rfl
  · exact o8
  · exact o9

end Fold

/-! ## Every variable -/

section Loop
variable {m : Mode} {q : ℕ}

/-- The fold's scratch: every tape but the kept tapes `0..9`. -/
def scrF (tP tC : ℕ) (j : Fin (1210 + tP + tC)) : Fin (1220 + tP + tC) := ⟨j.val + 10, by omega⟩

theorem scrF_inj (tP tC : ℕ) : Function.Injective (scrF tP tC) := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp [scrF] at this; omega)

theorem scrF_iff (tP tC : ℕ) (t : Fin (1220 + tP + tC)) : (∃ j, scrF tP tC j = t) ↔ 10 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scrF]
  · intro h; exact ⟨⟨t.val - 10, by omega⟩, Fin.ext (by simp [scrF]; omega)⟩

/-- **The writers' fold.** -/
noncomputable def foldM (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) :=
  foldLoop (foldBody (FrontFoldRound.roundM Pw.M Pw.inS Pw.outS Cw.M Cw.inS Cw.outS) (scrF Pw.t Cw.t)
    (idleA (1220 + Pw.t + Cw.t + 2)))

/-- **The writers' fold is ready**: from the padded state before any variable and the unary count `nv`, the fold ends
at the padded state after every variable: the parity codes, the carrier codes and the envelope bits of all `nv`
variables, for a uniform round fuel `cw` and a width `total` that dominates it and every kept tape. -/
theorem fold_run (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (deg T Z0 Wa : ℕ)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ Z0) (henv : ∀ X < F.nv, EnvFit (F.car X) deg T)
    (total capT cw : ℕ) (hcap : total + 1 ≤ capT) (hcw : ∀ X < F.nv, rcost Pw Cw F T Wa X ≤ cw)
    (hcwT : cw + 1 ≤ total) (hlen : ∀ X ≤ F.nv, ∀ t, (F.st deg T Z0 X Pw.t Cw.t t).length ≤ total) :
    ClockJoin.ReadyRun (foldM Pw Cw) (1 + 1 + (F.nv * (cw + 1 + (2 * total + 4 + 1 + 0) + 2) + F.nv + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch (scrF Pw.t Cw.t) total (F.st deg T Z0 0 Pw.t Cw.t)) total capT)
        (fun _ => CompareMachine.word F.nv))
      (Fin.addCases (roundTapes (padScratch (scrF Pw.t Cw.t) total (F.st deg T Z0 F.nv Pw.t Cw.t)) total capT)
        (fun _ => CompareMachine.word F.nv)) := by
  have hround : ∀ X, ∃ out : Fin (1220 + Pw.t + Cw.t) → List Bool, X < F.nv →
      ClockJoin.ReadyRun (FrontFoldRound.roundM Pw.M Pw.inS Pw.outS Cw.M Cw.inS Cw.outS) cw
        (F.st deg T Z0 X Pw.t Cw.t) out ∧
      ∀ t : Fin (1220 + Pw.t + Cw.t), t.val < 10 → out t = F.st deg T Z0 (X + 1) Pw.t Cw.t t := by
    intro X
    by_cases hX : X < F.nv
    · obtain ⟨out, h1, h2⟩ := round_X Pw Cw F deg T Z0 Wa X hWa hX hZ0 (henv X hX)
      exact ⟨out, fun _ => ⟨ClockJoin.enlarge _ _ _ _ _ h1 (hcw X hX), h2⟩⟩
    · exact ⟨fun _ => [], fun h => absurd h hX⟩
  choose Q' hQ' using hround
  have hwork : ∀ X, X < F.nv → ClockJoin.ReadyRun (FrontFoldRound.roundM Pw.M Pw.inS Pw.outS Cw.M Cw.inS Cw.outS) cw
      (F.st deg T Z0 X Pw.t Cw.t) (Q' X) := fun X hX => (hQ' X hX).1
  exact uniformFold_ready (FrontFoldRound.roundM Pw.M Pw.inS Pw.outS Cw.M Cw.inS Cw.outS) (scrF Pw.t Cw.t)
    (scrF_inj Pw.t Cw.t) (idleA (1220 + Pw.t + Cw.t + 2)) total capT cw 0 F.nv hcap
    (fun X => F.st deg T Z0 X Pw.t Cw.t) Q' hwork
    (fun X hX j => by
      have hl := ready_lengths (hwork X hX) total (hlen X hX.le) (scrF Pw.t Cw.t j)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun X hX => by
      have e : blankScratch (scrF Pw.t Cw.t) (Q' X) = F.st deg T Z0 (X + 1) Pw.t Cw.t := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ i, scrF Pw.t Cw.t i = t
        · rw [if_pos ht]
          have h10 := (scrF_iff Pw.t Cw.t t).mp ht
          simp only [FoldIn.st, Qf]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm
        · rw [if_neg ht]
          have h10 : t.val < 10 := by
            by_contra hc; exact ht ((scrF_iff Pw.t Cw.t t).mpr (by omega))
          exact (hQ' X hX).2 t h10
      rw [e]; exact idleA_ready _ _)

end Loop

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
