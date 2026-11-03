import Proof.Packets.PacketsMetaSetup

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.PacketsMeta.CutoffMath
noncomputable section

namespace Prog
open Lev Setup Tail

/-- A framed field's cells. -/
def rdF (w : List Bool) : ℕ → Bool := fun j => readTapeBit (RepairOrdinary.frame w) j

/-- The entry roles (PG's `field_run2` bank: `frame topWord` on 0, `frame nativeWord` on 2). -/
def σ0 (nw tw : List Bool) : Fin 60 → TS :=
  ![.cells (rdF tw) 0, .out 0, .cells (rdF nw) 0, .cells (Ruler.rb 1) 0, .flag false, .reg 0, .cells blank 0,
    .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0,
    .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg 0]

/-- The roles after the header. -/
def Hv (nw tw : List Bool) (p7 r50 r51 r52 : ℕ) (b : Bool) : Fin 60 → TS :=
  ![.cells (rdF tw) (0 + (RepairOrdinary.frame tw).length), .out 0,
    .cells (rdF nw) (0 + (RepairOrdinary.frame nw).length), .ruler, .flag b, .reg 0, .cells blank 0,
    .cells (sf nw) p7, .cells (sf (List.replicate nw.length true)) p7, .cells (sf tw) 1,
    .cells (sf (List.replicate tw.length true)) 1, .cells blank 0, .cells blank 0, .cells blank 0,
    .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .cells blank 0, .reg 0, .reg 0, .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0,
    .reg 0, .reg 0, .reg r50, .reg r51, .reg r52, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0, .reg 0]

/-- Only the output is kept. -/
def outOnly (v : ℕ) : Fin 60 → TS := Function.update (fun _ => .any) 1 (.out v)

theorem weaken_out {s W n : ℕ} {P : Machine 60 s} {σ σ' : Fin 60 → TS} (h : LRuns W P n σ σ') (v : ℕ)
    (hv : σ' 1 = .out v) : LRuns W P n σ (outOnly v) := by
  refine h.weaken (fun i H A hA => ?_)
  by_cases hi : i = 1
  · subst hi
    rw [hv] at hA
    simpa [outOnly] using hA
  · simp only [outOnly, Function.update_of_ne hi]
    trivial

theorem sf_read (nw A B C : List Bool) (h : nw = A ++ B ++ C) :
    ∀ k, k < B.length → sf nw (1 + A.length + k) = B.getD k false :=
  read_sub (sf nw) 1 A B C (by intro k _; rw [Nat.add_comm, sf_succ, h])

theorem rfinish_at' {N W : ℕ} (σ : Fin N → TS) (r : Fin N) (P : ℕ) (hr : σ r = .cells (Ruler.rb P) P)
    (hP : P = W + 1) : LRuns W (RecoveryFocus.machine ![r] Ruler.finish) (W + 3) σ (Function.update σ r .ruler) := by
  subst hP
  exact rfinish_at σ r hr

/-! ## The header -/

def hdrM := Composition.machine (RecoveryFocus.machine (![2, 7, 8] : Fin 3 → Fin 60) Unframe.machine)
  (Composition.machine (RecoveryFocus.machine (![0, 9, 10] : Fin 3 → Fin 60) Unframe.machine)
  (Composition.machine (RecoveryFocus.machine (![3] : Fin 1 → Fin 60) moveR)
  (Composition.machine (RecoveryFocus.machine (![8, 7, 3] : Fin 3 → Fin 60) (Ruler.append 32))
  (Composition.machine (RecoveryFocus.machine (![10, 9, 3] : Fin 3 → Fin 60) (Ruler.append 32))
  (Composition.machine (RecoveryFocus.machine (![3] : Fin 1 → Fin 60) Ruler.finish)
    (ReadNat.at5 (N := 60) 3 7 8 6 51))))))

def hdrCost (nw tw : List Bool) (W : ℕ) : ℕ :=
  (5 * nw.length + 10) + 1 + ((5 * tw.length + 10) + 1 + (1 + 1 + (((32 + 1) * nw.length + nw.length + 7) + 1 +
    (((32 + 1) * tw.length + tw.length + 7) + 1 + ((W + 3) + 1 + (3 * W + 5))))))

theorem hdr_run (nw tw rest : List Bool) (tag : ℕ) (hnw : nw = natWord tag ++ rest) (W : ℕ)
    (hW : W = 32 * (nw.length + tw.length)) (htag : natBitLength tag ≤ W) :
    LRuns W hdrM (hdrCost nw tw W) (σ0 nw tw) (Hv nw tw (1 + (natWord tag).length) 0 tag 0 false) := by
  have hX : ∀ w : List Bool, ∀ i, i < (RepairOrdinary.frame w).length →
      rdF w (0 + i) = (RepairOrdinary.frame w).getD i false := by
    intro w i _
    simp [rdF, readTapeBit]
  have hS : ∀ i, i < (natWord tag).length → sf nw (1 + i) = (natWord tag).getD i false := by
    intro i hi
    have h := sf_read nw [] (natWord tag) rest (by rw [hnw]; rfl) i hi
    simpa using h
  have hall := (unframe_at (W := W) (σ0 nw tw) 2 7 8 (by decide) 0 nw (rdF nw) (hX nw) rfl rfl rfl).seq
    ((unframe_at (W := W) _ 0 9 10 (by decide) 0 tw (rdF tw) (hX tw) (by rfl) (by rfl) (by rfl)).seq
    ((moveR_at (W := W) _ 3 0 (Ruler.rb 1) (by rfl)).seq
    ((rappend_at (W := W) _ 8 7 3 (by decide) 32 (by norm_num) nw.length 1 (le_refl 1) (sf nw) (by rfl) (by rfl)
      (by rfl)).seq
    ((rappend_at (W := W) _ 10 9 3 (by decide) 32 (by norm_num) tw.length (1 + 32 * nw.length) (by omega) (sf tw)
      (by rfl) (by rfl) (by rfl)).seq
    ((rfinish_at' (W := W) _ 3 (1 + 32 * nw.length + 32 * tw.length) (by rfl) (by rw [hW]; ring)).seq
    (ReadNat.at_run (W := W) _ 3 7 8 6 51 (by decide) 1 tag 0 (sf nw) (sf (List.replicate nw.length true)) htag hS
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))))
  refine hall.congr_out ?_
  funext i
  fin_cases i <;> rfl

/-! ## The THR main -/

def tailSlots : Fin 17 → Fin 60 := ![3, 4, 5, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 41, 42, 1]

theorem tailSlots_inj : Function.Injective tailSlots := by decide

def thrM {sT : ℕ} (Tm : Machine 17 sT) :=
  Composition.machine (Composition.machine (ReadNat.at5 (N := 60) 3 7 8 6 52)
    (Composition.machine (ReadNat.at5 (N := 60) 3 7 8 6 52) (ReadNat.at5 (N := 60) 3 7 8 6 50)))
  (Composition.machine extAll (Composition.machine loops (RecoveryFocus.machine tailSlots Tm)))

def thrCost (W : ℕ) (ds : List CD) (nT : ℕ) : ℕ :=
  ((3 * W + 5) + 1 + ((3 * W + 5) + 1 + (3 * W + 5))) + 1 + (extCost ds + 1 + (loopsCost W (dOf ds) + 1 + nT))

/-- The loop entry state. -/
def g0 (b : Bool) : GS := ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, b⟩

/-- The two accumulator values. -/
def Fv (ds : List CD) : ℕ :=
  nestedSum (tab (dOf ds 0)) (tab (dOf ds 1)) (tab (dOf ds 2)) (tab (dOf ds 3)) selMag
def Cv (ds : List CD) : ℕ :=
  (tab (dOf ds 0)).length * ((tab (dOf ds 1)).length * ((tab (dOf ds 2)).length * ((tab (dOf ds 3)).length * 1)))

theorem gv_entry (fx : Fin 60 → TS) (ds : List CD) (p : ℕ) (b : Bool) (h6 : fx 6 = .cells blank 0)
    (hreg : ∀ i : Fin 60, 19 ≤ i.val → i.val ≤ 49 → fx i = .reg 0) :
    Gv (Sv fx (twOf ds) (fun c => some (pay (dOf ds c))) p b) (dOf ds) (g0 b) =
      Sv fx (twOf ds) (fun c => some (pay (dOf ds c))) p b := by
  funext i
  fin_cases i <;> simp [Gv, Sv, g0, sOf, mOf, mk, h6] <;> exact (hreg _ (by decide) (by decide)).symm

theorem hv_regs (nw tw : List Bool) (p7 r50 r51 r52 : ℕ) (b : Bool) :
    ∀ i : Fin 60, 19 ≤ i.val → i.val ≤ 49 → Hv nw tw p7 r50 r51 r52 b i = .reg 0 := by
  intro i h1 h2
  fin_cases i <;> simp_all [Hv]

theorem hv_sv (nw tw : List Bool) (p7 r50 r51 r52 : ℕ) (b : Bool) :
    Hv nw tw p7 r50 r51 r52 b = Sv (Hv nw tw p7 r50 r51 r52 b) tw (fun _ => none) 1 b := by
  funext i
  fin_cases i <;> rfl

theorem reads_hv (nw tw : List Bool) (p0 p1 p2 p3 q L tgt : ℕ) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Hv nw tw p0 0 0 0 false)
        7 (.cells (sf nw) p1)) 8 (.cells (sf (List.replicate nw.length true)) p1)) 52 (.reg q))
        7 (.cells (sf nw) p2)) 8 (.cells (sf (List.replicate nw.length true)) p2)) 52 (.reg L))
        7 (.cells (sf nw) p3)) 8 (.cells (sf (List.replicate nw.length true)) p3)) 50 (.reg tgt) =
      Hv nw tw p3 tgt 0 L false := by
  funext i
  fin_cases i <;> rfl

theorem thr_run (nw rest : List Bool) (q L tgt : ℕ)
    (hnw : nw = natWord 1 ++ natWord q ++ natWord L ++ natWord tgt ++ rest) (ds : List CD) (W : ℕ)
    (hq : natBitLength q ≤ W) (hL : natBitLength L ≤ W) (ht : natBitLength tgt ≤ W) (hW1 : 1 ≤ W) (R : ℕ)
    (hR : 4 * R + 11 ≤ W) (hfit : ∀ j, Fits W (dOf ds j))
    (hrec : ∀ (j : Fin 4) (x : Rec), x ∈ tab (dOf ds j) → recMag x < 2 ^ R)
    (hFm : Fv ds < 2 ^ W) (hCm : Cv ds < 2 ^ W)
    {sT : ℕ} (Tm : Machine 17 sT) (nT : ℕ) (ρT : Fin 17 → TS) (v : ℕ)
    (hT : ∀ b, LRuns W Tm nT (tst (Fv ds) (Cv ds) tgt 0 0 0 0 0 0 0 0 b 0) ρT) (hv : ρT 16 = .out v) :
    LRuns W (thrM Tm) (thrCost W ds nT) (Hv nw (twOf ds) (1 + (natWord 1).length) 0 0 0 false) (outOnly v) := by
  have hSq : ∀ i, i < (natWord q).length →
      sf nw (1 + (natWord 1).length + i) = (natWord q).getD i false :=
    sf_read nw (natWord 1) (natWord q) (natWord L ++ natWord tgt ++ rest) (by rw [hnw]; simp [List.append_assoc])
  have hSL : ∀ i, i < (natWord L).length →
      sf nw (1 + (natWord 1).length + (natWord q).length + i) = (natWord L).getD i false := by
    intro i hi
    have h := sf_read nw (natWord 1 ++ natWord q) (natWord L) (natWord tgt ++ rest)
      (by rw [hnw]; simp [List.append_assoc]) i hi
    rw [List.length_append, ← Nat.add_assoc] at h
    exact h
  have hSt : ∀ i, i < (natWord tgt).length →
      sf nw (1 + (natWord 1).length + (natWord q).length + (natWord L).length + i) = (natWord tgt).getD i false := by
    intro i hi
    have h := sf_read nw (natWord 1 ++ natWord q ++ natWord L) (natWord tgt) rest
      (by rw [hnw]) i hi
    rw [List.length_append, List.length_append, ← Nat.add_assoc, ← Nat.add_assoc] at h
    exact h
  have hR3 := (ReadNat.at_run (W := W) (Hv nw (twOf ds) (1 + (natWord 1).length) 0 0 0 false) 3 7 8 6 52 (by decide)
      (1 + (natWord 1).length) q 0 (sf nw) (sf (List.replicate nw.length true)) hq hSq rfl rfl rfl rfl rfl).seq
    ((ReadNat.at_run (W := W) _ 3 7 8 6 52 (by decide) (1 + (natWord 1).length + (natWord q).length) L q (sf nw)
      (sf (List.replicate nw.length true)) hL hSL (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).seq
    (ReadNat.at_run (W := W) _ 3 7 8 6 50 (by decide)
      (1 + (natWord 1).length + (natWord q).length + (natWord L).length) tgt 0 (sf nw)
      (sf (List.replicate nw.length true)) ht hSt (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))
  have hR3' := hR3.congr_out ((reads_hv nw (twOf ds) _ _ _ _ q L tgt).trans (hv_sv nw (twOf ds) _ tgt 0 L false))
  have hE := ext_run (W := W)
    (Hv nw (twOf ds) (1 + (natWord 1).length + (natWord q).length + (natWord L).length + (natWord tgt).length)
      tgt 0 L false) ds false
  have hInR : InR (dOf ds) (g0 (decide (3 < ds.length))) := by
    intro j
    refine ⟨le_refl 1, ?_⟩
    show 1 ≤ (pay (dOf ds j)).length + 1
    omega
  have hLp := loops_run (W := W)
    (Sv (Hv nw (twOf ds) (1 + (natWord 1).length + (natWord q).length + (natWord L).length + (natWord tgt).length)
      tgt 0 L false) (twOf ds) (fun c => some (pay (dOf ds c))) (p9 ds 4) (decide (3 < ds.length)))
    (dOf ds) rfl rfl hW1 R hR hfit hrec (Fv ds) (Cv ds) hFm hCm
    (g0 (decide (3 < ds.length))) hInR (by simp [g0, Fv]) (by simp [g0, Cv])
  rw [gv_entry _ ds _ _ rfl (hv_regs _ _ _ _ _ _ _)] at hLp
  have hFv : (loopS (dOf ds) (g0 (decide (3 < ds.length)))).f = Fv ds := by
    rw [loopS_f]
    simp [g0, Fv]
  have hCv : (loopS (dOf ds) (g0 (decide (3 < ds.length)))).cnt = Cv ds := by
    rw [loopS_cnt]
    simp [g0, Cv]
  have hT' := (hT (loopS (dOf ds) (g0 (decide (3 < ds.length)))).fl).congr_in
    (σ0 := tst (loopS (dOf ds) (g0 (decide (3 < ds.length)))).f (loopS (dOf ds) (g0 (decide (3 < ds.length)))).cnt
      tgt 0 0 0 0 0 0 0 0 (loopS (dOf ds) (g0 (decide (3 < ds.length)))).fl 0) (by rw [hFv, hCv])
  have hD := hT'.dock tailSlots tailSlots_inj
    (Gv (Sv (Hv nw (twOf ds) (1 + (natWord 1).length + (natWord q).length + (natWord L).length +
      (natWord tgt).length) tgt 0 L false) (twOf ds) (fun c => some (pay (dOf ds c))) (p9 ds 4)
      (decide (3 < ds.length))) (dOf ds) (loopS (dOf ds) (g0 (decide (3 < ds.length)))))
    (by intro j; fin_cases j <;> simp [Gv, Sv, Hv, tst, tailSlots])
  have hall := hR3'.seq (hE.seq (hLp.seq hD))
  refine weaken_out hall v ?_
  have e1 : (1 : Fin 60) = tailSlots 16 := rfl
  rw [e1, dockS_slot tailSlots tailSlots_inj]
  exact hv

/-! ## The whole program: header, then the tag dispatch -/

def dispC := swAt subF false false (3 : Fin 60) 5 51 4
def dispC2 := Composition.machine (swAt subF true true (3 : Fin 60) 51 5 4) (swAt subF false false (3 : Fin 60) 5 51 4)

/-- **The cutoff/`|Sel|` program**, one fixed machine for every request (the tail `Tm` is fixed). -/
def prog {sT : ℕ} (Tm : Machine 17 sT) :=
  Composition.machine hdrM (Ite dispC (Ite dispC2 (nop 60) (thrM Tm) 4) (nop 60) 4)

theorem two_le (W : ℕ) (hW : 2 ≤ W) : 4 ≤ 2 ^ W :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW

/-- SYM (tag 0): empty output. -/
theorem prog_sym {sT : ℕ} (Tm : Machine 17 sT) (nw tw rest : List Bool) (hnw : nw = natWord 0 ++ rest) (W : ℕ)
    (hW : W = 32 * (nw.length + tw.length)) (h2 : 2 ≤ W) :
    LRuns W (prog Tm) (hdrCost nw tw W + 1 + ((2 * W + 3) + 0 + 0 + 2)) (σ0 nw tw) (outOnly 0) := by
  have h4 := two_le W h2
  have hH := hdr_run nw tw rest 0 hnw W hW (by simp [natBitLength]; omega)
  have hO : LRuns W (Ite dispC (Ite dispC2 (nop 60) (thrM Tm) 4) (nop 60) 4) ((2 * W + 3) + 0 + 0 + 2)
      (Hv nw tw (1 + (natWord 0).length) 0 0 0 false) (outOnly 0) :=
    Ite.runs (W := W) (nc := 2 * W + 3) (np := 0) (nq := 0) _ _ _ 4 (decide (0 < 0))
      (lt_at (W := W) (Hv nw tw (1 + (natWord 0).length) 0 0 0 false) 3 5 51 4 (by decide) 0 0 false rfl rfl rfl rfl
        (by omega) (by omega)) rfl
      (fun h => absurd h (by decide))
      (fun _ => weaken_out (nop_lruns _) 0 rfl)
  exact hH.seq hO

/-- Terminal (tag 2): empty output. -/
theorem prog_term {sT : ℕ} (Tm : Machine 17 sT) (nw tw : List Bool) (hnw : nw = natWord 2 ++ []) (W : ℕ)
    (hW : W = 32 * (nw.length + tw.length)) (h2 : 2 ≤ W) :
    LRuns W (prog Tm) (hdrCost nw tw W + 1 + ((2 * W + 3) + (((2 * W + 3) + 1 + (2 * W + 3)) + 0 + 0 + 2) + 0 + 2))
      (σ0 nw tw) (outOnly 0) := by
  have h4 := two_le W h2
  have hb2 : natBitLength 2 ≤ W := by
    have e := ReadNat.natWord_length 2
    have hl : (natWord 2).length ≤ nw.length := by rw [hnw, List.append_nil]
    omega
  have hH := hdr_run nw tw [] 2 hnw W hW hb2
  have hO : LRuns W (Ite dispC (Ite dispC2 (nop 60) (thrM Tm) 4) (nop 60) 4)
      ((2 * W + 3) + (((2 * W + 3) + 1 + (2 * W + 3)) + 0 + 0 + 2) + 0 + 2)
      (Hv nw tw (1 + (natWord 2).length) 0 2 0 false) (outOnly 0) :=
    Ite.runs (W := W) (nc := 2 * W + 3) (np := ((2 * W + 3) + 1 + (2 * W + 3)) + 0 + 0 + 2) (nq := 0) _ _ _ 4
      (decide (0 < 2))
      (lt_at (W := W) (Hv nw tw (1 + (natWord 2).length) 0 2 0 false) 3 5 51 4 (by decide) 0 2 false rfl rfl rfl rfl
        (by omega) (by omega)) rfl
      (fun _ => Ite.runs (W := W) (nc := (2 * W + 3) + 1 + (2 * W + 3)) (np := 0) (nq := 0) _ _ _ 4 (decide (0 < 2 - 1))
        ((dec_at (W := W) _ 3 51 5 4 (by decide) 2 0 (decide (0 < 2)) (by rfl) (by rfl) (by rfl) (by rfl) rfl
          (by omega) (by omega)).seq
          (lt_at (W := W) _ 3 5 51 4 (by decide) 0 (2 - 1) false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)
            (by omega))) rfl
        (fun _ => weaken_out (nop_lruns _) 0 rfl)
        (fun h => absurd h (by decide)))
      (fun h => absurd h (by decide))
  exact hH.seq hO

/-- THR (tag 1): the tail's output. -/
theorem prog_thr (nw rest : List Bool) (q L tgt : ℕ)
    (hnw : nw = natWord 1 ++ natWord q ++ natWord L ++ natWord tgt ++ rest) (ds : List CD) (W : ℕ)
    (hW : W = 32 * (nw.length + (twOf ds).length)) (h2 : 2 ≤ W)
    (hq : natBitLength q ≤ W) (hL : natBitLength L ≤ W) (ht : natBitLength tgt ≤ W) (R : ℕ)
    (hR : 4 * R + 11 ≤ W) (hfit : ∀ j, Fits W (dOf ds j))
    (hrec : ∀ (j : Fin 4) (x : Rec), x ∈ tab (dOf ds j) → recMag x < 2 ^ R)
    (hFm : Fv ds < 2 ^ W) (hCm : Cv ds < 2 ^ W)
    {sT : ℕ} (Tm : Machine 17 sT) (nT : ℕ) (ρT : Fin 17 → TS) (v : ℕ)
    (hT : ∀ b, LRuns W Tm nT (tst (Fv ds) (Cv ds) tgt 0 0 0 0 0 0 0 0 b 0) ρT) (hv : ρT 16 = .out v) :
    LRuns W (prog Tm) (hdrCost nw (twOf ds) W + 1 +
      ((2 * W + 3) + (((2 * W + 3) + 1 + (2 * W + 3)) + 0 + thrCost W ds nT + 2) + 0 + 2))
      (σ0 nw (twOf ds)) (outOnly v) := by
  have h4 := two_le W h2
  have hH := hdr_run nw (twOf ds) (natWord q ++ natWord L ++ natWord tgt ++ rest) 1
    (by rw [hnw]; simp [List.append_assoc]) W hW (by simp [natBitLength]; omega)
  have hThr := thr_run nw rest q L tgt hnw ds W hq hL ht (by omega) R hR hfit hrec hFm hCm Tm nT ρT v hT hv
  have hO : LRuns W (Ite dispC (Ite dispC2 (nop 60) (thrM Tm) 4) (nop 60) 4)
      ((2 * W + 3) + (((2 * W + 3) + 1 + (2 * W + 3)) + 0 + thrCost W ds nT + 2) + 0 + 2)
      (Hv nw (twOf ds) (1 + (natWord 1).length) 0 1 0 false) (outOnly v) :=
    Ite.runs (W := W) (nc := 2 * W + 3) (np := ((2 * W + 3) + 1 + (2 * W + 3)) + 0 + thrCost W ds nT + 2) (nq := 0)
      _ _ _ 4 (decide (0 < 1))
      (lt_at (W := W) (Hv nw (twOf ds) (1 + (natWord 1).length) 0 1 0 false) 3 5 51 4 (by decide) 0 1 false
        rfl rfl rfl rfl (by omega) (by omega)) rfl
      (fun _ => Ite.runs (W := W) (nc := (2 * W + 3) + 1 + (2 * W + 3)) (np := 0) (nq := thrCost W ds nT) _ _ _ 4
        (decide (0 < 1 - 1))
        ((dec_at (W := W) _ 3 51 5 4 (by decide) 1 0 (decide (0 < 1)) (by rfl) (by rfl) (by rfl) (by rfl) rfl
          (by omega) (by omega)).seq
          (lt_at (W := W) _ 3 5 51 4 (by decide) 0 (1 - 1) false (by rfl) (by rfl) (by rfl) (by rfl) (by omega)
            (by omega))) rfl
        (fun h => absurd h (by decide))
        (fun _ => hThr.congr_in (by funext i; fin_cases i <;> rfl)))
      (fun h => absurd h (by decide))
  exact hH.seq hO

end Prog

end
end NearCubicWires.PacketsMeta

