import Proof.Rows.RowsSymC5Pure
import Proof.MachineModel.OrdinaryAdd

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymC5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep
open RowsConstruction.KeyTop (cellPort slR slS slR_injective slS_injective carryCost wl_master wl_cell
  wl_loop_update wl_c5_update loopBank_update c5_seed_update masterPort_val cellPort_val c5Port_val)
noncomputable section

/-! ## 1. Ports, slot maps and the stages -/

section Ports
variable (NI : Nat)

theorem initPort_val' (i : Fin NI) : (initPort NI i).val = 2 + i.val := by
  simp [initPort]

/-- C5 port of offset digit `c` (3–6). -/
def offP (c : Fin 4) : Fin 16 := ⟨3 + c.val, by omega⟩

def fIx (c : Fin 4) : Fin 9 := ⟨4 + c.val, by omega⟩
def zIx : Fin 9 := 8

/-- Recompute scratch map for target `c` (only slots 0 and 3 are used, by `KeyStep.incM`): master `140+c`, the
flag word, cells 0–3, clock, log. -/
def slT (ini : Fin 9 → Fin NI) (c : Fin 4) : Fin 8 → Fin (2+rowsWork NI) :=
  ![masterPort NI (tgtP c), initPort NI (ini (fIx c)), cellPort NI 0, cellPort NI 1, cellPort NI 2, cellPort NI 3,
    cellPort NI 254, cellPort NI 255]

theorem slT_injective (ini : Fin 9 → Fin NI) (c : Fin 4) : Function.Injective (slT NI ini c) := by
  intro x y h
  have hv := congrArg Fin.val h
  have h1 := (ini (fIx c)).isLt
  have h2 := c.isLt
  fin_cases x <;> fin_cases y <;> simp [slT, masterPort_val, cellPort_val, initPort_val', tgtP] at hv ⊢ <;> omega

/-- The no-op: flag reset of the blank cell 0 (clock 254, log 255). -/
def noop := rstM (slR NI)

/-- Add slots: two summands, the destination, the log cell 3. -/
def addSl (src off dst : Fin (2+rowsWork NI)) : Fin (3+1) → Fin (2+rowsWork NI) := ![src, off, dst, cellPort NI 3]

def addM (src off dst : Fin (2+rowsWork NI)) := RecoveryFocus.machine (addSl NI src off dst)
  (MaskedReset.machine NearCubicWires.RepairOrdinary.Add.machine (fun _ => true))

theorem addSl_injective (src off dst : Fin (2+rowsWork NI)) (h01 : src ≠ off) (h02 : src ≠ dst)
    (h03 : src ≠ cellPort NI 3) (h12 : off ≠ dst) (h13 : off ≠ cellPort NI 3) (h23 : dst ≠ cellPort NI 3) :
    Function.Injective (addSl NI src off dst) := by
  intro x y h
  fin_cases x <;> fin_cases y
  all_goals first
    | rfl
    | exact absurd h h01
    | exact absurd h.symm h01
    | exact absurd h h02
    | exact absurd h.symm h02
    | exact absurd h h03
    | exact absurd h.symm h03
    | exact absurd h h12
    | exact absurd h.symm h12
    | exact absurd h h13
    | exact absurd h.symm h13
    | exact absurd h h23
    | exact absurd h.symm h23

/-- Target 0 := offset 0 (+ the zero word). -/
def body0 (ini : Fin 9 → Fin NI) :=
  addM NI (c5Port NI (offP 0)) (initPort NI (ini zIx)) (masterPort NI (tgtP 0))

/-- Target `c` := target `p` + offset `c` + 1. -/
def bodyS (ini : Fin 9 → Fin NI) (p c : Fin 4) :=
  Composition.machine (addM NI (masterPort NI (tgtP p)) (c5Port NI (offP c)) (masterPort NI (tgtP c)))
    (incM (slT NI ini c))

/-- Target stage `c`: switch on the resident active flag. -/
def tstage (ini : Fin 9 → Fin NI) (c : Fin 4) {s : Nat}
    (body : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) s) :=
  CloseoutRowsOriginalSwitch.machine body (noop NI) (initPort NI (ini (fIx c)))

/-- The target recompute. -/
def recomp (ini : Fin 9 → Fin NI) :=
  Composition.machine (tstage NI ini 0 (body0 NI ini)) (Composition.machine (tstage NI ini 1 (bodyS NI ini 0 1))
    (Composition.machine (tstage NI ini 2 (bodyS NI ini 1 2)) (tstage NI ini 3 (bodyS NI ini 2 3))))

end Ports

/-! ## 2. Costs -/

def tcost (w R : Nat) : Nat := (2*(2*w+1)+2) + 1 + (4*w+2) + (2*R+4) + 2

def recCost (w R : Nat) : Nat := tcost w R + 1 + (tcost w R + 1 + (tcost w R + 1 + tcost w R))

/-- The nine resident `init` words of the SYM C5 machine: the offset bounds, the target flags, the zero word. -/
def symInit (w n : Nat) (b : Fin 4 → Nat) (m : Fin 9) : List Bool :=
  if h : m.val < 4 then fb w (b ⟨m.val, h⟩) else if m.val < 8 then [decide (m.val - 4 < n)] else fb w 0

/-! ## 3. Local stages -/

theorem add_local (w a b x L : Nat) (hab : a + b < 2^w) (hL : 2*w+1 ≤ L) :
    Step (MaskedReset.machine NearCubicWires.RepairOrdinary.Add.machine (fun _ => true)) (2*(2*w+1)+2) (fun _ => 0)
      (Fin.addCases ![fb w a, fb w b, fb w x] (fun _ : Fin 1 => List.replicate L false))
      (fun _ => 0)
      (Fin.addCases ![fb w a, fb w b, fb w (a+b)] (fun _ : Fin 1 => List.replicate L false)) := by
  obtain ⟨r, hr, h0, h1, h2, _, _, _, hs, _⟩ :=
    NearCubicWires.RepairOrdinary.Add.add_run w a b (fb w x) hab (by simp [KeyStep.fb])
  have st : Step NearCubicWires.RepairOrdinary.Add.machine (2*w+1) (fun _ => 0) ![fb w a, fb w b, fb w x]
      r.final.heads ![fb w a, fb w b, fb w (a+b)] := by
    refine ⟨r, ?_, rfl, ?_, by omega⟩
    · have e : (⟨NearCubicWires.RepairOrdinary.Add.machine.start, fun _ => 0, ![fb w a, fb w b, fb w x]⟩ :
          Configuration 3 5) = NearCubicWires.RepairOrdinary.Add.config
            (NearCubicWires.RepairOrdinary.Add.scanState false) (fb w a) (fb w b) 0 0 [] (fb w x) := by
        apply configuration_ext
        · rfl
        · funext i
          fin_cases i <;> rfl
        · funext i
          fin_cases i <;> rfl
      rw [e]
      exact hr
    · funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  have sm := st.mask (fun _ => true) (fun _ _ => rfl) (cap := L) hL
  refine (sm.congr_in ?_ rfl).congr ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

section Dock
variable (NI : Nat)

theorem wdockS {t s n : Nat} {p : NearCubicWires.LocalBitMultitape.Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin (2+rowsWork NI)) (hi : Function.Injective sl)
    (A : Fin (2+rowsWork NI) → List Bool) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n (fun _ => 0) A (fun _ => 0) (install sl A tout) :=
  (h.dock sl hi _ A (fun _ => rfl) hA).congr
    (NearCubicWires.ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl

theorem add_at (src off dst : Fin (2+rowsWork NI)) (hi : Function.Injective (addSl NI src off dst))
    (w a b x R : Nat) (A : Fin (2+rowsWork NI) → List Bool) (hs : A src = fb w a) (ho : A off = fb w b)
    (hd : A dst = fb w x) (hl : A (cellPort NI 3) = List.replicate R false) (hab : a + b < 2^w) (hR : 2*w+1 ≤ R) :
    Step (addM NI src off dst) (2*(2*w+1)+2) (fun _ => 0) A (fun _ => 0) (Function.update A dst (fb w (a+b))) := by
  have d := wdockS NI (add_local w a b x R hab hR) (addSl NI src off dst) hi A (fun j => by
    fin_cases j
    · exact hs
    · exact ho
    · exact hd
    · exact hl)
  rw [SymVerdict.install_update _ hi A _ 2 (fun j hj => by
    fin_cases j
    · exact hs.symm
    · exact ho.symm
    · exact absurd rfl hj
    · exact hl.symm)] at d
  exact d

/-- The no-op on any bank whose cell 0 is blank. -/
theorem noop_run (R : Nat) (hR : 1 ≤ R) (A : Fin (2+rowsWork NI) → List Bool)
    (h0 : A (cellPort NI 0) = List.replicate R false) (h1 : A (cellPort NI 254) = List.replicate R true)
    (h2 : A (cellPort NI 255) = List.replicate (R+1) false) :
    Step (noop NI) (2*R+4) (fun _ => 0) A (fun _ => 0) A := by
  have s := rst_at (slR NI) (slR_injective NI) false R hR (fun _ => 0) A (fun _ => rfl)
    (by rw [show slR NI 2 = cellPort NI 0 from rfl, h0, pad_false R hR]) h1 h2
  rwa [update_same A (slR NI 2) _ h0] at s

end Dock

/-! ## 4. The bank family `Mk M e o`: row masters `M`, seed index `e`, padded offsets `o` -/

section Bank
variable {NI : Nat} (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rowp : Fin 8 → List Bool)
  (rcp : Fin 64 → List Bool) (c6 : Fin 2 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
  (cut : List Bool) (N S w : Nat)

/-- The work bank with loop masters `M`, seed index `e` and padded offsets `o` (all other blocks fixed). -/
def Mk (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) : Fin (2+rowsWork NI) → List Bool :=
  workLayout pub init rowp rcp (loopBank live R M) c6 (c5Words (seedWords e N) cut (fun c => fb w (o c)) S)

theorem Mk_master (M : Fin 254 → List Bool) (k : Fin 254) (v : List Bool) (e : Nat) (o : Fin 4 → Nat) :
    Mk pub init rowp rcp c6 live R cut N S w (Function.update M k v) e o =
      Function.update (Mk pub init rowp rcp c6 live R cut N S w M e o) (masterPort NI k) v := by
  unfold Mk
  rw [loopBank_update, wl_loop_update]
  rfl

theorem Mk_off_at (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (c : Fin 4) :
    Mk pub init rowp rcp c6 live R cut N S w M e o (c5Port NI (offP c)) = fb w (o c) := by
  unfold Mk
  rw [layout_c5]
  fin_cases c <;> rfl

theorem Mk_master_at (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (k : Fin 254) :
    Mk pub init rowp rcp c6 live R cut N S w M e o (masterPort NI k) = M k := by
  unfold Mk
  rw [wl_master]

theorem Mk_init_at (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (i : Fin NI) :
    Mk pub init rowp rcp c6 live R cut N S w M e o (initPort NI i) = init i := by
  unfold Mk
  rw [layout_init]

theorem Mk_cell (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (c : Fin 257) :
    Mk pub init rowp rcp c6 live R cut N S w M e o (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R
        (List.replicate (2^liveᶜ.card) false) c := by
  unfold Mk
  rw [wl_cell]

theorem noop_Mk (hR : 1 ≤ R) (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) :
    Step (noop NI) (2*R+4) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o) (fun _ => 0)
      (Mk pub init rowp rcp c6 live R cut N S w M e o) :=
  noop_run NI R hR _ (by rw [Mk_cell]; rfl) (by rw [Mk_cell]; rfl) (by rw [Mk_cell]; rfl)

/-! ## 5. The cascade -/

/-! ## 6. The target recompute -/

theorem tstage_run (ini : Fin 9 → Fin NI) (c : Fin 4) {s : Nat}
    (body : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) s) (nb : Nat) (hR : 1 ≤ R) (bf : Bool)
    (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (v : List Bool)
    (hflag : init (ini (fIx c)) = [bf])
    (hbody : bf = true → Step body nb (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o) (fun _ => 0)
      (Mk pub init rowp rcp c6 live R cut N S w (Function.update M (tgtP c) v) e o))
    (hsame : bf = false → M (tgtP c) = v) :
    Step (tstage NI ini c body) (nb + (2*R+4) + 2) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o)
      (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w (Function.update M (tgtP c) v) e o) := by
  cases bf with
  | true =>
    exact (CloseoutRowsOriginalSwitch.true_run body (noop NI) _ (hbody rfl)
      (by rw [Mk_init_at, hflag]; rfl)).enlarge (by omega)
  | false =>
    rw [Function.update_eq_self_iff.mpr (hsame rfl).symm]
    exact (CloseoutRowsOriginalSwitch.false_run body (noop NI) _ (noop_Mk pub init rowp rcp c6 live R cut N S w hR M e o)
      (by rw [Mk_init_at, hflag]; rfl)).enlarge (by omega)

/-- Target 0: `Tg 0 = off 0` when the request has a circuit, `0` (unchanged) otherwise. -/
theorem stage0_run (ini : Fin 9 → Fin NI) (n : Nat) (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (x0 : Nat)
    (hflag : init (ini (fIx 0)) = [decide (0 < n)]) (hz : init (ini zIx) = fb w 0) (ht : M (tgtP 0) = fb w x0)
    (hx0 : ¬ 0 < n → x0 = 0) (htg : tgv n o 0 < 2^w) (hw : 2*w+1 ≤ R) :
    Step (tstage NI ini 0 (body0 NI ini)) (tcost w R) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o)
      (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w (Function.update M (tgtP 0) (fb w (tgv n o 0))) e o) := by
  have hR : 1 ≤ R := by omega
  have hi : Function.Injective (addSl NI (c5Port NI (offP 0)) (initPort NI (ini zIx)) (masterPort NI (tgtP 0))) := by
    have h1 := (ini zIx).isLt
    apply addSl_injective <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp [c5Port_val, initPort_val', masterPort_val, cellPort_val, offP, tgtP] at hv <;> omega
  refine (tstage_run pub init rowp rcp c6 live R cut N S w ini 0 (body0 NI ini) (2*(2*w+1)+2) hR (decide (0 < n))
    M e o _ hflag (fun hd => ?_) (fun hd => ?_)).enlarge (by unfold tcost; omega)
  · have hn : 0 < n := of_decide_eq_true hd
    have e0 := tgv_zero n o hn
    rw [e0, Mk_master]
    exact add_at NI _ _ _ hi w (o 0) 0 x0 R _ (Mk_off_at pub init rowp rcp c6 live R cut N S w M e o 0)
      (by rw [Mk_init_at, hz]) (by rw [Mk_master_at, ht]) (by rw [Mk_cell]; rfl) (by rw [← e0]; exact htg) hw
  · have hn : ¬ 0 < n := of_decide_eq_false hd
    rw [ht, hx0 hn, tgv_ge n o 0 (by simpa using hn)]

/-- Target `c = p+1`: `Tg c = Tg p + off c + 1` when active, `0` (unchanged) otherwise. -/
theorem stageS_run (ini : Fin 9 → Fin NI) (n : Nat) (p c : Fin 4) (hpc : p.val + 1 = c.val)
    (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat) (xc : Nat)
    (hflag : init (ini (fIx c)) = [decide (c.val < n)]) (hp : M (tgtP p) = fb w (tgv n o p))
    (ht : M (tgtP c) = fb w xc) (hxc : ¬ c.val < n → xc = 0) (htg : tgv n o c < 2^w) (hw : 2*w+1 ≤ R) :
    Step (tstage NI ini c (bodyS NI ini p c)) (tcost w R) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o)
      (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w (Function.update M (tgtP c) (fb w (tgv n o c))) e o) := by
  have hR : 1 ≤ R := by omega
  have hpc' : p ≠ c := fun h => by rw [h] at hpc; omega
  have hi : Function.Injective (addSl NI (masterPort NI (tgtP p)) (c5Port NI (offP c)) (masterPort NI (tgtP c))) := by
    apply addSl_injective <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp [c5Port_val, masterPort_val, cellPort_val, offP, tgtP] at hv <;> omega
  refine (tstage_run pub init rowp rcp c6 live R cut N S w ini c (bodyS NI ini p c)
    ((2*(2*w+1)+2) + 1 + (4*w+2)) hR (decide (c.val < n)) M e o _ hflag (fun hd => ?_) (fun hd => ?_)).enlarge
    (by unfold tcost; omega)
  · have hn : c.val < n := of_decide_eq_true hd
    have hs := tgv_succ n o c (by omega) hn
    have ep : (⟨c.val - 1, by omega⟩ : Fin 4) = p := Fin.ext (by simp; omega)
    rw [ep] at hs
    have s1 := add_at NI _ _ _ hi w (tgv n o p) (o c) xc R (Mk pub init rowp rcp c6 live R cut N S w M e o)
      (by rw [Mk_master_at, hp])
      (Mk_off_at pub init rowp rcp c6 live R cut N S w M e o c) (by rw [Mk_master_at, ht])
      (by rw [Mk_cell]; rfl) (by omega) hw
    have hne : cellPort NI 1 ≠ masterPort NI (tgtP c) := by
      intro h
      have hv := congrArg Fin.val h
      simp [cellPort_val, masterPort_val, tgtP] at hv
      omega
    have s2 := inc_at (slT NI ini c) (slT_injective NI ini c) w (tgv n o p + o c) R (fun _ => 0)
      (Function.update (Mk pub init rowp rcp c6 live R cut N S w M e o) (masterPort NI (tgtP c))
        (fb w (tgv n o p + o c))) (fun _ => rfl)
      (by rw [show slT NI ini c 0 = masterPort NI (tgtP c) from rfl, Function.update_self])
      (by rw [show slT NI ini c 3 = cellPort NI 1 from rfl, Function.update_of_ne hne, Mk_cell]; rfl)
      (by omega) (by omega)
    refine (s1.seq s2).congr rfl ?_
    rw [show slT NI ini c 0 = masterPort NI (tgtP c) from rfl, Function.update_idem, ← hs, Mk_master]
  · have hn : ¬ c.val < n := of_decide_eq_false hd
    rw [ht, hxc hn, tgv_ge n o c hn]

/-- **The recompute**: from `Mk M e o` to `Mk (tupd M w (tgv n o)) e o` — every target port holds the cumulative
target of the offsets `o`. -/
theorem recomp_run (ini : Fin 9 → Fin NI) (n : Nat) (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat)
    (t0 : Fin 4 → Nat) (hM : ∀ c, M (tgtP c) = fb w (t0 c)) (ht0 : ∀ c : Fin 4, ¬ c.val < n → t0 c = 0)
    (hflags : ∀ c : Fin 4, init (ini (fIx c)) = [decide (c.val < n)]) (hz : init (ini zIx) = fb w 0)
    (htg : ∀ c, tgv n o c < 2^w) (hw : 2*w+1 ≤ R) :
    Step (recomp NI ini) (recCost w R) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o) (fun _ => 0)
      (Mk pub init rowp rcp c6 live R cut N S w (tupd M w (tgv n o)) e o) := by
  have t01 : tgtP 1 ≠ tgtP 0 := by decide
  have t02 : tgtP 2 ≠ tgtP 0 := by decide
  have t03 : tgtP 3 ≠ tgtP 0 := by decide
  have t12 : tgtP 2 ≠ tgtP 1 := by decide
  have t13 : tgtP 3 ≠ tgtP 1 := by decide
  have t23 : tgtP 3 ≠ tgtP 2 := by decide
  have s0 := stage0_run pub init rowp rcp c6 live R cut N S w ini n M e o (t0 0) (hflags 0) hz (hM 0) (ht0 0)
    (htg 0) hw
  set M1 := Function.update M (tgtP 0) (fb w (tgv n o 0)) with hM1
  have s1 := stageS_run pub init rowp rcp c6 live R cut N S w ini n 0 1 rfl M1 e o (t0 1) (hflags 1)
    (by rw [hM1, Function.update_self]) (by rw [hM1, Function.update_of_ne t01, hM]) (ht0 1) (htg 1) hw
  set M2 := Function.update M1 (tgtP 1) (fb w (tgv n o 1)) with hM2
  have s2 := stageS_run pub init rowp rcp c6 live R cut N S w ini n 1 2 rfl M2 e o (t0 2) (hflags 2)
    (by rw [hM2, Function.update_self])
    (by rw [hM2, Function.update_of_ne t12, hM1, Function.update_of_ne t02, hM]) (ht0 2) (htg 2) hw
  set M3 := Function.update M2 (tgtP 2) (fb w (tgv n o 2)) with hM3
  have s3 := stageS_run pub init rowp rcp c6 live R cut N S w ini n 2 3 rfl M3 e o (t0 3) (hflags 3)
    (by rw [hM3, Function.update_self])
    (by rw [hM3, Function.update_of_ne t23, hM2, Function.update_of_ne t13, hM1, Function.update_of_ne t03, hM])
    (ht0 3) (htg 3) hw
  exact s0.seq (s1.seq (s2.seq s3))

end Bank

/-! ## 7. SYM C5 on `symBase` -/

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- `symBase` at a row whose key is `k`, as a member of the bank family. -/
theorem symBase_Mk (j : Nat) (k : RCFive.RowKeys.SymKey r L target) (hk : symKeyAt r L target j = some k) :
    symBase a r four L target NI pub init rcp C cC hF j =
      Mk pub init (rowpWords (symN r L target) C cC hF) rcp (c6Words (symLive r L)ᶜ.card) (symLive r L)
        (symRes r.q (symT a r four L target)) [] (sNS r L target) (seedScratch (sNS r L target))
        (sw a r four L target) (symMasters a r four L target (symRes r.q (symT a r four L target)) k)
        (symSeedIdx r L target k) (offN r L target k) := by
  simp only [symBase, hk]
  rfl

end Sym

end
end RowsConstruction.SymC5
