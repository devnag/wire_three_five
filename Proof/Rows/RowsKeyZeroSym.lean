import Proof.Rows.RowsSymC5

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyZero
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.SymC5
open RowsConstruction.KeyTop (cellPort masterPort_val cellPort_val c5Port_val)
noncomputable section

/-! ## 1. The add stage on an arbitrary (padded) backing -/

theorem addCases_zero3 {m : Nat} (f : Fin m → ℕ) (hf : ∀ i, f i = 0) :
    (fun i => Fin.addCases (motive := fun _ => ℕ) (n := 1) f (fun _ => 0) i) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [hf]
  · simp

/-- `fb w a + fb w b` written onto the padded backing `pad F bk` (any `bk` of length `≤ 2w+1`). -/
theorem add_localP (w a b F L : Nat) (bk : List Bool) (hab : a + b < 2^w) (hbk : bk.length ≤ 2*w+1)
    (hL : 2*w+1 ≤ L) :
    Step (MaskedReset.machine NearCubicWires.RepairOrdinary.Add.machine (fun _ => true)) (2*(2*w+1)+2) (fun _ => 0)
      (Fin.addCases ![fb w a, fb w b, ZeroPadding.pad F bk] (fun _ : Fin 1 => List.replicate L false))
      (fun _ => 0)
      (Fin.addCases ![fb w a, fb w b, ZeroPadding.pad F (fb w (a+b))] (fun _ : Fin 1 => List.replicate L false)) := by
  obtain ⟨r, hr, h0, h1, h2, _, _, _, hs, _⟩ := NearCubicWires.RepairOrdinary.Add.add_run w a b bk hab hbk
  have st : Step NearCubicWires.RepairOrdinary.Add.machine (2*w+1) (fun _ => 0) ![fb w a, fb w b, bk]
      r.final.heads ![fb w a, fb w b, fb w (a+b)] := by
    refine ⟨r, ?_, rfl, ?_, by omega⟩
    · have e : (⟨NearCubicWires.RepairOrdinary.Add.machine.start, fun _ => 0, ![fb w a, fb w b, bk]⟩ :
          Configuration 3 5) = NearCubicWires.RepairOrdinary.Add.config
            (NearCubicWires.RepairOrdinary.Add.scanState false) (fb w a) (fb w b) 0 0 [] bk := by
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
  have sp := st.pad ![0, 0, F]
  have sm := sp.mask (fun _ => true) (fun _ _ => rfl) (cap := L) hL
  refine (sm.congr_in (addCases_zero3 _ (fun _ => rfl)) ?_).congr (addCases_zero3 _ (fun _ => by simp)) ?_
  · funext i
    fin_cases i <;> first | rfl | exact KeyStep.pad_zero _
  · funext i
    fin_cases i <;> first | rfl | exact KeyStep.pad_zero _

/-- The docked padded add. -/
theorem addP_at (NI : Nat) (src off dst : Fin (2+rowsWork NI)) (hi : Function.Injective (addSl NI src off dst))
    (w a b F R : Nat) (bk : List Bool) (A : Fin (2+rowsWork NI) → List Bool) (hs : A src = fb w a)
    (ho : A off = fb w b) (hd : A dst = ZeroPadding.pad F bk) (hl : A (cellPort NI 3) = List.replicate R false)
    (hab : a + b < 2^w) (hbk : bk.length ≤ 2*w+1) (hR : 2*w+1 ≤ R) :
    Step (addM NI src off dst) (2*(2*w+1)+2) (fun _ => 0) A (fun _ => 0)
      (Function.update A dst (ZeroPadding.pad F (fb w (a+b)))) := by
  have d := wdockS NI (add_localP w a b F R bk hab hbk hR) (addSl NI src off dst) hi A (fun j => by
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

/-! ## 2. The SYM key-0 machine -/

section Ports
variable (NI : Nat)

/-- Zero copy onto target master `c`: zero word `init (ini 8)` + offset digit `c`. -/
def zstage (ini : Fin 9 → Fin NI) (c : Fin 4) :=
  addM NI (initPort NI (ini zIx)) (c5Port NI (offP c)) (masterPort NI (tgtP c))

/-- **The SYM key-0 writer**: four zero copies, then the target recompute. -/
def symK0 (ini : Fin 9 → Fin NI) :=
  Composition.machine (zstage NI ini 0) (Composition.machine (zstage NI ini 1) (Composition.machine (zstage NI ini 2)
    (Composition.machine (zstage NI ini 3) (recomp NI ini))))

/-- The four target master ports blanked. -/
def symBlank0 (B : Fin (2+rowsWork NI) → List Bool) : Fin (2+rowsWork NI) → List Bool :=
  Function.update (Function.update (Function.update (Function.update B (masterPort NI (tgtP 0)) [])
    (masterPort NI (tgtP 1)) []) (masterPort NI (tgtP 2)) []) (masterPort NI (tgtP 3)) []

end Ports

def zcost (w : Nat) : Nat := 2*(2*w+1)+2

/-- The SYM key-0 writer's cost. -/
def symK0Cost (w R : Nat) : Nat := zcost w + 1 + (zcost w + 1 + (zcost w + 1 + (zcost w + 1 + recCost w R)))

/-- The four target masters blanked. -/
def blankT (M : Fin 254 → List Bool) : Fin 254 → List Bool :=
  Function.update (Function.update (Function.update (Function.update M (tgtP 0) []) (tgtP 1) []) (tgtP 2) [])
    (tgtP 3) []

theorem tupd_collapse (M : Fin 254 → List Bool) (w : Nat) (t z : Fin 4 → Nat) (hM : ∀ c, M (tgtP c) = fb w (t c)) :
    tupd (tupd (blankT M) w z) w t = M := by
  funext i
  unfold tupd blankT
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | (subst_vars; exact (hM _).symm)

section Bank
variable {NI : Nat} (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rowp : Fin 8 → List Bool)
  (rcp : Fin 64 → List Bool) (c6 : Fin 2 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
  (cut : List Bool) (N S w : Nat)

theorem zstage_run (ini : Fin 9 → Fin NI) (c : Fin 4) (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat)
    (hM : M (tgtP c) = []) (ho : o c = 0) (hz : init (ini zIx) = fb w 0) (hw : 2*w+1 ≤ R) :
    Step (zstage NI ini c) (zcost w) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w M e o) (fun _ => 0)
      (Mk pub init rowp rcp c6 live R cut N S w (Function.update M (tgtP c) (fb w 0)) e o) := by
  have hi : Function.Injective (addSl NI (initPort NI (ini zIx)) (c5Port NI (offP c)) (masterPort NI (tgtP c))) := by
    have h1 := (ini zIx).isLt
    have h2 := c.isLt
    apply addSl_injective <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp [c5Port_val, initPort_val', masterPort_val, cellPort_val, offP, tgtP] at hv <;> omega
  have s := addP_at NI _ _ _ hi w 0 0 0 R [] (Mk pub init rowp rcp c6 live R cut N S w M e o)
    (by rw [Mk_init_at, hz]) (by rw [Mk_off_at, ho])
    (by rw [Mk_master_at, hM, KeyStep.pad_zero]) (by rw [Mk_cell]; rfl) (by have := Nat.one_le_two_pow (n := w); omega)
    (by simp) hw
  rw [KeyStep.pad_zero, ← Mk_master] at s
  exact s

/-- **The SYM key-0 writer on the bank family**: from blank target masters to the targets of offsets `o`. -/
theorem symK0_Mk (ini : Fin 9 → Fin NI) (n : Nat) (M : Fin 254 → List Bool) (e : Nat) (o : Fin 4 → Nat)
    (ho : ∀ c, o c = 0) (hflags : ∀ c : Fin 4, init (ini (fIx c)) = [decide (c.val < n)])
    (hz : init (ini zIx) = fb w 0) (htg : ∀ c, tgv n o c < 2^w) (hw : 2*w+1 ≤ R) :
    Step (symK0 NI ini) (symK0Cost w R) (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w (blankT M) e o)
      (fun _ => 0) (Mk pub init rowp rcp c6 live R cut N S w (tupd (tupd (blankT M) w (fun _ => 0)) w (tgv n o)) e o) := by
  have t01 : tgtP 1 ≠ tgtP 0 := by decide
  have t02 : tgtP 2 ≠ tgtP 0 := by decide
  have t03 : tgtP 3 ≠ tgtP 0 := by decide
  have t12 : tgtP 2 ≠ tgtP 1 := by decide
  have t13 : tgtP 3 ≠ tgtP 1 := by decide
  have t23 : tgtP 3 ≠ tgtP 2 := by decide
  have bl : ∀ c, blankT M (tgtP c) = [] := by
    intro c
    fin_cases c <;> simp [blankT, Function.update_apply]
  set M0 := blankT M with hM0
  have s0 := zstage_run pub init rowp rcp c6 live R cut N S w ini 0 M0 e o (bl 0) (ho 0) hz hw
  set M1 := Function.update M0 (tgtP 0) (fb w 0) with hM1
  have s1 := zstage_run pub init rowp rcp c6 live R cut N S w ini 1 M1 e o
    (by rw [hM1, Function.update_of_ne t01, bl]) (ho 1) hz hw
  set M2 := Function.update M1 (tgtP 1) (fb w 0) with hM2
  have s2 := zstage_run pub init rowp rcp c6 live R cut N S w ini 2 M2 e o
    (by rw [hM2, Function.update_of_ne t12, hM1, Function.update_of_ne t02, bl]) (ho 2) hz hw
  set M3 := Function.update M2 (tgtP 2) (fb w 0) with hM3
  have s3 := zstage_run pub init rowp rcp c6 live R cut N S w ini 3 M3 e o
    (by rw [hM3, Function.update_of_ne t23, hM2, Function.update_of_ne t13, hM1, Function.update_of_ne t03, bl])
    (ho 3) hz hw
  have s4 := recomp_run pub init rowp rcp c6 live R cut N S w ini n (tupd M0 w (fun _ => 0)) e o (fun _ => 0)
    (fun c => by fin_cases c <;> simp [tupd, Function.update_apply]) (fun _ _ => rfl) hflags hz htg hw
  exact s0.seq (s1.seq (s2.seq (s3.seq s4)))

end Bank

/-! ## 3. The SYM key-0 writer on `symBase 0` -/

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- **SYM key-0 writer.** On `symBase 0` with its four target masters blank, the fixed machine `symK0 NI ini` (the same
nine `symInit` words as SYM C5) writes them, reaching `symBase 0` exactly, all heads `0`. -/
theorem sym_key0_run (ini : Fin 9 → Fin NI)
    (hinit : ∀ m, init (ini m) = symInit (sw a r four L target) r.circuits.length (sbnd r) m)
    (h0 : 0 < (RCFive.RowKeys.symKeys r L target).length) :
    Step (symK0 NI ini) (symK0Cost (sw a r four L target) (symRes r.q (symT a r four L target))) (fun _ => 0)
      (symBlank0 NI (symBase a r four L target NI pub init rcp C cC hF 0))
      (fun _ => 0) (symBase a r four L target NI pub init rcp C cC hF 0) := by
  set k := (skeys r L target)[0] with hkdef
  have hmem : k ∈ skeys r L target := List.getElem_mem h0
  have hw := sw_fits a r four L target k
  have hflags : ∀ c : Fin 4, init (ini (fIx c)) = [decide (c.val < r.circuits.length)] := by
    intro c
    rw [hinit]
    have := c.isLt
    simp [symInit, fIx]
    omega
  have hz : init (ini zIx) = fb (sw a r four L target) 0 := by
    rw [hinit]
    simp [symInit, zIx]
  have hd := RowsConstruction.SymC5.sym_key0 a r four L target h0
  have ho : ∀ c, offN r L target k c = 0 := by
    intro c
    rw [← sdig_off r L target k c, hd]
  have hB := symBase_Mk a r four L target NI pub init rcp C cC hF 0 k (keyAt_eq r L target 0 h0)
  have hblank : symBlank0 NI (symBase a r four L target NI pub init rcp C cC hF 0) =
      Mk pub init (rowpWords (symN r L target) C cC hF) rcp (c6Words (symLive r L)ᶜ.card) (symLive r L)
        (symRes r.q (symT a r four L target)) [] (sNS r L target) (seedScratch (sNS r L target))
        (sw a r four L target) (blankT (symMasters a r four L target (symRes r.q (symT a r four L target)) k))
        (symSeedIdx r L target k) (offN r L target k) := by
    rw [hB]
    unfold symBlank0 blankT
    rw [Mk_master, Mk_master, Mk_master, Mk_master]
  have s := symK0_Mk pub init (rowpWords (symN r L target) C cC hF) rcp (c6Words (symLive r L)ᶜ.card) (symLive r L)
    (symRes r.q (symT a r four L target)) [] (sNS r L target) (seedScratch (sNS r L target)) (sw a r four L target)
    ini r.circuits.length (symMasters a r four L target (symRes r.q (symT a r four L target)) k)
    (symSeedIdx r L target k) (offN r L target k) ho hflags hz
    (fun c => by rw [← tg_eq r four L target k c]; exact tg_lt a r four L target k hmem c) hw
  rw [tupd_collapse _ _ _ _ (fun c => by rw [masters_tgt, tg_eq r four L target k c])] at s
  rw [hblank, hB]
  exact s

end Sym

end
end RowsConstruction.KeyZero
