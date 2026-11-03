import Proof.Rows.RowsKeyZeroSym
import Proof.Rows.RowsThrSelBase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyZeroThr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep
open RowsConstruction.SymC5 (addM addSl addSl_injective initPort_val' wdockS)
open RowsConstruction.KeyZero (addP_at)
open RowsConstruction.KeyTop (cellPort masterPort_val cellPort_val wl_master wl_cell wl_loop_update loopBank_update)
noncomputable section

/-! ## 1. The erase stage -/

theorem erase_local (D : Nat) (x : List Bool) (hx : x.length ≤ D) :
    Step (RecoveryScratchErase.resetMachine 1) (2*D+4) (fun _ => 0)
      ![x, List.replicate D true, List.replicate (D+1) false] (fun _ => 0)
      ![List.replicate D false, List.replicate D true, List.replicate (D+1) false] := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) D (D+1) (fun _ => x) (fun _ => hx))
  have e1 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => x)
        (fun _ : Fin 1 => List.replicate D true)) (fun _ : Fin 1 => List.replicate (D+1) false)) =
      ![x, List.replicate D true, List.replicate (D+1) false] := by
    funext i; fin_cases i <;> rfl
  have e2 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => List.replicate D false)
        (fun _ : Fin 1 => List.replicate D true)) (fun _ : Fin 1 => List.replicate (max (D+1) (D+1)) false)) =
      ![List.replicate D false, List.replicate D true, List.replicate (D+1) false] := by
    funext i; fin_cases i <;> (simp only [max_self]; rfl)
  rw [e1, e2] at h
  exact h

section Ports
variable (NI : Nat)

def eraseM (p d l : Fin (2+rowsWork NI)) := RecoveryFocus.machine ![p, d, l] (RecoveryScratchErase.resetMachine 1)

theorem erase_at (p d l : Fin (2+rowsWork NI)) (hi : Function.Injective ![p, d, l]) (D : Nat) (x : List Bool)
    (hx : x.length ≤ D) (A : Fin (2+rowsWork NI) → List Bool) (hp : A p = x) (hd : A d = List.replicate D true)
    (hl : A l = List.replicate (D+1) false) :
    Step (eraseM NI p d l) (2*D+4) (fun _ => 0) A (fun _ => 0) (Function.update A p (List.replicate D false)) := by
  have s := wdockS NI (erase_local D x hx) ![p, d, l] hi A (fun j => by
    fin_cases j
    · exact hp
    · exact hd
    · exact hl)
  rw [SymVerdict.install_update _ hi A _ 0 (fun j hj => by
    fin_cases j
    · exact absurd rfl hj
    · exact hd.symm
    · exact hl.symm)] at s
  exact s

/-- A master port. -/
abbrev mp (k : Fin 254) : Fin (2+rowsWork NI) := masterPort NI k
/-- A resident word's port. -/
abbrev ip (iz : Fin 9 → Fin NI) (m : Fin 9) : Fin (2+rowsWork NI) := initPort NI (iz m)

/-- **The THR key-0 writer** (one fixed machine for fixed `NI`, `iz`, `ib`, `iOne`). -/
def thrK0 (iz : Fin 9 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) :=
  Composition.machine (addM NI (ip NI iz 0) (ip NI iz 1) (mp NI 242))
  (Composition.machine (addM NI (ip NI iz 2) (ip NI iz 0) (mp NI 240))
  (Composition.machine (addM NI (ip NI iz 2) (mp NI 240) (mp NI 149))
  (Composition.machine (addM NI (mp NI 149) (ip NI iz 0) (mp NI 240))
  (Composition.machine (addM NI (mp NI 149) (ip NI iz 0) (mp NI 218))
  (Composition.machine (eraseM NI (mp NI 209) (ip NI iz 5) (ip NI iz 6))
  (Composition.machine (addM NI (mp NI 149) (ip NI iz 0) (mp NI 209))
  (Composition.machine (eraseM NI (mp NI 220) (ip NI iz 7) (ip NI iz 8))
  (Composition.machine (addM NI (ip NI iz 0) (mp NI 242) (mp NI 220))
  (Composition.machine (addM NI (ip NI iz 3) (ip NI iz 4) (mp NI 228))
  (Composition.machine (addM NI (ip NI iz 3) (mp NI 228) (mp NI 229))
  (Composition.machine (addM NI (ip NI iz 3) (mp NI 228) (mp NI 230))
  (Composition.machine (addM NI (ip NI iz 3) (mp NI 228) (mp NI 231))
    (RowsConstruction.ThrSelBase.baseW NI ib iOne)))))))))))))

/-- The ten THR key masters blanked. -/
def thrBlank0 (B : Fin (2+rowsWork NI) → List Bool) : Fin (2+rowsWork NI) → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update B
      (mp NI 149) []) (mp NI 209) []) (mp NI 218) []) (mp NI 220) []) (mp NI 228) []) (mp NI 229) [])
      (mp NI 230) []) (mp NI 231) []) (mp NI 240) []) (mp NI 242) []

theorem ii_ne (iz : Fin 9 → Fin NI) (hiz : Function.Injective iz) (m m' : Fin 9) (h : m ≠ m') :
    ip NI iz m ≠ ip NI iz m' := by
  intro e
  have hv := congrArg Fin.val e
  rw [initPort_val', initPort_val'] at hv
  exact h (hiz (Fin.ext (by omega)))

theorem im_ne (iz : Fin 9 → Fin NI) (m : Fin 9) (k : Fin 254) : ip NI iz m ≠ mp NI k :=
  RowsConstruction.ThrKey.initPort_ne_master NI (iz m) k

theorem ic_ne (iz : Fin 9 → Fin NI) (m : Fin 9) : ip NI iz m ≠ cellPort NI 3 := by
  intro e
  have hv := congrArg Fin.val e
  rw [initPort_val', cellPort_val] at hv
  have := (iz m).isLt
  omega

theorem mc_ne (k : Fin 254) : mp NI k ≠ cellPort NI 3 :=
  fun e => RowsConstruction.ThrKey.cell_ne_master NI 3 k e.symm

theorem mm_ne (k k' : Fin 254) (h : k ≠ k') : mp NI k ≠ mp NI k' := RowsConstruction.ThrKey.master_ne NI k k' h

theorem erase_inj (iz : Fin 9 → Fin NI) (hiz : Function.Injective iz) (p : Fin 254) (m m' : Fin 9) (h : m ≠ m') :
    Function.Injective ![mp NI p, ip NI iz m, ip NI iz m'] := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  all_goals first
    | rfl
    | exact absurd hxy (im_ne NI iz m p).symm
    | exact absurd hxy.symm (im_ne NI iz m p).symm
    | exact absurd hxy (im_ne NI iz m' p).symm
    | exact absurd hxy.symm (im_ne NI iz m' p).symm
    | exact absurd hxy (ii_ne NI iz hiz m m' h)
    | exact absurd hxy.symm (ii_ne NI iz hiz m m' h)

end Ports

/-- The nine resident words of the THR key-0 writer. -/
def thrZInit (w T F U : Nat) : Fin 9 → List Bool :=
  ![fb w 0, fb w 0, fb w 1, fb T 0, fb T 0, List.replicate F true, List.replicate (F+1) false,
    List.replicate U true, List.replicate (U+1) false]

def zc (w : Nat) : Nat := 2*(2*w+1)+2

/-- The THR key-0 writer's cost (`b` = the base stage's cost). -/
def thrK0Cost (w T F U b : Nat) : Nat :=
  zc w + 1 + (zc w + 1 + (zc w + 1 + (zc w + 1 + (zc w + 1 + ((2*F+4) + 1 + (zc w + 1 + ((2*U+4) + 1 +
    (zc w + 1 + (zc T + 1 + (zc T + 1 + (zc T + 1 + (zc T + 1 + b))))))))))))

/-! ## 2. The bank family `MkT M` (loop masters `M`, everything else fixed) -/

section Bank
variable {NI : Nat} (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rowp : Fin 8 → List Bool)
  (rcp : Fin 64 → List Bool) (c6 : Fin 2 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
  (c5 : Fin 16 → List Bool)

def MkT (M : Fin 254 → List Bool) : Fin (2+rowsWork NI) → List Bool :=
  workLayout pub init rowp rcp (loopBank live R M) c6 c5

theorem MkT_master (M : Fin 254 → List Bool) (k : Fin 254) (v : List Bool) :
    MkT pub init rowp rcp c6 live R c5 (Function.update M k v) =
      Function.update (MkT pub init rowp rcp c6 live R c5 M) (masterPort NI k) v := by
  unfold MkT
  rw [loopBank_update, wl_loop_update]
  rfl

theorem MkT_m (M : Fin 254 → List Bool) (k : Fin 254) : MkT pub init rowp rcp c6 live R c5 M (masterPort NI k) = M k := by
  unfold MkT
  rw [wl_master]

theorem MkT_i (M : Fin 254 → List Bool) (i : Fin NI) : MkT pub init rowp rcp c6 live R c5 M (initPort NI i) = init i := by
  unfold MkT
  rw [layout_init]

theorem MkT_c (M : Fin 254 → List Bool) (c : Fin 257) :
    MkT pub init rowp rcp c6 live R c5 M (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R
        (List.replicate (2^liveᶜ.card) false) c := by
  unfold MkT
  rw [wl_cell]

/-- An add stage on the family: master `dst` := `v` (= `pad F (fb w (a+b))`). -/
theorem addT (src off : Fin (2+rowsWork NI)) (dst : Fin 254) (hi : Function.Injective (addSl NI src off (masterPort NI dst)))
    (w a b F : Nat) (bk : List Bool) (M : Fin 254 → List Bool) (v : List Bool)
    (hs : MkT pub init rowp rcp c6 live R c5 M src = fb w a) (ho : MkT pub init rowp rcp c6 live R c5 M off = fb w b)
    (hd : M dst = ZeroPadding.pad F bk) (hab : a + b < 2^w) (hbk : bk.length ≤ 2*w+1) (hR : 2*w+1 ≤ R)
    (hv : ZeroPadding.pad F (fb w (a+b)) = v) :
    Step (addM NI src off (masterPort NI dst)) (zc w) (fun _ => 0) (MkT pub init rowp rcp c6 live R c5 M) (fun _ => 0)
      (MkT pub init rowp rcp c6 live R c5 (Function.update M dst v)) := by
  have s := addP_at NI src off (masterPort NI dst) hi w a b F R bk (MkT pub init rowp rcp c6 live R c5 M) hs ho
    (by rw [MkT_m, hd]) (by rw [MkT_c]; rfl) hab hbk hR
  rw [hv, ← MkT_master] at s
  exact s

/-- An erase stage on the family: master `p` := `0^D`. -/
theorem eraseT (p : Fin 254) (d l : Fin (2+rowsWork NI)) (hi : Function.Injective ![masterPort NI p, d, l]) (D : Nat)
    (M : Fin 254 → List Bool) (hp : M p = []) (hd : MkT pub init rowp rcp c6 live R c5 M d = List.replicate D true)
    (hl : MkT pub init rowp rcp c6 live R c5 M l = List.replicate (D+1) false) :
    Step (eraseM NI (masterPort NI p) d l) (2*D+4) (fun _ => 0) (MkT pub init rowp rcp c6 live R c5 M) (fun _ => 0)
      (MkT pub init rowp rcp c6 live R c5 (Function.update M p (List.replicate D false))) := by
  have s := erase_at NI (masterPort NI p) d l hi D [] (by simp) (MkT pub init rowp rcp c6 live R c5 M)
    (by rw [MkT_m, hp]) hd hl
  rw [← MkT_master] at s
  exact s

end Bank

theorem pad_nil (F : Nat) : ZeroPadding.pad F ([] : List Bool) = List.replicate F false := by
  simp [ZeroPadding.pad]

/-! ## 3. The THR key-0 writer on `thrBase 0` -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- **THR key-0 writer.** On `thrBase 0` with its ten key masters blank, the fixed machine `thrK0` (resident words
`thrZInit` at `init (iz ·)`, and the base stage's words at `init (ib ·)`, `init iOne` — the same words THR C5 reads)
writes them, reaching `thrBase 0` exactly, all heads `0`. -/
theorem thr_key0_run (iz : Fin 9 → Fin NI) (hiz : Function.Injective iz)
    (hz : ∀ m, init (iz m) = thrZInit (KeyTop.wT a r four L target) (ThrWidth.T a r four L target)
      (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target)) m)
    (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib) (hone : ib 9 ≠ iOne)
    (hinitB : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = ThrSelBase.baseInit a r four L target k)
    (hinitO : init iOne = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target))
      (fb (KeyTop.wT a r four L target) 1))
    (h0 : 0 < (RCFive.RowKeys.thrKeys a r L target).length) :
    Step (thrK0 NI iz ib iOne)
      (thrK0Cost (KeyTop.wT a r four L target) (ThrWidth.T a r four L target) (Ff r.q (ThrWidth.T a r four L target))
        (Uf r.q (ThrWidth.T a r four L target))
        (ThrSelBase.baseCost (ThrSelBase.bF (ThrWidth.T a r four L target)) (KeyTop.wT a r four L target)))
      (fun _ => 0) (thrBlank0 NI (thrBase a r four L target NI pub init rcp C cC hF 0))
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF 0) := by
  set T := ThrWidth.T a r four L target with hT
  set w := KeyTop.wT a r four L target with hw
  set F := Ff r.q T with hF'
  set U := Uf r.q T with hU
  set RR := KeyTop.RT a r four L target with hRR
  set k := (KeySucc.keys a r L target)[0] with hk
  -- key 0's digits, prime and residue
  have hd0 := ThrSel.dig_key0 a r four L target h0
  have hres : k.residue.val = 0 := (KeySucc.dig_res a r four L target k).symm.trans (congrFun hd0 6)
  have hpr : k.prime.val = 2 := by
    rw [← KeySucc.primeAt_dig a r four L target k, congrFun hd0 4]
    exact NearCubicWires.PacketsGlue.RequestMeta.primeAt_zero _ (ThrKey.cut_ge a r target)
  have hdg : ∀ c : Fin 4, (PCJ45bee56da9f34d5a_StreamPair.data a r four k.selection).digits c = 0 := by
    intro c
    rw [ThrSel.data_digits a r four L target k c, hd0]
  -- numeric side conditions
  have hwR : 2*w+1 ≤ RR := KeyTop.wT_fits a r four L target k
  have hTw : T ≤ w := by rw [hw]; unfold KeyTop.wT; omega
  have hTR : 2*T+1 ≤ RR := by omega
  have hw2 : 2 < 2^w := by
    have : 2^2 ≤ 2^w := Nat.pow_le_pow_right (by norm_num) (by rw [hw]; unfold KeyTop.wT; omega)
    omega
  have hT0 : 0 < 2^T := Nat.two_pow_pos T
  have hUf : 4*w+3 ≤ U := by
    have hb := (fns_thr a r four L target k.selection _ rfl k.prime k.residue).2.1
    have hcap := hb.capacity
    rw [← hT] at hcap
    have hsq : 12*T+19+1 ≤ (12*T+19+1)^2 := Nat.le_self_pow (by norm_num) _
    rw [hw]
    unfold KeyTop.wT
    omega
  have hR4 : 4*w+3 ≤ RR := by
    have h1' := thrR_le_res r.q T
    have h2' : Uf r.q T ≤ thrR r.q T := by unfold thrR thrLmax; omega
    show _ ≤ thrRes r.q T
    omega
  -- the bank family at key 0
  have hB := KeyTop.base_eq a r four L target NI pub init rcp C cC hF 0 h0
  set c5 := c5Words (seedWords (thrSeedIdx a r L target k) (KeyTop.NS a r L target))
    (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
    (seedScratch (KeyTop.NS a r L target)) with hc5
  set rowp := rowpWords (thrN a r L target) C cC hF with hrowp
  set c6 := c6Words (thrLive r L)ᶜ.card with hc6
  set M := thrMasters a r four L target RR k with hM
  have hBM : thrBase a r four L target NI pub init rcp C cC hF 0 = MkT pub init rowp rcp c6 (thrLive r L) RR c5 M := hB
  set M0 := Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update M
      149 []) 209 []) 218 []) 220 []) 228 []) 229 []) 230 []) 231 []) 240 []) 242 [] with hM0
  have hblank : thrBlank0 NI (thrBase a r four L target NI pub init rcp C cC hF 0) =
      MkT pub init rowp rcp c6 (thrLive r L) RR c5 M0 := by
    rw [hBM, hM0]
    unfold thrBlank0
    simp only [MkT_master]
  -- resident values
  have vi : ∀ (N : Fin 254 → List Bool) (m : Fin 9), MkT pub init rowp rcp c6 (thrLive r L) RR c5 N (ip NI iz m) =
      thrZInit w T F U m := fun N m => by rw [ip, MkT_i, hz]
  -- the thirteen copies and two erases
  have inj3 : ∀ (s o : Fin (2+rowsWork NI)) (d : Fin 254), s ≠ o → s ≠ masterPort NI d → s ≠ cellPort NI 3 →
      o ≠ masterPort NI d → o ≠ cellPort NI 3 → Function.Injective (addSl NI s o (masterPort NI d)) :=
    fun s o d h1 h2 h3 h4 h5 => addSl_injective NI s o (masterPort NI d) h1 h2 h3 h4 h5 (mc_ne NI d)
  have s1 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 0) (ip NI iz 1) 242
    (inj3 _ _ _ (ii_ne NI iz hiz 0 1 (by decide)) (im_ne NI iz 0 242) (ic_ne NI iz 0) (im_ne NI iz 1 242) (ic_ne NI iz 1))
    w 0 0 0 [] M0 (fb w 0) (vi M0 0) (vi M0 1) (by simp [hM0]) (by omega) (by simp) hwR
    (by simp)
  set M1 := Function.update M0 242 (fb w 0) with hM1
  have s2 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 2) (ip NI iz 0) 240
    (inj3 _ _ _ (ii_ne NI iz hiz 2 0 (by decide)) (im_ne NI iz 2 240) (ic_ne NI iz 2) (im_ne NI iz 0 240) (ic_ne NI iz 0))
    w 1 0 0 [] M1 (fb w 1) (vi M1 2) (vi M1 0) (by simp [hM1, hM0]) (by omega) (by simp) hwR
    (by simp)
  set M2 := Function.update M1 240 (fb w 1) with hM2
  have s3 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 2) (mp NI 240) 149
    (inj3 _ _ _ (im_ne NI iz 2 240) (im_ne NI iz 2 149) (ic_ne NI iz 2) (mm_ne NI 240 149 (by decide)) (mc_ne NI 240))
    w 1 1 0 [] M2 (fb w 2) (vi M2 2) (by rw [mp, MkT_m, hM2, Function.update_self])
    (by simp [hM2, hM1, hM0]) (by omega) (by simp) hwR (by simp)
  set M3 := Function.update M2 149 (fb w 2) with hM3
  have s4 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (mp NI 149) (ip NI iz 0) 240
    (inj3 _ _ _ (fun e => im_ne NI iz 0 149 e.symm) (mm_ne NI 149 240 (by decide)) (mc_ne NI 149)
      (im_ne NI iz 0 240) (ic_ne NI iz 0))
    w 2 0 0 (fb w 1) M3 (fb w 2) (by rw [mp, MkT_m, hM3, Function.update_self]) (vi M3 0)
    (by simp [hM3, hM2]) (by omega) (by simp) hwR (by simp)
  set M4 := Function.update M3 240 (fb w 2) with hM4
  have s5 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (mp NI 149) (ip NI iz 0) 218
    (inj3 _ _ _ (fun e => im_ne NI iz 0 149 e.symm) (mm_ne NI 149 218 (by decide)) (mc_ne NI 149)
      (im_ne NI iz 0 218) (ic_ne NI iz 0))
    w 2 0 0 [] M4 (fb w 2) (by simp [mp, MkT_m, hM4, hM3]) (vi M4 0)
    (by simp [hM4, hM3, hM2, hM1, hM0]) (by omega) (by simp) hwR (by simp)
  set M5 := Function.update M4 218 (fb w 2) with hM5
  have s6 := eraseT pub init rowp rcp c6 (thrLive r L) RR c5 209 (ip NI iz 5) (ip NI iz 6)
    (erase_inj NI iz hiz 209 5 6 (by decide))
    F M5 (by simp [hM5, hM4, hM3, hM2, hM1, hM0]) (vi M5 5) (vi M5 6)
  set M6 := Function.update M5 209 (List.replicate F false) with hM6
  have s7 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (mp NI 149) (ip NI iz 0) 209
    (inj3 _ _ _ (fun e => im_ne NI iz 0 149 e.symm) (mm_ne NI 149 209 (by decide)) (mc_ne NI 149)
      (im_ne NI iz 0 209) (ic_ne NI iz 0))
    w 2 0 F [] M6 (ZeroPadding.pad F (fb w 2)) (by simp [mp, MkT_m, hM6, hM5, hM4, hM3]) (vi M6 0)
    (by rw [hM6, Function.update_self, pad_nil]) (by omega) (by simp) hwR (by simp)
  set M7 := Function.update M6 209 (ZeroPadding.pad F (fb w 2)) with hM7
  have s8 := eraseT pub init rowp rcp c6 (thrLive r L) RR c5 220 (ip NI iz 7) (ip NI iz 8)
    (erase_inj NI iz hiz 220 7 8 (by decide))
    U M7 (by simp [hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0]) (vi M7 7) (vi M7 8)
  set M8 := Function.update M7 220 (List.replicate U false) with hM8
  have s9 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 0) (mp NI 242) 220
    (inj3 _ _ _ (im_ne NI iz 0 242) (im_ne NI iz 0 220) (ic_ne NI iz 0) (mm_ne NI 242 220 (by decide)) (mc_ne NI 242))
    w 0 0 U [] M8 (ZeroPadding.pad U (fb w 0)) (vi M8 0) (by simp [mp, MkT_m, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1])
    (by rw [hM8, Function.update_self, pad_nil]) (by omega) (by simp) hwR (by simp)
  set M9 := Function.update M8 220 (ZeroPadding.pad U (fb w 0)) with hM9
  have s10 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 3) (ip NI iz 4) 228
    (inj3 _ _ _ (ii_ne NI iz hiz 3 4 (by decide)) (im_ne NI iz 3 228) (ic_ne NI iz 3) (im_ne NI iz 4 228) (ic_ne NI iz 4))
    T 0 0 0 [] M9 (fb T 0) (vi M9 3) (vi M9 4)
    (by simp [hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0]) (by omega) (by simp) hTR
    (by simp)
  set M10 := Function.update M9 228 (fb T 0) with hM10
  have s11 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 3) (mp NI 228) 229
    (inj3 _ _ _ (im_ne NI iz 3 228) (im_ne NI iz 3 229) (ic_ne NI iz 3) (mm_ne NI 228 229 (by decide)) (mc_ne NI 228))
    T 0 0 0 [] M10 (fb T 0) (vi M10 3) (by rw [mp, MkT_m, hM10, Function.update_self])
    (by simp [hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0]) (by omega) (by simp) hTR
    (by simp)
  set M11 := Function.update M10 229 (fb T 0) with hM11
  have s12 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 3) (mp NI 228) 230
    (inj3 _ _ _ (im_ne NI iz 3 228) (im_ne NI iz 3 230) (ic_ne NI iz 3) (mm_ne NI 228 230 (by decide)) (mc_ne NI 228))
    T 0 0 0 [] M11 (fb T 0) (vi M11 3) (by simp [mp, MkT_m, hM11, hM10])
    (by simp [hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0]) (by omega) (by simp) hTR
    (by simp)
  set M12 := Function.update M11 230 (fb T 0) with hM12
  have s13 := addT pub init rowp rcp c6 (thrLive r L) RR c5 (ip NI iz 3) (mp NI 228) 231
    (inj3 _ _ _ (im_ne NI iz 3 228) (im_ne NI iz 3 231) (ic_ne NI iz 3) (mm_ne NI 228 231 (by decide)) (mc_ne NI 228))
    T 0 0 0 [] M12 (fb T 0) (vi M12 3) (by simp [mp, MkT_m, hM12, hM11, hM10])
    (by simp [hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0]) (by omega)
    (by simp) hTR (by simp)
  set M13 := Function.update M12 231 (fb T 0) with hM13
  
  have s14 := ThrSelBase.base_step a r four L target NI ib iOne hib hone k.selection U RR 0
    (MkT pub init rowp rcp c6 (thrLive r L) RR c5 M13)
    (fun c => by
      rw [MkT_m, hdg c]
      fin_cases c <;> simp [ThrSelCasc.dPort, hM13, hM12, hM11, hM10] <;> rfl)
    (fun kk hk' => by rw [MkT_i, hinitB kk hk'])
    (by rw [MkT_i, hinitO])
    (by rw [MkT_m]; simp [hM13, hM12, hM11, hM10, hM9]; rfl)
    (by rw [MkT_c]; rfl) (by rw [MkT_c]; rfl) hUf hR4
  rw [← MkT_master] at s14
  -- the final bank is `thrBase 0`
  have hfin : Function.update M13 220 (ZeroPadding.pad U (fb w (PCJ45bee56da9f34d5a_StreamPair.radix a r four
      k.selection))) = M := by
    have m242 : M 242 = fb w 0 := by rw [hM, KeyTop.masters_242, hres]
    have m240 : M 240 = fb w 2 := by rw [hM, KeyTop.masters_240, hpr]
    have m149 : M 149 = fb w 2 := by
      rw [hM, ThrKey.masters_at a r four L target _ k 149 (by decide), keyPad_key _ (by decide), ← hpr]
      exact KeySucc.thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 149 (Or.inl rfl)
    have m218 : M 218 = fb w 2 := by
      rw [hM, ThrKey.masters_at a r four L target _ k 218 (by decide), keyPad_key _ (by decide), ← hpr]
      exact KeySucc.thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 218 (Or.inr (Or.inl rfl))
    have m209 : M 209 = ZeroPadding.pad F (fb w 2) := by
      rw [hM, ThrKey.masters_at a r four L target _ k 209 (by decide), keyPad_key _ (by decide), ← hpr]
      exact KeySucc.thr_209 a r four _ _ L target _ _ _ _ _ _ _ _
    have m220 : M 220 = ZeroPadding.pad U (fb w (PCJ45bee56da9f34d5a_StreamPair.radix a r four k.selection)) := by
      rw [hM, ThrSelBase.master_220]
    have mdig : ∀ c : Fin 4, M (ThrSelCasc.dPort c) = fb T 0 := by
      intro c
      rw [hM, ThrSelBase.digit_master, hd0]
    have m228 : M 228 = fb T 0 := mdig 0
    have m229 : M 229 = fb T 0 := mdig 1
    have m230 : M 230 = fb T 0 := mdig 2
    have m231 : M 231 = fb T 0 := mdig 3
    funext i
    by_cases hk : i = 149 ∨ i = 209 ∨ i = 218 ∨ i = 220 ∨ i = 228 ∨ i = 229 ∨ i = 230 ∨ i = 231 ∨ i = 240 ∨ i = 242
    · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, m149]
      · simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, m209]
      · simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, m218]
      · simp [m220]
      · simp [hM13, hM12, hM11, hM10, m228]
      · simp [hM13, hM12, hM11, m229]
      · simp [hM13, hM12, m230]
      · simp [hM13, m231]
      · simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, m240]
      · simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, m242]
    · simp only [not_or] at hk
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hk
      simp [hM13, hM12, hM11, hM10, hM9, hM8, hM7, hM6, hM5, hM4, hM3, hM2, hM1, hM0,
        n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]
  rw [hfin] at s14
  rw [hblank, hBM]
  exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq
    (s13.seq s14))))))))))))

end Thr

end
end RowsConstruction.KeyZeroThr
