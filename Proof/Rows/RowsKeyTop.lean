import Proof.Rows.RowsKeySucc

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyTop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc
noncomputable section

/-! ## 1. Ports and slot maps -/

/-- The work port of cell-bank tape `c` of the loop block (cells 0–253 `0^R`, clock 254 `1^R`, log 255 `0^(R+1)`). -/
def cellPort (NI : Nat) (c : Fin 257) : Fin (2+rowsWork NI) :=
  loopPort NI (((RowsConstruction.ThrCell.cellP c).castAdd 1).castAdd 1)

theorem masterPort_val (NI : Nat) (k : Fin 254) : (masterPort NI k).val = 2+NI+72+257+k.val := by
  simp [masterPort, loopPort, fixPort, RowsConstruction.ThrCell.masterP, RowsConstruction.CellReload.masterPort]
  omega

theorem cellPort_val (NI : Nat) (c : Fin 257) : (cellPort NI c).val = 2+NI+72+c.val := by
  simp [cellPort, loopPort, fixPort, RowsConstruction.ThrCell.cellP, RowsConstruction.CellReload.cellPort]
  omega

theorem c5Port_val (NI : Nat) (i : Fin 16) : (c5Port NI i).val = 2+NI+594+i.val := by
  simp [c5Port, fixPort, RowsConstruction.ThrCell.MT]
  omega

/-- Residue level: digit master 242, bound master 240 (the prime), flag and scratch cells 0–3, clock 254, log 255. -/
def slR (NI : Nat) : Fin 8 → Fin (2+rowsWork NI) :=
  ![masterPort NI 242, masterPort NI 240, cellPort NI 0, cellPort NI 1, cellPort NI 2, cellPort NI 3,
    cellPort NI 254, cellPort NI 255]

/-- Seed level: digit C5 port 0, bound C5 port 1 (the seed count), flag and scratch C5 7–10, driver 11, log 12. -/
def slS (NI : Nat) : Fin 8 → Fin (2+rowsWork NI) :=
  ![c5Port NI 0, c5Port NI 1, c5Port NI 7, c5Port NI 8, c5Port NI 9, c5Port NI 10, c5Port NI 11, c5Port NI 12]

theorem slR_injective (NI : Nat) : Function.Injective (slR NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [slR, masterPort_val, cellPort_val] at hv ⊢

theorem slS_injective (NI : Nat) : Function.Injective (slS NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [slS, c5Port_val] at hv ⊢

/-- The cost of a carried digit step at width `w` and blank size `R`, continuing with a stage of cost `n`. -/
def carryCost (w R n : Nat) : Nat := 4*w+2+1+((4*w+4)+1+(((2*(2*w+1)+2)+1+((2*R+4)+1+n))+2))

/-! ## 2. Bank identities of the work layout -/

section Bank
variable {NI : Nat} (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rowp : Fin 8 → List Bool)
  (rcp : Fin 64 → List Bool) (c6 : Fin 2 → List Bool)

theorem wl_master (c5 : Fin 16 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
    (M : Fin 254 → List Bool) (k : Fin 254) :
    workLayout pub init rowp rcp (loopBank live R M) c6 c5 (masterPort NI k) = M k := by
  simp only [masterPort, layout_loop, loopBank, Fin.addCases_left, RowsConstruction.ThrCell.tapes,
    RowsConstruction.ThrCell.layout_master]

theorem wl_cell (c5 : Fin 16 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
    (M : Fin 254 → List Bool) (c : Fin 257) :
    workLayout pub init rowp rcp (loopBank live R M) c6 c5 (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R
        (List.replicate (2^liveᶜ.card) false) c := by
  simp only [cellPort, layout_loop, loopBank, Fin.addCases_left, RowsConstruction.ThrCell.tapes,
    RowsConstruction.ThrCell.layout_cell]

theorem wl_loop_update (c5 : Fin 16 → List Bool) (loop : Fin (RowsConstruction.ThrCell.MT+1+1) → List Bool)
    (i : Fin (RowsConstruction.ThrCell.MT+1+1)) (v : List Bool) :
    workLayout pub init rowp rcp (Function.update loop i v) c6 c5 =
      Function.update (workLayout pub init rowp rcp loop c6 c5) (loopPort NI i) v := by
  unfold workLayout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_left,
    RowsConstruction.CellInput.addCases_update_left, RowsConstruction.CellInput.addCases_update_right,
    RowsConstruction.CellInput.addCases_update_right]
  rfl

theorem wl_c5_update (loop : Fin (RowsConstruction.ThrCell.MT+1+1) → List Bool) (c5 : Fin 16 → List Bool)
    (i : Fin 16) (v : List Bool) :
    workLayout pub init rowp rcp loop c6 (Function.update c5 i v) =
      Function.update (workLayout pub init rowp rcp loop c6 c5) (c5Port NI i) v := by
  unfold workLayout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_right,
    RowsConstruction.CellInput.addCases_update_right]
  rfl

end Bank

theorem loopBank_update {q : Nat} (live : Finset (Fin q)) (R : Nat) (M : Fin 254 → List Bool) (k : Fin 254)
    (v : List Bool) :
    loopBank live R (Function.update M k v) =
      Function.update (loopBank live R M) (((RowsConstruction.ThrCell.masterP k).castAdd 1).castAdd 1) v := by
  unfold loopBank RowsConstruction.ThrCell.tapes RowsConstruction.ThrCell.layout RowsConstruction.CellReload.layout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_left,
    RowsConstruction.CellInput.addCases_update_left, RowsConstruction.CellInput.addCases_update_left]
  rfl

theorem c5_seed_update (e e' N : Nat) (cut : List Bool) (off : Fin 4 → List Bool) (S : Nat) :
    c5Words (seedWords e' N) cut off S =
      Function.update (c5Words (seedWords e N) cut off S) 0 (fb (natBitLength N) e') := by
  funext i
  fin_cases i <;> rfl

/-! ## 3. The key facts at the THR request -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The THR framed width. -/
abbrev wT : Nat := 12*RowsConstruction.ThrWidth.T a r four L target+19
/-- The loop block's blank size (the cell reserve). -/
abbrev RT : Nat := thrRes r.q (RowsConstruction.ThrWidth.T a r four L target)
/-- The seed count. -/
abbrev NS : Nat := (thrSeeds a r L target).length

theorem keyAt_eq (j : Nat) (hj : j < (KeySucc.keys a r L target).length) :
    thrKeyAt a r L target j = some (KeySucc.keys a r L target)[j] := by
  simp only [thrKeyAt, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj]

theorem masters_242 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 242 = fb (wT a r four L target) k.residue.val := by
  unfold thrMasters
  rw [if_neg (by decide), keyPad_key _ (by decide)]
  exact thr_242 a r four _ _ L target _ _ _ _ _ _ _ _

theorem masters_240 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 240 = fb (wT a r four L target) k.prime.val := by
  unfold thrMasters
  rw [if_neg (by decide), keyPad_key _ (by decide)]
  exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 240 (Or.inr (Or.inr rfl))

theorem wT_fits (k : RCFive.RowKeys.ThrKey a r L target) :
    2*wT a r four L target+1 ≤ RT a r four L target := by
  have h := thr_hml a r four L target (RT a r four L target) (thrR_le_res _ _) k 242
  rw [masters_242, fb, frame_length, SignedSortKey.binary_length] at h
  exact h

/-! ## 4. The carry cascade on the last key and the two closed cases -/

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

theorem base_eq (j : Nat) (hj : j < (KeySucc.keys a r L target).length) :
    thrBase a r four L target NI pub init rcp C cC hF j =
      workLayout pub init (rowpWords (thrN a r L target) C cC hF) rcp
        (loopBank (thrLive r L) (RT a r four L target)
          (thrMasters a r four L target (RT a r four L target) (KeySucc.keys a r L target)[j]))
        (c6Words (thrLive r L)ᶜ.card)
        (c5Words (seedWords (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) (NS a r L target))
          (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
          (seedScratch (NS a r L target))) := by
  simp only [thrBase, keyAt_eq a r L target j hj]

/-! ## 5. The top machine -/

end Thr

end
end RowsConstruction.KeyTop
