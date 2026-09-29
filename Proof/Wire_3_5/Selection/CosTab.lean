import Proof.Wire_3_5.Selection.Top

/-! # C1.5: the gate table and one gate's fetch (P3:1326-1329, 1356-1358)

Paper: "polynomially many bottom gates, each gate given by a polynomial-bit integer threshold description"
(P3:1326-1328); "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357).
The coset loop keeps every gate's record (C1.4's `gateRec`: each weight's sign cell and framed magnitude, then the
threshold's) on one table stream, in the request's order (`gateTable`). Before a gate call, **`fetch`** copies gate
`i`'s record into the gate routine's record stream `GA` (over its old contents): it skips `i·(n+1)` records and copies
`n + 1` (C1.4's `skipNN_rst`, `copyN_rst`), then returns both heads. The streams and registers are two injective maps
`S : Fin 50 → streams`, `Q : Fin 64 → registers`; the gate routine runs on `S 0 … S 27` and `Q 0 … Q 47`.
Main declarations: `gRecs`, `allRecs`, `gateTable`, `recAt_allRecs`, `fetch`, **`fetch_spec`**. Paper quantity: a
gate's integer threshold description on the machine's tape. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## The gate table -/

/-- A gate's records: its weights in coordinate order, then its threshold. -/
def gRecs {n : ℕ} (g : NormalizedThresholdGate n) : List (Bool × ℕ) :=
  coordRecs g ++ [(decide (g.threshold < 0), g.threshold.natAbs)]

theorem gRecs_length {n : ℕ} (g : NormalizedThresholdGate n) : (gRecs g).length = n + 1 := by
  simp [gRecs, coordRecs_length]

theorem tbl_gRecs (W : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : tbl W (gRecs g) = gateRec W g := by
  rw [gateRec_eq]
  simp [gRecs, tbl, List.flatMap_append]

/-- The request's gate records, gate after gate. -/
def allRecs (R : SelectionReq) : List (Bool × ℕ) := R.gates.flatMap fun g => gRecs (gateOf g)

/-- **The gate table**: every gate's record, in the request's order. -/
def gateTable (W : ℕ) (R : SelectionReq) : List Bool := tbl W (allRecs R)

theorem getD_flatMap_uniform {α β : Type} (f : α → List β) (m : ℕ) (hf : ∀ a, (f a).length = m) (d : β) :
    ∀ (l : List α) (i t : ℕ) (hi : i < l.length), t < m →
      (l.flatMap f).getD (i * m + t) d = (f l[i]).getD t d
  | [], i, t, hi, _ => absurd hi (by simp)
  | a :: l, 0, t, _, ht => by
    rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hf]; exact ht)]
    rfl
  | a :: l, i + 1, t, hi, ht => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith)]
    have e : (i + 1) * m + t - (f a).length = i * m + t := by rw [hf]; ring_nf; omega
    rw [e, getD_flatMap_uniform f m hf d l i t (by simpa using hi) ht]
    rfl

theorem allRecs_length (R : SelectionReq) : (allRecs R).length = R.gates.length * (R.n + 1) := by
  unfold allRecs
  rw [List.length_flatMap]
  simp [gRecs_length, List.sum_replicate]

theorem recAt_allRecs (R : SelectionReq) (i t : ℕ) (hi : i < R.gates.length) (ht : t < R.n + 1) :
    recAt (allRecs R) (i * (R.n + 1) + t) = recAt (gRecs (gateOf R.gates[i])) t := by
  unfold recAt allRecs
  exact getD_flatMap_uniform (fun g => gRecs (gateOf g)) (R.n + 1) (fun g => gRecs_length _) _ R.gates i t hi ht

theorem range_recs (W : ℕ) (rs : List (Bool × ℕ)) (m : ℕ) (hm : rs.length = m) (F : ℕ → Bool × ℕ)
    (hF : ∀ t < m, F t = recAt rs t) : (List.range m).flatMap (fun t => recBits W (F t)) = tbl W rs := by
  have e : (List.range m).map F = rs := by
    apply List.ext_getElem (by simp [hm])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hF t (by simpa using h1)]
    unfold recAt
    rw [List.getD_eq_getElem _ _ h2]
  rw [← e, tbl, List.flatMap_map]

/-! ## The fetch -/

/-- **Fetch gate `i`** (`i` in `Q 54`) from the table `S 30` into `GA = S 1`. -/
def fetch (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .seq (cloop (Q 54) (Q 55) (cloop (Q 60) (Q 56) (skipRec (S 30) (Q 48))))
    (.seq (cloop (Q 60) (Q 55) (copyRec false (S 30) (S 1) (Q 48) (Q 49)))
      (.seq (WM.rewind (S 30) (Q 48)) (WM.rewind (S 1) (Q 49))))

/-- The fetch's cost. -/
def fetchCost (n W i : ℕ) : ℕ :=
  i * ((n + 1) * (13 * W + 13 + 8) + 1 + 1 + (7 * (n + 1) + 1) + 8) + 1 + 1 + (7 * i + 1) + 1 +
    ((n + 1) * (40 * W + 40 + 8) + 1 + 1 + (7 * (n + 1) + 1) + 1 +
      (5 * ((i * (n + 1) + (n + 1)) * (2 * W + 2)) + 1 + 1 + (5 * ((n + 1) * (2 * W + 2)) + 1)))

/-- **The fetch**: `GA := gateRec W (gateOf gᵢ)` over its old contents (at most one record long); the table's and
`GA`'s heads and counters return to `0`; `Q 54` keeps `i`. -/
theorem fetch_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap W : ℕ) (R : SelectionReq) (σ : WState ns nr) (i : ℕ) (hi : i < R.gates.length)
    (hGT : σ.st (S 30) = gateTable W R) (h30 : σ.sh (S 30) = 0) (h1 : σ.sh (S 1) = 0)
    (hGA : (σ.st (S 1)).length ≤ (R.n + 1) * (2 * W + 2)) (q48 : σ.val (Q 48) = 0) (q49 : σ.val (Q 49) = 0)
    (q54 : σ.val (Q 54) = i) (q55 : σ.val (Q 55) = 0) (q56 : σ.val (Q 56) = 0) (q60 : σ.val (Q 60) = R.n + 1)
    (hcap : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap) :
    WExec cap (fetch S Q) σ (σ.sets (S 1) (gateRec W (gateOf R.gates[i]))) (fetchCost R.n W i) := by
  have hAB : S 30 ≠ S 1 := hS.ne (by decide)
  have hC : Q 48 ≠ Q 49 := hQ.ne (by decide)
  have hlen := allRecs_length R
  have hi1 : i * (R.n + 1) + (R.n + 1) ≤ R.gates.length * (R.n + 1) := by
    have := Nat.mul_le_mul_right (R.n + 1) (show i + 1 ≤ R.gates.length by omega); rw [add_one_mul] at this; omega
  have hcapn : (allRecs R).length * (2 * W + 2) + 2 < cap := by rw [hlen]; exact hcap
  have hA : σ.st (S 30) = tbl W (allRecs R) ++ [] := by rw [hGT, List.append_nil]; rfl
  have hi0 : i ≤ cap := by
    have : i ≤ R.gates.length * (R.n + 1) * (2 * W + 2) := by
      calc i ≤ R.gates.length := hi.le
        _ ≤ R.gates.length * (R.n + 1) * (2 * W + 2) := by
          rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hbig : (R.n + 1) * (2 * W + 2) ≤ R.gates.length * (R.n + 1) * (2 * W + 2) := by
    have h1 : 1 ≤ R.gates.length := by omega
    calc (R.n + 1) * (2 * W + 2) = 1 * ((R.n + 1) * (2 * W + 2)) := by ring
      _ ≤ R.gates.length * ((R.n + 1) * (2 * W + 2)) := Nat.mul_le_mul_right _ h1
      _ = _ := by ring
  have e0 := rst_self σ hAB hC h30 q48 h1 q49
  have x1 := skipNN_rst cap σ (σ.st (S 1)) hAB hC (Q 54) (Q 55) (Q 60) (Q 56)
    (by have := List.Nodup.map hQ (show ([54, 55, 60, 56, 48, 49] : List (Fin 64)).Nodup by decide); simpa using this)
    W (allRecs R) [] hA 0 i (R.n + 1) [] q54 q55 q60 q56 (by rw [hlen]; omega) hcapn hi0
  rw [Nat.zero_mul, e0, Nat.zero_add] at x1
  have x2 := copyN_rst cap σ (σ.st (S 1)) hAB hC false (Q 60) (Q 55) (hQ.ne (by decide)) (hQ.ne (by decide))
    (hQ.ne (by decide)) (hQ.ne (by decide)) (hQ.ne (by decide)) W (allRecs R) [] hA (i * (R.n + 1)) (R.n + 1) []
    q60 q55 (by rw [hlen]; exact hi1) hcapn (by simp only [List.length_nil, Nat.zero_add]; omega)
  have hout : ([] : List Bool) ++ (List.range (R.n + 1)).flatMap (fun t => recBits W
      (xor (recAt (allRecs R) (i * (R.n + 1) + t)).1 false, (recAt (allRecs R) (i * (R.n + 1) + t)).2)) =
      gateRec W (gateOf R.gates[i]) := by
    rw [List.nil_append, ← tbl_gRecs]
    exact range_recs W _ (R.n + 1) (gRecs_length _) _ (fun t ht => by
      rw [recAt_allRecs R i t hi ht]; simp)
  rw [hout] at x2
  have hglen : (gateRec W (gateOf R.gates[i])).length = (R.n + 1) * (2 * W + 2) := by
    rw [← tbl_gRecs, tbl_length, gRecs_length]
  have x3 := rewA_rst cap σ (σ.st (S 1)) hAB hC ((i * (R.n + 1) + (R.n + 1)) * (2 * W + 2))
    (gateRec W (gateOf R.gates[i])) (by have := Nat.mul_le_mul_right (2 * W + 2) hi1; omega)
  have x4 := rewB_rst cap σ (σ.st (S 1)) hAB hC h30 q48 h1 q49 (gateRec W (gateOf R.gates[i])) (by
    rw [hglen]; omega)
  rw [overlay_full _ _ (by rw [hglen]; exact hGA)] at x4
  unfold fetch
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))) rfl (le_of_eq ?_)
  rw [hglen]
  unfold fetchCost
  ring

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
