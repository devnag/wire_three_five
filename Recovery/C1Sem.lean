import Recovery.CaseOneRuns

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.C1Sem

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces NearCubicGates.Close.Transfer NearCubicGates.Close.Recovery
open NearCubicGates.Close.Gadget

/-- The cyclic list: `K` entries, entry `i` is `wl[i mod |wl|]`. -/
def cycList (wl : List Bool) (K : ℕ) : List Bool := (List.range K).map fun i => wl.getD (i % wl.length) false

/-- The address bits of `i < 2^q` restricted to `a` bits (`false` past `q`) encode `i mod 2^a`. -/
theorem address_mod (a q i : ℕ) (hi : i < 2 ^ q) :
    binaryAddress (fun j : Fin a => if h : j.val < q then (fun k : Fin q => i.testBit k.val) ⟨j.val, h⟩ else false) =
      ⟨i % 2 ^ a, Nat.mod_lt _ (by positivity)⟩ := by
  have hfun : (fun j : Fin a => if h : j.val < q then (fun k : Fin q => i.testBit k.val) ⟨j.val, h⟩ else false) =
      fun j : Fin a => (i % 2 ^ a).testBit j.val := by
    funext j
    rw [Nat.testBit_mod_two_pow]
    simp only [decide_eq_true j.isLt, Bool.true_and]
    split_ifs with h
    · rfl
    · symm
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hfun, binaryAddress_testBit (Nat.mod_lt _ (by positivity))]

/-- **The truth table of `cycFn`** is the cyclic list of `w`. -/
theorem table_cycFn (a q : ℕ) (w : BitInput (2 ^ a)) :
    boolFunctionTable (cycFn a w q) = cycList (List.ofFn w) (2 ^ q) := by
  apply List.ext_getElem
  · simp [boolFunctionTable, cycList]
  · intro i h1 h2
    have hi : i < 2 ^ q := by simpa [cycList] using h2
    simp only [boolFunctionTable, cycList, List.getElem_map, List.getElem_range, cycFn]
    rw [address_mod a q i hi]
    simp only [List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; exact Nat.mod_lt _ (by positivity)), List.getElem_ofFn]

end NearCubicGates.Close.Recovery.C1Sem
