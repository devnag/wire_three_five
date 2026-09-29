import Proof.Wire_3_5.Recovery.HybridProgLayout

/-! # The hybrid `E^NP` program: the program (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgram`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: One finite oracle control graph on every input length. Inactive inputs print false; live inputs run the original full recovery and its selected output worker. The Case1 edge performs the paid common-query clear.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

def liveFlag (p : Parameters) : Fin (tapes p):=prefixSlot p
  (CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
    (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p))))
def recoveryFlag (p : Parameters) : Fin (tapes p):=lift1 p (flagBank p)
def pieces (p : Parameters) : Fin 6→Piece (tapes p):=
  ![focused (prefixProgram p) (prefixSlot p),
    focused (recovery p) (recoverySlot p),
    ordinary (RecoveryFocus.machine (clearSlot p) (CloseoutCommonQueryClear.machine p.Aq p.Bq)),
    focused (one p) (oneSlot p),
    ordinary (RecoveryFocus.machine (twoSlot p) (two p)),
    ordinary (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false]))]
def next (p : Parameters) (j : Fin 6) (_ : Fin (pieces p j).states)
    (read : Fin (tapes p)→Bool) : Option (Fin 6):=
  if j.val=0 then some (if read (liveFlag p) then 1 else 5)
  else if j.val=1 then some (if read (recoveryFlag p) then 4 else 2)
  else if j.val=2 then some 3 else none
def program (p : Parameters):=(ports p).program (graph (pieces p) 0 (next p))
def input (p : Parameters) (bits : List Bool) (i : Fin (tapes p)):=
  if i.val=0 then frame bits else []

end
end NearCubicWires.RepairSource.HybridProgram
