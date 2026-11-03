import Proof.Packets.NativeIndexedAtom
import Proof.Packets.PacketVector
import Proof.Packets.ReusableNativeNormalize

/-! Exact states of the descending physical atom-table loop. The index
addresses the original native cache while its unchanged decoded code selects the
dense packet entry. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
open NearCubicWires NearCubicWires.RepairOrdinary
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open PacketVector (Packet)

def index (cs : List Pair) (j : Nat) := cs.length-1-j
def code (coding : Nat→Nat) (cs : List Pair) (j : Nat) := coding (index cs j)
def atom (cs : List Pair) (j : Nat) := cs.getD (index cs j) ([],[])
def codeList (coding : Nat→Nat) (cs : List Pair) := (List.range cs.length).map (code coding cs)
def codes (coding : Nat→Nat) (cs : List Pair) := (codeList coding cs).flatMap NativeLiteralCode.word
def codePrefix (coding : Nat→Nat) (cs : List Pair) (j : Nat) := ((codeList coding cs).take j).flatMap NativeLiteralCode.word
def table (C : Nat) (coding : Nat→Nat) (cs : List Pair) (initial : List Packet) : Nat→List Packet
  | 0=>initial
  | j+1=>(table C coding cs initial j).set (code coding cs j) (NativeAtomStore.answer C (atom cs j))

theorem index_lt (cs : List Pair) (j : Nat) (hj : j<cs.length) : index cs j<cs.length := by
  unfold index;omega

theorem atom_eq (cs : List Pair) (j : Nat) (hj : j<cs.length) :
    atom cs j=cs[index cs j]'(index_lt cs j hj) := by
  simp [atom,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (index_lt cs j hj)]

theorem atom_mem (cs : List Pair) (j : Nat) (hj : j<cs.length) : atom cs j∈cs := by
  rw [atom_eq cs j hj]
  exact List.getElem_mem _

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomProgram
