import Proof.Assembly.Driver

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
namespace PCJ34388a2fbfa9464b_
namespace Bank
open PCJ515eaa990d75455b_FamilyInit (Scalars)

/-- The literal existing family layout, followed by the seven paid drivers. -/
def layout {α : Type} (t : Nat) (payload : Fin t→α) (cap : α)
 (row : Fin 2→α) (body : Fin 4→α) (count : α) (extra : Fin 11→α) (drivers : Fin 7→α) :
 Fin (t+26)→α :=
 Fin.addCases (m:=t+19) (n:=7) (motive:=fun _=>α)
  (Fin.addCases (m:=t+8) (n:=11) (motive:=fun _=>α)
   (Fin.addCases (m:=t+7) (n:=1) (motive:=fun _=>α)
    (Fin.addCases (m:=t+3) (n:=4) (motive:=fun _=>α)
     (Fin.addCases (m:=t+1) (n:=2) (motive:=fun _=>α)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>α) payload (fun _=>cap)) row) body)
    (fun _=>count)) extra) drivers

def cap (t : Nat) (i : Fin 1) : Fin (t+26) :=
 (((((i.natAdd t).castAdd 2).castAdd 4).castAdd 1).castAdd 11).castAdd 7
def row (t : Nat) (i : Fin 2) : Fin (t+26) :=
 ((((i.natAdd (t+1)).castAdd 4).castAdd 1).castAdd 11).castAdd 7
def body (t : Nat) (i : Fin 4) : Fin (t+26) :=
 (((i.natAdd (t+1+2)).castAdd 1).castAdd 11).castAdd 7
def count (t : Nat) (i : Fin 1) : Fin (t+26) :=
 ((i.natAdd (t+1+2+4)).castAdd 11).castAdd 7
def extra (t : Nat) (i : Fin 11) : Fin (t+26) :=
 (i.natAdd (t+1+2+4+1)).castAdd 7
def source (t : Nat) (i : Fin 7) : Fin (t+26) := i.natAdd (t+19)


def values (m : Scalars) : Fin 7→Nat := ![m.S,m.R,m.B,m.b,m.v,m.N,m.N*m.b]
def inputH (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 0 (fun _=>0) (fun _=>1)
def heads (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 1 ![0,0,0,0,0,0,0,0,0,1,0] (fun _=>1)
def finalH (t : Nat) : Fin (t+26)→Nat :=
 layout t (fun _=>0) 0 (fun _=>0) (fun _=>0) 1 (fun _=>0) (fun _=>1)
def input (t : Nat) (m : Scalars) (D : List Bool) : Fin (t+26)→List Bool :=
 layout t (fun _=>[]) [] (fun _=>[]) ![D,[],[],[]] [] (fun _=>[])
  (fun i=>CompareMachine.word (values m i))
def bank (t : Nat) (m : Scalars) (D : List Bool) (k : Nat) : Fin (t+26)→List Bool :=
 layout t (fun _=>if 1≤k then List.replicate m.S false else [])
  (if 2≤k then List.replicate m.R false else [])
  ![[],if 3≤k then List.replicate m.B true else []]
  ![D,if 1≤k then List.replicate m.S false else [],
    if 1≤k then List.replicate m.S true else [],
    if 1≤k then List.replicate (m.S+1) false else []]
  (if 6≤k then CompareMachine.word m.N else [false])
  ![if 7≤k then List.replicate (m.N*m.b) true else [],[],
    if 4≤k then List.replicate m.b true else [],
    if 5≤k then List.replicate m.v true else [],[],
    if 5≤k then List.replicate (2*m.v+1) false else [],
    if 5≤k then frame (SignedSortKey.binary m.v 0) else [],[],[],
    if 6≤k then CompareMachine.word m.N else [false],[]]
  (fun i=>CompareMachine.word (values m i))

def first (t : Nat) : Fin 7→Fin (t+26)→Option Bool :=
 ![layout t (fun _=>some false) none (fun _=>none) ![none,some false,some true,some false] none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) (some false) (fun _=>none) (fun _=>none) none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) none ![none,some true] (fun _=>none) none (fun _=>none) (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,some true,none,none,none,none,none,none,none,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,none,some true,none,some false,some true,none,none,none,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) (some true) ![none,none,none,none,none,none,none,none,none,some true,none] (fun _=>none),
   layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![some true,none,none,none,none,none,none,none,none,none,none] (fun _=>none)]
def second (t : Nat) (j : Fin 7) : Fin (t+26)→Option Bool :=
 if j=4 then
  layout t (fun _=>none) none (fun _=>none) (fun _=>none) none ![none,none,none,none,none,some false,some false,none,none,none,none] (fun _=>none)
 else fun _=>none
def tail (t : Nat) (j : Fin 7) : Fin (t+26)→Option Bool :=
 if j=0 then layout t (fun _=>none) none (fun _=>none) ![none,none,none,some false] none (fun _=>none) (fun _=>none)
 else if j=4 then second t j else fun _=>none

def pass (t : Nat) (j : Fin 7) : Machine (t+26) 5 :=
 Driver.machine (source t j) (first t j) (second t j) (tail t j)

@[simp] theorem replicate_tail (b : Bool) (n : Nat) :
 List.replicate n b++[b]=List.replicate (n+1) b := by
 rw [List.replicate_add]; rfl

namespace Once
variable {t : Nat}
def machine (W : Fin t→Option Bool) (M : Fin t→HeadMove) : Machine t 2 where
 descriptionBits:=0
 start:=0
 halted:=fun q=>q.val==1
 rule:=fun q _=>if q.val=0 then some ⟨1,W,M⟩ else none

end Once

def setupW (t : Nat) : Fin (t+26)→Option Bool :=
 layout t (fun _=>none) none (fun _=>none) (fun _=>none) (some false)
  ![none,none,none,none,none,none,none,none,none,some false,none] (fun _=>none)
def setupM (t : Nat) : Fin (t+26)→HeadMove :=
 layout t (fun _=>.stay) .stay (fun _=>.stay) (fun _=>.stay) .right
  ![.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.right,.stay] (fun _=>.stay)
def cleanupM (t : Nat) : Fin (t+26)→HeadMove :=
 layout t (fun _=>.stay) .stay (fun _=>.stay) (fun _=>.stay) .stay
  ![.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.stay,.left,.stay] (fun _=>.stay)
def setup (t : Nat) := Once.machine (setupW t) (setupM t)
def cleanup (t : Nat) := Once.machine (fun _ : Fin (t+26)=>none) (cleanupM t)

def machine (t : Nat) : Machine (t+26) 39 :=
 Composition.machine (setup t)
  (Composition.machine (pass t 0)
   (Composition.machine (pass t 1)
    (Composition.machine (pass t 2)
     (Composition.machine (pass t 3)
      (Composition.machine (pass t 4)
       (Composition.machine (pass t 5)
        (Composition.machine (pass t 6) (cleanup t))))))))

attribute [local irreducible] Step Composition.machine pass setup cleanup machine values bank heads inputH input finalH

end Bank
end PCJ34388a2fbfa9464b_
