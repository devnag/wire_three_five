import Proof.SourceAssembly.SourcePoolSeedFanout
import Proof.SourceAssembly.PoolColdCompatible

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 1000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolBank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourcePoolSeedFanout (pad_pad)
noncomputable section

def data {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 9→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.masters live (B+q+1))
    (![List.replicate (PoolEntry.reserve B q (B+q+1)) true,source,natWord (2*N),CompareMachine.word N])
def lift (o : Option (Fin 5)) : Option (Fin 9):=o.map (fun i=>i.castAdd 4)
def child (i : Fin 64) : Option (Fin 9):=
  if i=61 then some 7 else lift (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.select i)
def select : Fin 132→Option (Fin 9):=
  Fin.addCases (motive:=fun _=>Option (Fin 9))
    (Fin.addCases (motive:=fun _=>Option (Fin 9))
      (Fin.addCases (motive:=fun _=>Option (Fin 9)) child
        (Fin.addCases (motive:=fun _=>Option (Fin 9))
          (fun j : Fin 62=>lift (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.select (PoolEntryRestore.work j)))
          (![none,some 5,none] : Fin 3→Option (Fin 9))))
      (![some 6,none] : Fin 2→Option (Fin 9))) (fun _ : Fin 1=>some 8)

def prefixWord (N : Nat):=natWord (2*N)++RepairOrdinary.frame []
def startBank {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 132→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (PoolEntryOccurrence.bank live B (B+q+1) source
      (List.replicate (PoolEntry.reserve B q (B+q+1)) false) (prefixWord N))
    (fun _ : Fin 1=>CompareMachine.word N)

theorem word_lift {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) (o : Option (Fin 5)) :
    (lift o).elim [] (data live B N source)=
    o.elim [] (PCJ6e421fabe2aa4155_SourcePoolSeedFanout.masters live (B+q+1)) := by
  cases o <;>simp only [lift,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some,data,Fin.addCases_left]

theorem pad_append_false (P : Nat) (bits : List Bool) (h:bits.length+1≤P) :
    ZeroPadding.pad P (bits++[false])=ZeroPadding.pad P bits := by
  have he:ZeroPadding.pad (bits.length+1) bits=bits++[false]:=by simp [ZeroPadding.pad]
  rw [←he];exact pad_pad _ _ _ h

attribute [local irreducible] PoolEntry.input

theorem bank_at {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool) (i : Fin 64) :
    PoolEntryBaseline.bank live B w framed out i=
    if i=55 then framed else if i=61 then out else PCJ6e421fabe2aa4155_SourcePoolSeedShape.table live B w i := by
  by_cases h:i=55
  · subst i;rw [PoolEntryBaseline.bank_source,if_pos rfl]
  rw [if_neg h]
  by_cases ho:i=61
  · subst i;rw [PoolEntryBaseline.bank_output,if_pos rfl]
  rw [if_neg ho,PoolEntryBaseline.bank_outside _ _ _ _ _ _ ho]
  have he:PoolEntryBaseline.bank live B w framed [] i=PoolEntryBaseline.bank live B w [] [] i:=by
    simp only [PoolEntryBaseline.bank,Function.update_of_ne h]
  rw [he,PCJ6e421fabe2aa4155_SourcePoolSeedShape.bank_eq]


theorem child_scalar {q : Nat} (live : Finset (Fin q)) (B N P S : Nat) (source : List Bool)
    (hs:S≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad (P)
      (ZeroPadding.pad (PoolEntryRestore.caps (S) i)
        (if i=55 then List.replicate (S) false else
          if i=61 then prefixWord N else PCJ6e421fabe2aa4155_SourcePoolSeedShape.table live B (B+q+1) i))=
    ZeroPadding.pad (P)
      ((child i).elim [] (data live B N source)) := by
  by_cases ho:i=61
  · subst i
    rw [if_neg (by decide : (61 : Fin 64)≠55),if_pos rfl]
    change ZeroPadding.pad P (ZeroPadding.pad 0 (prefixWord N))=ZeroPadding.pad P (natWord (2*N))
    rw [ZeroPadding.pad_zero]
    exact pad_append_false P _ hp
  by_cases hi:i=55
  · subst i
    rw [if_pos rfl]
    change ZeroPadding.pad P (ZeroPadding.pad 0 (List.replicate (S) false))=ZeroPadding.pad P []
    rw [ZeroPadding.pad_zero]
    exact pad_replicate_false _ _ hs
  rw [if_neg hi,if_neg ho,PoolEntryRestore.caps,if_neg (not_or_intro ho hi),pad_pad _ _ _ hs]
  rw [child,if_neg ho,word_lift]
  exact PCJ6e421fabe2aa4155_SourcePoolSeedFanout.padded_table live B (B+q+1) P
    hc he hl i


theorem child_padded {q : Nat} (live : Finset (Fin q)) (B N P : Nat) (source : List Bool)
    (hs:PoolEntry.reserve B q (B+q+1)≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad (P)
      (PoolEntryRestore.padded (PoolEntryBaseline.bank live B (B+q+1)
        (List.replicate (PoolEntry.reserve B q (B+q+1)) false)) (prefixWord N)
        (PoolEntry.reserve B q (B+q+1)) i)=
    ZeroPadding.pad (P)
      ((child i).elim [] (data live B N source)) := by
  rw [PoolEntryRestore.padded,bank_at]
  exact child_scalar live B N P _ source hs hp hc he hl i


theorem start_padded {q : Nat} (live : Finset (Fin q)) (B N P : Nat) (source : List Bool)
    (hs:PoolEntry.reserve B q (B+q+1)+1≤P) (hp:(natWord (2*N)).length+1≤P)
    (hc:ConstantGateReusable.C (B+q+1)+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 132) :
    ZeroPadding.pad (P) (startBank live B N source i)=
    ZeroPadding.pad (P)
      (NativeFanout.word select (data live B N source) i) := by
  simp only [startBank,PoolEntryOccurrence.bank,PoolEntryBaseline.state,
    PoolEntryRestore.input,PoolEntryRestore.state,NativeFanout.word,select]
  refine Fin.addCases (m:=131) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
    simp only [Fin.addCases_left,Fin.addCases_right]
  · refine Fin.addCases (m:=129) (n:=2) (fun j=>?_) (fun j=>?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (m:=64) (n:=65) (fun j=>?_) (fun j=>?_) j <;>
        simp only [Fin.addCases_left,Fin.addCases_right]
      · exact child_padded live B N P source (by omega) hp hc he hl j
      · refine Fin.addCases (m:=62) (n:=3) (fun j=>?_) (fun j=>?_) j <;>
          simp only [Fin.addCases_left,Fin.addCases_right]
        · change ZeroPadding.pad _ (PoolEntryBaseline.bank live B (B+q+1)
            (List.replicate (PoolEntry.reserve B q (B+q+1)) false) [] (PoolEntryRestore.work j))=
            ZeroPadding.pad _ ((lift _).elim [] (data live B N source))
          have hj:PoolEntryRestore.work j≠55:=by fin_cases j <;>decide
          have he:PoolEntryBaseline.bank live B (B+q+1)
              (List.replicate (PoolEntry.reserve B q (B+q+1)) false) [] (PoolEntryRestore.work j)=
              PoolEntryBaseline.bank live B (B+q+1) [] [] (PoolEntryRestore.work j):=by
            simp only [PoolEntryBaseline.bank,Function.update_of_ne hj]
          rw [he,PCJ6e421fabe2aa4155_SourcePoolSeedShape.bank_eq,word_lift]
          exact PCJ6e421fabe2aa4155_SourcePoolSeedFanout.padded_table live B _ P hc ‹ConstantGateReusable.E B q≤P› hl _
        · fin_cases j
          · exact pad_replicate_false _ _ (by omega)
          · rfl
          · exact pad_replicate_false _ _ hs
    · simp only [Fin.addCases_right]
      fin_cases j
      · rfl
      · exact pad_replicate_false _ _ (by omega)
  · rfl

end
end PCJ6e421fabe2aa4155_SourcePoolBank
