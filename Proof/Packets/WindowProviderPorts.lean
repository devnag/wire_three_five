import Proof.Rows.PhysicalFocusBoundary

/-! Fixed provider ports. Native normalization shares exactly its width,
output and reserve masters with the reusable arithmetic arena. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

def nativePorts : Fin 36→Fin 256 :=
  ![96,97,98,99,100,101,102,103,104,105,106,107,108,13,109,110,111,112,
    113,114,115,116,117,118,24,119,26,27,120,121,122,123,30,31,32,33]
def rawPorts : Fin 12→Fin 256 := ![78,186,132,133,134,135,136,137,138,139,122,30]
def substitutionPorts : Fin 44→Fin 256 := Fin.addCases (m:=34) (n:=10)
  (fun i=>i.castAdd 222) (![140,141,142,143,144,145,146,147,148,149])
def windowPorts (i : Fin 62) : Fin 256 :=
  if i=50 then 32 else if i=51 then 33 else ⟨i.val+34,by have h:=i.isLt;omega⟩


end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
