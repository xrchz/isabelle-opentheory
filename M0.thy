
theory M0
imports ARM
begin

art_file "m0-model-1.0.art"


setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.m0.RName", @{type_name "HOL4.m0.RName"}),
   ("HOL4.m0.ARM_Exception", @{type_name "HOL4.m0.ARM_Exception"}),
   ("HOL4.m0.SHPR2", @{type_name "HOL4.m0.SHPR2"}),
   ("HOL4.m0.SHPR3", @{type_name "HOL4.m0.SHPR3"}),
   ("HOL4.m0.PRIMASK", @{type_name "HOL4.m0.PRIMASK"}),
   ("HOL4.m0.IPR", @{type_name "HOL4.m0.IPR"}),
   ("HOL4.m0.Mode", @{type_name "HOL4.m0.Mode"}),
   ("HOL4.m0.CCR", @{type_name "HOL4.m0.CCR"}),
   ("HOL4.m0.m0_state", @{type_name "HOL4.m0.m0_state"}),
   ("HOL4.m0.PSR", @{type_name "HOL4.m0.PSR"}),
   ("HOL4.m0.CONTROL", @{type_name "HOL4.m0.CONTROL"}),
   ("HOL4.m0.AIRCR", @{type_name "HOL4.m0.AIRCR"}),
   ("HOL4.m0.SRType", @{type_name "HOL4.m0.SRType"}),
   ("HOL4.m0.MachineCode", @{type_name "HOL4.m0.MachineCode"}),
   ("HOL4.m0.instruction", @{type_name "HOL4.m0.instruction"}),
   ("HOL4.m0.exception", @{type_name "HOL4.m0.exception"})]
\<close>

art_file "m0-step-1.0.art"
art_file "m0-prog-1.0.art"

setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.m0_prog.m0_component", @{type_name "HOL4.m0_prog.m0_component"}),
   ("HOL4.m0_prog.m0_data", @{type_name "HOL4.m0_prog.m0_data"})]

\<close>

art_file "m0-decomp-1.0.art"


end