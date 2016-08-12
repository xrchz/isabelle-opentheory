
theory ARM_step
imports ARM_model 
begin




setup {*
  fold OpenTheory.add_tyop
  [("HOL4.arm.arm_state", @{type_name "HOL4.arm.arm_state"}),
   ("HOL4.arm.SCR", @{type_name "HOL4.arm.SCR"}),
   ("HOL4.arm.CP15", @{type_name "HOL4.arm.CP15"}),
   ("HOL4.arm.PSR", @{type_name "HOL4.arm.PSR"}),
   ("HOL4.arm.Architecture", @{type_name "HOL4.arm.Architecture"}),
   ("HOL4.arm.Extensions", @{type_name "HOL4.arm.Extensions"}),
   ("HOL4.arm.RName", @{type_name "HOL4.arm.RName"}),
   ("HOL4.arm.exception", @{type_name "HOL4.arm.exception"}),
   ("HOL4.arm.FPSCR", @{type_name "HOL4.arm.FPSCR"}),
   ("HOL4.arm.FP", @{type_name "HOL4.arm.FP"}),
   ("HOL4.arm.CP14", @{type_name "HOL4.arm.CP14"}),
   ("HOL4.arm.Encoding", @{type_name "HOL4.arm.Encoding"}),
   ("HOL4.arm.InstrSet", @{type_name "HOL4.arm.InstrSet"}),
   ("HOL4.arm.SRType", @{type_name "HOL4.arm.SRType"}),
   ("HOL4.arm.MachineCode", @{type_name "HOL4.arm.MachineCode"}),
   ("HOL4.arm.instruction", @{type_name "HOL4.arm.instruction"})]
*}



setup {* OpenTheory.read_article "arm-step.art" [] *}


end