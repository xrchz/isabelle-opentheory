theory ARM
imports HOL_floating_point 
begin


setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.binary_ieee.rounding", @{type_name "HOL4.binary_ieee.rounding"})]
\<close>

setup \<open>
  fold OpenTheory.add_const
  [("HOL4.state_transformer.FOR", @{const_name "HOL_base.HOL4.state_transformer.FOR"})]
\<close>

setup \<open>OpenTheory.read_article "arm-model-1.1.art" []\<close>



setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.arm.VFPExtension", @{type_name "HOL4.arm.VFPExtension"})]

\<close>


setup \<open>
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
\<close>



setup \<open>OpenTheory.read_article "arm-step-1.1.art" []\<close>



setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.fcp.cart", @{type_name "HOL4.fcp.cart"}),
   ("HOL4.fcp.bit0", @{type_name "HOL4.fcp.bit0"}),
   ("HOL4.fcp.bit1", @{type_name "HOL4.fcp.bit1"})]
\<close>

lemma[opentheory] :
"\<forall>A B C. (A \<or> B \<and> C) = ((A \<or> B) \<and> (A \<or> C))"
by fastforce


setup \<open>OpenTheory.read_article "machine-code-hoare-logic-1.1.art" []\<close>
setup \<open>OpenTheory.read_article "machine-code-hoare-logic-state-1.1.art" []\<close>



setup \<open>OpenTheory.read_article "arm-prog-1.1.art" []\<close>



setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.arm_prog.arm_component", @{type_name "HOL4.arm_prog.arm_component"}),
   ("HOL4.arm_prog.arm_data", @{type_name "HOL4.arm_prog.arm_data"})]

\<close>


setup \<open>OpenTheory.read_article "arm-decomp-1.0.art" []\<close>

end