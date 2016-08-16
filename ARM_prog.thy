
theory ARM_prog
imports ARM_step
begin

setup {*
  fold OpenTheory.add_tyop
  [("HOL4.fcp.cart", @{type_name "HOL4.fcp.cart"}),
   ("HOL4.fcp.bit0", @{type_name "HOL4.fcp.bit0"}),
   ("HOL4.fcp.bit1", @{type_name "HOL4.fcp.bit1"})]

*}

lemma[opentheory] :
"\<forall>A B C. (A \<or> B \<and> C) = ((A \<or> B) \<and> (A \<or> C))"
by fastforce


setup {* OpenTheory.read_article "machine-code-hoare-logic.art" [] *}
setup {* OpenTheory.read_article "machine-code-hoare-logic-state.art" [] *}



setup {* OpenTheory.read_article "arm-prog.art" [] *}

end