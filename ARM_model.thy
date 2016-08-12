
theory ARM_model
imports HOL_floating_point 
begin


setup {*
  fold OpenTheory.add_tyop
  [("HOL4.binary_ieee.rounding", @{type_name "HOL4.binary_ieee.rounding"})]
*}

setup {*
  fold OpenTheory.add_const
  [("HOL4.state_transformer.FOR", @{const_name "HOL_base.HOL4.state_transformer.FOR"})]
*}

setup {* OpenTheory.read_article "arm-model.art" [] *}


end