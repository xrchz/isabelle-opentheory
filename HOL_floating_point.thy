

theory HOL_floating_point
imports HOL_real
begin

setup {*
  fold OpenTheory.add_tyop
  [("HOL4.fcp.bit0", @{type_name "HOL4.fcp.bit0"}),
   ("HOL4.fcp.bit1", @{type_name "HOL4.fcp.bit1"})]
*}

setup {* OpenTheory.read_article "hol-floating-point-1.1.art" [] *}

end