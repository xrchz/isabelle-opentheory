

theory HOL_floating_point
imports HOL_real
begin

setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.fcp.bit0", @{type_name "HOL4.fcp.bit0"}),
   ("HOL4.fcp.bit1", @{type_name "HOL4.fcp.bit1"})]
\<close>

art_file "hol-floating-point-1.1.art"

end