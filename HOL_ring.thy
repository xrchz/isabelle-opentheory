
theory HOL_ring
imports HOL_base
begin


setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.ind_type.recspace", @{type_name "HOL_base.HOL4.ind_type.recspace"})]
\<close>

setup \<open>OpenTheory.read_article "hol-ring-1.1.art" []\<close>


end