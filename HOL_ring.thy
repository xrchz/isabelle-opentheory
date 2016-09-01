
theory HOL_ring
imports HOL_base
begin


setup {*
  fold OpenTheory.add_tyop
  [("HOL4.ind_type.recspace", @{type_name "HOL_base.HOL4.ind_type.recspace"})]
*}

setup {* OpenTheory.read_article "hol-ring-1.2.art" [] *}


end