
theory HOL_words 
imports HOL_string
begin


setup {*
  fold OpenTheory.add_tyop
  [("HOL4.ind_type.recspace", @{type_name "HOL_base.HOL4.ind_type.recspace"}),
   ("HOL4.bool.itself", @{type_name "HOL_base.HOL4.bool.itself"}),
   ("HOL4.string.char", @{type_name "HOL_string.HOL4.string.char"})]

*}


setup {* OpenTheory.read_article "hol-words.art" [] *}


end