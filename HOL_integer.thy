
theory HOL_integer
imports HOL_words HOL_ring HOL_quotient
begin


setup \<open>
  fold OpenTheory.add_tyop
  [("HOL4.fcp.cart", @{type_name "HOL_words.HOL4.fcp.cart"}),
   ("HOL4.ring.ring", @{type_name "HOL_ring.HOL4.ring.ring"}),
   ("HOL4.canonical.canonical_sum", @{type_name "HOL_ring.HOL4.canonical.canonical_sum"}),
   ("HOL4.canonical.spolynom", @{type_name "HOL_ring.HOL4.canonical.spolynom"}),
   ("HOL4.ringNorm.polynom", @{type_name "HOL_ring.HOL4.ringNorm.polynom"}),
   ("HOL4.quote.varmap", @{type_name "HOL_ring.HOL4.quote.varmap"}),
   ("HOL4.quote.index", @{type_name "HOL_ring.HOL4.quote.index"}),
   ("HOL4.prelim.ordering", @{type_name "HOL_ring.HOL4.prelim.ordering"})]
\<close>


art_file "hol-integer-1.1.art"


end