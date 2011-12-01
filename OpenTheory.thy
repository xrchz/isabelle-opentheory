theory OpenTheory
imports Main Parity
uses ("opentheory.ML")
begin

subsection {* OpenTheory package *}

text {* Lemmas used by the package *}

lemma type_definition_Collect_iff:
  assumes "type_definition Rep Abs (Collect P)"
  shows "P r \<longleftrightarrow> (Rep (Abs r) = r)"
proof
  assume "P r"
  hence "r \<in> Collect P" by simp
  thus "Rep (Abs r) = r"
    by (rule type_definition.Abs_inverse [OF assms])
next
  have "Rep (Abs r) \<in> Collect P"
    by (rule type_definition.Rep [OF assms])
  also assume "Rep (Abs r) = r"
  finally show "P r" by simp
qed

text {* Load opentheory package *}

use "opentheory.ML"
setup OpenTheory.setup


subsection {* Load boolean theories *}

setup {*
  fold OpenTheory.add_tyop
  [("->", @{type_name "fun"}),
   ("bool", @{type_name "bool"})]
*}

setup {*
  fold OpenTheory.add_const
  [("=", @{const_name "HOL.eq"}),
   ("Data.Bool.!", @{const_name "All"}),
   ("Data.Bool.==>", @{const_name "HOL.implies"}),
   ("Data.Bool.\\\\/", @{const_name "HOL.disj"}),
   ("Data.Bool./\\\\", @{const_name "HOL.conj"}),
   ("Data.Bool.?", @{const_name "Ex"}),
   ("Data.Bool.T", @{const_name "True"}),
   ("Data.Bool.F", @{const_name "False"}),
   ("Data.Bool.~", @{const_name "Not"}),
   ("Data.Bool.?!", @{const_name "Ex1"})]
*}

lemma [opentheory]:
  "True = ((\<lambda>p::bool. p) = (\<lambda>p. p))"
by auto

lemma [where 'A='A, opentheory]: "All = (\<lambda>P. P = (\<lambda>x::'A. True))"
by (auto intro!: ext)

lemma [opentheory]: "op \<longrightarrow> = (\<lambda>p q. (p \<and> q) = p)"
by (auto intro!: ext)

lemma [opentheory]: "op \<and> = (\<lambda>p q. (\<lambda>f. f p q :: bool) = (\<lambda>f. f True True))"
apply (simp add: fun_eq_iff, safe, simp_all)
apply (drule_tac x="\<lambda>x y. x" in spec, simp)
apply (drule_tac x="\<lambda>x y. y" in spec, simp)
done

lemma [opentheory]: "op \<or> = (\<lambda>p q. \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r)"
by (auto intro!: ext)

lemma [where 'A='A, opentheory]: "Ex = (\<lambda>P. \<forall>q. (\<forall>x::'A. P x \<longrightarrow> q) \<longrightarrow> q)"
by (auto intro!: ext)

lemma [opentheory]: "False = (\<forall>p. p)"
by auto

lemma [opentheory]: "Not = (\<lambda>p. p \<longrightarrow> False)"
by auto

lemma [where 'A='A, opentheory]:
  "Ex1 = (\<lambda>P. Ex P \<and> (\<forall>x y::'A. P x \<and> P y \<longrightarrow> x = y))"
by (auto intro!: ext)

setup {* OpenTheory.read_article "bool-int-1.0.art" [] *}

setup {*
  fold OpenTheory.add_const
  [("Data.Bool.select", @{const_name "Eps"}),
   ("Data.Bool.cond", @{const_name "If"})]
*}

lemma [where 'A='A and 'B='B, opentheory]:
  "\<forall>t\<Colon>'A \<Rightarrow> 'B. (\<lambda>x\<Colon>'A. t x) = t"
by auto

lemma [where 'A='A, opentheory]: "\<forall>(P\<Colon>'A \<Rightarrow> bool) x\<Colon>'A. P x \<longrightarrow> P (Eps P)"
by (auto intro: someI)

lemma [where 'A='A and 'B='B, opentheory]:
  "\<forall>(f\<Colon>'A \<Rightarrow> 'B) g\<Colon>'A \<Rightarrow> 'B. (\<forall>x\<Colon>'A. f x = g x) \<longrightarrow> f = g"
by (auto intro: ext)

lemma [where 'A='A, opentheory]:
  "If = (\<lambda>t t1 t2. SOME x\<Colon>'A. (t = True \<longrightarrow> x = t1) \<and> (t = False \<longrightarrow> x = t2))"
by (auto intro!: ext)

lemma [where 'A='A and 'B='B, opentheory]:
  "\<forall>(f::'A \<Rightarrow> 'B) g. (f = g) = (\<forall>x. f x = g x)"
by (auto intro: ext)

setup {* OpenTheory.read_article "bool-choice-1.0.art" [] *}


subsection {* Load natural number theories *}

setup {*
  OpenTheory.add_tyop ("Number.Natural.natural", @{type_name "nat"})
*}

text {* FIXME: 'odd' is an abbreviation in Isabelle, so we can't use
it directly. We define a copy of it to use instead. *}
definition [simp]: "odd' = odd"

setup {*
  fold OpenTheory.add_const
  [("Number.Numeral.zero", @{const_name "Groups.zero"}),
   ("Number.Natural.suc", @{const_name "Suc"}),
   ("Number.Natural.+", @{const_name "plus"}),
   ("Number.Natural.*", @{const_name "times"}),
   ("Number.Natural.exp", @{const_name "power"}),
   ("Number.Natural.even", @{const_name "even"}),
   ("Number.Natural.odd", @{const_name "odd'"}),
   ("Number.Natural.<=", @{const_name "less_eq"}),
   ("Number.Natural.<", @{const_name "less"})]
*}

text {* Properties of constructors, induction and recursion: *}

lemma [opentheory]:
  "\<forall>n. Suc n \<noteq> 0"
  "\<forall>(m\<Colon>nat) n\<Colon>nat. (Suc m = Suc n) = (m = n)"
by simp_all

lemma [opentheory]:
  "\<forall>P\<Colon>nat \<Rightarrow> bool. P (0\<Colon>nat) \<and> (\<forall>n\<Colon>nat. P n \<longrightarrow> P (Suc n)) \<longrightarrow> (\<forall>n\<Colon>nat. P n)"
by (clarify, erule nat_induct, simp)

lemma [where 'A='A, opentheory]: "\<forall>(e\<Colon>'A) f\<Colon>'A \<Rightarrow> nat \<Rightarrow> 'A.
   \<exists>fn\<Colon>nat \<Rightarrow> 'A. fn (0\<Colon>nat) = e \<and> (\<forall>n\<Colon>nat. fn (Suc n) = f (fn n) n)"
by (intro allI, rule_tac x="nat_rec e (\<lambda>n a. f a n)" in exI, simp)

text {* Binary numerals for natural numbers: *}

setup {* OpenTheory.read_article "natural-numeral-1.0.art" [] *}

lemma bit_simps:
  "bit0 0 = 0 \<and> (\<forall>n. bit0 (Suc n) = Suc (Suc (bit0 n)))"
  "\<forall>n. bit1 n = Suc (bit0 n)"
by (rule opentheory)+

text {* Primitive recursion equations for constants: *}

lemma [opentheory]:
  "(\<forall>n. (0\<Colon>nat) + n = n) \<and> (\<forall>m n. Suc m + n = Suc (m + n))"
  "(\<forall>n. (0\<Colon>nat) * n = 0) \<and> (\<forall>m n. Suc m * n = m * n + n)"
  "(\<forall>m\<Colon>nat. m ^ 0 = bit1 0) \<and> (\<forall>(m\<Colon>nat) n. m ^ Suc n = m * m ^ n)"
  "even (0\<Colon>nat) = True \<and> (\<forall>n. even (Suc n) = (\<not> even n))"
  "odd' (0\<Colon>nat) = False \<and> (\<forall>n. odd' (Suc n) = (\<not> odd' n))"
by (simp_all add: bit_simps)

lemma [opentheory]:
  "(\<forall>m. (m < (0\<Colon>nat)) = False) \<and> (\<forall>m n. (m < Suc n) = (m = n \<or> m < n))"
by (simp add: less_Suc_eq disj_commute)

lemma [opentheory]:
  "(\<forall>m. (m \<le> (0\<Colon>nat)) = (m = (0\<Colon>nat))) \<and>
  (\<forall>m n. (m \<le> Suc n) = (m = Suc n \<or> m \<le> n))"
by (simp add: le_Suc_eq disj_commute)

setup {* OpenTheory.read_article "natural-add-thm-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-add-numeral-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-mult-thm-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-exp-thm-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-order-thm-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-add-order-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-mult-order-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-set-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-even-odd-thm-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-recursion-1.0.art" [] *}
setup {* OpenTheory.read_article "natural-cases-1.0.art" [] *}

subsection {* Configure other datatypes *}

setup {*
  fold OpenTheory.add_tyop
  [("Data.Pair.*", @{type_name "prod"}),
   ("Data.Option.option", @{type_name "option"}),
   ("Data.List.list", @{type_name "list"})]
*}

setup {*
  fold OpenTheory.add_const
  [("Data.Pair.,", @{const_name "Pair"}),
   ("Data.Pair.fst", @{const_name "fst"}),
   ("Data.Pair.snd", @{const_name "snd"}),
   ("Data.Option.none", @{const_name "None"}),
   ("Data.Option.some", @{const_name "Some"}),
   ("Data.Option.case", @{const_name "option_case"}),
   ("Data.List.[]", @{const_name "Nil"}),
   ("Data.List.::", @{const_name "Cons"}),
   ("Data.List.@", @{const_name "append"}),
   ("Data.List.length", @{const_name "size"}),
   ("Data.List.concat", @{const_name "concat"}),
   ("Data.List.map", @{const_name "map"})]
*}

text {* Constructors, induction, and recursion for pairs: *}

lemma [where 'A='A and 'B='B, opentheory]:
  "\<forall>(x::'A) (y::'B). fst (x, y) = x"
  "\<forall>(x::'A) (y::'B). snd (x, y) = y"
  "\<forall>p. \<exists>(x::'A) (y::'B). p = (x, y)"
  "\<forall>(x\<Colon>'A) (y\<Colon>'B) (a\<Colon>'A) b\<Colon>'B. ((x, y) = (a, b)) = (x = a \<and> y = b)"
by simp_all

setup {* OpenTheory.read_article "pair-induct-1.0.art"
  [("?4547", "A"), ("?4546", "B")] *}
setup {* OpenTheory.read_article "pair-abs-1.0.art"
  [("?4704", "A"), ("?4703", "B"), ("?4729", "A"), ("?4728", "B"),
   ("?4751", "A"), ("?4750", "B"), ("?4743", "C")] *}

text {* Constructors, induction, and recursion for options: *}

lemma [where 'A='A, opentheory]:
  "\<forall>P\<Colon>'A option \<Rightarrow> bool. P None \<and> (\<forall>a\<Colon>'A. P (Some a)) \<longrightarrow> (\<forall>x\<Colon>'A option. P x)"
by (clarify, induct_tac x, simp_all)

lemma [where 'A='A and 'Z='Z, opentheory]:
  "\<forall>(NONE'\<Colon>'Z) SOME'\<Colon>'A \<Rightarrow> 'Z.
    \<exists>fn\<Colon>'A option \<Rightarrow> 'Z. fn None = NONE' \<and> (\<forall>a\<Colon>'A. fn (Some a) = SOME' a)"
by (clarify, rule_tac x="option_case NONE' SOME'" in exI, simp)

setup {* OpenTheory.read_article "option-thm-1.0.art" [] *}

lemma [where 'A='A and 'B='B, opentheory]:
  "(\<forall>(b\<Colon>'B) f\<Colon>'A \<Rightarrow> 'B. option_case b f None = b) \<and>
(\<forall>(b\<Colon>'B) (f\<Colon>'A \<Rightarrow> 'B) a\<Colon>'A. option_case b f (Some a) = f a)"
by simp

lemma [where 'A='A, opentheory]:
  "\<forall>x\<Colon>'A option. option_case None Some x = x"
by (clarify, case_tac x, simp_all)

text {* Constructors, induction, and recursion for lists: *}

lemma [where 'A='A, opentheory]: "\<forall>P\<Colon>'A list \<Rightarrow> bool.
   P [] \<and> (\<forall>(a0\<Colon>'A) a1\<Colon>'A list. P a1 \<longrightarrow> P (a0 # a1)) \<longrightarrow> (\<forall>x\<Colon>'A list. P x)"
by (clarify, erule list.induct, simp)

lemma [where 'A='A and 'Z='Z, opentheory]:
  "\<forall>(NIL'\<Colon>'Z) CONS'\<Colon>'A \<Rightarrow> 'A list \<Rightarrow> 'Z \<Rightarrow> 'Z.
   \<exists>fn\<Colon>'A list \<Rightarrow> 'Z.
      fn [] = NIL' \<and>
      (\<forall>(a0\<Colon>'A) a1\<Colon>'A list. fn (a0 # a1) = CONS' a0 a1 (fn a1))"
by (intro allI, rule_tac x="list_rec NIL' CONS'" in exI, simp)

text {* Primitive recursion equations for constants: *}

lemma [where 'A='A, opentheory]:
  "(\<forall>l\<Colon>'A list. [] @ l = l) \<and>
    (\<forall>(h\<Colon>'A) (t\<Colon>'A list) l\<Colon>'A list. (h # t) @ l = h # t @ l)"
  "size ([]::'A list) = (0\<Colon>nat) \<and>
    (\<forall>(h\<Colon>'A) t\<Colon>'A list. size (h # t) = Suc (size t))"
  "concat [] = ([]::'A list) \<and>
    (\<forall>(h\<Colon>'A list) t\<Colon>'A list list. concat (h # t) = h @ concat t)"
by simp_all

lemma [where 'A='A and 'B='B, opentheory]:
  "(\<forall>f\<Colon>'A \<Rightarrow> 'B. map f [] = []) \<and>
    (\<forall>(f\<Colon>'A \<Rightarrow> 'B) (h\<Colon>'A) t\<Colon>'A list. map f (h # t) = f h # map f t)"
by simp

setup {* OpenTheory.read_article "list-thm-1.0.art" [] *}

subsection {* Well-founded relations *}

setup {* OpenTheory.add_const ("Function.id", @{const_name "id"}) *}

lemma [where 'A='A, opentheory]: "\<forall>x::'A. id x = x"
by simp

ML {* PolyML.profiling 0 *}

setup {* OpenTheory.read_article "relation-1.0.art"
  [("?4704","A"),("?4703","B"),("<<","r1"),("<<<","r2"),("?12472","A")] *}

subsection {* Load parser theories *}

setup {*
OpenTheory.read_article "parser-1.5.art"
  [("HOLLight._dest_rec", "HOLLight.Rep_recspace"),
   ("HOLLight._mk_rec", "HOLLight.Abs_recspace"),
   ("HOLLight._dest_stream", "HOLLight.Rep_stream"),
   ("HOLLight._mk_stream", "HOLLight.Abs_stream"),
   ("HOLLight._64145", "HOLLight.\<alpha>64145"),
   ("HOLLight._64146", "HOLLight.\<alpha>64146"),
   ("HOLLight._64147", "HOLLight.\<alpha>64147"),
   ("?86560", "A"), ("?86728", "A")]
*}

thm opentheory

end
