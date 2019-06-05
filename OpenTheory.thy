(* Version: Isabelle2016 *)

theory OpenTheory
imports Main

begin

subsection \<open>OpenTheory package\<close>

text \<open>Lemmas used by the package\<close>

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

text \<open>Load opentheory package\<close>


ML_file "opentheory.ML"

setup OpenTheory.setup


subsection \<open>Load boolean theories\<close>

setup \<open>
  fold OpenTheory.add_tyop
  [("->", @{type_name "fun"}),
   ("bool", @{type_name "bool"})]
\<close>

setup \<open>
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
\<close>

lemma [opentheory]: "True = ((\<lambda>p::bool. p) = (\<lambda>p. p))"
  by auto

lemma [opentheory]: "All = (\<lambda>P. P = (\<lambda>x::'A. True))"
  unfolding fun_eq_iff by auto

lemma [opentheory]: "(\<longrightarrow>) = (\<lambda>p q. (p \<and> q) = p)"
  unfolding fun_eq_iff by auto

lemma [opentheory]: "(\<and>) = (\<lambda>p q. (\<lambda>f. f p q :: bool) = (\<lambda>f. f True True))"
apply (simp add: fun_eq_iff, safe, simp_all)
apply (drule_tac x="\<lambda>x y. x" in spec, simp)
apply (drule_tac x="\<lambda>x y. y" in spec, simp)
done

lemma [opentheory]: "(\<or>) = (\<lambda>p q. \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r)"
  unfolding fun_eq_iff by auto

lemma [opentheory]: "Ex = (\<lambda>P. \<forall>q. (\<forall>x::'A. P x \<longrightarrow> q) \<longrightarrow> q)"
  unfolding fun_eq_iff by auto

lemma [opentheory]: "False = (\<forall>p. p)"
  by auto

lemma [opentheory]: "Not = (\<lambda>p. p \<longrightarrow> False)"
  by auto

lemma [opentheory]:
  "Ex1 = (\<lambda>P. Ex P \<and> (\<forall>x y::'A. P x \<and> P y \<longrightarrow> x = y))"
  unfolding fun_eq_iff by auto

setup \<open>OpenTheory.read_article "bool-int-1.0.art" []\<close>

setup \<open>
  fold OpenTheory.add_const
  [("Data.Bool.select", @{const_name "Eps"}),
   ("Data.Bool.cond", @{const_name "If"})]
\<close>

lemma [opentheory]:
  "\<forall>(t::'A \<Rightarrow> 'B). (\<lambda>(x::'A). t x) = t"
by auto

lemma [opentheory]: "\<forall>(P :: 'A \<Rightarrow> bool) (x :: 'A). P x \<longrightarrow> P (Eps P)"
by (auto intro: someI)

lemma [opentheory]:
  "\<forall>(f :: 'A \<Rightarrow> 'B)(g :: 'A \<Rightarrow> 'B). (\<forall>x :: 'A. f x = g x) \<longrightarrow> f = g"
  unfolding fun_eq_iff by auto

lemma [opentheory]:
  "If = (\<lambda>t t1 t2. SOME(x::'A). (t = True \<longrightarrow> x = t1) \<and> (t = False \<longrightarrow> x = t2))"
  unfolding fun_eq_iff by auto

lemma [opentheory]:
  "\<forall>(f::'A \<Rightarrow> 'B) g. (f = g) = (\<forall>x. f x = g x)"
  unfolding fun_eq_iff by auto

setup \<open>OpenTheory.read_article "bool-choice-1.0.art" []\<close>


subsection \<open>Load natural number theories\<close>

setup \<open>
  OpenTheory.add_tyop ("Number.Natural.natural", @{type_name "nat"})
\<close>

setup \<open>
  fold OpenTheory.add_const
  [("Number.Numeral.zero", @{const_name "Groups.zero"}),
   ("Number.Natural.suc", @{const_name "Suc"}),
   ("Number.Natural.+", @{const_name "plus"}),
   ("Number.Natural.*", @{const_name "times"}),
   ("Number.Natural.-", @{const_name "minus"}),
   ("Number.Natural.exp", @{const_name "power"}),
   ("Number.Natural.<=", @{const_name "less_eq"}),
   ("Number.Natural.<", @{const_name "less"})]
\<close>

ML \<open>Binding.qualified_name @{const_name power}\<close>

text \<open>Properties of constructors, induction and recursion:\<close>

lemma [opentheory]:
  "\<forall>n. Suc n \<noteq> 0"
  "\<forall>(m::nat) n::nat. (Suc m = Suc n) = (m = n)"
by simp_all

lemma [opentheory]:
  "\<forall>P::nat \<Rightarrow> bool. P (0::nat) \<and> (\<forall>n::nat. P n \<longrightarrow> P (Suc n)) \<longrightarrow> (\<forall>n::nat. P n)"
by (clarify, erule nat_induct, simp)

lemma [opentheory]: "\<forall>(e::'A) f::'A \<Rightarrow> nat \<Rightarrow> 'A.
   \<exists>(fn::nat \<Rightarrow> 'A). fn (0::nat) = e \<and> (\<forall>n::nat. fn (Suc n) = f (fn n) n)"
by (intro allI, rule_tac x="rec_nat e (\<lambda>n a. f a n)" in exI, simp)

text \<open>Binary numerals for natural numbers:\<close>

setup \<open>OpenTheory.read_article "natural-numeral-1.0.art" []\<close>

lemma bit_simps[simp]:
  "bit0 0 = 0 \<and> (\<forall>n. bit0 (Suc n) = Suc (Suc (bit0 n)))"
  "\<forall>n. bit1 n = Suc (bit0 n)"
by (rule opentheory)+

text \<open>Primitive recursion equations for constants:\<close>

lemma [opentheory]:
  "(\<forall>n. (0::nat) + n = n) \<and> (\<forall>m n. Suc m + n = Suc (m + n))"
  "(\<forall>n. (0::nat) * n = 0) \<and> (\<forall>m n. Suc m * n = m * n + n)"
  "(\<forall>m::nat. m ^ 0 = bit1 0) \<and> (\<forall>(m::nat) n. m ^ Suc n = m * m ^ n)"
(*
  "even (0::nat) = True \<and> (\<forall>n. even (Suc n) = (\<not> even n))"
  "odd (0::nat) = False \<and> (\<forall>n. odd (Suc n) = (\<not> odd n))"
*)
by (simp_all add: bit_simps)

lemma [opentheory]:
  "(\<forall>m. (m < (0::nat)) = False) \<and> (\<forall>m n. (m < Suc n) = (m = n \<or> m < n))"
by (simp add: less_Suc_eq disj_commute)

lemma [opentheory]:
  "(\<forall>m. (m \<le> (0::nat)) = (m = (0::nat))) \<and>
  (\<forall>m n. (m \<le> Suc n) = (m = Suc n \<or> m \<le> n))"
by (simp add: le_Suc_eq disj_commute)

setup \<open>OpenTheory.read_article "natural-add-thm-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-add-numeral-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-mult-thm-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-exp-thm-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-order-thm-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-add-order-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-mult-order-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-set-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-even-odd-def-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-even-odd-thm-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-recursion-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "natural-cases-1.0.art" []\<close>



subsection \<open>Configure other datatypes\<close>

setup \<open>
  fold OpenTheory.add_tyop
  [("Data.Pair.*", @{type_name "prod"}),
   ("Data.Option.option", @{type_name "option"}),
   ("Data.List.list", @{type_name "list"})]
\<close>

setup \<open>
  fold OpenTheory.add_const
  [("Data.Pair.,", @{const_name "Pair"}),
   ("Data.Pair.fst", @{const_name "fst"}),
   ("Data.Pair.snd", @{const_name "snd"}),
   ("Data.Option.none", @{const_name "None"}),
   ("Data.Option.some", @{const_name "Some"}),
   ("Data.Option.case", @{const_name "case_option"}),
   ("Data.List.[]", @{const_name "Nil"}),
   ("Data.List.::", @{const_name "Cons"}),
   ("Data.List.@", @{const_name "append"}),
   ("Data.List.length", @{const_name "size"}),
   ("Data.List.concat", @{const_name "concat"}),
   ("Data.List.map", @{const_name "map"})]
\<close>

text \<open>Constructors, induction, and recursion for pairs:\<close>

lemma [opentheory]:
  "\<forall>(x::'A) (y::'B). fst (x, y) = x"
  "\<forall>(x::'A) (y::'B). snd (x, y) = y"
  "\<forall>p. \<exists>(x::'A) (y::'B). p = (x, y)"
  "\<forall>(x::'A) (y::'B) (a::'A) b::'B. ((x, y) = (a, b)) = (x = a \<and> y = b)"
by simp_all

setup \<open>OpenTheory.read_article "pair-induct-1.0.art" []\<close>
setup \<open>OpenTheory.read_article "pair-abs-1.0.art" []\<close>

text \<open>Constructors, induction, and recursion for options:\<close>

lemma [opentheory]:
  "\<forall>P::'A option \<Rightarrow> bool. P None \<and> (\<forall>a::'A. P (Some a)) \<longrightarrow> (\<forall>x::'A option. P x)"
by (clarify, induct_tac x, simp_all)

lemma [opentheory]:
  "\<forall>(NONE'::'Z) SOME'::'A \<Rightarrow> 'Z.
    \<exists>fn::'A option \<Rightarrow> 'Z. fn None = NONE' \<and> (\<forall>a::'A. fn (Some a) = SOME' a)"
by (clarify, rule_tac x="\<lambda>x. case x of None \<Rightarrow> NONE' | Some y \<Rightarrow> SOME' y" in exI, simp)

setup \<open>OpenTheory.read_article "option-thm-1.0.art" []\<close>

lemma [opentheory]:
  "(\<forall>(b::'B) f::'A \<Rightarrow> 'B. case_option b f None = b) \<and>
(\<forall>(b::'B) (f::'A \<Rightarrow> 'B) a::'A. case_option b f (Some a) = f a)"
by simp

lemma [opentheory]:
  "\<forall>x::'A option. case_option None Some x = x"
by (clarify, case_tac x, simp_all)

text \<open>Constructors, induction, and recursion for lists:\<close>

lemma [opentheory]: "\<forall>P::'A list \<Rightarrow> bool.
   P [] \<and> (\<forall>(a0::'A) a1::'A list. P a1 \<longrightarrow> P (a0 # a1)) \<longrightarrow> (\<forall>x::'A list. P x)"
by (clarify, erule list.induct, simp)

lemma [opentheory]:
  "\<forall>(NIL'::'Z) CONS'::'A \<Rightarrow> 'A list \<Rightarrow> 'Z \<Rightarrow> 'Z.
   \<exists>fn::'A list \<Rightarrow> 'Z.
      fn [] = NIL' \<and>
      (\<forall>(a0::'A) a1::'A list. fn (a0 # a1) = CONS' a0 a1 (fn a1))"
by (intro allI, rule_tac x="rec_list NIL' CONS'" in exI, simp)

text \<open>Primitive recursion equations for constants:\<close>

lemma [opentheory]:
  "(\<forall>l::'A list. [] @ l = l) \<and>
    (\<forall>(h::'A) (t::'A list) l::'A list. (h # t) @ l = h # t @ l)"
  "size ([]::'A list) = (0::nat) \<and>
    (\<forall>(h::'A) t::'A list. size (h # t) = Suc (size t))"
  "concat [] = ([]::'A list) \<and>
    (\<forall>(h::'A list) t::'A list list. concat (h # t) = h @ concat t)"
  by simp_all

lemma [opentheory]:
  "(\<forall>f::'A \<Rightarrow> 'B. map f [] = []) \<and>
    (\<forall>(f::'A \<Rightarrow> 'B) (h::'A) t::'A list. map f (h # t) = f h # map f t)"
  by simp

setup \<open>OpenTheory.read_article "list-thm-1.0.art" []\<close>

subsection \<open>Well-founded relations\<close>

setup \<open>OpenTheory.add_const ("Function.id", @{const_name "id"})\<close>

lemma [opentheory]: "\<forall>x::'A. id x = x"
  by simp

setup \<open>OpenTheory.read_article "relation-1.0.art" []\<close>

end