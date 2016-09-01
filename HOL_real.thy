
theory HOL_real
imports HOL_integer
begin


setup {*
  fold OpenTheory.add_const
  [("Number.Natural.-", @{const_name "Groups.minus_class.minus"})]
*}

lemma[opentheory] :
"\<forall>(m::nat) (n::nat) p::nat. p \<le> n \<longrightarrow> m * (n - p) = m * n - m * p"
by(clarify, subst diff_mult_distrib2, rule refl)

lemma[opentheory] :
"\<forall>(p::nat \<Rightarrow> nat \<Rightarrow> nat) (a::nat) b::nat.
   p (0::nat) (0::nat) = (0::nat) \<and> (\<forall>(m::nat) n::nat. p m n \<le> a * (m + n) + b) \<longrightarrow>
   (\<exists>c::nat. \<forall>(m::nat) n::nat. p m n \<le> c * (m + n))"
apply clarsimp
apply(rule_tac x="a + b" in exI)
apply clarsimp
apply(drule_tac x=m in spec)
apply(drule_tac x=n in spec)
apply(case_tac "n = 0", clarsimp)
apply(case_tac "m = 0", clarsimp)
apply(erule le_trans)
apply(subst add_mult_distrib)
apply force
apply(erule le_trans)
apply(subst add_mult_distrib)
apply force
done

lemma[opentheory] :
"\<forall>p::nat \<Rightarrow> nat.
 (\<exists>b::nat. \<forall>n::nat. p n \<le> b) = (\<exists>(a::nat) b::nat. \<forall>n::nat. n * p n \<le> a * n + b)"
apply clarify
apply(rule iffI)
apply clarsimp
apply(rule_tac x=b in exI)
apply(rule_tac x=0 in exI)
apply clarsimp
apply clarify
apply(rule_tac x="a + b + p 0" in exI)
apply clarify
apply(drule_tac x=n in spec)
apply(case_tac n, simp)
apply clarify
apply(rename_tac m)
apply(subgoal_tac "a * Suc m + b \<le> Suc m * a + Suc m * b")
apply(drule le_trans, assumption)
apply(subst (asm) add_mult_distrib2[THEN sym])+
apply(subst (asm) Suc_mult_le_cancel1)
by simp_all


lemma[opentheory]: 
"\<forall>(a::nat) b::nat. (\<forall>n::nat. a * n \<le> b) = (a = (0::nat))"
apply(clarify, rule iffI)
apply(rule ccontr)
apply(drule_tac x="Suc b" in spec)
by(case_tac a, simp_all)


lemma[opentheory] :
"\<forall>(a::nat) (b::nat) c::nat. (\<forall>n::nat. a * n \<le> b * n + c) = (a \<le> b)"
apply clarify
apply(rule iffI)
apply(rule ccontr)
apply(drule not_le_imp_less)
apply(case_tac "c = 0", fastforce)
apply(subgoal_tac "\<exists>d > 0. a = b + d")
apply clarify
apply(drule_tac x="c + 1" in spec)
apply(subst (asm) add_mult_distrib)
apply(subst (asm) nat_add_left_cancel_le)
apply(case_tac c, clarify)
apply(case_tac d, clarify)
apply clarsimp
apply(rule_tac x="a - b" in exI)
apply force
apply clarsimp
apply(drule_tac k=n and l=n in mult_le_mono, rule le_refl)
apply(erule le_trans)
by simp


lemma[opentheory] :
"\<forall>(p::nat \<Rightarrow> nat) q::nat \<Rightarrow> nat.
 (\<exists>b::nat. \<forall>i::nat. p i \<le> q i + b) = (\<exists>(b::nat) n::nat. \<forall>i\<ge>n. p i \<le> q i + b)"
apply clarify
apply(rule iffI)
apply fastforce
apply clarify
apply(rule mp)
prefer 2
apply assumption
apply(rule_tac x=b in spec)
apply(induct_tac n)
apply clarsimp
apply clarify
apply(rename_tac m b)
apply(drule_tac x="p m + b" in spec, erule mp)
apply clarify
apply(case_tac "i = m", simp)
apply(drule_tac x=i in spec, drule mp, subst less_eq_Suc_le[THEN sym])
apply fastforce
apply(erule le_trans)
by simp


lemma[opentheory] :
"\<forall>(m::nat) n::nat. (m \<le> Suc n) = (m = Suc n \<or> m \<le> n)"
by fastforce

lemma[opentheory] :
"\<forall>s::'A set. (\<exists>x::'A. x \<in> s) = (s \<noteq> {})"
by fastforce

lemma[opentheory] :
"\<forall>(A::bool) (B::bool) C::bool. (A \<or> B \<and> C) = ((A \<or> B) \<and> (A \<or> C))"
by fastforce


setup {* OpenTheory.read_article "natural-distance-1.52.art" [] *}



setup {*
  fold OpenTheory.add_const
  [("Number.Natural.distance", @{const_name "Number.Natural.distance"}),
    ("Set.{}", @{const_name "Orderings.bot_class.bot"})]
*}

setup {* OpenTheory.read_article "real-1.61.art" [] *}

setup {*
  fold OpenTheory.add_tyop
  [("Number.Real.real", @{type_name "Number.Real.real"}),
   ("HOL4.integer.int", @{type_name "HOL4.integer.int"})]
*}



setup {* OpenTheory.read_article "hol-real-1.1.art" [] *}


end