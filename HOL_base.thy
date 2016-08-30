theory HOL_base
imports OpenTheory
begin


lemma[opentheory] :
"\<forall>(e::'B) f::'A \<Rightarrow> 'B. \<exists>fn::'A option \<Rightarrow> 'B. fn None = e \<and> (\<forall>x::'A. fn (Some x) = f x)"
apply clarify
apply(rule_tac x="\<lambda>x. case x of
                       None \<Rightarrow> e
                     | Some z \<Rightarrow> f z" in exI)
by simp


lemma[opentheory] :
"\<forall>(f::'A \<Rightarrow> unit) g::'A \<Rightarrow> unit. f = g"
by(clarsimp, rule ext, simp)


lemma[opentheory] :
"\<forall>(P::bool) (Q::bool) R::bool. (P \<longrightarrow> Q \<and> R) = ((P \<longrightarrow> Q) \<and> (P \<longrightarrow> R))"
by fastforce

lemma[opentheory] :
"op \<circ> = (\<lambda>(f::'B \<Rightarrow> 'C) (g::'A \<Rightarrow> 'B) x::'A. f (g x))"
by((rule ext)+, simp)

lemma[opentheory] :
"\<forall>x::'A + 'B. (\<exists>a::'A. x = Inl a) \<or> (\<exists>b::'B. x = Inr b)"
by(clarsimp, case_tac x, fastforce+)

fun destLeft :: "'A + 'B \<Rightarrow> 'A"
where "destLeft (Inl a) = a"

fun destRight :: "'A + 'B \<Rightarrow> 'B"
where "destRight (Inr a) = a"

fun isLeft :: "'A + 'B \<Rightarrow> bool"
where "isLeft (Inl a) = True"
    | "isLeft _ = False"

fun isRight :: "'A + 'B \<Rightarrow> bool"
where "isRight (Inr a) = True"
    | "isRight _ = False"

fun isSome :: "'A option \<Rightarrow> bool"
where "isSome (Some a) = True"
    | "isSome _ = False"

fun isNone :: "'A option \<Rightarrow> bool"
where "isNone None = True"
    | "isNone _ = False"

fun left_right :: "('A \<Rightarrow> 'C) \<Rightarrow> ('B \<Rightarrow> 'C) \<Rightarrow> 'A + 'B \<Rightarrow> 'C"
where "left_right l r (Inl x) = l x" |
      "left_right l r (Inr x) = r x" 


definition "injective f = inj_on f UNIV"
declare injective_def[simp add]

definition "surjective f = surj f"
declare surjective_def[simp add]


lemma[opentheory] :
"\<forall>f::'A \<Rightarrow> 'B. surjective f = (\<forall>y::'B. \<exists>x::'A. y = f x)"
by force

lemma[opentheory] : 
"\<forall>f::'A \<Rightarrow> 'B. injective f = (\<forall>(x1::'A) x2::'A. f x1 = f x2 \<longrightarrow> x1 = x2)"
apply clarsimp
apply(rule iffI)
apply(clarify, erule injD, assumption)
by(rule injI, simp)

lemma[opentheory] :
"\<exists>f::ind \<Rightarrow> ind. injective f \<and> \<not> surjective f"
apply simp
apply(rule_tac x=Suc_Rep in exI)
apply(rule conjI)
apply(rule injI)
apply(erule Suc_Rep_inject)
apply clarsimp
apply(drule_tac y="Zero_Rep" in surjD)
apply clarify
apply(drule sym)
apply(drule not_not[THEN iffD2])
apply(erule notE) 
apply(rule Suc_Rep_not_Zero_Rep)
done


definition emptyR :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
where "emptyR = (\<lambda>a b. False)"
 
declare emptyR_def[simp add]

definition univR :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
where "univR = (\<lambda>a b. True)"
 
declare univR_def[simp add]


definition subrelation :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
where "subrelation S T = (\<forall>a b. S a b \<longrightarrow> T a b)" 

lemma subrelation[simp] : "\<forall>r s. subrelation r s = (\<forall>x y. r x y \<longrightarrow> s x y)" 
by(simp add: subrelation_def)


definition reflexive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where "reflexive T = (\<forall>a. T a a)"

lemma reflexive[simp] : "\<forall>r. reflexive r = (\<forall>x. r x x)" 
by(simp add: reflexive_def)


definition irreflexive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where "irreflexive T = (\<forall>a. \<not> T a a)"

lemma irreflexive[simp] : "\<forall>r. irreflexive r = (\<forall>x. \<not> r x x)" 
by(simp add: irreflexive_def)


definition transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where "transitive T = (\<forall>a b c. T a b \<longrightarrow> T b c \<longrightarrow> T a c)"

lemma transitive[where 'a="'A", opentheory] : 
"\<forall>T. transitive T = (\<forall>a b c. T a b \<and> T b c \<longrightarrow> T a c)" 
by(simp add: transitive_def, blast)


definition const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
where "const a b = a"

lemma const[simp] : "const = (\<lambda>a b. a)" by(rule ext, rule ext, simp add: const_def)

definition "combinatorS f g = (\<lambda>x. f x (g x))"

lemma combinatorS[simp] : "combinatorS = (\<lambda>f g x. f x (g x))" 
by(rule ext, rule ext, simp add: combinatorS_def)

lemma combinator_S_const[opentheory] : "\<forall>(x :: 'A \<Rightarrow> 'B). combinatorS const x = id" 
by(simp add: const_def combinatorS_def id_def)

definition "combinatorW f = (\<lambda>x. f x x)"

lemma combinatorW[simp] : "combinatorW = (\<lambda>f x. f x x)" 
by(rule ext, simp add: combinatorW_def)


definition "bigIntersectR s = (\<lambda>u v. \<forall>r \<in> s. r u v)"

lemma bigIntersectR[opentheory] :
"\<forall>(s::('A \<Rightarrow> 'B \<Rightarrow> bool) set) (x::'A) y::'B.
  bigIntersectR s x y = (\<forall>r::'A \<Rightarrow> 'B \<Rightarrow> bool. r \<in> s \<longrightarrow> r x y)"
by(clarsimp simp: bigIntersectR_def, fastforce)

definition "unionR s t = (\<lambda>a b. s a b \<or> t a b)"

declare unionR_def[simp add]

definition "interR s t = (\<lambda>a b. s a b \<and> t a b)"

declare interR_def[simp add]
 
definition "unionS s t = (s \<union> t)"

declare unionS_def[simp add]
 
definition "interS s t = (s \<inter> t)"

declare interS_def[simp add]

definition "fromPredicate p = Collect p"

declare fromPredicate_def[simp add]

definition "fromSet s = (\<lambda>a b. (a, b) \<in> s)"

declare fromSet_def[simp add]

definition "toSet t = {(a, b). t a b}"

declare toSet_def[simp add]


lemma[opentheory] : 
"\<forall>p q r. (p \<and> q \<or> r) = ((p \<or> r) \<and> (q \<or> r))"
by force

lemma[opentheory] :
"\<forall>(f::'A \<Rightarrow> 'B) g::'A \<Rightarrow> 'B. (\<forall>x::'A. f x = g x) = (f = g)"
by force

lemma[opentheory] :
"\<forall>r::'A \<Rightarrow> 'A \<Rightarrow> bool.
 r\<^sup>+\<^sup>+ = bigIntersectR {s |s::'A \<Rightarrow> 'A \<Rightarrow> bool. subrelation r s \<and> transitive s}"
apply(clarsimp simp: bigIntersectR_def transitive_def)
apply(rule ext, rule ext)
apply(rule iffI)
apply(erule tranclp_induct)
apply fastforce
apply clarsimp
apply(rename_tac r')
apply(drule_tac x="r'" in spec)
apply(drule mp, fastforce)
apply force
apply(drule spec, erule mp)
by force



definition grN :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
where "grN n m = (n > m)"

declare grN_def[simp add]

definition gr_eqN :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
where "gr_eqN n m = (n \<ge> m)"

declare gr_eqN_def[simp add]



lemma[opentheory] :
"\<forall>(m::nat) n::nat. max m n = (if m \<le> n then n else m)"
by(simp add: max_def)


lemma[opentheory] :
"\<forall>(m::nat) n::nat. min m n = (if m \<le> n then m else n)"
by(simp add: min_def)


lemma[opentheory] :
"\<forall>p. p (0::nat) \<and> (\<forall>x. p x \<longrightarrow> p (Suc x)) \<longrightarrow> (\<forall>x. p x)"
by(clarsimp, induct_tac x, simp_all)

lemma[opentheory] :
"\<forall>m. \<not> m < (0::nat)"
by simp 

lemma[opentheory] :
"\<forall>n. Suc n \<noteq> (0::nat)"
by simp 

lemma[opentheory] :
"\<forall>m. m = (0::nat) \<or> (\<exists>n. m = Suc n)"
by(rule allI, case_tac m, simp_all)

lemma[opentheory] :
"\<not> Natural.odd (0::nat)"
apply(simp add: Natural.odd_def)
apply(rule_tac a=Parity.odd in someI2)
by simp_all

lemma[opentheory] :
"my_even (0::nat)"
apply(simp add: my_even_def) 
apply(rule_tac a=Parity.even in someI2)
by simp_all

lemma[opentheory] :
"\<forall>n::nat. Natural.odd (Suc n) = (\<not> Natural.odd n)"
apply(clarsimp simp: Natural.odd_def)
apply(rule_tac a=Parity.odd in someI2)
by simp_all

lemma[opentheory] :
"\<forall>n::nat. my_even (Suc n) = (\<not> my_even n)"
apply(clarsimp simp: my_even_def)
apply(rule_tac a=Parity.even in someI2)
by simp_all

fun factorial :: "nat \<Rightarrow> nat"
where "factorial 0 = 1" |
      "factorial (Suc n) = Suc n * factorial n"



definition "flip f = (\<lambda>a b. f b a)"

declare flip_def[simp add]

fun null
where "null [] = True" |
      "null _ = False" 

lemma[opentheory] :
"\<forall>l::'A list. null l = (l = [])"
by(rule allI, case_tac l, simp_all)

lemma[opentheory] :
"\<forall>(h::'A) t::'A list. last (h # t) = (if null t then h else last t)"
by(clarify, case_tac t, simp_all)


lemma[opentheory] :
"flip = (\<lambda>(f::'A \<Rightarrow> 'B \<Rightarrow> 'C) (x::'B) y::'A. f y x)"
by(rule ext, simp)

fun forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where "forall P [] = True" |
      "forall P (x#xs) = (P x \<and> forall P xs)"
  
fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where "exists P [] = False" |
      "exists P (x#xs) = (P x \<or> exists P xs)"


fun unzip 
where "unzip [] = ([], [])"
    | "unzip ((a, b)#xs) = (let (l, r) = unzip xs in
                             (a#l, b#r))"

lemma[opentheory] :
"\<forall>(h::'A \<times> 'B) (x::'A) (y::'B) (t::('A \<times> 'B) list) (xs::'A list) ys::'B list.
                        (unzip (h # t) = (x # xs, y # ys)) = (h = (x, y) \<and> unzip t = (xs, ys))"
apply clarify
apply(simp add: Let_def split_def)
by fastforce


fun foldr' :: "'B \<Rightarrow> ('A \<Rightarrow> 'A list \<Rightarrow> 'B \<Rightarrow> 'B) \<Rightarrow> 'A list \<Rightarrow> 'B"
where "foldr' b f [] = b" |
      "foldr' b f (x#xs) = f x xs (foldr' b f xs)"
    

lemma[opentheory] :
"\<forall>(b::'B) f::'A \<Rightarrow> 'A list \<Rightarrow> 'B \<Rightarrow> 'B.
 \<exists>fn::'A list \<Rightarrow> 'B. fn [] = b \<and> (\<forall>(h::'A) t::'A list. fn (h # t) = f h t (fn t))"
apply clarsimp
apply(rule_tac x="foldr' b f" in exI)
apply clarsimp
done




setup {*
  fold OpenTheory.add_const
  [("select", @{const_name "Eps"}),
   ("Data.Unit.()", @{const_name "Product_Type.Unity"}),
   ("Function.o", @{const_name "Fun.comp"}),
   ("Function.const", @{const_name "const"}),
   ("Function.Combinator.s", @{const_name "combinatorS"}),
   ("Function.Combinator.w", @{const_name "combinatorW"}),
   ("Function.flip", @{const_name "flip"}),
   ("Function.injective", @{const_name "injective"}),
   ("Function.surjective", @{const_name "surjective"}),
   ("Relation.reflexive", @{const_name "reflexive"}),
   ("Relation.transitive", @{const_name "transitive"}),
   ("Relation.irreflexive", @{const_name "irreflexive"}),
   ("Relation.empty", @{const_name "emptyR"}),
   ("Relation.universe", @{const_name "univR"}),
   ("Relation.subrelation", @{const_name "subrelation"}),
   ("Relation.transitiveClosure", @{const_name "tranclp"}),
   ("Relation.union", @{const_name "unionR"}),
   ("Relation.intersect", @{const_name "interR"}),
   ("Relation.bigIntersect", @{const_name "bigIntersectR"}),
   ("Relation.fromSet", @{const_name "fromSet"}),
   ("Relation.toSet", @{const_name "toSet"}),
   ("Set.fromPredicate", @{const_name "Set.Collect"}),
   ("Set.member", @{const_name "Set.member"}),
   ("Set.union", @{const_name "sup"}),
   ("Set.intersect", @{const_name "inf"}),
   ("Data.Sum.left", @{const_name "Sum_Type.Inl"}),
   ("Data.Sum.right", @{const_name "Sum_Type.Inr"}),
   ("Data.Sum.case.left.right", @{const_name "left_right"}),
   ("Data.Sum.destLeft", @{const_name "destLeft"}),
   ("Data.Sum.destRight", @{const_name "destRight"}),
   ("Data.Sum.isLeft", @{const_name "isLeft"}),
   ("Data.Sum.isRight", @{const_name "isRight"}),
   ("Data.Option.isSome", @{const_name "isSome"}),
   ("Data.Option.isNone", @{const_name "isNone"}),
   ("Data.Option.map", @{const_name "map_option"}),
   ("Data.List.all", @{const_name "forall"}),
   ("Data.List.any", @{const_name "exists"}),
   ("Data.List.reverse", @{const_name "List.rev"}),
   ("Data.List.null", @{const_name "null"}),
   ("Data.List.last", @{const_name "List.last"}),
   ("Data.List.unzip", @{const_name "unzip"}),
   ("Data.List.head", @{const_name "List.hd"}),
   ("Data.List.tail", @{const_name "List.tl"}),
   ("Data.List.filter", @{const_name "List.filter"}),
   ("Number.Natural.zero", @{const_name "Groups.zero_class.zero"}),
   ("Number.Natural.bit0", @{const_name "OpenTheory.Number.Numeral.bit0"}),
   ("Number.Natural.bit1", @{const_name "OpenTheory.Number.Numeral.bit1"}),
   ("Number.Natural.^", @{const_name "power"}),
   ("Number.Natural.>", @{const_name "grN"}),
   ("Number.Natural.>=", @{const_name "gr_eqN"}),
   ("Number.Natural.mod", @{const_name "Divides.div_class.mod"}),
   ("Number.Natural.div", @{const_name "Rings.divide_class.divide"}),
   ("Number.Natural.max", @{const_name "max"}),
   ("Number.Natural.min", @{const_name "min"}),
   ("Number.Natural.factorial", @{const_name "factorial"})]
*}

setup {*
  fold OpenTheory.add_tyop
  [("ind", @{type_name "ind"}),
   ("Set.set", @{type_name "set"}),
   ("Data.Unit.unit", @{type_name "Product_Type.unit"}),
   ("Data.Sum.+", @{type_name "Sum_Type.sum"})]
*}


setup {* OpenTheory.read_article "hol-base.art" [] *}


setup {* OpenTheory.read_article "hol-monad.art" [] *}

end