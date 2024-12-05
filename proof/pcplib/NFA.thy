theory NFA
  imports Main
begin

lemma Min_existance_set:
  assumes "(S::nat set) \<noteq> {}"
  shows   "\<exists>m. m\<in>S \<and> (\<forall>s. s \<in> S \<longrightarrow> m \<le> s)"
proof -
  obtain m' where M':"m' \<in> S" using assms by blast
  show ?thesis using ex_has_least_nat[of "(\<lambda>s. s \<in> S)" m'] 
    using M' by presburger
qed


datatype ('a, 's) NA = NA
  (start_list: "'s list")
  (step: "'a \<Rightarrow> 's \<Rightarrow> 's list")
  (fin_list: "'s list")

abbreviation starts:: "('a, 's) NA \<Rightarrow>'s set" where
  "starts A == set (start_list A)"
abbreviation fins:: "('a, 's) NA \<Rightarrow>'s set" where
  "fins A == set (fin_list A)"

abbreviation set_step:: "('a, 's) NA \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's set" where
  "set_step A a s == set (step A a s)"

fun steps::"('a, 's) NA \<Rightarrow>'a list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "steps A [] S = S" | 
  "steps A (c#w) S = steps A w (Set.bind S (set_step A c))"

lemma bind_union_iff:
"Set.bind (S\<union>T) P = Set.bind T P \<union> Set.bind S P"
  by auto

lemma bind_insert_iff: 
"Set.bind (insert a S) P = P a \<union> Set.bind S P"
  by auto
fun steps_list::"('a, 's) NA \<Rightarrow>'a list \<Rightarrow> 's list \<Rightarrow> 's list" where
  "steps_list A [] S = S" | 
  "steps_list A (c#w) S = steps_list A w (List.bind S (step A c))"
lemma set_list_bind:"set (List.bind S (\<lambda>x. P x)) = Set.bind (set S) (\<lambda>x. set (P x))"
  by (simp add: bind_UNION set_list_bind)
lemma steps_list_equiv_setver[simp]:
  "set(steps_list A w S) = steps A w (set S)"
  apply(induct w arbitrary:S) apply simp
  unfolding steps_list.simps steps.simps 
proof -
  fix a and w and S
  have K:"(set (List.bind S (step A a))) = Set.bind (set S) (set_step A a)"
    using set_list_bind by fast
  assume A:"(\<And>S. set (steps_list A w S) = steps A w (set S)) "
  show "set (steps_list A w (List.bind S (step A a))) = steps A w (Set.bind (set S) (set_step A a))"
    unfolding A[of "List.bind S (step A a)"] using K by simp
qed

lemma single_steps_is_step:
  "steps A [a] s = Set.bind s (set_step A a)"
  by simp

lemma steps_snoc: 
  "steps A (w@[a]) s = Set.bind (steps A w s) (set_step A a)"
proof(induct "w@[a]" arbitrary: a w s)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  fix s
  show "steps A (w @ [a]) s = Set.bind (steps A w s) (set_step A a)"
  proof (cases xs)
    case Nil
    then show ?thesis using Cons.hyps(2) by auto
  next
    case XSCons:(Cons xsa xss)
    then have "length xs \<ge> 1" by simp
    then obtain w' where W':"xs = w' @ [a]" using Cons(2)
      by (metis XSCons last.simps list.discI snoc_eq_iff_butlast)
    have IH:"steps A (w' @ [a]) (Set.bind s (set_step A x)) = Set.bind (steps A w' (Set.bind s (set_step A x))) (set_step A a)"
      using Cons(1)[OF W', of "(Set.bind s (set_step A x))"] by simp
    have WA:"w @ [a] = x # w' @[a]" using W' Cons by simp
    have "steps A w' (Set.bind s (set_step A x)) = steps A w s" 
      using WA by auto
    then show ?thesis 
      unfolding WA using IH by simp
  qed
qed

lemma steps_assoc:
  "steps A (a@b) s = steps A b (steps A a s)"
proof(induct b arbitrary: s rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case 
    unfolding steps_snoc
    using steps_snoc[of A "a @ xs" x s] by auto
qed 


lemma Set_bind_monotone:
  assumes "S \<subseteq> T"
  shows   "Set.bind S P \<subseteq> Set.bind T P"
  unfolding Set.bind_def using assms by auto

lemma steps_monotone:
  assumes "S \<subseteq> T"
  shows "steps A w S \<subseteq> steps A w T"
using assms proof(induct w arbitrary: S T)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  fix a and w
  have A: "S \<subseteq> T" using Cons by blast
  assume ASM:"\<And>S T.  S \<subseteq> T \<Longrightarrow> steps A w S \<subseteq> steps A w T"
  show "steps A (a # w) S \<subseteq> steps A (a # w) T" 
    unfolding steps.simps
    using  ASM[OF Set_bind_monotone[OF A, of "set_step A a"]] by simp
qed

lemma steps_elem:
  "a \<in> steps A w1 s \<Longrightarrow> b \<in> steps A w2 {a} \<Longrightarrow> b \<in> steps A (w1@w2) s"
  unfolding steps_assoc
  using steps_monotone[of "{a}"]
  by auto

fun reachable_states::"('a, 's) NA \<Rightarrow> 's set" where
  "reachable_states A = Set.bind UNIV (\<lambda>w. steps A w (starts A))"

lemma reachable_sanity:
  "(x \<in> reachable_states A) = (\<exists>s. x \<in> steps A s (starts A))"
  by simp

lemma reachabele_states_closed_with_step:
  fixes A::"('a, 's) NA"
  shows "x \<in> (reachable_states A) \<Longrightarrow> set_step A c x \<subseteq> reachable_states A"
  unfolding reachable_states.simps
  using steps_snoc
  by fastforce


fun accept::"('a, 's) NA \<Rightarrow>'a list \<Rightarrow> bool" where
  "accept A w = (steps A w (starts A) \<inter> (fins A) \<noteq> {})"

fun accept_from::"('a, 's) NA \<Rightarrow> 'a list \<Rightarrow> 's set \<Rightarrow> bool" where
  "accept_from A w s = ((fins A) \<inter> steps A w s \<noteq> {})"

lemma accept_from_start_is_accept:
  shows "accept_from A w (starts A) \<Longrightarrow> accept A w"
  by auto

lemma steps_union_iff:"steps A w (S \<union> T) = (steps A w S \<union> steps A w T)"
  apply(induct w arbitrary: S T) apply auto[1] unfolding steps.simps unfolding bind_union_iff by auto

lemma accept_union:
  assumes "accept_from A w (S \<union> T)"
  shows "accept_from A w S \<or> accept_from A w T"
  using assms unfolding accept_from.simps unfolding steps_union_iff by blast

fun lang_from::"('a, 's) NA \<Rightarrow> 's set \<Rightarrow> 'a list set" where
  "lang_from A s = {w |w. accept_from A w s}"

definition lang::"('a, 's) NA \<Rightarrow>'a list set" where
  "lang A = {w | w. accept A w}"

datatype ('s1,'s2) UnionState = L 's1 | R 's2
fun union::"('a, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('a, ('s1, 's2) UnionState) NA" where
  "union A B = NA
    ((map L (start_list A)) @ (map R (start_list B)))
    (\<lambda> c. \<lambda> L s \<Rightarrow> map L (step A c s) | R s \<Rightarrow> map R (step B c s))
    ((map L (fin_list A)) @ (map R (fin_list B)))
  "

lemma UnionState_UNIV_finite:
  assumes "finite (UNIV::'a set)" and "finite (UNIV::'b set)"
  shows "finite (UNIV::('a, 'b) UnionState set)"
proof -
  have "(UNIV::('a, 'b) UnionState set) = L`(UNIV::'a set) \<union> R`(UNIV::'b set)" 
    by (metis UNIV_eq_I Un_iff UnionState.exhaust rangeI)
  then show ?thesis using assms
    by (metis finite_Un finite_imageI)
qed

lemma step_hom_steps:
  assumes "\<And>t a s. t \<in> set_step A a s \<Longrightarrow> P t \<in> set_step B a (P s)"
  shows   "t \<in> steps A w S \<Longrightarrow> P t \<in> steps B w (P ` S)"
proof (induct w arbitrary: t S)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  have K3:"t \<in> steps A w (Set.bind S (set_step A a))" using Cons(2) by simp
  have K2: "P t \<in> steps B w (P ` Set.bind S (set_step A a))" 
    using Cons(1)[OF K3] assms by blast
  have K4:"P ` Set.bind S (set_step A a) \<subseteq> Set.bind (P ` S) (set_step B a)"
    using assms by fastforce
  show ?case using steps_monotone[OF K4] unfolding steps.simps using K2 by blast
qed
lemma bind_to_union:"Set.bind S P = \<Union>{P s | s. s \<in> S}" 
  by fastforce

lemma step_hom_steps_unwrap:
  assumes "\<And>a b. (P a = P b) = (a = b)"
  assumes "\<And>s c. \<exists>S. P`S = set_step A c (P s)"
  assumes "\<And>t a s. P t \<in> set_step A a (P s) \<Longrightarrow> t \<in> set_step B a s"
  shows   "P t \<in> steps A w (P`S) \<Longrightarrow> t \<in> steps B w S"
proof (induct w arbitrary: t S)
  case Nil
  then show ?case using assms by auto
next
  case (Cons a w)
  have A1:"Set.bind (P ` S) (set_step A a) = \<Union> {set_step A a (P s) |s. s \<in> S}" 
    unfolding bind_to_union[of "P ` S" "set_step A a"] by auto
  have A2:"Set.bind (P ` S) (set_step A a) = \<Union> {P ` st |s st. s \<in> S \<and> P ` st = set_step A a (P s)}"
    unfolding A1 using assms(2)[of a] assms(1) by metis
  have A3:"Set.bind (P ` S) (set_step A a) = P ` \<Union> { st |s st. s \<in> S \<and> P ` st = set_step A a (P s)}"
    unfolding A2 by auto
  then obtain sa where SA:"P ` sa = Set.bind (P ` S) (set_step A a)" 
    unfolding A3 by blast
  have K3:"P t \<in> steps A w (P`sa)" using Cons(2) SA by simp
  have K2: "t \<in> steps B w sa" using Cons(1)[OF K3] assms by blast
  have K4:"sa \<subseteq> Set.bind S (set_step B a)" using assms(3) SA by fastforce
  show ?case using steps_monotone[OF K4] unfolding steps.simps using K2 by blast
qed

lemma union_sanity_steps_1_1:
  "t \<in> steps A w S \<Longrightarrow> L t \<in> steps (union A B) w (L`S)"
  using step_hom_steps[of A L "union A B" t w S] by auto

lemma P_then_P_steps:
  assumes "\<And>a b. (P a = P b \<longleftrightarrow> a = b)"
  assumes "\<And>c s. \<exists>S. P`S = set_step A c (P s)"
  shows "\<exists>S. P`S = steps A w (P`T)"
proof(induct w arbitrary: T)
  case Nil
  then show ?case by auto
next
  case (Cons a w)
  have A1:"Set.bind (P ` T) (set_step A a) = \<Union> {sa |s sa. s \<in> T \<and> sa = set_step A a (P s)}"
    unfolding bind_to_union by blast
  have A2:"Set.bind (P ` T) (set_step A a) = \<Union> {P`sa |s sa. s \<in> T \<and> P`sa = set_step A a (P s)}"
    unfolding A1 using assms(2)[of a] by metis
  have A3:"Set.bind (P ` T) (set_step A a) = P`\<Union> {sa |s sa. s \<in> T \<and> P`sa = set_step A a (P s)}"
    unfolding A2 by blast
  show ?case unfolding steps.simps A3 using Cons by blast
qed

lemma L_then_L:
  "\<exists>S. L`S = set_step (union A B) c (L s)"
  by auto

lemma L_then_L_steps:
  "\<exists>S. L`S = steps (union A B) w (L`T)"
  using P_then_P_steps[OF UnionState.inject(1) L_then_L] by metis

lemma R_then_R:
  "\<exists>S. R`S = set_step (union A B) c (R s)"
  by auto

lemma R_then_R_steps:
  "\<exists>S. R`S = steps (union A B) w (R`T)"
  using P_then_P_steps[OF UnionState.inject(2) R_then_R] by metis

lemma union_sanity_steps_2_1:
  shows   "L t \<in> steps (union A B) w (L`S) \<Longrightarrow> t \<in> steps A w S"
using step_hom_steps_unwrap[OF UnionState.inject(1) L_then_L, of A B A] by auto

lemma union_sanity_steps_2_2:
  shows   "R t \<in> steps (union A B) w (R`S) \<Longrightarrow> t \<in> steps B w S"
using step_hom_steps_unwrap[OF UnionState.inject(2) R_then_R, of A B B] by auto

lemma union_sanity_steps_1_2:
  "t \<in> steps B w S \<Longrightarrow> R t \<in> steps (union A B) w (R`S)"
using step_hom_steps[of B R "union A B" t w S] by auto

lemma union_sanity_accept_1_1:
  "accept A w \<Longrightarrow> accept (union A B) w"
proof -
  assume "accept A w"
  then obtain e where "e \<in> (steps A w (starts A) \<inter> (fins A))" by auto
  then have A:"L e \<in> steps (union A B) w (L` starts A) \<inter> L`(fins A)"
    using union_sanity_steps_1_1 by fast
  have B:"steps (union A B) w (L ` starts A) \<subseteq>
        steps (union A B) w (L ` starts A \<union> R ` starts B)"
    by (simp add: steps_monotone)
  then have "L e \<in> steps (union A B) w (starts (NFA.union A B)) \<inter> fins (NFA.union A B)"
    using steps_monotone[OF B] A by auto
  then show "accept (union A B) w"
    unfolding accept.simps by blast
qed

lemma union_sanity_accept_1_2:
  "accept B w \<Longrightarrow> accept (union A B) w"
proof -
  assume "accept B w"
  then obtain e where "e \<in> (steps B w (starts B) \<inter> (fins B))" by auto
  then have A:"R e \<in> steps (union A B) w (R` starts B) \<inter> R`(fins B)"
    using union_sanity_steps_1_2 by fast
  have B:"steps (union A B) w (R ` starts B) \<subseteq>
        steps (union A B) w (L ` starts A \<union> R ` starts B)"
    by (simp add: steps_monotone)
  then have "R e \<in> steps (union A B) w (starts (NFA.union A B)) \<inter> fins (NFA.union A B)"
    using steps_monotone[OF B] A by auto
  then show "accept (union A B) w"
    unfolding accept.simps by blast
qed

lemma union_sanity_1:
  shows "lang A \<union> lang B \<subseteq> lang (union A B)"
  using union_sanity_accept_1_1 union_sanity_accept_1_2 
  unfolding lang_def by blast


lemma union_sanity_accept_2_1:
  assumes "accept_from (union A B) w (L ` (starts A))"
  shows "accept A w"
proof -
  obtain e where "L e \<in> (steps (union A B) w (L ` (starts A)) \<inter> (fins (union A B)))" 
    using union_sanity_steps_2_1[of _ A B] using assms L_then_L_steps[of A B w "starts A"] by auto
  then have A:"e \<in> steps A w (starts A) \<inter> (fins A)"
    using union_sanity_steps_2_1 by fastforce
  have B:"L ` (steps A w (starts A)) \<subseteq>
        steps (union A B) w (L`(starts A))"
    by (metis image_subsetI union_sanity_steps_1_1)
  then have "e \<in> steps A w (starts A) \<inter> fins A"
    using steps_monotone[OF B] A by auto
  then show "accept A w" by auto
qed

lemma union_sanity_accept_2_2:
  assumes "accept_from (union A B) w (R ` (starts B))"
  shows "accept B w"
proof -
  obtain e where "R e \<in> (steps (union A B) w (R ` (starts B)) \<inter> (fins (union A B)))" 
    using union_sanity_steps_2_2[of _ A B] using assms R_then_R_steps[of A B w "starts B"] by auto
  then have A:"e \<in> steps B w (starts B) \<inter> (fins B)"
    using union_sanity_steps_2_2 by fastforce
  have B:"R ` (steps B w (starts B)) \<subseteq>
        steps (union A B) w (R`(starts B))"
    by (metis image_subsetI union_sanity_steps_1_2)
  then have "e \<in> steps B w (starts B) \<inter> fins B"
    using steps_monotone[OF B] A by auto
  then show "accept B w" by auto
qed

lemma union_sanity_accept_2:
  assumes "accept_from (union A B) w (starts (NFA.union A B))"
  shows "accept B w \<or> accept A w"
proof -
  have START:"starts (NFA.union A B) = (L`starts A) \<union> (R`starts B)"
    unfolding union.simps by simp
  have ASM:"accept_from (union A B) w ((L`starts A) \<union> (R`starts B))"
    using assms unfolding START by blast
  have "accept_from (union A B) w (L`starts A) \<or> accept_from (union A B) w (R`starts B)"
    using accept_union[OF ASM] by blast
  then show ?thesis
    using union_sanity_accept_2_1[of A B w] union_sanity_accept_2_2[of A B w] by blast
qed


lemma union_sanity_2:
  shows "lang (union A B) \<subseteq> lang A \<union> lang B"
  using union_sanity_accept_2[of A B] unfolding lang_def by auto

lemma union_sanity:
  shows "lang (union A B) = lang A \<union> lang B"
  using union_sanity_1 union_sanity_2 
  by blast

datatype 's AppendWordState = Orig 's | Appended nat

fun append_word::"('a, 's) NA \<Rightarrow> 'a list \<Rightarrow> ('a, 's AppendWordState) NA" where
  "append_word A [] = NA 
    (map Orig (start_list A))
    (\<lambda> c. \<lambda> Orig s \<Rightarrow> map Orig (step A c s) | Appended n \<Rightarrow> [])
    (map Orig (fin_list A))
  " |
  "append_word A (w1#w) = NA 
    (map Orig (start_list A))
    (\<lambda> c. \<lambda> Orig s \<Rightarrow> (let nexts = map Orig (step A c s) in
      if s \<in> fins A \<and> c = w1 then (Appended 0)#nexts 
                              else nexts)|
            Appended n \<Rightarrow> (if n < length w \<and> c = w!n
                              then [Appended (n + 1)] else []))
    [Appended (length w)]
  "

lemma append_word_sanity_steps_1:
  "t \<in> steps A w S \<Longrightarrow> Orig t \<in> steps (append_word A s) w (Orig`S)"
  apply(rule step_hom_steps[of A Orig "append_word A s" t w S]) 
   apply auto
  apply (cases s) apply simp
  apply(case_tac "sa \<in> fins A \<and> a = aa") apply simp by auto

lemma append_word_sanity_step_2:
  "Orig t \<in> set_step (append_word A s) w (Orig S) \<Longrightarrow> t \<in> set_step A w S"
  apply(cases s) apply simp apply blast
  apply simp 
  apply(case_tac "S \<in> fins A \<and> w = a")
  by auto

fun inv_orig::"'s AppendWordState \<Rightarrow> 's" where
  "inv_orig (Orig s) = s" |
  "inv_orig _ = undefined"

lemma append_word_sanity_step_2':
  "S \<in> range Orig \<and> t \<in> range Orig \<Longrightarrow> t \<in> set_step (append_word A s) w S \<Longrightarrow> inv_orig t \<in> set_step A w (inv_orig S)"
  using append_word_sanity_step_2 by force

lemma Appended_n_to_Appended_n_plus_1:
  assumes "n < length xs"
  shows "Appended (n + 1) \<in> set_step (append_word A (x#xs)) (xs!n) (Appended n)"
  using assms by auto

lemma Appended_0_to_Appended_n:
  assumes "n \<le> length xs"
  shows "Appended n \<in> steps (append_word A (x#xs)) (take n xs) {Appended 0}"
  using assms proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have A:"Appended (n + 1) \<in> steps (append_word A (x#xs)) [xs!n] {Appended n}"
    using Appended_n_to_Appended_n_plus_1 by simp
  have B:"take (Suc n) xs = (take n xs) @ [xs ! n]" using Suc(2) 
    using Suc_le_lessD take_Suc_conv_app_nth by blast
  show ?case unfolding B unfolding steps_assoc using steps_elem[OF Suc(1) A] Suc by force
qed

lemma Appended0_to_fin:
  "Appended (length xs) \<in> steps (append_word A (x#xs)) xs {Appended 0}"
  using Appended_0_to_Appended_n by force

lemma append_word_sanity_accept_1:
  "accept A w \<Longrightarrow> accept (append_word A s) (w@s)"
proof (cases s)
  case Nil
  assume "accept A w"
  then obtain f where F:"f \<in> steps A w (starts A)" and FFINS:"f \<in> fins A" by auto
  have "Orig f \<in> steps (append_word A s) w (Orig ` starts A)"
    using append_word_sanity_steps_1[OF F, of s] by simp
  have A:"Orig f \<in> steps (append_word A s) w (Orig ` starts A)"
    using append_word_sanity_steps_1[OF F, of s] by simp
  have "Orig f \<in> fins (append_word A s)" using FFINS Nil unfolding append_word.simps by simp
  then show ?thesis using Nil A by auto
next
  case (Cons x xs)
  assume "accept A w"
  then obtain f where F:"f \<in> steps A w (starts A)" and FFIN:"f \<in> fins A" by auto
  have A:"Orig f \<in> steps (append_word A s) w (Orig ` starts A)"
    using append_word_sanity_steps_1[OF F, of s] by simp
  have "Appended 0 \<in> (set_step (append_word A (x # xs)) x) (Orig f)"
    using FFIN by simp
  then have ZERO:"Appended 0 \<in> steps (append_word A (x#xs)) (w@[x]) (Orig ` starts A)"
    unfolding steps.simps Cons
    unfolding steps_snoc
    using A
    unfolding Cons
    by force
  have FIN:"Appended (length xs) \<in> fins (append_word A (x#xs))" by auto
  have "Appended (length xs) \<in>  (steps (append_word A (x#xs)) (w@[x]@xs) (Orig ` starts A))"
    using steps_elem[OF ZERO Appended0_to_fin] by simp
  then show "accept (append_word A s) (w@s)" using FIN unfolding Cons accept.simps by simp
qed

lemma append_word_sanity_1:
  shows "{w@s | w. w \<in> lang A} \<subseteq> lang (append_word A s)"
  using append_word_sanity_accept_1 unfolding lang_def by blast

lemma cannnot_reach_appended_length_w:
  "n \<ge> length w \<Longrightarrow> Appended n \<notin> set_step (append_word A w) c s"
proof(cases w)
  case Nil
  then show ?thesis unfolding Nil append_word.simps
     AppendWordState.distinct(1) AppendWordState.exhaust AppendWordState.simps(5) AppendWordState.simps(6) NA.sel(2) empty_iff image_iff
    by auto
next
  case (Cons a list)
  assume L:"length w \<le> n"
  show ?thesis 
  proof(cases s)
    case (Orig x1)
    show ?thesis using L
      unfolding Cons append_word.simps NA.sel(2) Orig apply simp
      apply(cases "x1 \<in> fins A \<and> c = a") by auto
  next
    case (Appended x2)
    show ?thesis using L
      unfolding Cons append_word.simps NA.sel(2) Appended 
      by simp
  qed
qed


lemma accept_from_step:"accept_from A (c#w) {s} = accept_from A w (set_step A c s)"
  apply(rule)
  unfolding accept_from.simps steps.simps bind_insert_iff
   apply simp by simp
lemma accept_from_step_set:"accept_from A (c#w) S = accept_from A w (Set.bind S (set_step A c))"
  apply(rule)
  unfolding accept_from.simps steps.simps bind_insert_iff
   apply simp by simp
lemma accept_from_concat_set:"accept_from A (v@w) S = accept_from A w (steps A v S)"
  apply(induct v arbitrary: w S) apply simp
  by auto


fun pref_quotient::"('a, 's) NA \<Rightarrow> 'a list \<Rightarrow> ('a, 's) NA" where
  "pref_quotient A w = NA
    (steps_list A w (start_list A))
    (step A)
    (fin_list A)"

lemma if_step_eq_then_steps_eq:
  assumes "step A = step B"
  shows   "steps A x xa = steps B x xa"
  apply(induct x arbitrary: xa) 
   apply simp unfolding steps.simps 
  using assms by force

lemma pref_quotient_sanity_1:
  shows "{s | s. w@s \<in> lang A} \<subseteq> lang (pref_quotient A w)"
proof -
  have "(\<And>w s. accept A (w@s) \<Longrightarrow> accept (pref_quotient A w) s)"  proof -
    fix w s
    assume ASM:"accept A (w@s)"
    have A:"steps (pref_quotient A w) w (starts A) = steps A w (starts A)"
        using if_step_eq_then_steps_eq[of A "(pref_quotient A w)"] by simp
    have ST:"starts (pref_quotient A w) = steps A w (starts A)" 
      by simp  
    then have "accept_from A s (steps A w (starts A))"
      using accept_from_concat_set ASM by fastforce
    then have "accept_from (pref_quotient A w) s (starts (pref_quotient A w))"
      unfolding ST using A 
      unfolding accept_from.simps unfolding pref_quotient.simps NA.sel 
      by (metis NA.sel(2) if_step_eq_then_steps_eq)
    then show "accept (pref_quotient A w) s" by auto
  qed
  then show ?thesis using lang_def by blast
qed

fun explore_rel_less_eq::
  "('s1 \<times> 's2 set) => ('s1 \<times> 's2 set) => bool" where
  "explore_rel_less_eq (s1, s2) (t1, t2) = (s1 = t1 \<and> t2 \<subseteq> s2)"

fun explore_rel_less::
  "('s1 \<times> 's2 set) => ('s1 \<times> 's2 set) => bool" where
  "explore_rel_less (s1, s2) (t1, t2) = (s1 = t1 \<and> t2 \<subset> s2)"

interpretation explore_ordering: ordering explore_rel_less_eq explore_rel_less
  apply unfold_locales 
  apply auto[1]
  apply auto[1]
   apply force by auto

fun is_not_comparable::
  "('s1 \<times> 's2 set) set => ('s1 \<times> 's2 set) => bool" where
  "is_not_comparable rels (s, t) = Ball rels (\<lambda>(s',t'). \<not>explore_rel_less_eq (s, t) (s', t'))"

lemma accept_from_subset_monotone:
  assumes "S \<subseteq> T"
  shows "accept_from A w S \<Longrightarrow> accept_from A w T"
  using assms unfolding accept_from.simps using steps_monotone by blast

lemma lang_from_subset_monotone:
  assumes "S \<subseteq> T"
  shows "lang_from A S \<subseteq> lang_from A T"
  using assms unfolding lang_from.simps using accept_from_subset_monotone by fast



lemma lang_from_step_iff: "(c#w) \<in> lang_from A {s} = (w \<in> (lang_from A (set_step A c s)))"
  unfolding lang_from.simps
  using accept_from_step by fast

lemma lang_from_step_iff_set: "(c#w) \<in> lang_from A S = (w \<in> (lang_from A (Set.bind S (set_step A c))))"
  using lang_from_step_iff by simp

lemma lang_from_starts_is_lang:
  "lang_from A (starts A) = lang A"
  unfolding lang_def
  using accept_from_start_is_accept by auto

fun diff_lang_set::"('a, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> 'a list set" where
  "diff_lang_set A B (a, bs) = (lang_from A {a}) - (lang_from B bs)"

lemma diff_lang_set_rel_monotone:
  assumes "explore_rel_less_eq a b"
  shows "diff_lang_set A B a \<subseteq> diff_lang_set A B b"
  using assms
  apply (cases a, cases b)
  apply (simp del:lang_from.simps)
  unfolding diff_lang_set.simps 
  using lang_from_subset_monotone 
  by blast

fun exists_diff_rel::"('a, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> bool" where
  "exists_diff_rel A B (a, bs) = (diff_lang_set A B (a, bs) \<noteq> {})"

lemma explore_rel_less_then_diff_exists:
  assumes "exists_diff_rel A B a"
  and     "explore_rel_less_eq a b"
  shows "exists_diff_rel A B b"
  using assms 
  apply(cases a, cases b)
proof -
  fix aa and ba and aaa and baa
  assume ex_a:"exists_diff_rel A B a" and A:"a = (aa, ba)" and ex_b:"explore_rel_less_eq a b"and B:"b = (aaa, baa)"
  have AL:"lang_from A {aa} - lang_from B ba \<noteq> {}" using ex_a unfolding A by simp
  have LSUB:"lang_from B baa \<subseteq> lang_from B ba" using ex_b unfolding B A using lang_from_subset_monotone[of baa ba B] by simp
  have "lang_from A {aaa} - lang_from B baa \<noteq> {}"using ex_b unfolding B A unfolding explore_rel_less_eq.simps using AL LSUB by blast
  then show "exists_diff_rel A B b" unfolding B unfolding exists_diff_rel.simps diff_lang_set.simps by auto
qed


fun inv_cond::"('a, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set)list \<times> ('s1 \<times> 's2 set)list \<Rightarrow> bool" where
  "inv_cond A B (todos, explored) = (
       (list_ex (exists_diff_rel A B) todos) \<and>
          (\<forall>ce. ce \<in> Set.bind (set explored) (diff_lang_set A B) \<longrightarrow> 
            (ce = [] \<or> (\<exists>t. t \<in> set todos \<and> (\<exists>cee. length cee < length ce \<and> cee \<in> diff_lang_set A B t)))
          )
  )"

fun step_rel::
  "('a::enum, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> ('s1 \<times> 's2 set) list" where
  "step_rel A B (s, t) = 
    List.bind (enum_class.enum::'a list) (\<lambda>c. map (\<lambda>ss. (ss, Set.bind t (set_step B c))) (step A c s))"

(*lemma "set (enum_class.enum::'a::enum list) = (UNIV::'a set)"*)

fun set_step_rel::
  "('a::enum, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> ('s1 \<times> 's2 set) set" where
  "set_step_rel A B (s, t) = 
    Set.bind (UNIV::'a set) (\<lambda>c. (\<lambda>ss. (ss, Set.bind t (set_step B c))) ` (set_step A c s))"

lemma set_step_rel_equiv:
fixes A::"('a::enum, 's1) NA"
shows "set (step_rel A B (a,bs)) = set_step_rel A B (a,bs)"
  unfolding step_rel.simps
  unfolding set_step_rel.simps
  unfolding set_list_bind
  unfolding enum_UNIV
  by simp

fun is_not_subsumed_by_all::
  "('s1 \<times> 's2 set) list => ('s1 \<times> 's2 set) => bool" where
  "is_not_subsumed_by_all rels (s, t) = List.list_all (\<lambda>(s',t'). \<not>explore_rel_less_eq (s, t) (s', t')) rels"

fun explore_state_step::"('a::enum, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> ('s1 \<times> 's2 set) list \<Rightarrow> ('s1 \<times> 's2 set) list \<Rightarrow>
('s1 \<times> 's2 set) list \<times> ('s1 \<times> 's2 set) list" where
"explore_state_step A B cur todos explored = (
  if is_not_subsumed_by_all (todos@explored) cur then
      (todos@(step_rel A B cur), cur#explored)
  else (todos, explored) 
  )"

fun init_explore_state::"('a, 's1) NA \<Rightarrow> ('a, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) list" where
  "init_explore_state A B = map (\<lambda>sa. (sa, starts B)) (start_list A)"

lemma diff_lang_set_emp:"a \<in> fins A \<and> bs \<inter> fins B = {} \<longleftrightarrow> [] \<in> diff_lang_set A B (a, bs)"
  by auto

lemma bins_steps:"steps A w S = Set.bind S (\<lambda>s. steps A w {s})"
proof (induct w arbitrary: S)
  case Nil
  then show ?case by auto
next
  case (Cons h w)
  have A:"Set.bind S (\<lambda>s. steps A w (set_step A h s)) = 
         Set.bind S (\<lambda>s. Set.bind (set_step A h s) (\<lambda>s. steps A w {s}))"
    using Cons by metis
  show ?case unfolding steps.simps bind_insert_iff empty_bind Un_empty_right 
    unfolding Cons[of "Set.bind S (set_step A h)"] 
    unfolding A by (simp add: Set.bind_bind)
qed

lemma  "accept_from A (c # w) {a} = Bex (set_step A c a) (\<lambda>s. accept_from A w {s})"
  unfolding Bex_def accept_from.simps
  unfolding steps.simps bind_insert_iff empty_bind Un_empty_right 
  unfolding bins_steps[of A w "(set_step A c a)"] 
  unfolding Set.bind_def
  apply simp
  by blast

lemma accept_from_step_ex: "accept_from A w (set_step A c a) = Bex (set_step A c a) (\<lambda>s. accept_from A w {s})"
  unfolding Bex_def accept_from.simps
  unfolding steps.simps bind_insert_iff empty_bind Un_empty_right 
  unfolding bins_steps[of A w "(set_step A c a)"] 
  unfolding Set.bind_def
  apply simp
  by blast

lemma diff_lang_set_step_1:
  assumes "c#w \<in> diff_lang_set A B (a, bs)"
    and "a' \<in> set_step A c a" and "w \<in> lang_from A {a'}"
  shows "w \<in> diff_lang_set A B (a', Set.bind bs (set_step B c))"
      unfolding diff_lang_set.simps
      using assms by simp
lemma lang_from_set_step:
  assumes "w \<in> lang_from A (set_step A c a)"
  shows "\<exists>s. s \<in> set_step A c a \<and> w \<in> lang_from A {s}"
  using assms  unfolding lang_from.simps
proof -
  assume "w \<in> {w |w. accept_from A w (set_step A c a)}"
  then show "\<exists>s. s \<in> set_step A c a \<and> w \<in> {w |w. accept_from A w {s}}"
    unfolding accept_from.simps using accept_from_step_ex by force
qed
lemma diff_lang_set_step_2:
  assumes "c#w \<in> diff_lang_set A B (a, bs)"
  shows   "\<exists>a'. a' \<in> set_step A c a \<and> w \<in> lang_from A {a'}"
proof  -
  have A:"(c # w \<in> lang_from A {a}) = (w \<in> lang_from A (set_step A c a))"
    using assms unfolding diff_lang_set.simps
    using lang_from_step_iff[of c w A a] by auto

  have B:"(c # w \<in> lang_from B bs) = (w \<in> lang_from B (Set.bind bs (set_step B c)))"
    using assms unfolding diff_lang_set.simps
    using lang_from_step_iff_set[of c w B bs] by auto
  show ?thesis 
     using lang_from_set_step A B 
     by (metis Diff_iff assms diff_lang_set.simps)
 qed
lemma diff_lang_set_step:
  assumes "c#w \<in> diff_lang_set A B (a, bs)"
  shows "\<exists>a'. a' \<in> set_step A c a \<and> w \<in> lang_from A {a'} \<and> w \<in> diff_lang_set A B (a', Set.bind bs (set_step B c))"
  using diff_lang_set_step_2[OF assms]  diff_lang_set_step_1[OF assms] by blast

lemma diff_lang_set_step_rev:
  assumes "a' \<in> set_step A c a" and 
          "ce \<in> diff_lang_set A B (a', Set.bind bs (set_step B c))"
        shows "c#ce \<in> diff_lang_set A B (a, bs)" proof-

  have B:"ce \<in> lang_from A {a'}"
    using assms unfolding diff_lang_set.simps  by blast
  have "ce \<notin> lang_from B (Set.bind bs (set_step B c))"
    using assms unfolding diff_lang_set.simps by blast
  then have A:"(c # ce \<notin> lang_from B bs)"
     using lang_from_step_iff_set[symmetric, of ce B bs c] by blast
  have "(c # ce \<in> lang_from A {a})"
    using lang_from_step_iff_set[symmetric, of ce B bs c] 
    using assms
    unfolding lang_from_step_iff[of c] 
    using B lang_from_subset_monotone[of "{a'}"]
    by blast
  then show ?thesis using A by auto
qed

lemma diff_lang_set_emp_step:
  assumes "diff_lang_set A B (a, bs) = {}" and 
          "List.member (step_rel A B (a, bs)) (a',bs')"
        shows "(diff_lang_set A B (a',bs')) = {}"
  apply(rule ccontr)
proof -
  assume "diff_lang_set A B (a', bs') \<noteq> {}"
  then obtain ce where CE:"ce \<in> diff_lang_set A B (a', bs')" by blast
  then obtain c where C:"a' \<in> set_step A c a \<and> bs' = Set.bind bs (set_step B c)"
    using assms(2)
    unfolding List.member_def
    using set_step_rel_equiv[of A B a bs]
    by auto
  then have "c#ce \<in> diff_lang_set A B (a, bs)"
    using diff_lang_set_step_rev CE C by metis
  then show False using assms(1) by blast
qed

lemma diff_lang_set_emp_step':
  assumes "diff_lang_set A B (a, bs) = {}"
  shows "\<not>list_ex (exists_diff_rel A B) (step_rel A B (a, bs))"
  unfolding list_ex_iff Bex_def
  unfolding exists_diff_rel.simps
  using assms diff_lang_set_emp_step[OF assms]
  by (simp add: in_set_member)
lemma prod_exists: "\<exists>x. P x \<longleftrightarrow> (\<exists>a bs. P (a,bs))" by blast

lemma exists_diff_rel_imp:
"((c#ce) \<in> diff_lang_set A B (a, bs)) \<Longrightarrow> (list_ex (exists_diff_rel A B) (step_rel A B (a, bs)))"
proof -
  assume ASM:"(c#ce) \<in> diff_lang_set A B (a, bs)"
  obtain a' where A:" a' \<in> set_step A c a \<and> ce \<in> lang_from A {a'}"
    using ASM unfolding exists_diff_rel.simps  
    using diff_lang_set_step[of c ce A B a bs] by blast
  have B:"ce \<notin> lang_from B (Set.bind bs (set_step B c))"
    using ASM unfolding exists_diff_rel.simps unfolding diff_lang_set.simps
    using lang_from_step_iff_set[of c ce B bs] 
    using diff_lang_set_step by blast

  have "\<exists>a' bs'. (a',bs') \<in> set (step_rel A B (a, bs)) \<and> (exists_diff_rel A B (a',bs'))"
    unfolding set_step_rel_equiv
    unfolding set_step_rel.simps
    using A B by force
  then show ?thesis 
    using list_ex_iff by blast
qed

lemma exists_diff_rel_step:
  "exists_diff_rel A B (a, bs) \<longleftrightarrow>
  (a \<in> fins A \<and> bs \<inter> fins B = {}) \<or> (
    list_ex (exists_diff_rel A B) (step_rel A B (a,bs))
)"
  unfolding exists_diff_rel.simps
  apply(cases "a \<in> fins A \<and> bs \<inter> fins B = {}")
  using diff_lang_set_emp[of a A bs B] proof blast
  assume ASM:"\<not> (a \<in> fins A \<and> bs \<inter> fins B = {})"
  then have NONEMP:"[] \<notin> diff_lang_set A B (a, bs)"
    using diff_lang_set_emp[of a A bs B] by blast
  then have "(diff_lang_set A B (a, bs) \<noteq> {}) = (list_ex (exists_diff_rel A B) (step_rel A B (a, bs)))"
    by (metis all_not_in_conv diff_lang_set_emp_step' exists_diff_rel_imp list.exhaust)
  then show "(diff_lang_set A B (a, bs) \<noteq> {}) = (a \<in> fins A \<and> bs \<inter> fins B = {} \<or> list_ex (exists_diff_rel A B) (step_rel A B (a, bs)))"
    using ASM by blast
qed
value "List.upt 0 2"
lemma accept_from_iff_antichain:
  fixes todos::"('s1 \<times> 's2 set) list"
  fixes explored::"('s1 \<times> 's2 set) list"
  assumes "inv_cond A B (todos, explored)"
  shows   "if todos = [] then False else (
  let (cur_a, cur_bs) = hd todos in
    if (cur_a \<in> fins A) \<and> (fins B \<inter> cur_bs = {}) then True 
    else (
      inv_cond A B (explore_state_step A B (cur_a,cur_bs) (tl todos) explored)
    )
  )"
proof(cases "todos")
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons cur next_todos) 
  have todos_contain:"list_ex (exists_diff_rel A B) todos" using assms by auto
  show ?thesis proof(cases cur)
    case (Pair a bs)

    have "(a \<in> fins A \<longrightarrow> fins B \<inter> bs \<noteq> {}) \<Longrightarrow> inv_cond A B (explore_state_step A B (a, bs) next_todos explored)"
    proof (cases "is_not_subsumed_by_all (next_todos @ explored) (a, bs)")
      case True
      assume "(a \<in> fins A \<longrightarrow> fins B \<inter> bs \<noteq> {})"
      then have NO_EMPTY_LANG_DIFF: "[] \<notin> diff_lang_set A B (a,bs)" by simp
      have B:"\<exists>x. x \<in> set (next_todos@step_rel A B (a, bs)) \<and> exists_diff_rel A B x" 
      proof(cases "exists_diff_rel A B (a, bs)")
        case True
        have "\<exists>x. x \<in> set (step_rel A B (a, bs)) \<and> exists_diff_rel A B x" 
          using NO_EMPTY_LANG_DIFF todos_contain 
          by (metis Bex_set True \<open>a \<in> fins A \<longrightarrow> fins B \<inter> bs \<noteq> {}\<close> exists_diff_rel_step inf_commute)
        then show ?thesis by auto
      next
        case False
        have "list_ex (exists_diff_rel A B) next_todos" 
          using todos_contain unfolding Cons using False by (simp add: Pair)
        then have "\<exists>x. x \<in> set next_todos \<and> exists_diff_rel A B x" unfolding list_ex_iff Bex_def by blast
        then show ?thesis by auto
      qed
      have C':"\<forall>c ce. c#ce \<in> Set.bind (set ((a, bs) # explored)) (diff_lang_set A B) \<longrightarrow>
          (\<exists>t. t \<in> set (next_todos @ step_rel A B (a, bs)) \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t))"
      proof(rule,rule,rule)
        fix c and ce
        assume ASM:"c # ce \<in> Set.bind (set ((a, bs) # explored)) (diff_lang_set A B)"
        then show "\<exists>t. t \<in> set (next_todos @ step_rel A B (a, bs)) \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t)"
        proof (cases "c # ce \<in> diff_lang_set A B (a,bs)")
          case True
          then obtain a' where A':"a' \<in> set_step A c a \<and> ce \<in> lang_from A {a'} \<and> ce \<in> diff_lang_set A B (a', Set.bind bs (set_step B c))"
            using diff_lang_set_step[OF True] by blast
          have "(a', Set.bind bs (set_step B c)) \<in> set (step_rel A B (a, bs))"
            unfolding set_step_rel_equiv set_step_rel.simps 
            using True A' by auto
          then have K:"(a', Set.bind bs (set_step B c)) \<in>  set (next_todos @ step_rel A B (a, bs))" by simp
          have "\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B (a', Set.bind bs (set_step B c))"
            unfolding set_step_rel_equiv set_step_rel.simps 
            using True A' by auto
          then show ?thesis using K by blast
        next
          case False
          then have ccce_explroed:"c # ce \<in> Set.bind (set explored) (diff_lang_set A B)"
            using ASM by auto
          then have "c #ce = [] \<or> (\<exists>t. t \<in> set todos \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t))"
            using assms unfolding inv_cond.simps by blast
          then obtain a' and bs' where A'BS':"(a', bs') \<in> set ((a,bs)#next_todos) \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B (a', bs'))"
            unfolding Cons Pair by fast
          then show ?thesis proof(cases "(a', bs') \<in> set next_todos")
            case True 
            then show ?thesis using UnCI A'BS' set_append by metis
          next
            case False
            then have A:"a = a'" and BS:"bs = bs'" using A'BS' apply simp using A'BS' by (simp add: False)
            then obtain cee where CEE:"length cee < length (c # ce) \<and> cee \<in> diff_lang_set A B (a, bs)" using A'BS' A BS by blast
            then obtain cee_h and cee_tl where CEE_CONS:"cee = cee_h#cee_tl"  apply(cases cee) using NO_EMPTY_LANG_DIFF apply blast by blast
            have CEE_DIFF:"cee_h # cee_tl \<in> diff_lang_set A B (a, bs)" using CEE CEE_CONS by blast
            obtain a'' where A'':"a'' \<in> set_step A cee_h a \<and> cee_tl \<in> lang_from A {a''} \<and> cee_tl \<in> diff_lang_set A B (a'', Set.bind bs (set_step B cee_h))"
              using diff_lang_set_step[OF CEE_DIFF] by blast
            have SS:"(a'', Set.bind bs (set_step B cee_h)) \<in> set (step_rel A B (a, bs))"
              unfolding set_step_rel_equiv set_step_rel.simps 
              using True A'' by auto
            then have K:"(a'', Set.bind bs (set_step B cee_h)) \<in>  set (next_todos @ step_rel A B (a, bs))" by simp
            then obtain cee' where "length cee' < length (cee_h#cee_tl) \<and> cee' \<in> diff_lang_set A B (a'', Set.bind bs (set_step B cee_h))"
              unfolding set_step_rel_equiv set_step_rel.simps 
              using True A'' by auto
            then have "length cee' < length (c # ce) \<and> cee' \<in> diff_lang_set A B (a'', Set.bind bs (set_step B cee_h))" 
              using CEE CEE_CONS by force
            then have "\<exists>t. t \<in> set (step_rel A B (a, bs)) \<and> (\<exists>cee'. length cee' < length (c#ce) \<and> cee' \<in> diff_lang_set A B t)"
              using CEE SS by blast
            then show ?thesis by fastforce
          qed 
        qed
      qed
      have C:"\<forall>ce. ce \<in> Set.bind (set ((a, bs) # explored)) (diff_lang_set A B) \<longrightarrow>
          (ce = [] \<or> (\<exists>t. t \<in> set (next_todos @ step_rel A B (a, bs)) \<and> (\<exists>cee. length cee < length (ce) \<and> cee \<in> diff_lang_set A B t)))"
        apply (rule) apply(case_tac ce) apply blast using C' by blast
      have A:"inv_cond A B (next_todos @ step_rel A B (a, bs), (a, bs)#explored)"
        unfolding inv_cond.simps list_ex_iff Bex_def using B C by blast
      show ?thesis using A True by fastforce
    next
      case False
      then obtain cova and covbs where COVSTATE:"(cova, covbs) \<in> set (next_todos @ explored)"and COV_SUBSUME:"explore_rel_less_eq (a, bs) (cova, covbs)"
        unfolding is_not_subsumed_by_all.simps list_all_def by blast
      assume "(a \<in> fins A \<longrightarrow> fins B \<inter> bs \<noteq> {})"
      then have NO_EMPTY_LANG_DIFF: "[] \<notin> diff_lang_set A B (a,bs)" by simp
      have B:"\<exists>x. x \<in> set (next_todos) \<and> exists_diff_rel A B x" 
      proof(cases "exists_diff_rel A B (a, bs)")
        case True
        have EX:"exists_diff_rel A B (cova, covbs)"
          using explore_rel_less_then_diff_exists[OF True, of "(cova, covbs)"] using COV_SUBSUME by blast
        then show ?thesis using COVSTATE proof (cases "(cova, covbs) \<in> set next_todos")
          case True
          then show ?thesis using COVSTATE EX by blast
        next
          case False
          then have COV:"(cova, covbs) \<in> set explored" using COVSTATE by simp
          have LEN_NONEMP:"length ` (diff_lang_set A B (a, bs)) \<noteq> {}" 
            using True unfolding exists_diff_rel.simps by blast

          then obtain min_length where MIN_IN:"min_length \<in> (length ` (diff_lang_set A B (a, bs)))" and 
                                       MIN_PP:"\<forall>s. s\<in>length ` (diff_lang_set A B (a, bs)) \<longrightarrow> min_length \<le> s" 
            using Min_existance_set[OF LEN_NONEMP] by blast
          then obtain ce' where "min_length = length ce'" and CE'_IN:"ce' \<in> (diff_lang_set A B (a, bs))" 
            using MIN_IN MIN_PP by blast
          then have "ce' \<noteq> []" using NO_EMPTY_LANG_DIFF by blast
          then obtain c and ce where CE':"ce' = c#ce" apply (cases ce') by auto

          have COVCEX:"c#ce \<in> diff_lang_set A B (cova, covbs)" using COV_SUBSUME unfolding explore_rel_less_eq.simps
            using CE'_IN unfolding CE' using diff_lang_set_rel_monotone[OF COV_SUBSUME] by blast

          have "c#ce \<in> Set.bind (set explored) (diff_lang_set A B)"
            using assms unfolding inv_cond.simps using COVCEX COV unfolding Set.bind_def by blast
          then obtain t where T:"t \<in> set todos \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t)"
            using assms unfolding inv_cond.simps by blast
          show ?thesis apply(cases "t \<in> set next_todos") 
            apply (metis T empty_iff exists_diff_rel.elims(3)) proof -
            assume "t \<notin> set next_todos" 
            then have "t = (a,bs)" using Cons Pair T by simp
            then have False using T MIN_PP by (metis CE' \<open>min_length = length ce'\<close> imageI linorder_not_le)
            then show ?thesis by blast
            qed
        qed
      next
        case False
        have "list_ex (exists_diff_rel A B) next_todos" 
          using todos_contain unfolding Cons using False by (simp add: Pair)
        then have "\<exists>x. x \<in> set next_todos \<and> exists_diff_rel A B x" unfolding list_ex_iff Bex_def by blast
        then show ?thesis by auto
      qed
      then have INV_COND_1:"list_ex (exists_diff_rel A B) next_todos"
        using False unfolding list_ex_iff by blast
      have INV_COND_2':"(\<forall>c ce. c#ce \<in> Set.bind (set explored) (diff_lang_set A B) \<longrightarrow> 
                        (\<exists>t. t \<in> set next_todos \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t)))"
      proof(rule, rule, rule)
        fix c and ce
        assume "c#ce \<in> Set.bind (set explored) (diff_lang_set A B)"
        then have "\<exists>t. t \<in> set ((a, bs)#next_todos) \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t)"
          using assms unfolding inv_cond.simps Cons Pair by blast
        then have NONEMP_LENSET:"{length cee | cee t. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t \<and> t \<in> set ((a, bs) # next_todos)} \<noteq> {}"
          by blast
        obtain min_cee_len where 
              "min_cee_len \<in> {length cee | cee t. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t \<and> t \<in> set ((a, bs) # next_todos)}" and 
              MCLEN:"\<forall>l. l \<in> {length cee | cee t. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t \<and> t \<in> set ((a, bs) # next_todos)} \<longrightarrow> min_cee_len \<le> l"
          using Min_existance_set[OF NONEMP_LENSET] by blast

        then obtain t and min_cee where 
              MC1:"length min_cee = min_cee_len" and 
              MC2:"length min_cee < length (c#ce) \<and> min_cee \<in> diff_lang_set A B t" and 
              T:"t \<in> set ((a, bs) # next_todos)"
          using assms unfolding inv_cond.simps Cons Pair by blast

        show "\<exists>t. t \<in> set next_todos \<and> (\<exists>cee. length cee < length (c#ce) \<and> cee \<in> diff_lang_set A B t)"
          apply(cases "t \<in> set next_todos") using T MC2 apply blast proof -
          assume"t \<notin> set next_todos"
          then have "t = (a,bs)" using T by simp
          then have MIN:"min_cee \<in> diff_lang_set A B (a,bs)" using T MC2 by blast
          then have "min_cee \<in> diff_lang_set A B (cova, covbs)" 
            using diff_lang_set_rel_monotone[OF COV_SUBSUME, of A B] by blast
          then have MC_IN:"min_cee \<in> Set.bind (set (next_todos@explored)) (diff_lang_set A B)" using COVSTATE by fastforce
          show "\<exists>t. t \<in> set next_todos \<and> (\<exists>cee. length cee < length (c # ce) \<and> cee \<in> diff_lang_set A B t)"
          proof(cases "min_cee \<in> Set.bind (set next_todos) (diff_lang_set A B)")
            case True
            then obtain t' where "t' \<in> set next_todos \<and> min_cee \<in> diff_lang_set A B t'" by fastforce
            then show ?thesis using MC2 by blast
          next
            case False
            then have "min_cee \<in> Set.bind (set explored) (diff_lang_set A B)" using MC_IN by simp
            then have MINCEE: "min_cee = [] \<or> (\<exists>t. t \<in> set ((a, bs) # next_todos) \<and> (\<exists>cee. length cee < length min_cee \<and> cee \<in> diff_lang_set A B t))"
              using assms unfolding inv_cond.simps Cons Pair by blast
            have "min_cee \<noteq> []" using MIN NO_EMPTY_LANG_DIFF by blast
            then obtain t' and cee' where T'CEE':"t' \<in> set ((a, bs) # next_todos) \<and> (length cee' < length min_cee \<and> cee' \<in> diff_lang_set A B t')"
              using MINCEE by blast
            then have "t' \<in> set ((a, bs) # next_todos) \<and> (length cee' < length (c#ce) \<and> cee' \<in> diff_lang_set A B t')" using MC1 MC2 T MCLEN by auto
            then have "length min_cee \<le> length cee'" using MC1 MC2 T MCLEN by blast
            then have False using T'CEE' by simp
            then show ?thesis by blast
          qed 
        qed
      qed
      have INV_COND_2:"(\<forall>ce. ce \<in> Set.bind (set explored) (diff_lang_set A B) \<longrightarrow> 
                        (ce=[] \<or> (\<exists>t. t \<in> set next_todos \<and> (\<exists>cee. length cee < length ce \<and> cee \<in> diff_lang_set A B t))))"
        apply(rule, case_tac ce)apply blast using INV_COND_2' 
        by (metis add.right_neutral add_Suc_right list.size(4))
      show ?thesis using INV_COND_1 INV_COND_2 False by auto
    qed

    then show ?thesis 
      unfolding Cons Pair 
      by (simp del:explore_state_step.simps inv_cond.simps) 
  qed
qed

lemma steps_union:"steps A w (S\<union>T) = (steps A w T)\<union>(steps A w S)"
proof(induct w arbitrary: S T)
  case Nil
  then show ?case by auto
next
  case (Cons a w)
  show ?case unfolding steps.simps unfolding bind_union_iff unfolding Cons by blast
qed

lemma steps_insert:"steps A w (insert a S) = (steps A w {a})\<union>(steps A w S)"
  using steps_union[of A w "{a}" S] by auto
lemma steps_empty:"steps A w {} = {}"
  apply(induct w) apply simp by simp
lemma A:"accept_from A w S = Bex S (\<lambda>s. accept_from A w {s})"
  unfolding accept_from.simps 
proof(induct w arbitrary: S)
  case Nil
  then show ?case by auto
next
  case (Cons a w)
  have "(\<exists>s\<in>Set.bind S (set_step A a). fins A \<inter> steps A w {s} \<noteq> {}) = 
        (\<exists>s\<in>S. fins A \<inter> steps A w (set_step A a s) \<noteq> {})"
    unfolding Set.bind_def apply simp
    by (meson local.Cons)
  then show ?case unfolding steps.simps bind_insert_iff Set.empty_bind Un_empty_right
    unfolding Cons[of "(Set.bind S (set_step A a))"]
    by simp
qed 
lemma "lang_from A S = Set.bind S (\<lambda>s. lang_from A {s})"
  unfolding lang_from.simps Set.bind_def
  using A[of A _ S] by simp
lemma accept_from_insert:
  "accept_from A w (insert a S) = (accept_from A w {a} \<or> accept_from A w S)"
  unfolding accept_from.simps
  using steps_insert by fast
lemma lang_from_exists: "e \<in> lang_from A S \<Longrightarrow> (\<exists>sa. sa \<in> S \<and> e \<in> lang_from A {sa})"
  unfolding lang_from.simps 
  using A[of A _ S] by auto



lemma inv_cond_init_False_then_contain:
  assumes "(inv_cond A B ((init_explore_state A B), []) \<Longrightarrow> False)" 
  shows "lang A \<subseteq> lang B"
proof -
  have "\<not>List.list_ex (exists_diff_rel A B) (init_explore_state A B)"
    using assms by auto
  then have "\<And>a bs. (a, bs) \<in> set (init_explore_state A B) \<Longrightarrow> \<not> exists_diff_rel A B (a, bs)"
    unfolding List.list_ex_iff
    by blast
  then have "\<And>a. a \<in> starts A \<Longrightarrow> \<not> exists_diff_rel A B (a, starts B)"
    unfolding init_explore_state.simps image_iff
    using assms by auto
  then have S:"\<And>a. a \<in> starts A \<Longrightarrow> lang_from A {a} - lang_from B (starts B) = {}"
    by simp
  then have "lang_from A (starts A) - lang_from B (starts B) \<noteq> {} \<Longrightarrow> False" proof -
    assume "lang_from A (starts A) - lang_from B (starts B) \<noteq> {}"
    then obtain e where EA:"e \<in> lang_from A (starts A)" and EB:"e \<notin> lang_from B (starts B)" by blast
    obtain sa where "e \<in> lang_from A {sa} \<and> sa \<in> starts A" using EA unfolding lang_from.simps 
      using lang_from_exists[of e A "starts A"] by auto
    then show ?thesis using S EB by auto
  qed
  then have "lang_from A (starts A) - lang_from B (starts B) = {}" by blast
  then show ?thesis 
    unfolding init_explore_state.simps  exists_diff_rel.simps
    unfolding lang_from_starts_is_lang by auto
qed
end