theory PCPTrans
  imports Main PCPDef.PCP PCPLemmas
begin

definition starts_with :: "string \<Rightarrow> string \<Rightarrow> bool"
  where "starts_with s1 s2 \<equiv> (s2 = take (length s2) s1)"

lemma starts_with_prefix: 
  fixes a::string
  fixes b::nat
  shows "starts_with a (take b a)"
  by (metis append_eq_conv_conj append_take_drop_id starts_with_def)

lemma non_common_prefix_monotone:
  fixes a::string
  fixes b::string
  fixes s::string
  fixes t::string
  shows "\<not>starts_with a b \<and> \<not>starts_with b a \<Longrightarrow> \<not>starts_with (a@s) (b@t)"
proof -
  assume "\<not>starts_with a b \<and> \<not>starts_with b a"
  then show ?thesis using starts_with_def 
    by (metis append.assoc append_eq_append_conv_if append_take_drop_id)
qed


datatype config = UP string | DN string

fun measure_config :: "config\<Rightarrow>nat" where
"measure_config (UP s) = length s" |
"measure_config (DN s) = 1 + (length s)"

fun swap_config :: "config \<Rightarrow> config" where
  "swap_config (UP s) = DN s"|
  "swap_config (DN s) = UP s"

fun step_config :: "tile \<Rightarrow> config \<Rightarrow> config set" where
  "step_config (u,d) (UP s) = (
    if (starts_with (s @ u) d ) 
      then {(UP (drop (length d) (s @ u)))}
    else(
      if (starts_with d (s @ u)) 
        then {(DN (drop (length (s @ u)) d))}
      else {}
    ))" | 
  "step_config (u,d)  (DN s)=  (
      if (starts_with u (s @ d)) 
        then {(UP (drop (length (s @ d)) u))}
    else(
    if (starts_with (s @ d) u ) 
      then {(DN (drop (length u) (s @ d)))}
      else {}
    ))"

lemma step_configs_upper_str:
  assumes "(PCPTrans.UP c') \<in> step_config (up,dn) (PCPTrans.UP c)"
  shows "dn@c' = c@up"
  by (metis append_take_drop_id assms config.inject(1) config.simps(4) empty_iff singletonD starts_with_def step_config.simps(1))

lemma step_configs_upper_to_lower_str:
  assumes "(PCPTrans.DN c') \<in> step_config (up,dn) (PCPTrans.UP c)"
  shows "dn = c@up@c'"
  by (metis append.assoc append_take_drop_id assms config.inject(2) config.simps(4) insertCI singletonD starts_with_def step_config.simps(1))

lemma step_configs_lower_str:
  assumes "(PCPTrans.DN c') \<in> step_config (up,dn) (PCPTrans.DN c)"
  shows "up@c' = c@dn"
  by (metis all_not_in_conv append_eq_conv_conj assms config.distinct(1) config.inject(2) insertE starts_with_def step_config.simps(2))

lemma step_configs_lower_to_upper_str:
  assumes "(PCPTrans.UP c') \<in> step_config (up,dn) (PCPTrans.DN c)"
  shows "up = c@dn@c'"
  by (metis append.assoc append_take_drop_id assms config.distinct(1) config.inject(1) insertCI singletonD starts_with_def step_config.simps(2))

lemma step_config_finite: 
  "finite (step_config t c)"
proof (cases t)
  case (Pair u d)
  then show ?thesis 
proof (cases c)
  case (UP s)
  then show ?thesis proof (cases "starts_with (s @ u) d")
    case True
    then show ?thesis using UP True Pair by auto
  next
    case False
    then show ?thesis using UP False Pair by auto
  qed
next
  case (DN s)
  then show ?thesis proof (cases "starts_with u (s @ d)")
    case True
    then show ?thesis using DN True Pair by auto
  next
    case False
    then show ?thesis using DN False Pair by auto
  qed
qed
qed
lemma step_config_card: 
  "card (step_config t c) \<le> 1"
proof (cases t)
  case (Pair u d)
  then show ?thesis 
proof (cases c)
  case (UP s)
  then show ?thesis proof (cases "starts_with (s @ u) d")
    case True
    then show ?thesis using UP True Pair by auto
  next
    case False
    then show ?thesis using UP False Pair by auto
  qed
next
  case (DN s)
  then show ?thesis proof (cases "starts_with u (s @ d)")
    case True
    then show ?thesis using DN True Pair by auto
  next
    case False
    then show ?thesis using DN False Pair by auto
  qed
qed
qed

lemma "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> card s > 0"
proof -
  assume A:"finite s"
  assume "s \<noteq> {}"
  then have "card s \<noteq> 0"
    using card_0_eq A by blast
  thus "card s > 0"
    by simp
qed


lemma step_config_is_deterministic:
  "a\<in>(step_config t c) \<Longrightarrow> {a}=(step_config t c)"
proof (cases "card (step_config t c) = 0")
  case True
  assume A:"a\<in>(step_config t c)"
  then have "\<not>(a\<in>(step_config t c))" using True step_config_finite by auto 
  then show ?thesis using A by auto
next
  case False
  assume A:"a\<in>(step_config t c)"
  have "card (step_config t c) = 1" using step_config_card[of t c] False by auto
  then show ?thesis by (metis A card_1_singletonE singletonD)
qed

lemma step_config_no_DN_empty:
  shows "DN [] \<notin> step_config (u, d) c"
proof (cases c)
  case (UP x1)
  then show ?thesis 
  proof (cases "(starts_with (x1 @ u) d )")
    case True
    then show ?thesis using UP by auto
  next
    case False
    then show ?thesis
      by (metis UP append.right_neutral empty_iff step_config.simps(1) step_configs_upper_to_lower_str)
  qed
next
  case (DN x2)
  then show ?thesis
  proof (cases "starts_with u (x2 @ d)")
    case True
    then show ?thesis using DN by auto
  next
    case False
    then show ?thesis using DN
    proof (cases "starts_with (x2 @ d) u")
      case True
      then show ?thesis 
        by (metis DN False append.right_neutral step_configs_lower_str)
    next
      case False
      then show ?thesis using DN by auto
    qed
    
  qed
  
qed


fun step_configs ::"tile \<Rightarrow> config set \<Rightarrow> config set" where
  "step_configs t cs = \<Union> ((step_config t) ` cs)"

fun pcp_step_config :: "pcp \<Rightarrow> config \<Rightarrow> config set" where
 "pcp_step_config ts c = \<Union> ( ((\<lambda>t. step_config t c) ` (set ts)))"

fun pcp_step_configs :: "pcp \<Rightarrow> config set \<Rightarrow> config set" where
 "pcp_step_configs ts cs = \<Union> ((pcp_step_config ts) ` cs)"

fun pcp_step_configs' :: "pcp \<Rightarrow> config set \<Rightarrow> config set" where
 "pcp_step_configs' ts cs = \<Union> ((\<lambda>t. step_configs t cs) ` (set ts))"

lemma pcp_step_configs_eq: "pcp_step_configs' ts cs = pcp_step_configs ts cs"
  by auto

lemma pcp_step_configs_simp:"pcp_step_configs pcp_instance (S\<union>T) = 
  pcp_step_configs pcp_instance S \<union> pcp_step_configs pcp_instance T
"
  "pcp_step_configs pcp_instance {} = {}
"
  by auto

fun pcp_init_set :: "pcp \<Rightarrow> config set" where
 "pcp_init_set ts = (pcp_step_config ts (UP []))"

value "pcp_init_set [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])]"

definition is_invariant :: "pcp \<Rightarrow> config set \<Rightarrow> bool" where
  "is_invariant ts confs \<equiv> (
    (pcp_init_set ts) \<subseteq> confs \<and>
    pcp_step_configs ts confs \<subseteq> confs \<and>
    (UP []) \<notin> confs\<and>
    (DN []) \<notin> confs
  )"

lemma is_invariant_imp:
"pcp_init_set pcp_instance \<subseteq> inv_set \<Longrightarrow>
pcp_step_configs pcp_instance inv_set \<subseteq> inv_set \<Longrightarrow> 
config.UP [] \<notin> inv_set \<Longrightarrow> 
config.DN [] \<notin> inv_set \<Longrightarrow> 
is_invariant pcp_instance inv_set" 
  unfolding is_invariant_def
  by simp

fun multi_step_pcp :: "pcp \<Rightarrow> config set \<Rightarrow> nat list \<Rightarrow> config set" where
  "multi_step_pcp _ c [] = c" |
  "multi_step_pcp ts c (i#s) = (multi_step_pcp ts (step_configs (ts!i) c) s)"

lemma multi_step_pcp_snoc:
  "multi_step_pcp ts C (ss @ [a]) = step_configs (ts!a) (multi_step_pcp ts C ss)"
  apply(induct ss arbitrary: a C) apply simp unfolding append_Cons unfolding multi_step_pcp.simps by simp

lemma all_resulting_conf_is_in_inv_1:
  fixes ts::pcp
  fixes inv::"config set"
  assumes "is_invariant ts inv"
  fixes i::"nat"
  assumes "i < length ts"
  shows "(multi_step_pcp ts {UP []} [i]) \<subseteq> inv"
proof -
  have "(ts ! i) \<in> set ts" using assms by auto
  then have "(step_config (ts ! i) (UP [])) \<subseteq> \<Union> ( ((\<lambda>t. step_config t (UP [])) ` (set ts)))"
    using assms by blast
  then have "(step_config (ts ! i) (UP [])) \<subseteq> (pcp_init_set ts)" by auto
  then show ?thesis using assms(1) is_invariant_def by auto
qed

lemma inv_closed_forward_pcp:
  fixes ts::pcp
  fixes inv
  assumes "is_invariant ts inv"
  fixes s::"config set"
  shows "s \<subseteq> inv \<Longrightarrow> (pcp_step_configs ts s) \<subseteq> inv"
proof -
  have A:"pcp_step_configs ts inv \<subseteq> inv" 
    using is_invariant_def assms by simp
  assume "s \<subseteq> inv"
  then have "pcp_step_configs ts s \<subseteq> pcp_step_configs ts inv" by auto
  then show "(pcp_step_configs ts s) \<subseteq> inv" using A by blast
qed

lemma step_configs_is_part_of_pcp_step_configs: "a < length ts \<Longrightarrow> step_configs (ts!a) c \<subseteq> pcp_step_configs ts c"
proof -
  assume "a < length ts"
  then show "step_configs (ts!a) c \<subseteq> pcp_step_configs ts c" using nth_mem by auto
qed

lemma all_resulting_conf_is_in_inv:
  fixes ts::pcp
  fixes inv::"config set"
  assumes "is_invariant ts inv"
  fixes s::"nat list"
  shows "all_less s (length ts) \<Longrightarrow> s\<noteq>[] \<Longrightarrow> (multi_step_pcp ts {UP []} s) \<subseteq> inv"
proof (induct s rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a ss)
  have AL: "a < length ts" using snoc by auto
  show ?case apply(cases "ss = []") using assms snoc is_invariant_def apply force proof -
    assume "ss \<noteq> []"
    then have IH:"multi_step_pcp ts {UP []} ss \<subseteq> inv" using snoc by auto
    then have "pcp_step_configs ts (multi_step_pcp ts {UP []} ss) \<subseteq> inv" using inv_closed_forward_pcp[OF assms IH] by blast
    then have "step_configs (ts!a) (multi_step_pcp ts {UP []} ss) \<subseteq> inv" using AL by fastforce
    then show ?thesis unfolding multi_step_pcp.simps using multi_step_pcp_snoc by blast
  qed
qed


fun diff_conf :: "string \<Rightarrow> string \<Rightarrow> config set" where
  "diff_conf up dn = (
    if(starts_with up dn) 
      then {UP (drop (length dn) up)}
      else (
        if(starts_with dn up)
        then {DN (drop (length up) dn)}
        else {}
      ))"

lemma diff_conf_starts_cases: obtains 
  (UP_STARTSWITH_DN) "starts_with up dn" |
  (DN_STARTSWITH_UP) "\<not> starts_with up dn \<and> starts_with dn up" |
  (NO_COMMON) "\<not> starts_with up dn \<and> \<not> starts_with dn up" 
  by auto

lemma starts_with_concat_diff:
  assumes "length a \<ge> length b" and "length a + length c \<ge> length b + length d"
  shows "drop (length (b@d)) (a@c) = drop (length d) ((drop (length b) a)@c)"
proof -
  show ?thesis by (simp add: add.commute assms(1))
qed

lemma starts_with_concat_diff_opp:
  assumes "length a \<ge> length b" and "length a + length c \<le> length b + length d"
  shows "drop (length (a@c)) (b@d) = drop (length ((drop (length b) a)@c)) d"
proof -
  show ?thesis using assms(1) by auto
qed

lemma take_decompose:
  assumes "length a \<ge> s" and "length a + length b \<ge> s + t" 
  shows "take (s + t) (a@c) = (take s a) @ (take t ((drop s a)@c))"
  by (simp add: add.commute assms(1) take_add)

lemma starts_with_concat:
  assumes "starts_with a b"
  shows "starts_with (a@c) (b@d) = starts_with ((drop (length b) a)@c) d"
proof (cases "starts_with ((drop (length b) a)@c) d")
  case True
  then show ?thesis using assms by (metis (no_types, lifting) assms(1) append.assoc append_eq_conv_conj starts_with_def)
next
  case F1:False
  then show ?thesis proof (cases "length (a@c) \<ge> length (b@d)")
    case True
    have "take (length (b@d)) (a@c) = (take (length b) a) @ (take (length d) ((drop (length b) a)@c) )"
      using take_decompose by (metis True assms(1) length_append nat_le_linear starts_with_def take_all_iff)
    then show ?thesis using F1 starts_with_def by (metis assms(1) same_append_eq)
  next
    case False
    then show ?thesis using starts_with_def F1 by (metis nat_le_linear take_all)
  qed
qed


lemma starts_with_concat_opp:
  assumes "starts_with a b"
  shows "starts_with (b@d) (a@c) = starts_with d ((drop (length b) a)@c)"
proof (cases "starts_with d ((drop (length b) a)@c)")
  case True
  then show ?thesis using assms starts_with_def by (metis (no_types, opaque_lifting) append.assoc append_eq_conv_conj)
next
  case F1:False
  then show ?thesis  using assms starts_with_def 
  proof (cases "length (b@d) \<ge> length (a@c)")
    case True
    have "(take (length b) a) @ (take (length ((drop (length b) a)@c)) d ) = take (length (a@c)) (b@d)"
      apply simp
      by (metis (no_types, lifting) Nat.add_diff_assoc2 add.commute assms nat_le_linear starts_with_def take_all_iff trans_le_add2)
    then show ?thesis using F1 starts_with_def 
      by (metis (no_types, opaque_lifting) append.assoc append_eq_conv_conj assms)
  next
    case False
    then show ?thesis using starts_with_def F1 by (metis nat_le_linear take_all)
  qed
qed


lemma starts_with_then_length_larger:
  assumes "starts_with a b"
  shows "length a \<ge> length b"
  by (metis assms nat_le_linear starts_with_def take_all_iff)

lemma diff_conf_step_iff:
  shows "diff_conf (p @ up) (q @ dn) = step_configs (up,dn) (diff_conf p q)"
proof(cases p q rule: diff_conf_starts_cases)
  case ORIG_UP: UP_STARTSWITH_DN

  then obtain orig_up_rem where ORIG_REM:"diff_conf p q = {UP orig_up_rem}" by simp
  then show ?thesis proof(cases "p @ up" "q @ dn" rule: diff_conf_starts_cases)
    case NEXT_UP: UP_STARTSWITH_DN

    then obtain next_up_rem where NEXT_REM:"diff_conf (p @ up) (q @ dn) = {UP next_up_rem}" by simp
    have A:"{UP next_up_rem} = step_config (up,dn) (UP orig_up_rem)" 
      unfolding step_config.simps using ORIG_UP NEXT_UP 
      by (metis NEXT_REM ORIG_REM config.inject(1) diff_conf.elims length_append starts_with_concat starts_with_concat_diff starts_with_then_length_larger the_elem_eq)
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  next
    case NEXT_DN: DN_STARTSWITH_UP
    then obtain next_dn_rem where NEXT_REM:"diff_conf (p @ up) (q @ dn) = {DN next_dn_rem}" by simp
    have A:"{DN next_dn_rem} = step_config (up,dn) (UP orig_up_rem)" 
      unfolding step_config.simps using ORIG_UP NEXT_DN 
      by (metis NEXT_REM ORIG_REM config.inject(1) diff_conf.elims length_append starts_with_concat starts_with_concat_diff_opp starts_with_concat_opp starts_with_then_length_larger the_elem_eq) 
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  next
    case NEXT_NO:NO_COMMON
    then have NEXT_REM:"diff_conf (p @ up) (q @ dn) = {}" by simp
    have A:"{} = step_config (up,dn) (UP orig_up_rem)" 
      unfolding step_config.simps using ORIG_UP NEXT_NO 
      using ORIG_REM starts_with_concat starts_with_concat_opp by auto
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  qed
next
  case ORIG_DN: DN_STARTSWITH_UP

  then obtain orig_dn_rem where ORIG_REM:"diff_conf p q = {DN orig_dn_rem}" by simp
  then show ?thesis proof(cases "p @ up" "q @ dn" rule: diff_conf_starts_cases)
    case NEXT_UP: UP_STARTSWITH_DN

    then obtain next_up_rem where NEXT_REM:"diff_conf (p @ up) (q @ dn) = {UP next_up_rem}" by simp
    have A:"{UP next_up_rem} = step_config (up,dn) (DN orig_dn_rem)"
      unfolding step_config.simps using ORIG_DN NEXT_UP
      by (metis NEXT_REM ORIG_REM config.inject(2) diff_conf.elims length_append starts_with_concat_diff_opp starts_with_concat_opp starts_with_then_length_larger the_elem_eq)
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  next
    case NEXT_DN: DN_STARTSWITH_UP
    then obtain next_dn_rem where NEXT_REM:"diff_conf (p @ up) (q @ dn) = {DN next_dn_rem}" by simp
    have A:"{DN next_dn_rem} = step_config (up,dn) (DN orig_dn_rem)" 
      unfolding step_config.simps using ORIG_DN NEXT_DN 
      by (metis NEXT_REM ORIG_REM config.inject(2) diff_conf.elims length_append singleton_inject starts_with_concat starts_with_concat_diff starts_with_concat_opp starts_with_then_length_larger)
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  next
    case NEXT_NO:NO_COMMON
    then have NEXT_REM:"diff_conf (p @ up) (q @ dn) = {}" by simp
    have A:"{} = step_config (up,dn) (DN orig_dn_rem)" 
      unfolding step_config.simps using ORIG_DN NEXT_NO 
      using ORIG_REM starts_with_concat starts_with_concat_opp by auto
    show ?thesis unfolding NEXT_REM ORIG_REM unfolding step_configs.simps using A by blast
  qed
next
  case NO_COMMON
  then have "diff_conf p q = {}" by simp
  then show ?thesis apply(cases "p @ up" "q @ dn" rule: diff_conf_starts_cases) 
    using NO_COMMON non_common_prefix_monotone apply blast 
    using NO_COMMON non_common_prefix_monotone apply blast by simp
qed
  

lemma multi_step_conf_eq':
  fixes ts::pcp
  fixes s::"nat list"
  assumes "all_less s (length ts)"
  shows "(diff_conf (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s)) = (multi_step_pcp ts {UP []} s)"
using assms proof (induct s rule: rev_induct)
  case Nil
  then show ?case by (simp add: starts_with_def)
next
  case (snoc a ss)
  then have AL:"a < length ts" by simp
  then have IH:"diff_conf (concatenate_tiles_seq_upper ts ss) (concatenate_tiles_seq_bottom ts ss) = multi_step_pcp ts {UP []} ss" using snoc by simp
  show ?case
    unfolding concatenate_tiles_seq_upper_snoc[of ts ss a] concatenate_tiles_seq_bottom_snoc[of ts ss a] 
    unfolding multi_step_pcp_snoc unfolding snoc(1)[symmetric] 
    using diff_conf_step_iff[of "concatenate_tiles_seq_upper ts ss" "fst(ts!a)" "concatenate_tiles_seq_bottom ts ss" "snd(ts!a)"]
    using IH by auto
qed

lemma multi_step_conf_eq: 
  fixes ts::pcp
  fixes s::"nat list"
  assumes "all_less s (length ts)"
  shows "multi_step_pcp ts {UP []} s = 
          diff_conf (concatenate_tiles_seq_upper ts s)  (concatenate_tiles_seq_bottom ts s)"
  using assms multi_step_conf_eq' by auto

lemma multi_step_conf_eq_sol: 
  fixes ts::pcp
  fixes s::"nat list"
  assumes "is_solution ts s"
  shows "(UP []) \<in> multi_step_pcp ts {UP []} s"
proof -
  have A:"multi_step_pcp ts {UP []} s= diff_conf (concatenate_tiles_seq_upper ts s)  (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def by auto
  have "(concatenate_tiles_seq_upper ts s) = (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def by auto
  then have "(UP []) \<in> diff_conf (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def starts_with_def by auto
  then show ?thesis using A by auto
qed

lemma no_solution_if_exists_invariant:
  fixes ts::pcp
  assumes "\<exists>inv. is_invariant ts inv"
  shows "\<not> have_solution ts"
proof (cases "have_solution ts")
case True
  then obtain ans where sol_cond:"is_solution ts ans" using have_solution_def by auto
  then have contain_emp: "(UP '''') \<in> multi_step_pcp ts {(UP '''')} ans" using multi_step_conf_eq_sol by auto
  have nonempty: "length ans > 0" using is_solution_def sol_cond by auto
  obtain inv where inv_cond:"is_invariant ts inv" using assms by auto
  have False
  proof -
    have "(multi_step_pcp ts {(UP '''')} ans) \<subseteq> inv" 
        using all_resulting_conf_is_in_inv nonempty inv_cond sol_cond is_solution_def by auto
    then have "(UP '''') \<in> inv" using contain_emp by auto
    then show ?thesis using inv_cond is_invariant_def by auto
  qed
  then show ?thesis by auto
next
  case False
qed


end