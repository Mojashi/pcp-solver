theory PCPNFA
  imports Main PCPDef.PCP PCPTrans NFA
begin

datatype ('state) autconfig = UP "(alphabet,'state) NFA.NA" | DN "(alphabet,'state) NFA.NA"

fun underlying_aut::"('state) autconfig \<Rightarrow> (alphabet,'state) NFA.NA" where
  "underlying_aut (DN a) = a" |
  "underlying_aut (UP a) = a"

lemma config_set_eq:
  "config.DN ` a \<subseteq> config.DN ` b \<longleftrightarrow> a \<subseteq> b"
  "config.UP ` a \<subseteq> config.UP ` b \<longleftrightarrow> a \<subseteq> b"
   apply blast by blast

fun lang_autconf::"'s autconfig \<Rightarrow> PCPTrans.config set" where
  "lang_autconf (UP a) = PCPTrans.UP ` (lang a)"|
  "lang_autconf (DN a) = PCPTrans.DN ` (lang a)"


lemma config_set_accept_eq:
  "config.DN a \<in> PCPTrans.DN ` (lang b) \<longleftrightarrow> accept b a" 
  "config.UP a \<in> PCPTrans.UP ` (lang b) \<longleftrightarrow> accept b a"
  unfolding lang_def apply blast by blast

fun split::"alphabet list \<Rightarrow> nat \<Rightarrow> (alphabet list)\<times>(alphabet list)" where
  "split w i = (take i w, drop i w)"

fun enumerate_splits_all::"PCP.string \<Rightarrow> (PCP.string\<times>PCP.string) set" where
  "enumerate_splits_all [] = {([], [])}" |
  "enumerate_splits_all (x#xs) = insert ([], x#xs) ((\<lambda> (f,s). (x#f, s)) ` (enumerate_splits_all xs))"

fun enumerate_splits::"PCP.string \<Rightarrow> (PCP.string\<times>PCP.string) set" where
  "enumerate_splits xs = (enumerate_splits_all xs) - {(xs, [])}"

fun enumerate_splits'::"PCP.string \<Rightarrow> (PCP.string\<times>PCP.string) set" where
  "enumerate_splits' [] = {}" |
  "enumerate_splits' (x#xs) = insert ([], x#xs) ((\<lambda> (f,s). (x#f, s)) ` (enumerate_splits' xs))"

lemma enumerate_splits'_eq:
  "enumerate_splits = enumerate_splits'"
proof -
  have "\<And>x. enumerate_splits' x = enumerate_splits x" proof -
    fix x
    show "enumerate_splits' x = enumerate_splits x" apply(induct x) apply simp by force
  qed
  then show ?thesis by blast
qed

lemma splits_is_splits2:
  shows "(s@p = dn) \<longleftrightarrow> (s,p)\<in>(enumerate_splits_all dn)"
proof
  show "(s, p) \<in> enumerate_splits_all dn \<Longrightarrow> s @ p = dn" 
  proof (induct dn arbitrary: s p)
    case Nil
    then show ?case by auto
  next
    case (Cons a dn)
    then have IH: "(s, p) \<in> enumerate_splits_all dn \<Longrightarrow> s @ p = dn" by auto
    assume "(s, p) \<in> enumerate_splits_all (a#dn)"
    then have C:"(s, p) = ([], a#dn) \<or> (s, p) \<in> ((\<lambda> (f,s). (a#f, s)) ` (enumerate_splits_all dn))"
      by auto
    have CASE2: "(s, p) \<in> ((\<lambda> (f,s). (a#f, s)) ` (enumerate_splits_all dn)) \<Longrightarrow> s @ p = a#dn"
    proof -
      assume "(s, p) \<in> ((\<lambda> (f,s). (a#f, s)) ` (enumerate_splits_all dn))"
      then obtain ss where "((\<lambda> (f,s). (a#f, s)) (ss,p) = (s,p)) \<and> (ss, p) \<in> enumerate_splits_all dn" 
        using IH by force
      then show "s @ p = a#dn" using Cons.hyps by force
    qed
    then show "s @ p = a#dn" using local.C by blast
  qed
  show "s @ p = dn \<Longrightarrow> (s, p) \<in> enumerate_splits_all dn"
  proof (induct dn arbitrary: s p)
    case Nil
    then show ?case by auto
  next
    case (Cons a dn)
    then have IH: "s @ p = dn \<Longrightarrow> (s, p) \<in> enumerate_splits_all dn" by auto
    assume ASM:"s @ p = (a#dn)"
    then show "(s, p) \<in> enumerate_splits_all (a#dn)" 
    proof (cases "s = []")
      case True
      then have "p = a#dn" using ASM by auto
      then show ?thesis by (simp add: True)
    next
      case False
      then obtain ss where "a#ss = s" using ASM by (metis Cons_eq_append_conv)
      then have "ss@p = dn" using ASM by auto 
      then have "(ss, p) \<in> enumerate_splits_all dn" using IH by (simp add: Cons.hyps)
      then show "(s, p) \<in> enumerate_splits_all (a#dn)" using \<open>a # ss = s\<close> by force
    qed
  qed
qed


lemma splits_is_splits:
  shows "(s@p = dn \<and> p \<noteq> []) \<longleftrightarrow> (s,p)\<in>(enumerate_splits dn)"
  by (metis Diff_iff append.right_neutral enumerate_splits.simps insertI1 old.prod.inject singletonD splits_is_splits2)


fun step_autconf_tile::"'s autconfig \<Rightarrow> PCP.tile \<Rightarrow> ('s AppendWordState autconfig \<times> (PCPTrans.config set))" where
  "step_autconf_tile (UP a) (up,dn) = (
    (UP (pref_quotient (append_word a up) dn)),
    PCPTrans.DN`((\<lambda> (s,p).  (drop (length up) p)) ` (Set.filter (\<lambda>(s,p). accept a s \<and> starts_with p up) (enumerate_splits dn)))
  )" |
  "step_autconf_tile (DN a) (up,dn) = (
    (DN (pref_quotient (append_word a dn) up)),
    PCPTrans.UP`((\<lambda> (s,p).  (drop (length dn) p)) ` (Set.filter (\<lambda>(s,p). accept a s \<and> starts_with p dn) (enumerate_splits_all up)))
  )"


lemma step_autconf_tile_configs_simp:
  "snd (step_autconf_tile (DN a) (up, dn)) \<subseteq> S \<longleftrightarrow> 
  (\<forall>s p. (s,p)\<in>(enumerate_splits_all up) \<longrightarrow> (accept a s \<and> starts_with p dn) \<longrightarrow> (PCPTrans.UP (drop (length dn) p)) \<in> S)"
  "snd (step_autconf_tile (UP a) (up, dn)) \<subseteq> S \<longleftrightarrow> 
  (\<forall>s p. (s,p)\<in>(enumerate_splits dn) \<longrightarrow> (accept a s \<and> starts_with p up) \<longrightarrow> (PCPTrans.DN (drop (length up) p)) \<in> S)"
  apply fastforce by fastforce


fun step_autconf::"'s autconfig \<Rightarrow> PCP.pcp \<Rightarrow> (('s AppendWordState autconfig set) \<times> (PCPTrans.config set))" where
  "step_autconf a ts = (
    let as = step_autconf_tile a ` (set ts) in 
    (fst ` as, \<Union>(snd ` as))
  )"


lemma pref_dn_append_up_lang[simp]:
  "{s |s. dn@s \<in> {s'@up |s'. s' \<in> lang a}} \<subseteq> lang (pref_quotient (append_word a up) dn)"
proof -
  have A:"{s |s. (dn@s) \<in> lang (append_word a up)} \<subseteq> lang (pref_quotient (append_word a up) dn)"
    using pref_quotient_sanity_1 by metis
  have B:"{s@up |s. s \<in> lang a} \<subseteq> lang (append_word a up)"
    by (metis append_word_sanity_1)
  then show ?thesis using A B by blast
qed

lemma step_autconf_tile_eq_up:
  fixes t::PCP.tile
  fixes a::"'s autconfig"
  assumes "(up,dn) = t"
  assumes "(nex, confs) = step_autconf_tile a t"
  assumes "(PCPTrans.UP c) \<in> (lang_autconf a)"
  shows "step_config t (PCPTrans.UP c) \<subseteq> (lang_autconf nex) \<union> confs"
proof -
  have "\<exists>a'. UP a' = a"  proof (cases a)
    case (UP x1)
    then have "(UP x1) = a" by auto
    then show ?thesis by auto
  next
    case (DN x2)
    then have False using assms(3) by auto
    then show ?thesis by simp
  qed
  then obtain a' where "UP a' = a" by auto
  then have NEX:"nex = (UP (pref_quotient (append_word a' up) dn))" using assms by auto
  have "\<forall>c'. c' \<in> (step_config t (PCPTrans.UP c)) \<longrightarrow> c' \<in> (lang_autconf nex) \<union> confs" 
  proof (rule allI, rule impI) 
    fix c'
    assume CP:"c' \<in> (step_config t (PCPTrans.UP c))"
    then have stepped_cs: "step_config t (PCPTrans.UP c) = {c'}" using step_config_is_deterministic by auto
    show "c' \<in> (lang_autconf nex) \<union> confs"
    proof (cases c')
      case (UP x1)
      have LANG_NEX:"PCPTrans.UP ` {s |s. dn@s \<in> {s'@up |s'. s' \<in> lang a'}} \<subseteq> lang_autconf nex" 
        using pref_dn_append_up_lang NEX lang_autconf.simps by blast
      then have "dn@x1 = c@up"
        using step_configs_upper_str by (metis CP UP assms(1))
      then have "c' \<in> lang_autconf nex" 
        using LANG_NEX UP \<open>autconfig.UP a' = a\<close> assms(3) config.inject(1) mem_Collect_eq setcompr_eq_image by force
      then show ?thesis by auto
    next
      case (DN x2)
      then have "dn=c@up@x2"
        using step_configs_upper_to_lower_str CP using assms(1) by auto
      then have "(c,up@x2) \<in> enumerate_splits dn" 
        using splits_is_splits 
        by (metis DN append_is_Nil_conv assms(1) config.distinct(1) insert_iff singletonD step_config.simps(1) stepped_cs)
      have "starts_with (up@x2) up" using starts_with_def by auto
      have "c\<in>lang a'" using assms(3) 
        using \<open>autconfig.UP a' = a\<close> by fastforce
      then have "accept a' c" using lang_def by blast
      then have "(c,up@x2) \<in> Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p up) (enumerate_splits dn)"
          using \<open>(c, up @ x2) \<in> enumerate_splits dn\<close> \<open>starts_with (up @ x2) up\<close> by force
      then have "x2 \<in> ((\<lambda> (s,p). (drop (length up) p)) ` (Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p up) (enumerate_splits dn)))"
        using splits_is_splits step_configs_upper_to_lower_str CP DN 
        by (metis (no_types, lifting) append_eq_conv_conj pair_imageI)
      then have "confs = PCPTrans.DN ` ((\<lambda> (s,p). (drop (length up) p)) ` (Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p up) (enumerate_splits dn)))"
        using \<open>autconfig.UP a' = a\<close> assms(1) assms(2) step_autconf_tile.simps(1) 
        by (metis snd_conv)
      then have "PCPTrans.DN x2 \<in> confs" 
        using \<open>x2 \<in> (\<lambda>(s, p). drop (length up) p) ` Set.filter (\<lambda>(s, p). accept a' s \<and> starts_with p up) (enumerate_splits dn)\<close> by blast
      then show ?thesis by (simp add: DN)
    qed
  qed
  then show ?thesis by auto
qed


lemma step_autconf_tile_eq_dn:
  fixes t::PCP.tile
  fixes a::"'s autconfig"
  assumes "(up,dn) = t"
  assumes "(nex, confs) = step_autconf_tile a t"
  assumes "(PCPTrans.DN c) \<in> (lang_autconf a)"
  shows "step_config t (PCPTrans.DN c) \<subseteq> (lang_autconf nex) \<union> confs"
proof -
  have "\<exists>a'. DN a' = a"  proof (cases a)
    case (UP x1)
    then have False using assms(3) by auto
    then show ?thesis by simp
  next
    case (DN x2)
    then have "(DN x2) = a" by auto
    then show ?thesis by auto
  qed
  then obtain a' where "DN a' = a" by auto
  then have NEX:"nex = (DN (pref_quotient (append_word a' dn) up))" using assms by auto
  have "\<forall>c'. c' \<in> (step_config t (PCPTrans.DN c)) \<longrightarrow> c' \<in> (lang_autconf nex) \<union> confs" 
  proof (rule allI, rule impI) 
    fix c'
    assume CP:"c' \<in> (step_config t (PCPTrans.DN c))"
    then have stepped_cs: "step_config t (PCPTrans.DN c) = {c'}" using step_config_is_deterministic by auto
    show "c' \<in> (lang_autconf nex) \<union> confs"
    proof (cases c')
      case (DN x1)
      have LANG_NEX:"PCPTrans.DN ` {s |s p. up@s \<in> {s'@dn |s'. s' \<in> lang a'}} \<subseteq> lang_autconf nex"
        using pref_dn_append_up_lang NEX by fastforce
      have "up@x1 = c@dn"
        using step_configs_lower_str by (metis CP DN assms(1))
      then have "c' \<in> lang_autconf nex" 
        using LANG_NEX DN \<open>autconfig.DN a' = a\<close> assms(3) config.inject(2) mem_Collect_eq setcompr_eq_image by force
      then show ?thesis by auto
    next
      case (UP x2)
      then have "up=c@dn@x2"
        using step_configs_lower_to_upper_str CP using assms(1) by auto
      then have "(c,dn@x2) \<in> enumerate_splits_all up" 
        using splits_is_splits2[of c "dn@x2" up] by auto
      have "starts_with (dn@x2) dn" using starts_with_def by auto
      have "c\<in>lang a'" using assms(3) 
        using \<open>autconfig.DN a' = a\<close> by fastforce
      then have "accept a' c" using lang_def by blast
      then have "(c,dn@x2) \<in> Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p dn) (enumerate_splits_all up)"
          using \<open>(c, dn @ x2) \<in> enumerate_splits_all up\<close> \<open>starts_with (dn @ x2) dn\<close> by force
      then have "x2 \<in> ((\<lambda> (s,p). (drop (length dn) p)) ` (Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p dn) (enumerate_splits_all up)))"
        using splits_is_splits step_configs_lower_to_upper_str CP UP 
        by (metis (no_types, lifting) append_eq_conv_conj pair_imageI)
      then have "confs = PCPTrans.UP ` ((\<lambda> (s,p). (drop (length dn) p)) ` (Set.filter (\<lambda>(s,p). accept a' s \<and> starts_with p dn) (enumerate_splits_all up)))"
        using \<open>autconfig.DN a' = a\<close> assms(1) assms(2) step_autconf_tile.simps(2) by force
      then have "PCPTrans.UP x2 \<in> confs" 
        using \<open>x2 \<in> (\<lambda>(s, p). drop (length dn) p) ` Set.filter (\<lambda>(s, p). accept a' s \<and> starts_with p dn) (enumerate_splits_all up)\<close> by blast
      then show ?thesis by (simp add: UP)
    qed
  qed
  then show ?thesis by auto
qed
  
lemma step_autconf_tile_eq:
  fixes t::PCP.tile
  fixes a::"'s autconfig"
  assumes "(nex, confs) = step_autconf_tile a t"
  shows "step_configs t (lang_autconf a) \<subseteq> ((lang_autconf nex) \<union> confs)"
proof (cases a)
case (UP x1)
  then have "\<forall> c \<in> lang x1. step_config t (PCPTrans.UP c) \<subseteq> (lang_autconf nex) \<union> confs"
        using step_autconf_tile_eq_up
        by (metis assms image_eqI lang_autconf.simps(1) prod.collapse)
      then show ?thesis using UP by auto
next
case (DN x1)
  then have "\<forall> c \<in> lang x1. step_config t (PCPTrans.DN c) \<subseteq> (lang_autconf nex) \<union> confs"
        using step_autconf_tile_eq_dn[of "fst t" "snd t" t nex confs a]
        using Collect_cong assms by auto
  then show ?thesis using DN by auto
qed


theorem step_autconf_tile_eq_l:
  fixes t::PCP.tile
  fixes a::"'s autconfig"
  assumes "lang_autconf (fst (step_autconf_tile a t)) = nex_lang" 
    and "snd (step_autconf_tile a t) = nex_confs"
  shows "step_configs t (lang_autconf a) \<subseteq> nex_lang \<union> nex_confs"
proof (cases "step_autconf_tile a t")
  case (Pair au b)
  then show ?thesis using step_autconf_tile_eq[of au nex_confs a t] 
    using assms(1) assms(2) by auto
qed
  
theorem step_autconf_eq:
  fixes ts::PCP.pcp
  fixes a::"'s autconfig"
  assumes "(nex_auts, confs) = step_autconf a ts"
  shows "PCPTrans.pcp_step_configs ts (lang_autconf a) \<subseteq> (\<Union>(lang_autconf ` nex_auts) \<union> confs)"
proof -
  have B:"nex_auts = fst ` (step_autconf_tile a ` (set ts))" using assms by auto
  have "confs = \<Union> (snd ` (step_autconf_tile a ` (set ts)))" using assms by auto
  then have A:"\<forall>t\<in>(set ts). snd(step_autconf_tile a t) \<subseteq> confs" by auto
  have "\<forall>t\<in>(set ts). (step_configs t (lang_autconf a) \<subseteq> ((lang_autconf (fst(step_autconf_tile a t))) \<union> (snd(step_autconf_tile a t))))"
    using step_autconf_tile_eq using prod.collapse by blast
  then have "\<forall>t\<in>(set ts). (step_configs t (lang_autconf a) \<subseteq> ((lang_autconf (fst(step_autconf_tile a t))) \<union> confs))"
    using A by blast
  then have "\<forall>t\<in>(set ts). (step_configs t (lang_autconf a) \<subseteq> (\<Union>(lang_autconf ` nex_auts) \<union> confs))"
    using B by auto
  then show ?thesis by auto
qed

lemma union_langautconf:
"lang_autconf (autconfig.UP (NFA.union A B)) = lang_autconf (autconfig.UP A) \<union> lang_autconf (autconfig.UP B)"
"lang_autconf (autconfig.DN (NFA.union A B)) = lang_autconf (autconfig.DN A) \<union> lang_autconf (autconfig.DN B)"
  using union_sanity[of A B]
  by auto


lemma fst_step_autconf_insert:"fst (step_autconf conf (t#r)) = insert (fst (step_autconf_tile conf t)) (fst (step_autconf conf r))"
  by auto

lemma fst_step_autconf_empty:"fst (step_autconf conf []) = {}"
  by auto

lemma snd_step_autconf_insert:"snd (step_autconf conf (t#r)) = (snd (step_autconf_tile conf t)) \<union> (snd (step_autconf conf r))"
  by auto

lemma snd_step_autconf_empty:"snd (step_autconf conf []) = {}"
  by auto

lemma lang_autconf_elem_iff_accept:
"PCPTrans.UP s \<in> lang_autconf (autconfig.UP A) \<longleftrightarrow> accept A s"
"PCPTrans.DN s \<in> lang_autconf (autconfig.DN A) \<longleftrightarrow> accept A s"
  using lang_def by auto


end