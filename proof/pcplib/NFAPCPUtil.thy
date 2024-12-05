theory NFAPCPUtil
  imports Main "NFA" "PCPDef.PCP" "PCPNFA"
begin


lemma bind_insert_iff[simp]: 
"Set.bind (insert a S) P = P a \<union> Set.bind S P"
  by auto

fun step_rel'::
  "(alphabet, 's1) NA \<Rightarrow> (alphabet, 's2) NA \<Rightarrow> ('s1 \<times> 's2 set) \<Rightarrow> ('s1 \<times> 's2 set) list" where
  "step_rel' A B (s, t) = 
    (map (\<lambda>sa. (sa, Set.bind t (set_step B C0)))) (step A C0 s) @
    (map (\<lambda>sa. (sa, Set.bind t (set_step B C1)))) (step A C1 s)"

lemma step_rel'_sanity[simp]:
  "step_rel A B (a,b) = step_rel' A B (a,b)"
  unfolding step_rel'.simps step_rel.simps
proof-
  show " List.bind (enum_class.enum) (\<lambda>c. map (\<lambda>ss. (ss, Set.bind b (set_step B c))) (step A c a)) =
    map (\<lambda>sa. (sa, Set.bind b (set_step B C0))) (step A C0 a) @
    map (\<lambda>sa. (sa, Set.bind b (set_step B C1))) (step A C1 a)"
    unfolding bind_def enum_alphabet_def by simp
qed

lemma [simp]: "{x. x = A \<or> P x} = insert A {x. P x}" by auto

lemma filter_insert_iff[simp]:
  "Set.filter P (insert a S) = (if P a then insert a (Set.filter P S) else Set.filter P S)"
  by auto

lemma filter_empty[simp]:
"Set.filter P {} = {}"
  by auto

declare image_Un[simp]
declare step_rel.simps [simp del]
declare exists_diff_rel.simps [simp del]
declare inv_cond.simps [simp del]

definition empty_aut::"(alphabet, nat) NA" where
  "empty_aut == NA [] (\<lambda>c s. []) []"

lemma empty_aut_sanity[simp]:
"lang empty_aut = {}"
  unfolding empty_aut_def lang_def
  by simp

lemma empty_aut_langconf_sanity[simp]:
"lang_autconf (autconfig.DN empty_aut) = {}"
"lang_autconf (autconfig.UP empty_aut) = {}"
  by simp_all


lemma notin_union:"A \<notin> B \<Longrightarrow> A \<notin> C \<Longrightarrow> A \<notin> B \<union> C" by auto
lemma not_accept_empty_simp:
"\<not>accept A [] \<Longrightarrow> config.DN [] \<notin> lang_autconf (autconfig.DN A)"
"\<not>accept A [] \<Longrightarrow> config.UP [] \<notin> lang_autconf (autconfig.UP A)"
"config.UP [] \<notin> lang_autconf (autconfig.DN A)"
"config.DN [] \<notin> lang_autconf (autconfig.UP A)"
  using lang_autconf_elem_iff_accept(2) apply blast 
  using lang_autconf_elem_iff_accept(1) apply blast
  by auto

lemma u_subset:"A\<subseteq>B\<union>{} \<Longrightarrow> B\<subseteq>C \<Longrightarrow> A \<subseteq> C"
  by auto

lemma u_subset_empty:"A\<subseteq>{} \<Longrightarrow> A \<subseteq> C"
  by auto
end