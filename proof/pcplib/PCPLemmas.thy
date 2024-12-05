theory PCPLemmas
  imports Main PCPDef.PCP
begin

instantiation alphabet :: enum begin
  definition "enum_alphabet == [C0, C1]"
  definition "enum_all_alphabet P == P C0 \<and> P C1"
definition "enum_ex_alphabet P == P C0 \<or> P C1"
instance proof (standard)
  show UNIV:"(UNIV::alphabet set) = set enum_class.enum"
    unfolding enum_alphabet_def apply(rule) using subset_UNIV 
    using alphabet.exhaust apply auto[1] by simp
  show "distinct (enum_class.enum::alphabet list)" unfolding enum_alphabet_def by simp
  show "\<And>P. enum_class.enum_all P = Ball (UNIV::alphabet set) P"
    unfolding enum_all_alphabet_def UNIV enum_alphabet_def by simp
  show "\<And>P. enum_class.enum_ex P = Bex (UNIV::alphabet set) P"
    unfolding enum_ex_alphabet_def UNIV enum_alphabet_def by simp
qed
end

fun reverse_tile :: "tile \<Rightarrow> tile" where
"reverse_tile (s1, s2) = ((rev s1), (rev s2))"

fun reverse_pcp :: "pcp => pcp" where
"reverse_pcp ts = (map reverse_tile ts)"

value "(reverse_tile (([C0,C1,C0,C0], [C1,C1,C0])))"
value "reverse_pcp [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C1,C0,C0], [C1,C0])]"


fun concatenate_strings_seq :: "alphabet list list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_strings_seq _ [] = ''''" |
"concatenate_strings_seq ss (i # is) = (ss ! i)@(concatenate_strings_seq ss is)"

lemma concatenate_strings_seq_m:
  "(concatenate_strings_seq ss is)@(concatenate_strings_seq ss js) = concatenate_strings_seq ss (is@js)"
  apply(induct "is") apply simp by simp

fun concatenate_tiles_seq_upper :: "tile list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_tiles_seq_upper _ [] = ''''" |
"concatenate_tiles_seq_upper ts (i # is) = 
     (fst (ts ! i))@(concatenate_tiles_seq_upper ts is)"

fun concatenate_tiles_seq_bottom :: "tile list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_tiles_seq_bottom _ [] = []" |
"concatenate_tiles_seq_bottom ts (i # is) = (snd (ts ! i))@(concatenate_tiles_seq_bottom ts is)"

lemma [simp]:"concat_top_strings = concatenate_tiles_seq_upper"
  apply(rule, rule, induct_tac xa) apply simp by simp

lemma [simp]:"concat_bottom_strings = concatenate_tiles_seq_bottom"
  apply(rule, rule, induct_tac xa) apply simp by simp

value "concatenate_tiles_seq_upper [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C0,C0], [C1,C1,C0])] [1,0,0,0]"

lemma concatenate_tiles_seq_upper_eq:
  shows "all_less is (length ts) \<Longrightarrow> concatenate_tiles_seq_upper ts is = concatenate_strings_seq (map fst ts) is"
proof(induct "is")
  case Nil
  then show ?case by auto
next
  case (Cons a "is")
  then have "(map fst ts) ! a = fst(ts !a)" by auto
  then show ?case using Cons.hyps Cons.prems by auto
qed

fun swap_tile :: "tile \<Rightarrow> tile" where
  "swap_tile (a,b) = (b,a)"

fun swap_pcp :: "pcp \<Rightarrow> pcp" where
"swap_pcp ts = map swap_tile ts"

lemma swap_swap_pcp:"swap_pcp (swap_pcp ts) = ts"
  apply(induct ts) apply simp by auto

value "swap_pcp [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C1], [C0])]"




lemma concatenate_tiles_seq_bottom_eq:
  shows "all_less is (length ts) \<Longrightarrow> concatenate_tiles_seq_bottom ts is = concatenate_strings_seq (map snd ts) is"
proof(induct "is")
  case Nil
  then show ?case by auto
next
  case (Cons a "is")
  then have "(map snd ts) ! a = snd(ts !a)" by auto
  then show ?case using Cons.hyps Cons.prems by auto
qed

lemma map_swap_tile: "\<forall>i < length ts. (map swap_tile ts) ! i = swap_tile (ts ! i)"
  using nth_map [of _ ts reverse_tile] by auto

lemma concat_swap_eq: 
  fixes s::"nat list"
  shows "all_less s (length ts) \<Longrightarrow> concatenate_tiles_seq_bottom ts s = concatenate_tiles_seq_upper (swap_pcp ts) s"
proof (induct s)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  then have IH: "concatenate_tiles_seq_bottom ts s = concatenate_tiles_seq_upper (swap_pcp ts) s" by auto
  then have "concatenate_tiles_seq_upper (swap_pcp ts) (a#s) = 
    (fst(((swap_pcp ts)!a)))@(concatenate_tiles_seq_upper (swap_pcp ts) s)" using map_swap_tile by auto
  then have K:"concatenate_tiles_seq_upper (swap_pcp ts) (a#s) = 
    (fst(swap_tile (ts!a)))@(concatenate_tiles_seq_upper (swap_pcp ts) s)" using map_swap_tile Cons by auto
  have "fst (swap_tile (ts ! a)) = snd (ts ! a)" using Cons 
    by (metis fst_conv prod.collapse swap_tile.simps)
  then show ?case using Cons unfolding concatenate_tiles_seq_bottom.simps IH K by auto
qed

lemma concat_swap_eq_rev:
  assumes "all_less s (length ts)"
  shows "concatenate_tiles_seq_upper ts s = concatenate_tiles_seq_bottom (swap_pcp ts) s"
proof -
  have "concatenate_tiles_seq_upper (swap_pcp (swap_pcp ts)) s = concatenate_tiles_seq_bottom (swap_pcp ts) s"
    using concat_swap_eq using assms by force
  then show?thesis using swap_swap_pcp by simp
qed

definition is_solution' :: "pcp \<Rightarrow> nat list \<Rightarrow> bool" where
"is_solution' p l \<equiv>  all_less l (length p) \<and> (length l) > 0 \<and> (concatenate_tiles_seq_upper p l) = (concatenate_tiles_seq_bottom p l)"

lemma [simp]:"is_solution=is_solution'"
  apply(rule,rule) unfolding is_solution_def is_solution'_def by auto

value "is_solution [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])] [0,2,0,0,2,1,1]"
value "is_solution (reverse_pcp [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])]) (rev [0,2,0,0,2,1,1])"

value "let ts= [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])] in let is=[0,2,1] in 
  (rev (concatenate_tiles_seq_upper ts is) = (concatenate_tiles_seq_upper (reverse_pcp ts) (rev is)))"

lemma concatenate_tiles_seq_upper_snoc: "concatenate_tiles_seq_upper ts (a @ [b]) = (concatenate_tiles_seq_upper ts a)@(fst (ts ! b))"
  apply (induct "a" arbitrary: b) apply simp unfolding append_Cons by simp

lemma concatenate_tiles_seq_bottom_snoc: "concatenate_tiles_seq_bottom ts (a @ [b]) = (concatenate_tiles_seq_bottom ts a)@(snd (ts ! b))"
  apply (induct "a" arbitrary: b) apply simp unfolding append_Cons by simp

value "hd ([33,3,4] :: nat list)"

lemma map_reverse_tile: "\<forall>i < length ts. (map reverse_tile ts) ! i = reverse_tile (ts ! i)"
  using nth_map [of _ ts reverse_tile] by auto

lemma C: "\<forall>i < length ts. (reverse_pcp ts) ! i = reverse_tile (ts ! i)"
  using map_reverse_tile by auto

lemma swap_reverse:  "(swap_pcp (reverse_pcp ts)) = reverse_pcp(swap_pcp ts)"
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case
    by (metis list.simps(9) prod.exhaust_sel reverse_pcp.elims reverse_tile.simps swap_pcp.elims swap_tile.simps)
qed
lemma reverse_u: 
  fixes ts::pcp
  shows "all_less ans (length ts) \<Longrightarrow>
    rev (concatenate_tiles_seq_upper ts ans) = concatenate_tiles_seq_upper (reverse_pcp ts) (rev ans)"
proof (induct ans rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons i rest)
  have PREM: "all_less rest (length ts)" using Cons by auto
  have IPREM: "i < (length ts)" using Cons by simp
  have B: "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev rest))@(fst (reverse_pcp ts ! i)) = (concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest)))" 
    by (simp add: concatenate_tiles_seq_upper_snoc)
  then have "... = (concatenate_tiles_seq_upper (reverse_pcp ts) (rev rest))@(rev (fst (ts ! i)))" 
    using C IPREM by (metis old.prod.exhaust prod.sel(1) reverse_tile.simps)
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) = rev(concatenate_tiles_seq_upper ts rest)@rev (fst (ts ! i))"using Cons B  by auto
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) = rev((fst (ts ! i))@(concatenate_tiles_seq_upper ts rest))" by auto
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) = rev(concatenate_tiles_seq_upper ts (i # rest))" 
    using B Cons.hyps PREM append_same_eq concatenate_tiles_seq_upper_snoc concatenate_tiles_seq_upper.simps(2) rev.simps(2) rev_append by auto
  then show ?case by auto
qed

lemma swap_pcp_length_identiy: "length (swap_pcp ts) = length ts"
  apply (induction ts)
   apply (simp)
  apply(auto)
  done

lemma rev_pcp_length_identiy: "length (reverse_pcp ts) = length ts"
   by auto

lemma rev_all_less: "all_less ans (length ts) = all_less (rev ans) (length ts)"
  by auto

lemma reverse_d: 
  fixes ts::pcp
  shows "all_less ans (length ts) \<Longrightarrow>
  rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)"
proof -
  assume ASM:"all_less ans (length ts)"
  then show "rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)"
  proof -
    have A:"concatenate_tiles_seq_bottom ts ans = concatenate_tiles_seq_upper (swap_pcp ts) ans" using ASM concat_swap_eq by auto
    then have "rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)" 
      using reverse_u swap_reverse swap_pcp_length_identiy concat_swap_eq ASM 
      by (metis rev_all_less rev_pcp_length_identiy)
    then show ?thesis by auto
  qed
qed

lemma reverse_equivalence: 
  fixes ts::pcp
  assumes "all_less ans (length ts)"
  shows "is_solution ts ans = is_solution (reverse_pcp ts) (rev ans)"
proof -
  have "all_less (rev ans) (length ts)" using assms by auto

  have "is_solution (reverse_pcp ts) (rev ans) = ((all_less (rev ans) (length ts)) \<and> (length ans) > 0 \<and>  concatenate_tiles_seq_upper (reverse_pcp ts) (rev ans) = (concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)))" 
      using rev_pcp_length_identiy is_solution_def assms by auto
  then have "is_solution (reverse_pcp ts) (rev ans) = ((all_less (rev ans) (length ts))\<and> (length ans) > 0 \<and> rev (concatenate_tiles_seq_upper ts ans) = rev (concatenate_tiles_seq_bottom ts ans))" 
    using swap_pcp_length_identiy rev_pcp_length_identiy reverse_u reverse_d assms by auto
  then have "is_solution (reverse_pcp ts) (rev ans) = ((all_less (rev ans) (length ts))\<and> (length ans) > 0 \<and> rev (concatenate_tiles_seq_upper ts ans) = rev (concatenate_tiles_seq_bottom ts ans))" 
      using swap_pcp_length_identiy rev_pcp_length_identiy reverse_u reverse_d assms by fastforce
  then show ?thesis using is_solution_def assms reverse_d reverse_u by auto
qed


lemma rev_rev_tile_ident[simp]: "reverse_tile(reverse_tile t) = t"
proof (cases t)
  case (Pair a b)
  then show ?thesis using rev_rev_ident by auto
qed

lemma rev_rev_pcp_ident[simp]: "reverse_pcp(reverse_pcp ts) = ts"
proof simp
  have "reverse_tile \<circ> reverse_tile = id" by auto
  then have "(map (reverse_tile \<circ> reverse_tile)) = (map id)" by auto
  then show "map (reverse_tile \<circ> reverse_tile) ts = ts" by auto
qed

lemma reverse_answer_existance_partial:"have_solution ts \<Longrightarrow> have_solution (reverse_pcp ts)"
proof - 
  assume ASM: "have_solution ts"
  then show ?thesis 
  proof -
    obtain ans where ans_cond:"is_solution ts ans" using have_solution_def ASM by auto
    then have A:"all_less ans (length ts)" using ASM is_solution_def by auto
    then have "all_less (rev ans) (length (reverse_pcp ts))" using ASM rev_pcp_length_identiy is_solution_def by auto
    then have "is_solution (reverse_pcp ts) (rev ans)" 
      using reverse_equivalence A ans_cond by blast
    then show "have_solution (reverse_pcp ts)" using have_solution_def by auto
  qed
qed

lemma reverse_answer_existance: "have_solution ts = have_solution (reverse_pcp ts)"
proof -
  have LR: "have_solution ts \<Longrightarrow> have_solution (reverse_pcp ts)" using reverse_answer_existance_partial by auto
  have RL: "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution ts"
  proof -
    have "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution (reverse_pcp(reverse_pcp ts))"
      using reverse_answer_existance_partial by force
    then show "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution ts"
      using rev_rev_pcp_ident by force
  qed
  then show ?thesis using LR RL by auto
qed

end
