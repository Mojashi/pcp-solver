theory PCP
  imports Main
begin

datatype alphabet = C0 | C1

type_synonym string = "alphabet list"
type_synonym tile = "string \<times> string"
type_synonym pcp = "tile list"

fun concat_top_strings::"pcp \<Rightarrow> nat list \<Rightarrow> string" where
  "concat_top_strings ts s = List.bind s (\<lambda>i. fst (ts!i))"

fun concat_bottom_strings::"pcp \<Rightarrow> nat list \<Rightarrow> string" where
  "concat_bottom_strings ts s = List.bind s (\<lambda>i. snd (ts!i))"

fun all_less :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "all_less ss u = list_all (\<lambda>x. x < u) ss"

definition is_solution :: "pcp \<Rightarrow> nat list \<Rightarrow> bool" where
"is_solution p l \<equiv>  all_less l (length p) \<and> length l > 0 \<and> concat_top_strings p l = concat_bottom_strings p l"

definition have_solution:: "pcp \<Rightarrow> bool" where
  "have_solution ts \<equiv> \<exists>sol. is_solution ts sol"

end
