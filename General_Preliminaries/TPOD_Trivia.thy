theory TPOD_Trivia
  imports 
    "Bounded_Deducibility_Security.Trivia"
    More_LazyLists.List_Filtermap
    (* TODO: I have renamed Relative_Security.Trivia \<Rightarrow> Relative_Security.RS_Trivia to avoid conflict *)
    Relative_Security.RS_Trivia
begin

\<comment> \<open>These are just abbreviations so will not impact proofs.\<close>
no_notation Trivia.Rcons (infix "##" 70)
no_notation Trivia.lmember ("(_/ \<in>\<in> _)" [50, 51] 50)

lemma length_filtermap_eq: \<open>length (filtermap pred func1 xs) = length (filtermap pred func2 xs)\<close>
proof (induct xs)
  fix a xs
  assume IH: "length (filtermap pred func1 xs) = length (filtermap pred func2 xs)"
    thus "length (filtermap pred func1 (a # xs)) = length (filtermap pred func2 (a # xs))"
    by (cases \<open>pred a\<close>, simp_all)
qed simp

lemma ball_inE:
  assumes major: "\<forall>x\<in>S. P x" and "x\<in>S"
      and minor: "P x \<Longrightarrow> Q"
    shows Q
  using assms by blast

abbreviation \<open>unzipL \<equiv> map fst\<close>
abbreviation \<open>unzipR \<equiv> map snd\<close>

lemmas hd_Cons = List.list.sel(1)

lemma Collect_eq: \<open>{s. P s} = {s. Q s} \<longleftrightarrow> (\<forall>s. P s \<longleftrightarrow> Q s)\<close>
  by blast

lemma list_all_True[simp]: "list_all (\<lambda>_. True) tr"
  using list.pred_True by metis

lemma measure_induct4[case_names IH]:
fixes meas :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> nat"
assumes "\<And>x1 x2 x3 x4. (\<And>y1 y2 y3 y4. meas y1 y2 y3 y4 < meas x1 x2 x3 x4 \<Longrightarrow> S y1 y2 y3 y4) \<Longrightarrow> S x1 x2 x3 x4"
shows "S x1 x2 x3 x4"
proof-
  let ?m = "\<lambda> x1x2 x3x4. meas (fst x1x2) (snd x1x2) (fst x3x4) (snd x3x4)" let ?S = "\<lambda> x1x2 x3x4. S (fst x1x2) (snd x1x2) (fst x3x4) (snd x3x4)"
  have "?S (x1,x2) (x3,x4)"
  apply(rule measure_induct2[of ?m ?S])
  using assms by (metis fst_conv snd_conv)
  thus ?thesis by auto
qed

lemma disj_notI1: "(\<not>P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q"
  by auto

lemma Not_Not_comp[simp]: "\<not> (Not \<circ> P) s \<equiv> P s"
  by auto

lemma map_filtermap: \<open>map T1 (filtermap P T2 xs) =  filtermap P (T1 o T2) xs\<close>
  by (simp add: List_Filtermap.filtermap_def)

end

