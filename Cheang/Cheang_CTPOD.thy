theory Cheang_CTPOD
  imports Cheang_TPOD 
          "../CTPOD"
begin

text \<open>Cheang's definition of Constrained TPOD\<close>

locale Cheang_CTPOD = tpod: Cheang_TPOD _ _ ops\<^sub>\<L> ops\<^sub>\<H>
 (* TODO this is to rename the type parameters *)
  for ops\<^sub>\<L> :: \<open>'state trace \<Rightarrow> 'low\<close> and ops\<^sub>\<H> :: \<open>'state trace \<Rightarrow> 'high\<close>
+
  fixes U :: \<open>'state trace set\<close>

begin

no_notation tpod.Van.low_equivs (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<close> 100)
no_notation tpod.Opt.low_equivs (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<close> 100)

sublocale CTPOD
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>Tr \<inter> T\<close> and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L> and low_equiv\<^sub>v\<^sub>a\<^sub>n = low_equiv
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>{x \<in> Tr. x \<notin> T}\<close> and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L> and low_equiv\<^sub>o\<^sub>p\<^sub>t = low_equiv
    and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H> and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H> and U\<^sub>v\<^sub>a\<^sub>n = U and U\<^sub>o\<^sub>p\<^sub>t = U
  .

lemma Cheang_csecure: \<open>secure \<longleftrightarrow> (\<forall>\<pi>\<^sub>1 \<in> Tr. \<forall>\<pi>\<^sub>2 \<in> Tr. \<forall>\<pi>\<^sub>3 \<in> Tr. \<forall>\<pi>\<^sub>4 \<in> Tr.
    \<pi>\<^sub>1 \<in> T \<and> \<pi>\<^sub>2 \<in> T \<and> \<pi>\<^sub>3 \<notin> T \<and> \<pi>\<^sub>4 \<notin> T \<and>
    \<pi>\<^sub>1 \<in> U \<and> \<pi>\<^sub>2 \<in> U \<and> \<pi>\<^sub>3 \<in> U \<and> \<pi>\<^sub>4 \<in> U \<and>
    ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2 \<and> ops\<^sub>\<L> \<pi>\<^sub>3 = ops\<^sub>\<L> \<pi>\<^sub>4 \<and> ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>3 \<and>
    ops\<^sub>\<H> \<pi>\<^sub>1 = ops\<^sub>\<H> \<pi>\<^sub>3 \<and> ops\<^sub>\<H> \<pi>\<^sub>2 = ops\<^sub>\<H> \<pi>\<^sub>4 \<and>
    \<pi>\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>2 \<and> (hd \<pi>\<^sub>3) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>4)
    \<longrightarrow> \<pi>\<^sub>3 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>4)\<close>
  unfolding csecure_def apply (intro iffI allI ballI impI; elim conjE)
  subgoal by auto
  subgoal for ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2
    apply (erule ball_inE[where x = ctr\<^sub>1], simp)
    apply (erule ball_inE[where x = ctr\<^sub>2], simp)
    apply (erule ball_inE[where x = tr\<^sub>1], simp)
    apply (erule ball_inE[where x = tr\<^sub>2], simp)
    by simp
  .

end

end
