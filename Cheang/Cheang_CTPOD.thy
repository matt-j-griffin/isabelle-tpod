theory Cheang_CTPOD
  imports Cheang_TPOD 
          "../CTPOD"
begin

text \<open>Cheang's definition of Constrained TPOD\<close>


locale Cheang_CTPOD = tpod: Cheang_TPOD Tr ops\<^sub>\<L> (* lowEquiv *) ops\<^sub>\<H> T
  for Tr :: \<open>('state::low_equiv) trace set\<close> 
  and ops\<^sub>\<L> :: \<open>'state trace \<Rightarrow> 'low_op\<close> 
  (*and lowEquiv :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close>*)
  and ops\<^sub>\<H> :: \<open>'state trace \<Rightarrow> 'high_op\<close>
  and T :: \<open>'state trace set\<close>
+
  fixes U :: \<open>'state trace set\<close>

begin

(* abbreviation \<open>lowEquivs \<equiv> tpod.lowEquivs\<close> *)

sublocale CTPOD
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>Tr \<inter> T\<close> and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L>(* and lowEquiv\<^sub>v\<^sub>a\<^sub>n = lowEquiv*)
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>{x \<in> Tr. x \<notin> T}\<close> and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L>(* and lowEquiv\<^sub>o\<^sub>p\<^sub>t = lowEquiv*)
    and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H> and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H> and U\<^sub>v\<^sub>a\<^sub>n = U and U\<^sub>o\<^sub>p\<^sub>t = U
  .

lemma Cheang_csecure: \<open>secure \<longleftrightarrow> (\<forall>\<pi>\<^sub>1 \<in> Tr. \<forall>\<pi>\<^sub>2 \<in> Tr. \<forall>\<pi>\<^sub>3 \<in> Tr. \<forall>\<pi>\<^sub>4 \<in> Tr. 
    \<pi>\<^sub>1 \<in> T \<and> \<pi>\<^sub>2 \<in> T \<and> \<pi>\<^sub>3 \<notin> T \<and> \<pi>\<^sub>4 \<notin> T \<and>
    \<pi>\<^sub>1 \<in> U \<and> \<pi>\<^sub>2 \<in> U \<and> \<pi>\<^sub>3 \<in> U \<and> \<pi>\<^sub>4 \<in> U \<and>
    ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2 \<and> ops\<^sub>\<L> \<pi>\<^sub>3 = ops\<^sub>\<L> \<pi>\<^sub>4 \<and> ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>3 \<and>
    ops\<^sub>\<H> \<pi>\<^sub>1 = ops\<^sub>\<H> \<pi>\<^sub>3 \<and> ops\<^sub>\<H> \<pi>\<^sub>2 = ops\<^sub>\<H> \<pi>\<^sub>4 \<and>
    \<pi>\<^sub>1 \<approx>\<^sub>\<L> \<pi>\<^sub>2 \<and> (hd \<pi>\<^sub>3) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>4)
    \<longrightarrow> \<pi>\<^sub>3 \<approx>\<^sub>\<L> \<pi>\<^sub>4)\<close>
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
