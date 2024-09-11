theory Cheang_TPOD
  imports "../TPOD"   
          "../General_Preliminaries/TPOD_Trivia"
begin

text \<open>Cheang's definition of TPOD\<close>


locale Cheang_TPOD = od: OD _ ops\<^sub>\<L>
  for ops\<^sub>\<L> :: \<open>'state trace \<Rightarrow> 'lop\<close> (* TODO this is to rename the type parameters *)
+
fixes ops\<^sub>\<H> :: \<open>'state trace \<Rightarrow> 'hop\<close> 
  and T :: \<open>'state trace set\<close>
    
begin

sublocale TPOD
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>Tr \<inter> T\<close> and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L> and low_equiv\<^sub>v\<^sub>a\<^sub>n = low_equiv
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>{x \<in> Tr. x \<notin> T}\<close> and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L> and low_equiv\<^sub>o\<^sub>p\<^sub>t = low_equiv
    and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H> and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H>
  .

lemma Cheang_secure: \<open>secure \<longleftrightarrow> (\<forall>\<pi>\<^sub>1 \<in> Tr. \<forall>\<pi>\<^sub>2 \<in> Tr. \<forall>\<pi>\<^sub>3 \<in> Tr. \<forall>\<pi>\<^sub>4 \<in> Tr. 
    \<pi>\<^sub>1 \<in> T \<and> \<pi>\<^sub>2 \<in> T \<and> \<pi>\<^sub>3 \<notin> T \<and> \<pi>\<^sub>4 \<notin> T \<and>
    ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2 \<and> ops\<^sub>\<L> \<pi>\<^sub>3 = ops\<^sub>\<L> \<pi>\<^sub>4 \<and> ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>3 \<and>
    ops\<^sub>\<H> \<pi>\<^sub>1 = ops\<^sub>\<H> \<pi>\<^sub>3 \<and> ops\<^sub>\<H> \<pi>\<^sub>2 = ops\<^sub>\<H> \<pi>\<^sub>4 \<and>
    \<pi>\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>2 \<and> (hd \<pi>\<^sub>3) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>4)
    \<longrightarrow> \<pi>\<^sub>3 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>4)\<close>
  unfolding secure_def apply (intro iffI allI ballI impI; elim conjE)
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
