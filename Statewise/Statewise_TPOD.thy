theory Statewise_TPOD
  imports Statewise_CTPOD
begin

\<comment> \<open>For implementation purposes, we formalise statewise TPOD as CTPOD where the antecedent trace 
    property u = True.\<close>

locale Statewise_TPOD = Statewise_CTPOD _ _ _ _ _ _ _ _ op\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t op\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n op\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t \<open>\<lambda>_. True\<close> \<open>\<lambda>_. True\<close>
   \<comment> \<open>Bring back the type names - TODO is there a better way to do this?\<close>
  for op\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n :: "('vstate::low_equiv) \<Rightarrow> 'lowOp"
  and op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t :: "('ostate::low_equiv) \<Rightarrow> 'lowOp"
  and op\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n :: "('vstate::low_equiv) \<Rightarrow> 'highOp"
  and op\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t :: "('ostate::low_equiv) \<Rightarrow> 'highOp"

begin

sublocale asTPOD: TPOD
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>{\<pi>. istate\<^sub>v\<^sub>a\<^sub>n (hd \<pi>) \<and> validFromS\<^sub>v\<^sub>a\<^sub>n (hd \<pi>) \<pi> \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n (hd \<pi>) \<pi>}\<close>
    and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>{\<pi>. istate\<^sub>o\<^sub>p\<^sub>t (hd \<pi>) \<and> validFromS\<^sub>o\<^sub>p\<^sub>t (hd \<pi>) \<pi> \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t (hd \<pi>) \<pi>}\<close>
    and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t
  .

lemma U[simp]: \<open>U\<^sub>v\<^sub>a\<^sub>n tr\<close> \<open>U\<^sub>o\<^sub>p\<^sub>t tr'\<close>
  unfolding U\<^sub>o\<^sub>p\<^sub>t_def U\<^sub>v\<^sub>a\<^sub>n_def by auto 

lemma CTPOD_is_TPOD[simp]: \<open>asCTPOD.secure \<longleftrightarrow> asTPOD.secure\<close>
  unfolding asCTPOD.secure_def asTPOD.secure_def by auto

lemma secure_alt_def: \<open>secure \<longleftrightarrow> (\<forall>ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2.
  istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) \<and> validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1 \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1 \<and>
  istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) \<and> validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2 \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2 \<and>
  istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1)  \<and> validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1)  tr\<^sub>1  \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1)  tr\<^sub>1 \<and>
  istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)  \<and> validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)  tr\<^sub>2  \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)  tr\<^sub>2 \<and>
  ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
  ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
  hd tr\<^sub>1 \<approx>\<^sub>\<L> hd tr\<^sub>2 \<and> ctr\<^sub>1 \<approx>\<^sub>\<L> ctr\<^sub>2 \<longrightarrow>
                   tr\<^sub>1 \<approx>\<^sub>\<L> tr\<^sub>2)\<close>
  unfolding secure_alt_def by simp

lemma secure_def: \<open>secure \<longleftrightarrow> (\<forall>cs\<^sub>1 ctr\<^sub>1 cs\<^sub>2 ctr\<^sub>2 s\<^sub>1 tr\<^sub>1 s\<^sub>2 tr\<^sub>2.
  istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> 
    validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and> 
    completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and>
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>     
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> 
    ctr\<^sub>1 \<approx>\<^sub>\<L> ctr\<^sub>2 \<and> s\<^sub>1 \<approx>\<^sub>\<L> s\<^sub>2
   \<longrightarrow>
    tr\<^sub>1 \<approx>\<^sub>\<L> tr\<^sub>2
  )\<close>
  unfolding secure_def by simp

end

end
