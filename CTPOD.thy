theory CTPOD
  imports TPOD
begin

locale CTPOD = 
  fixes Tr\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace set\<close> and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'lop\<close> 
    and low_equiv\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> 'vstate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n\<close> 100)
    and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'hop\<close> and U\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace set\<close>

    and Tr\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace set\<close> and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'lop\<close> 
    and low_equiv\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> 'ostate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t\<close> 100)
    and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'hop\<close> and U\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace set\<close>
begin

sublocale TPOD 
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>Tr\<^sub>v\<^sub>a\<^sub>n \<inter> U\<^sub>v\<^sub>a\<^sub>n\<close>
    and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n
    and low_equiv\<^sub>v\<^sub>a\<^sub>n = low_equiv\<^sub>v\<^sub>a\<^sub>n
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>Tr\<^sub>o\<^sub>p\<^sub>t \<inter> U\<^sub>o\<^sub>p\<^sub>t\<close> 
    and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t 
    and low_equiv\<^sub>o\<^sub>p\<^sub>t = low_equiv\<^sub>o\<^sub>p\<^sub>t
    and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n 
    and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t
  .

lemma csecure_def: \<open>secure \<longleftrightarrow> (\<forall>ctr\<^sub>1 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>ctr\<^sub>2 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>tr\<^sub>1 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. \<forall>tr\<^sub>2 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. 
    ctr\<^sub>1 \<in> U\<^sub>v\<^sub>a\<^sub>n \<and> ctr\<^sub>2 \<in> U\<^sub>v\<^sub>a\<^sub>n \<and> tr\<^sub>1 \<in> U\<^sub>o\<^sub>p\<^sub>t \<and> tr\<^sub>2 \<in> U\<^sub>o\<^sub>p\<^sub>t \<and> 
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>     
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> 
    (hd tr\<^sub>1) \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) \<and>
    ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2
   \<longrightarrow>
    tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2
  )\<close>
  unfolding secure_def by auto

end

end
