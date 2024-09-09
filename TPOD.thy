theory TPOD
  imports OD
begin

locale TPOD = 

(* Vanilla semantics: *)
 Van: OD Tr\<^sub>v\<^sub>a\<^sub>n ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n low_equiv\<^sub>v\<^sub>a\<^sub>n
+   
(* Optimisation-enhanced semantics *)
 Opt: OD Tr\<^sub>o\<^sub>p\<^sub>t ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t low_equiv\<^sub>o\<^sub>p\<^sub>t

 for Tr\<^sub>v\<^sub>a\<^sub>n and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'lop\<close> and low_equiv\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> 'vstate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n\<close> 100)
 and Tr\<^sub>o\<^sub>p\<^sub>t and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'lop\<close> and low_equiv\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> 'ostate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t\<close> 100)
+
 fixes ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'hop\<close> and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'hop\<close>
begin

abbreviation 
  low_equivs\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'vstate trace \<Rightarrow> bool\<close>  (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n\<close> 100)
where
  \<open>low_equivs\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.low_equivs\<close> 

abbreviation 
  low_equivs\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'ostate trace \<Rightarrow> bool\<close>  (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t\<close> 100)
where
  \<open>low_equivs\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.low_equivs\<close> 

abbreviation \<open>secureFor\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.secureFor\<close>
abbreviation \<open>secureFor\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.secureFor\<close>

definition  
  secure :: bool
where
  \<open>secure \<longleftrightarrow> (\<forall>ctr\<^sub>1 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>ctr\<^sub>2 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>tr\<^sub>1 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. \<forall>tr\<^sub>2 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. 
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>     
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> 
    (hd tr\<^sub>1) \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) \<and>
    ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2
   \<longrightarrow>
    tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2
  )\<close>

lemma TPOD_as_OD: \<open>secure = (\<forall>ctr\<^sub>1 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>ctr\<^sub>2 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>tr\<^sub>1 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. \<forall>tr\<^sub>2 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. 
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2  \<and> 
    secureFor\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 ctr\<^sub>2 \<and> (hd tr\<^sub>1) \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)
    \<longrightarrow> secureFor\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 tr\<^sub>2)\<close>
  unfolding secure_def apply (intro iffI ballI impI; elim conjE)
  by auto

end

end
