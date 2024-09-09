theory TPOD
  imports OD
begin

locale TPOD = 

(* Vanilla semantics: *)
 Van: OD Tr\<^sub>v\<^sub>a\<^sub>n ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n (*lowEquiv\<^sub>v\<^sub>a\<^sub>n*)
+   
(* Optimisation-enhanced semantics *)
 Opt: OD Tr\<^sub>o\<^sub>p\<^sub>t ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t (*lowEquiv\<^sub>o\<^sub>p\<^sub>t*)

 for Tr\<^sub>v\<^sub>a\<^sub>n and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n :: \<open>('vstate::low_equiv) trace \<Rightarrow> 'lop\<close>(* and lowEquiv\<^sub>v\<^sub>a\<^sub>n*)
 and Tr\<^sub>o\<^sub>p\<^sub>t and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t :: \<open>('ostate::low_equiv) trace \<Rightarrow> 'lop\<close>(* and lowEquiv\<^sub>o\<^sub>p\<^sub>t*)
+
 fixes ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate trace \<Rightarrow> 'hop\<close> and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate trace \<Rightarrow> 'hop\<close>
begin
(*
abbreviation \<open>lowEquivs\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.lowEquivs\<close>
abbreviation \<open>lowEquivs\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.lowEquivs\<close>
*)
abbreviation \<open>secureFor\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.secureFor\<close>
abbreviation \<open>secureFor\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.secureFor\<close>

definition  
  secure :: bool
where
  \<open>secure \<longleftrightarrow> (\<forall>ctr\<^sub>1 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>ctr\<^sub>2 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>tr\<^sub>1 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. \<forall>tr\<^sub>2 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. 
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>     
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> 
    (hd tr\<^sub>1) \<approx>\<^sub>\<L> (hd tr\<^sub>2) \<and>
    ctr\<^sub>1 \<approx>\<^sub>\<L> ctr\<^sub>2
   \<longrightarrow>
    tr\<^sub>1 \<approx>\<^sub>\<L> tr\<^sub>2
  )\<close>

lemma TPOD_as_OD: \<open>secure = (\<forall>ctr\<^sub>1 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>ctr\<^sub>2 \<in> Tr\<^sub>v\<^sub>a\<^sub>n. \<forall>tr\<^sub>1 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. \<forall>tr\<^sub>2 \<in> Tr\<^sub>o\<^sub>p\<^sub>t. 
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2  \<and> 
    secureFor\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 ctr\<^sub>2 \<and> (hd tr\<^sub>1) \<approx>\<^sub>\<L> (hd tr\<^sub>2)
    \<longrightarrow> secureFor\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 tr\<^sub>2)\<close>
  unfolding secure_def apply (intro iffI ballI impI; elim conjE)
  by auto

end

end
