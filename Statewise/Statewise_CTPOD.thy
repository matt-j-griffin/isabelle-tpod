theory Statewise_CTPOD
  imports "../CTPOD"
    Statewise_OD_Base
    "../ForAllForAllSecure/Cond_BD_Security_STS"
begin

locale Statewise_CTPOD = 

(* vanilla semantics: *)
 Van: Statewise_OD_Base istate\<^sub>v\<^sub>a\<^sub>n validTrans\<^sub>v\<^sub>a\<^sub>n final\<^sub>v\<^sub>a\<^sub>n isInter\<^sub>v\<^sub>a\<^sub>n op\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n low_equiv\<^sub>v\<^sub>a\<^sub>n op\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n u\<^sub>v\<^sub>a\<^sub>n
+   
(* optimisation-enhanced semantics *)
 Opt: Statewise_OD_Base istate\<^sub>o\<^sub>p\<^sub>t validTrans\<^sub>o\<^sub>p\<^sub>t final\<^sub>o\<^sub>p\<^sub>t isInter\<^sub>o\<^sub>p\<^sub>t op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t low_equiv\<^sub>o\<^sub>p\<^sub>t op\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t u\<^sub>o\<^sub>p\<^sub>t

  for istate\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and istate\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool"
    and validTrans\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<times> 'vstate \<Rightarrow> bool" and validTrans\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<times> 'ostate \<Rightarrow> bool"
    and final\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> bool\<close> and final\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> bool\<close>
    and isInter\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> bool\<close> and isInter\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> bool\<close>  
    and op\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> 'lowOp" and op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> 'lowOp"
    and low_equiv\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> 'vstate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n\<close> 100)
    and low_equiv\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> 'ostate \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t\<close> 100)
    and op\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> 'highOp" and op\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> 'highOp"
    and u\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> bool\<close> and u\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> bool\<close>

begin

text \<open>Abbreviations for naming consistency\<close>


abbreviation \<open>validFromS\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.validFromS\<close>
abbreviation \<open>validFromS\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.validFromS\<close>
abbreviation \<open>completedFrom\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.completedFrom\<close>
abbreviation \<open>completedFrom\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.completedFrom\<close>
abbreviation \<open>ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.ops\<^sub>\<L>\<close> lemmas ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n_def = Van.ops\<^sub>\<L>_def
abbreviation \<open>ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.ops\<^sub>\<L>\<close> lemmas ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t_def = Opt.ops\<^sub>\<L>_def
abbreviation \<open>ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.ops\<^sub>\<H>\<close> lemmas ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n_def = Van.ops\<^sub>\<H>_def
abbreviation \<open>ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.ops\<^sub>\<H>\<close> lemmas ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t_def = Opt.ops\<^sub>\<H>_def
abbreviation \<open>validTrace\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.validTrace\<close>
abbreviation \<open>validTrace\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.validTrace\<close>

definition \<open>U\<^sub>v\<^sub>a\<^sub>n \<equiv> list_all u\<^sub>v\<^sub>a\<^sub>n\<close> 
definition \<open>U\<^sub>o\<^sub>p\<^sub>t \<equiv> list_all u\<^sub>o\<^sub>p\<^sub>t\<close>

sublocale asCTPOD: CTPOD
  where Tr\<^sub>v\<^sub>a\<^sub>n = \<open>{\<pi>. validTrace\<^sub>v\<^sub>a\<^sub>n \<pi>}\<close>
    and ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n and ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n = ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n
    and U\<^sub>v\<^sub>a\<^sub>n = \<open>{\<pi>. U\<^sub>v\<^sub>a\<^sub>n \<pi>}\<close>
    and Tr\<^sub>o\<^sub>p\<^sub>t = \<open>{\<pi>. validTrace\<^sub>o\<^sub>p\<^sub>t \<pi>}\<close>
    and ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t and ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t
    and U\<^sub>o\<^sub>p\<^sub>t = \<open>{\<pi>. U\<^sub>o\<^sub>p\<^sub>t \<pi>}\<close>
  .

abbreviation \<open>secure \<equiv> asCTPOD.secure\<close>

lemma secure_alt_def: \<open>secure \<longleftrightarrow> (\<forall>ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2.
  validTrace\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and> U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and>
  validTrace\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ctr\<^sub>2 \<noteq> [] \<and> U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and>
  validTrace\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1  \<and> tr\<^sub>1 \<noteq> []  \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and>
  validTrace\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2  \<and> tr\<^sub>2 \<noteq> []  \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
  ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
  ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
  hd tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t hd tr\<^sub>2 \<and> ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<longrightarrow>
                   tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2)\<close>
  unfolding asCTPOD.secure_def by auto

lemma secure_def: \<open>secure \<longleftrightarrow> (\<forall>cs\<^sub>1 ctr\<^sub>1 cs\<^sub>2 ctr\<^sub>2 s\<^sub>1 tr\<^sub>1 s\<^sub>2 tr\<^sub>2.
    istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> 
    validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and> 
    completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and>
    ctr\<^sub>1 \<noteq> [] \<and> ctr\<^sub>2 \<noteq> [] \<and> tr\<^sub>1 \<noteq> [] \<and> tr\<^sub>2 \<noteq> [] \<and>
    U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and> U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>
    ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and>     
    ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> 
    ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2
   \<longrightarrow>
    tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2
  )\<close>
unfolding asCTPOD.secure_def proof safe
  fix cs\<^sub>1 ctr\<^sub>1 cs\<^sub>2 ctr\<^sub>2 s\<^sub>1 tr\<^sub>1 s\<^sub>2 tr\<^sub>2
  assume "\<forall>ctr\<^sub>1 \<in>{\<pi>. Van.asBD.validTrace \<pi>} \<inter> Collect U\<^sub>v\<^sub>a\<^sub>n.
          \<forall>ctr\<^sub>2 \<in>{\<pi>. Van.asBD.validTrace \<pi>} \<inter> Collect U\<^sub>v\<^sub>a\<^sub>n.
          \<forall>tr\<^sub>1 \<in>{\<pi>. Opt.asBD.validTrace \<pi>} \<inter> Collect U\<^sub>o\<^sub>p\<^sub>t.
          \<forall>tr\<^sub>2 \<in>{\<pi>. Opt.asBD.validTrace \<pi>} \<inter> Collect U\<^sub>o\<^sub>p\<^sub>t. ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> hd tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t hd tr\<^sub>2 \<and> ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<longrightarrow> tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1"
    and "istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2"
    and "istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1"
    and "istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2"
    and "validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1"
    and "validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2"
    and "validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1"
    and "validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2"
    and "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1"
    and "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2"
    and "completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1"
    and "completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2"
    and \<open>ctr\<^sub>1 \<noteq> []\<close> "ctr\<^sub>2 \<noteq> []" "tr\<^sub>1 \<noteq> []" "tr\<^sub>2 \<noteq> []"
    and "U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1"
    and "U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2"
  thus "tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2" apply -
    apply (erule ball_inE[where x = ctr\<^sub>1], rule IntI, unfold mem_Collect_eq, simp add: Van.validFromS_def, assumption)
    apply (erule ball_inE[where x = ctr\<^sub>2], rule IntI, unfold mem_Collect_eq, simp add: Van.validFromS_def, assumption)
    apply (erule ball_inE[where x = tr\<^sub>1], rule IntI, unfold mem_Collect_eq, simp add: Opt.validFromS_def, assumption)
    apply (erule ball_inE[where x = tr\<^sub>2], rule IntI, unfold mem_Collect_eq, simp add: Opt.validFromS_def, assumption)
    apply (erule impE)
    by (simp_all add: Opt.validFromS_def)
next
  fix ctr\<^sub>1 :: "'vstate list"
    and ctr\<^sub>2 :: "'vstate list"
    and tr\<^sub>1 :: "'ostate list"
    and tr\<^sub>2 :: "'ostate list"
  assume "\<forall>cs\<^sub>1 ctr\<^sub>1 cs\<^sub>2 ctr\<^sub>2 s\<^sub>1 tr\<^sub>1 s\<^sub>2 tr\<^sub>2. istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> 
validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and> 
completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1 \<and> completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1 \<and> completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2 \<and> 
ctr\<^sub>1 \<noteq> [] \<and> ctr\<^sub>2 \<noteq> [] \<and> tr\<^sub>1 \<noteq> [] \<and> tr\<^sub>2 \<noteq> [] \<and>
U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and> U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 \<and> ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<longrightarrow> tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1"
    and "U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1)"
    and "istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2)"
    and "istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1)"
    and "istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)"
    and "validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1"
    and "completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1"
    and "validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2"
    and "completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2"
    and "validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1) tr\<^sub>1"
    and "completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1) tr\<^sub>1"
    and "validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) tr\<^sub>2"
    and "completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) tr\<^sub>2"
    and \<open>ctr\<^sub>1 \<noteq> []\<close> "ctr\<^sub>2 \<noteq> []" "tr\<^sub>1 \<noteq> []" "tr\<^sub>2 \<noteq> []"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "hd tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t hd tr\<^sub>2"
    and "ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
  thus "tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    apply -
    apply (erule allE[where x = \<open>hd ctr\<^sub>1\<close>], erule allE[where x = ctr\<^sub>1])
    apply (erule allE[where x = \<open>hd ctr\<^sub>2\<close>], erule allE[where x = ctr\<^sub>2])
    apply (erule allE[where x = \<open>hd tr\<^sub>1\<close>], erule allE[where x = tr\<^sub>1])
    apply (erule allE[where x = \<open>hd tr\<^sub>2\<close>], erule allE[where x = tr\<^sub>2])
    apply (erule impE)
    by auto
qed

abbreviation \<open>getSec\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.getSec\<close> lemmas getSec\<^sub>v\<^sub>a\<^sub>n_def = Van.getSec_def
abbreviation \<open>getSec\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.getSec\<close> lemmas getSec\<^sub>o\<^sub>p\<^sub>t_def = Opt.getSec_def

abbreviation \<open>getObs\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.getObs\<close> lemmas getObs\<^sub>v\<^sub>a\<^sub>n_def = Van.getObs_def
abbreviation \<open>getObs\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.getObs\<close> lemmas getObs\<^sub>o\<^sub>p\<^sub>t_def = Opt.getObs_def

definition
  B\<^sub>v\<^sub>a\<^sub>n :: \<open>'vstate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> 'vstate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> bool\<close> 
where  
  \<open>B\<^sub>v\<^sub>a\<^sub>n s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2 \<equiv> unzipL sl\<^sub>1 = unzipL sl\<^sub>2\<close>

definition
  B\<^sub>c\<^sub>t\<^sub>r :: \<open>'vstate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> 'ostate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> bool\<close> 
where  
  \<open>B\<^sub>c\<^sub>t\<^sub>r _ sl\<^sub>v\<^sub>a\<^sub>n  _ sl\<^sub>o\<^sub>p\<^sub>t \<equiv> sl\<^sub>v\<^sub>a\<^sub>n = sl\<^sub>o\<^sub>p\<^sub>t\<close>

definition
  B\<^sub>o\<^sub>p\<^sub>t :: \<open>'ostate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> 'ostate \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> bool\<close> 
where  
  \<open>B\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2 \<equiv> s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> unzipL sl\<^sub>1 = unzipL sl\<^sub>2\<close>

sublocale asCBD: Cond_BD_Security_STS
  where istate\<^sub>v\<^sub>a\<^sub>n = istate\<^sub>v\<^sub>a\<^sub>n and istate\<^sub>o\<^sub>p\<^sub>t = istate\<^sub>o\<^sub>p\<^sub>t
    and validTrans\<^sub>v\<^sub>a\<^sub>n = validTrans\<^sub>v\<^sub>a\<^sub>n and validTrans\<^sub>o\<^sub>p\<^sub>t = validTrans\<^sub>o\<^sub>p\<^sub>t
    and final\<^sub>v\<^sub>a\<^sub>n = final\<^sub>v\<^sub>a\<^sub>n and final\<^sub>o\<^sub>p\<^sub>t = final\<^sub>o\<^sub>p\<^sub>t
    and isSec\<^sub>v\<^sub>a\<^sub>n = isInter\<^sub>v\<^sub>a\<^sub>n and isSec\<^sub>o\<^sub>p\<^sub>t = isInter\<^sub>o\<^sub>p\<^sub>t
    and getSec\<^sub>v\<^sub>a\<^sub>n = getSec\<^sub>v\<^sub>a\<^sub>n and getSec\<^sub>o\<^sub>p\<^sub>t = getSec\<^sub>o\<^sub>p\<^sub>t
    and isObs\<^sub>v\<^sub>a\<^sub>n = Van.isObs and isObs\<^sub>o\<^sub>p\<^sub>t = Opt.isObs
    and getObs\<^sub>v\<^sub>a\<^sub>n = getObs\<^sub>v\<^sub>a\<^sub>n and getObs\<^sub>o\<^sub>p\<^sub>t = getObs\<^sub>o\<^sub>p\<^sub>t
    and T\<^sub>v\<^sub>a\<^sub>n = \<open>Not o u\<^sub>v\<^sub>a\<^sub>n\<close> and T\<^sub>o\<^sub>p\<^sub>t = \<open>Not o u\<^sub>o\<^sub>p\<^sub>t\<close>
    and B\<^sub>v\<^sub>a\<^sub>n = B\<^sub>v\<^sub>a\<^sub>n and B\<^sub>o\<^sub>p\<^sub>t = B\<^sub>o\<^sub>p\<^sub>t and B\<^sub>c\<^sub>t\<^sub>r = B\<^sub>c\<^sub>t\<^sub>r
  ..

lemmas S_ops\<^sub>o\<^sub>p\<^sub>t = Opt.S_eq_ops
lemmas S_ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t = Opt.S_unzipL
lemmas S_ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n = Van.S_unzipL

lemma S_ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t[simp]: \<open>unzipR (asCBD.S\<^sub>o\<^sub>p\<^sub>t tr) = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<close>
  unfolding S_ops\<^sub>o\<^sub>p\<^sub>t by (intro map_snd_zip Opt.length_ops)

lemmas S_ops\<^sub>v\<^sub>a\<^sub>n = Van.S_eq_ops

lemma S_ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n[simp]: \<open>unzipR (asCBD.S\<^sub>v\<^sub>a\<^sub>n tr) = ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n tr\<close>
  unfolding S_ops\<^sub>v\<^sub>a\<^sub>n by (intro map_snd_zip Van.length_ops)

lemmas zip_injectI = arg_cong2[where f = zip]

lemma asCBD_secureI: 
  assumes asCBD.ForAll_ForAll_CSecure 
    shows secure
unfolding secure_alt_def proof safe
  fix ctr\<^sub>1 ctr\<^sub>2 :: "'vstate list" and tr\<^sub>1 tr\<^sub>2 :: "'ostate list"
  assume "istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1)"
    and "asCBD.validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1"
    and "asCBD.completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>1) ctr\<^sub>1"
    and "istate\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2)"
    and "asCBD.validFromS\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2"
    and "asCBD.completedFrom\<^sub>v\<^sub>a\<^sub>n (hd ctr\<^sub>2) ctr\<^sub>2"
    and "istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1)"
    and "asCBD.validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1) tr\<^sub>1"
    and "asCBD.completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>1) tr\<^sub>1"
    and "istate\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2)"
    and "asCBD.validFromS\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) tr\<^sub>2"
    and "asCBD.completedFrom\<^sub>o\<^sub>p\<^sub>t (hd tr\<^sub>2) tr\<^sub>2"
    and \<open>ctr\<^sub>1 \<noteq> []\<close> "ctr\<^sub>2 \<noteq> []" "tr\<^sub>1 \<noteq> []" "tr\<^sub>2 \<noteq> []"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1"
    and "ops\<^sub>\<H>\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = ops\<^sub>\<H>\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    and "hd tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t hd tr\<^sub>2"
    and "ctr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2"
    and U: \<open>U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1\<close> \<open>U\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2\<close> \<open>U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1\<close> \<open>U\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2\<close>
  hence \<open>asCBD.O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 = asCBD.O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2\<close>
    using assms 
    unfolding asCBD.ForAll_ForAll_CSecure_def asCBD.B_def
    unfolding B\<^sub>v\<^sub>a\<^sub>n_def B\<^sub>o\<^sub>p\<^sub>t_def B\<^sub>c\<^sub>t\<^sub>r_def 
    apply -
    apply (erule allE[where x = ctr\<^sub>1], erule allE[where x = ctr\<^sub>2])
    apply (erule allE[where x = tr\<^sub>1],  erule allE[where x = tr\<^sub>2])
    apply (erule impE)
    apply simp_all
    unfolding S_ops\<^sub>o\<^sub>p\<^sub>t S_ops\<^sub>v\<^sub>a\<^sub>n U\<^sub>v\<^sub>a\<^sub>n_def[symmetric] U\<^sub>o\<^sub>p\<^sub>t_def[symmetric]
    apply (intro conjI Van.lowEquivs_imp_O zip_injectI)
    by simp_all
  thus "tr\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2"
    by (rule Opt.O_imp_lowEquivs)
qed


(* TODO goal is to drop \<Theta> to just two ops lists *)

abbreviation \<open>\<Lambda> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv> s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 
  \<and> unzipL vl\<^sub>1 = unzipL vl\<^sub>2 \<and> unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close>

definition \<open>proaction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 \<equiv> Opt.unwindFor (\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2)\<close>

lemma eqObs\<^sub>v\<^sub>a\<^sub>n_def: \<open>asCBD.eqObs\<^sub>v\<^sub>a\<^sub>n s s' \<longleftrightarrow> getObs\<^sub>v\<^sub>a\<^sub>n s = getObs\<^sub>v\<^sub>a\<^sub>n s'\<close>
  unfolding asCBD.eqObs\<^sub>v\<^sub>a\<^sub>n_def using Van.isObs by auto

lemma eqObs\<^sub>o\<^sub>p\<^sub>t_def: \<open>asCBD.eqObs\<^sub>o\<^sub>p\<^sub>t s s' \<longleftrightarrow> getObs\<^sub>o\<^sub>p\<^sub>t s = getObs\<^sub>o\<^sub>p\<^sub>t s'\<close>
  unfolding asCBD.eqObs\<^sub>o\<^sub>p\<^sub>t_def using Opt.isObs by auto

lemma unobservable[simp]: \<open>asCBD.unobservable cs\<close>
  unfolding asCBD.unobservable_def apply auto
  using Van.isObs 
  by (metis Van.validFromSE Van.validFromS_def list_ex_simps(1))

abbreviation \<open>consume\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.consume\<close> lemmas consume\<^sub>o\<^sub>p\<^sub>t_def = Opt.consume_def

lemma lowEquiv_finish: 
  \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<Longrightarrow> asCBD.Opt.finish s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
unfolding asCBD.Opt.finish_def eqObs\<^sub>o\<^sub>p\<^sub>t_def 
proof (intro impI Opt.lowEquiv_imp_getObs, elim conjE)
  assume "isInter\<^sub>o\<^sub>p\<^sub>t s\<^sub>1" "final\<^sub>o\<^sub>p\<^sub>t s\<^sub>1"
  thus "op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 = op\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2"
    using Opt.isInter_not_final by blast
qed

abbreviation \<open>unwindForOD \<equiv> Opt.unwindFor\<close> 

lemma unwindForOD_asCBD:
  assumes unwind: \<open>unwindForOD (\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
      and others: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close> 
                  \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2\<close>
                  \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close> \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close>
                shows \<open>asCBD.Opt.unwindFor (\<Lambda> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
  using unwind others(1-4) apply (rule asCBD.Opt.unwindFor_impI [OF Opt.unwindFor_asBD]; elim conjE, simp_all add: Opt.isObs_def)
  using others(5-) by simp

definition \<open>finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv>
  final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> cvl\<^sub>1 = [] \<and> cvl\<^sub>2 = [] \<and> cs\<^sub>1 \<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<longrightarrow>
  Opt.unwindFor (\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>

lemma finish_asCBD:
  assumes finish: \<open>finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      and others: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2\<close> 
                  \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close> \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close> 
    shows \<open>asCBD.finish (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
unfolding asCBD.finish_def 
proof (intro impI ; elim conjE)
  assume final: "final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1" "final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2"
    and consume: "asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 []" "asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 []"
    and obs: "asCBD.eqObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cs\<^sub>2"
  note not_isInter = Van.isInter_not_final[OF final(1)] Van.isInter_not_final[OF final(2)]
  have cvl\<^sub>1_empty: \<open>cvl\<^sub>1 = []\<close> 
    using consume(1) by (elim Van.final_consume_lastE[OF final(1)])
  have cvl\<^sub>2_empty: \<open>cvl\<^sub>2 = []\<close>
    using consume(2) by (elim Van.final_consume_lastE[OF final(2)])

  have unwind: \<open>unwindForOD (\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    using final cvl\<^sub>2_empty cvl\<^sub>1_empty obs
    using finish unfolding finish_def eqObs\<^sub>v\<^sub>a\<^sub>n_def apply (elim impE conjE)
    apply (intro conjI Van.getObs_imp_lowEquiv)
    by simp_all

  thus "asCBD.Opt.unwindFor (\<Lambda> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    using others by (rule unwindForOD_asCBD)
qed


lemma unwindForOD'_asBD:
  assumes unwind: \<open>unwindForOD (\<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      and others: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2\<close>
                  "asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1'""asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2'"
                  \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close> \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close> \<open>cs\<^sub>1 \<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
    shows \<open>asCBD.Opt.unwindFor (\<Lambda> \<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
  using unwind others(1-3,6) apply (rule asCBD.Opt.unwindFor_impI [OF Opt.unwindFor_asBD])
  using others  apply (simp_all add: Opt.isObs)
  apply (erule Van.low_equiv_interE)
  apply (erule asCBD.Van.consumeE)
  apply (erule asCBD.Van.consume_secE, blast)
  apply simp
  apply (metis map_tl)
  apply (erule asCBD.Van.consume_notSecE, blast)
  by simp

(*(final\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> final\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<longrightarrow> \<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2' s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2) \<and> *)
definition \<open>saction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv> \<forall>cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2'.
  validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1, cs\<^sub>1') \<and> asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1' \<and> validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2') \<and>
    asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2' \<and> cs\<^sub>1 \<approx>\<^sub>\<L>\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2
\<longrightarrow>
  asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1' \<or> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2' \<or> 
    (unwindForOD (\<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2)\<close>

lemma saction_asCBD:
  assumes saction: \<open>saction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      and finish: \<open>finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      and others: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1\<close> \<open>\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2\<close>
            \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close> \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close>
    shows \<open>asCBD.saction (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
unfolding asCBD.saction_def
proof (intro allI impI ; elim conjE ; intro disj_notI1)
  fix cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2' 
  assume vT: "validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1, cs\<^sub>1')" "validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2')"
    and consume: "asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1'""asCBD.consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2'"
    and obs_eq: "getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2"
    and nh: "\<not> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1'" "\<not> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2'"
  note \<L>van = Van.getObs_imp_lowEquiv[OF obs_eq]
  have unwind: \<open>unwindForOD (\<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    using \<L>van consume nh saction saction_def vT by blast
  thus "asCBD.Opt.unwindFor (\<Lambda> \<Theta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    using others(1-3) consume others(4-) \<L>van by (rule unwindForOD'_asBD)
qed

definition unwind where
"unwind \<Theta> \<equiv>
 \<forall> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2.
   asCBD.reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> asCBD.reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> asCBD.reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> asCBD.reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> 
   \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and> s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2
   \<longrightarrow>
   asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 \<or> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2
   \<or>
   proaction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<or>
   finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
   saction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"

lemma iactionLeft[simp]: \<open>asCBD.iactionLeft \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
  unfolding asCBD.iactionLeft_def by (auto simp add: Van.isObs)
  
lemma iactionRight[simp]: \<open>asCBD.iactionRight \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
  unfolding asCBD.iactionRight_def by (auto simp add: Van.isObs)

lemma unwind_asCBDI: 
  assumes unwind: \<open>unwind \<Theta>\<close>
    shows \<open>asCBD.unwind (\<Lambda> \<Theta>)\<close> 
unfolding asCBD.unwind_def proof (intro allI impI, elim conjE)
  fix cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2
  assume r: \<open>asCBD.reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close> \<open>asCBD.reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close> \<open>asCBD.reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1\<close> \<open>asCBD.reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close>
    and \<L>: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close>
    and \<Theta>: \<open>\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    and lops_eq: \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close>
    and clops_eq: \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close>
  have CBD: \<open>asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 \<or> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2
         \<or>
   proaction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<or>
   finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
   saction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    using unwind[unfolded unwind_def] apply -
    apply (erule allE[where x = cs\<^sub>1], erule allE[where x = cvl\<^sub>1],
           erule allE[where x = cs\<^sub>2], erule allE[where x = cvl\<^sub>2],
           erule allE[where x = s\<^sub>1], erule allE[where x = vl\<^sub>1],
           erule allE[where x = s\<^sub>2], erule allE[where x = vl\<^sub>2])
    apply (erule impE)
    using r \<Theta> \<L> by auto
  show \<open>asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 \<or> asCBD.hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1 \<or> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2 \<or>
       asCBD.proaction (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<or>
       asCBD.finish (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
       asCBD.iactionLeft (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
       asCBD.iactionRight (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
       asCBD.saction (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    apply (rule disj_notI1, rule disj_notI1, rule disj_notI1, rule disj_notI1)
    using CBD apply (elim disjE conjE)
    apply simp_all
    subgoal 
      unfolding proaction_def asCBD.proaction_def apply (rule disjI1)
      apply (rule unwindForOD_asCBD)
      using \<L> \<Theta> lops_eq clops_eq by blast+
    subgoal 
    proof (intro disjI2 conjI iactionLeft iactionRight)
      assume finish: "finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
        and nh: "\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1" "\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2"
      show "asCBD.finish (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
        using finish \<L> nh lops_eq clops_eq by (rule finish_asCBD)
    next
      assume saction: "saction \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
        and finish: "finish \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
        and nh: "\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1" "\<not> asCBD.hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2"
        show "asCBD.saction (\<Lambda> \<Theta>) cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
        using saction finish \<L> nh lops_eq clops_eq by (rule saction_asCBD)
    qed
    .
qed

lemma unwind_secure:
  assumes init: \<open>(\<And>cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2. \<lbrakk>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2; unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2;
              unzipL vl\<^sub>1 = unzipL vl\<^sub>2; cvl\<^sub>1 = vl\<^sub>1; cvl\<^sub>2 = vl\<^sub>2;
              istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1; istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2; istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1; istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<rbrakk> 
            \<Longrightarrow> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2)\<close>
      and unwind: \<open>unwind \<Theta>\<close>
    shows secure
proof (rule asCBD_secureI [OF asCBD.unwind_secure [where \<Delta> = \<open>\<Lambda> \<Theta>\<close>]])
  fix cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 
  assume B: "asCBD.B cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    and istate: "istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1" "istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2"  "istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1"  "istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2"
  also have asm: \<open>s\<^sub>1 \<approx>\<^sub>\<L>\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close> \<open>unzipL cvl\<^sub>1 = unzipL cvl\<^sub>2\<close> \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close> \<open>cvl\<^sub>1 = vl\<^sub>1\<close> 
                \<open>cvl\<^sub>2 = vl\<^sub>2\<close>
    using B
    unfolding asCBD.B_def case_prod_beta fst_conv snd_conv apply auto
    unfolding B\<^sub>o\<^sub>p\<^sub>t_def B\<^sub>c\<^sub>t\<^sub>r_def B\<^sub>v\<^sub>a\<^sub>n_def by auto
  moreover have \<open>\<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    using asm istate by (rule init)
  ultimately show "\<Lambda> \<Theta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    by auto
next
  show "asCBD.unwind (\<Lambda> \<Theta>)"
    by (intro unwind_asCBDI unwind)
qed

end

end
