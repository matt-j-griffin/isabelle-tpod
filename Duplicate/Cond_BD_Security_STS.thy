theory Cond_BD_Security_STS
  imports
    Cond_Abstract_BD_Security
    BD_Security_STS
begin

locale Cond_BD_Security_STS =
               
  Van: BD_Security_STS istate\<^sub>v\<^sub>a\<^sub>n validTrans\<^sub>v\<^sub>a\<^sub>n final\<^sub>v\<^sub>a\<^sub>n isSec\<^sub>v\<^sub>a\<^sub>n getSec\<^sub>v\<^sub>a\<^sub>n isObs\<^sub>v\<^sub>a\<^sub>n getObs\<^sub>v\<^sub>a\<^sub>n T\<^sub>v\<^sub>a\<^sub>n B\<^sub>v\<^sub>a\<^sub>n
+              
  Opt: BD_Security_STS istate\<^sub>o\<^sub>p\<^sub>t validTrans\<^sub>o\<^sub>p\<^sub>t final\<^sub>o\<^sub>p\<^sub>t isSec\<^sub>o\<^sub>p\<^sub>t getSec\<^sub>o\<^sub>p\<^sub>t isObs\<^sub>o\<^sub>p\<^sub>t getObs\<^sub>o\<^sub>p\<^sub>t T\<^sub>o\<^sub>p\<^sub>t B\<^sub>o\<^sub>p\<^sub>t

for istate\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and istate\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool" 
and validTrans\<^sub>v\<^sub>a\<^sub>n :: "('vstate \<times> 'vstate) \<Rightarrow> bool" and validTrans\<^sub>o\<^sub>p\<^sub>t :: "('ostate \<times> 'ostate) \<Rightarrow> bool"
and final\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and final\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool"
and isSec\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and isSec\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool" 
and getSec\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> 'vsecret" and getSec\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> 'osecret"
and isObs\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and isObs\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool" 
and getObs\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> 'vobs" and getObs\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> 'oobs"
and T\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> bool" and T\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> bool"
and B\<^sub>v\<^sub>a\<^sub>n :: "'vstate \<Rightarrow> 'vsecret list \<Rightarrow> 'vstate \<Rightarrow> 'vsecret list \<Rightarrow> bool" 
and B\<^sub>o\<^sub>p\<^sub>t :: "'ostate \<Rightarrow> 'osecret list \<Rightarrow> 'ostate \<Rightarrow> 'osecret list \<Rightarrow> bool"

and B\<^sub>c\<^sub>t\<^sub>r :: "'vstate \<Rightarrow> 'vsecret list \<Rightarrow> 'ostate \<Rightarrow> 'osecret list \<Rightarrow> bool"

begin

abbreviation \<open>S\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.S\<close> lemmas S\<^sub>v\<^sub>a\<^sub>n_def = Van.S_def
abbreviation \<open>S\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.S\<close> lemmas S\<^sub>o\<^sub>p\<^sub>t_def = Opt.S_def
abbreviation \<open>O\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.O\<close> lemmas O\<^sub>v\<^sub>a\<^sub>n_def = Van.O_def
abbreviation \<open>O\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.O\<close> lemmas O\<^sub>o\<^sub>p\<^sub>t_def = Opt.O_def
abbreviation \<open>consume\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.consume\<close>
abbreviation \<open>consume\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.consume\<close>
abbreviation \<open>hopeless\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.hopeless\<close>
abbreviation \<open>hopeless\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.hopeless\<close>
abbreviation \<open>reachNT\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.reachNT\<close>
abbreviation \<open>reachNT\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.reachNT\<close>
abbreviation \<open>validFromS\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.validFromS\<close>
abbreviation \<open>validFromS\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.validFromS\<close>
abbreviation \<open>completedFrom\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.completedFrom\<close>
abbreviation \<open>completedFrom\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.completedFrom\<close>

lemmas hopeless_def = Van.hopeless_def Opt.hopeless_def

sublocale asAbs: Cond_Abstract_BD_Security
  where validTrace\<^sub>v\<^sub>a\<^sub>n = Van.validTrace and validTrace\<^sub>o\<^sub>p\<^sub>t = Opt.validTrace
    and S\<^sub>v\<^sub>a\<^sub>n = \<open>\<lambda>tr. (hd tr, S\<^sub>v\<^sub>a\<^sub>n tr)\<close> and S\<^sub>o\<^sub>p\<^sub>t = \<open>\<lambda>tr. (hd tr, S\<^sub>o\<^sub>p\<^sub>t tr)\<close>
    and O\<^sub>v\<^sub>a\<^sub>n = Van.O and O\<^sub>o\<^sub>p\<^sub>t = Opt.O 
    and B\<^sub>v\<^sub>a\<^sub>n = \<open>\<lambda>(s\<^sub>1, sl\<^sub>1) (s\<^sub>2, sl\<^sub>2). B\<^sub>v\<^sub>a\<^sub>n s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2\<close> 
    and B\<^sub>o\<^sub>p\<^sub>t = \<open>\<lambda>(s\<^sub>1, sl\<^sub>1) (s\<^sub>2, sl\<^sub>2). B\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2\<close> 
    and B\<^sub>c\<^sub>t\<^sub>r = \<open>\<lambda>(s\<^sub>1, sl\<^sub>1) (s\<^sub>2, sl\<^sub>2). B\<^sub>c\<^sub>t\<^sub>r s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2\<close>
    and TT\<^sub>v\<^sub>a\<^sub>n = \<open>never T\<^sub>v\<^sub>a\<^sub>n\<close> and TT\<^sub>o\<^sub>p\<^sub>t = \<open>never T\<^sub>o\<^sub>p\<^sub>t\<close>
  .

abbreviation \<open>B cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv> asAbs.B (cs\<^sub>1, cvl\<^sub>1) (cs\<^sub>2, cvl\<^sub>2) (s\<^sub>1, vl\<^sub>1) (s\<^sub>2, vl\<^sub>2)\<close>
lemmas B_def = asAbs.B_def

abbreviation \<open>ForAll_ForAll_CSecure \<equiv> asAbs.ForAll_ForAll_CSecure\<close>
lemmas ForAll_ForAll_CSecure_def = asAbs.ForAll_ForAll_CSecure_def[unfolded B_def[symmetric]]

abbreviation \<open>eqObs\<^sub>v\<^sub>a\<^sub>n \<equiv> Van.eqObs\<close> lemmas eqObs\<^sub>v\<^sub>a\<^sub>n_def = Van.eqObs_def 
abbreviation \<open>eqObs\<^sub>o\<^sub>p\<^sub>t \<equiv> Opt.eqObs\<close> lemmas eqObs\<^sub>o\<^sub>p\<^sub>t_def = Opt.eqObs_def 

abbreviation 
  unobservable 
where
  \<open>unobservable \<equiv> Van.produces isObs\<^sub>v\<^sub>a\<^sub>n\<close>

lemmas unobservable_def = Van.produces_def

definition finish where \<open>finish \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv>
  final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 [] \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 [] \<and> eqObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cs\<^sub>2 
  \<longrightarrow> Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>


(* Independent actions (left and right): *)

definition iactionLeft where
"iactionLeft \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv>
 \<forall>cs\<^sub>1' cvl\<^sub>1'.
   validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1, cs\<^sub>1') \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1' 
   \<longrightarrow> 
   (\<not> isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<longrightarrow> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1' \<or> Opt.unwindFor (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2) \<and> 
   (isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 [] \<longrightarrow> 
      hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1' \<or> unobservable cs\<^sub>1')"

definition iactionRight where
"iactionRight \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv>
 \<forall>cs\<^sub>2' cvl\<^sub>2'.
   validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2') \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2' 
   \<longrightarrow> 
   (\<not> isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<longrightarrow> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2' \<or> Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2) \<and>
   (isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 [] \<longrightarrow> 
      hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2' \<or> unobservable cs\<^sub>2')"

definition saction where
"saction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<equiv>
 \<forall>cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2'.
   validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1, cs\<^sub>1') \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1' \<and> validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2') \<and> consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2' \<and> 
   isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2
   \<longrightarrow>
   hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1' \<or> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2' \<or> 
   Opt.unwindFor (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"

(*  *)

definition \<open>proaction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 \<equiv> Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2)\<close>

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2.
   reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 \<and> reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 \<and> reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 \<and> reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 \<and> 
   \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2
   \<longrightarrow>
   hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 \<or> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 \<or> hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1 \<or> hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2
   \<or>    
   proaction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<or>
   finish \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
   iactionLeft \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
   iactionRight \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and> 
   saction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
(*
lemma unwindI[intro?]:
assumes
"\<And>cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2.
   \<lbrakk>reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1; reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2; reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1; reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2; \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<rbrakk>
   \<Longrightarrow>
   hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 \<or> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 \<or> hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1 \<or> hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2 
   \<or>
   iactionLeft \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and> 
   iactionRight \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and> 
   saction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
shows "unwind \<Delta>"
using assms unfolding unwind_def by auto
*)
(*
lemma "\<not>(A \<and> F \<longrightarrow> C \<noteq> D) = (A \<and> F \<and> C = D)"
  unfolding de_Morgan_disj
  apply auto
*)
(*final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1; final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2;*)
proposition unwind_trace:
  assumes unwind: \<open>unwind \<Delta>\<close> 
      and r: \<open>reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close> "reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2" "reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1" "reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2" 
      and \<Delta>: \<open>\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
      and vn: \<open>validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1\<close> "never T\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1" "completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 tr\<^sub>1"
              \<open>validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2\<close> "never T\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2" "completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 tr\<^sub>2"
              \<open>validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1\<close> "never T\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1" "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctr\<^sub>1"
              \<open>validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2\<close> "never T\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2" "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctr\<^sub>2"
      and S: \<open>S\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = cvl\<^sub>1\<close> "S\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 = cvl\<^sub>2" "S\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 = vl\<^sub>1" "S\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 = vl\<^sub>2"
      and O: \<open>O\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = O\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2\<close>
    shows \<open>O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 = O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2\<close>
proof -
  let ?f = "\<lambda>ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2. length ctr\<^sub>1 + length ctr\<^sub>2 + length tr\<^sub>1 + length tr\<^sub>2"
  show ?thesis
  using r vn S O \<Delta> proof(induction ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2 arbitrary: cs\<^sub>1 cs\<^sub>2 cvl\<^sub>1 cvl\<^sub>2 s\<^sub>1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 rule: measure_induct4[of ?f])
    case (IH ctrr\<^sub>1 ctrr\<^sub>2 trr\<^sub>1 trr\<^sub>2 cs\<^sub>1 cs\<^sub>2 cvl\<^sub>1 cvl\<^sub>2 s\<^sub>1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2)
    note O = \<open>O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1 = O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2\<close> 
     and r = \<open>reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close> \<open>reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close> \<open>reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>1\<close> \<open>reachNT\<^sub>o\<^sub>p\<^sub>t s\<^sub>2\<close>
     and vnO1 = \<open>validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 trr\<^sub>1\<close> \<open>never T\<^sub>o\<^sub>p\<^sub>t trr\<^sub>1\<close> \<open>completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 trr\<^sub>1\<close>
     and vnO2 = \<open>validFromS\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 trr\<^sub>2\<close> \<open>never T\<^sub>o\<^sub>p\<^sub>t trr\<^sub>2\<close> \<open>completedFrom\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 trr\<^sub>2\<close>
     and vn1 = \<open>validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctrr\<^sub>1\<close> \<open>never T\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1\<close> \<open>completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 ctrr\<^sub>1\<close>
     and vn2 = \<open>validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctrr\<^sub>2\<close> \<open>never T\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2\<close> \<open>completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 ctrr\<^sub>2\<close>
     and S = \<open>S\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1 = cvl\<^sub>1\<close> \<open>S\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2 = cvl\<^sub>2\<close> \<open>S\<^sub>o\<^sub>p\<^sub>t trr\<^sub>1 = vl\<^sub>1\<close> \<open>S\<^sub>o\<^sub>p\<^sub>t trr\<^sub>2 = vl\<^sub>2\<close>
     and O = \<open>O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1 = O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2\<close>
     and \<Delta> = \<open>\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
    have nh: "\<not> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1" "\<not>hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2" "\<not> hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>1 vl\<^sub>1" "\<not>hopeless\<^sub>o\<^sub>p\<^sub>t s\<^sub>2 vl\<^sub>2"
      using vnO1 vnO2 vn1 vn2 S unfolding hopeless_def by auto 
    have \<open>proaction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<or>
     finish \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
     iactionLeft \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
     iactionRight \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2 \<and>
     saction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      using unwind[unfolded unwind_def] apply -
      apply (erule allE[where x = cs\<^sub>1], erule allE[where x = cvl\<^sub>1], 
             erule allE[where x = cs\<^sub>2], erule allE[where x = cvl\<^sub>2],
             erule allE[where x = s\<^sub>1],  erule allE[where x = vl\<^sub>1], 
             erule allE[where x = s\<^sub>2],  erule allE[where x = vl\<^sub>2])
      apply (erule impE)
      subgoal using r \<Delta> by (intro conjI)
      using nh by blast
    thus ?case 
    unfolding proaction_def proof (elim disjE conjE[where P = \<open>finish _ _ _ _ _ _ _ _ _\<close>]
           conjE[where P = \<open>iactionLeft _ _ _ _ _ _ _ _ _ \<close>] 
           conjE[where P = \<open>iactionRight _ _ _ _ _ _ _ _ _ \<close>])
      assume uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
      moreover have \<open>Opt.\<psi> (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) trr\<^sub>1 trr\<^sub>2\<close>
        unfolding Opt.\<psi>_def apply (intro allI impI)
        subgoal for tr\<^sub>1 tr\<^sub>2 s\<^sub>1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2
          by (rule IH.IH[OF _ r(1,2) _ _ _ _ _ _ _ _ vn1 vn2 S(1,2) _ _ O,simplified, of _ _ _ s\<^sub>2])
        .
      ultimately show ?thesis 
        using vnO1 vnO2 S(3,4) by (rule Opt.unwind_via_\<psi>[OF _ r(3,4)])
    next
      assume no: \<open>finish \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> and
             ial: "iactionLeft \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2" and 
             iar: "iactionRight \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2" and 
             sa: "saction \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
      show ?thesis 
      proof(cases \<open>length ctrr\<^sub>1 \<le> 1\<close>)
        case True \<comment> \<open>No more left steps\<close>
        hence ctrr\<^sub>1: \<open>ctrr\<^sub>1 = [cs\<^sub>1]\<close>
          using vn1(1) by (cases ctrr\<^sub>1, auto)
        hence cfinal\<^sub>1: \<open>final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>
          using vn1(3) by auto
        have consume\<^sub>1: \<open>consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 []\<close>
          using S(1) unfolding ctrr\<^sub>1 apply -
          apply (drule Van.S_Cons_consume)
          by simp
        note noactionL = IH.IH[OF _ r(1) _ _ _ _ _ _ _ _ _ vn1 _ _ _ S(1),simplified] 
        show ?thesis
        proof(cases \<open>length ctrr\<^sub>2 \<le> 1\<close>)
          case True \<comment> \<open>No more right steps\<close>
          hence ctrr\<^sub>2: \<open>ctrr\<^sub>2 = [cs\<^sub>2]\<close>
            using vn2(1) by (cases ctrr\<^sub>2, auto)
          hence cfinal\<^sub>2: \<open>final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
            using vn2(3) by auto
          have consume\<^sub>2: \<open>consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 []\<close>
            using S(2) unfolding ctrr\<^sub>2 apply -
            apply (drule Van.S_Cons_consume)
            by simp
          have eqObs: \<open>eqObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cs\<^sub>2\<close>
            using O ctrr\<^sub>1 ctrr\<^sub>2 
            apply (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>, auto)
            apply (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>, auto)
            unfolding eqObs\<^sub>v\<^sub>a\<^sub>n_def by auto
          note noaction = noactionL[OF _ r(2) _ _ _ _ _ _ _ _ vn2 S(2) _ _ O, simplified]
          have \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) trr\<^sub>1 trr\<^sub>2\<close>
            unfolding Opt.\<psi>_def apply (intro allI impI) 
            subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 by (rule noaction[of _ _ _ s\<^sub>2])
            .
          have uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
            using no[unfolded finish_def] eqObs cfinal\<^sub>1 cfinal\<^sub>2 consume\<^sub>1 consume\<^sub>2 by auto
          show ?thesis 
            by (rule Opt.unwind_via_\<psi>[OF uFor r(3) r(4) \<psi> vnO1 vnO2 S(3-)])
        next
          case False
          then obtain cs\<^sub>2' ctr\<^sub>2 where ctrr\<^sub>2: \<open>ctrr\<^sub>2 = cs\<^sub>2 # cs\<^sub>2' # ctr\<^sub>2\<close>
            apply (cases ctrr\<^sub>2, auto)
            subgoal for cs\<^sub>2' ctr\<^sub>2
              apply (cases ctr\<^sub>2, auto)
              using vn2(1) Van.validFromS_Cons_iff by auto
              .
          have trn2: \<open>validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2')\<close>
            using vn2(1) unfolding ctrr\<^sub>2 Van.validFromS_Cons_iff by auto
          hence s2': "reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2'"
            apply (rule Van.reachNT.Step[OF r(2)])
            using Van.validFromS_def list_all_hd vn2 by auto
          have tr2: "validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' (cs\<^sub>2' # ctr\<^sub>2)" "never T\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2)" "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' (cs\<^sub>2' # ctr\<^sub>2)"
            using vn2 unfolding ctrr\<^sub>2 Van.validFromS_Cons_iff by auto
          obtain cvl\<^sub>2' where vl\<^sub>2': "consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2'" and Vtr1: "S\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2) = cvl\<^sub>2'"
            using Van.S_Cons_consume[OF `S\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2 = cvl\<^sub>2`[unfolded ctrr\<^sub>2]] by blast
          hence nh2': "\<not> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2'" 
            unfolding hopeless_def apply auto
            using tr2(1) ctrr\<^sub>2 
            by (metis list_all_simps(1) vn2(2))
          show ?thesis
          proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>)
            case isObs2: True
            hence isObs1: \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>
            proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>)
              case False
              thus ?thesis 
              using O isObs2 unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp
            qed
            hence never: \<open>\<not>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2'\<close> \<open>never isObs\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2\<close>
              using isObs2 O unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp_all
            have getO: \<open>getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
              using O isObs1 isObs2 unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp
            show ?thesis
              using never iar trn2 vl\<^sub>2' isObs1 isObs2 getO unfolding iactionRight_def apply -
              apply (erule allE[where x = cs\<^sub>2'], erule allE[where x = cvl\<^sub>2']) 
              apply (erule impE)
              subgoal by auto
              using nh2' consume\<^sub>1 apply simp
              unfolding unobservable_def
              apply (erule allE[where x = \<open>cs\<^sub>2' # ctr\<^sub>2\<close>])
              using tr2 Van.O_Nil_list_ex by fastforce
          next
            case isObs2: False
            hence O: \<open>O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1 = O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2)\<close>
              using O unfolding ctrr\<^sub>2 by simp
            note iactionR = noactionL[OF _ s2' _ _ _ _ _ _ _ _ tr2  Vtr1 _ _ O, unfolded ctrr\<^sub>2, simplified]
            hence \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2' cvl\<^sub>2') trr\<^sub>1 trr\<^sub>2\<close>
              unfolding Opt.\<psi>_def apply (intro allI impI) 
              subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 
                by (rule iactionR[of _ _ _ s\<^sub>2], simp)
              .
            have uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
              using iar trn2 vl\<^sub>2' isObs2 unfolding iactionRight_def apply -
              apply (erule allE[where x = cs\<^sub>2'], erule allE[where x = cvl\<^sub>2']) 
              apply (erule impE)
              subgoal by auto
              using nh2' by simp
            show ?thesis by (rule Opt.unwind_via_\<psi>[OF uFor r(3-) \<psi> vnO1 vnO2 S(3-)])
          qed
        qed
      next
        case False
        then obtain cs\<^sub>1' ctr\<^sub>1 where ctrr\<^sub>1: \<open>ctrr\<^sub>1 = cs\<^sub>1 # cs\<^sub>1' # ctr\<^sub>1\<close>
          apply (cases ctrr\<^sub>1, auto)
          subgoal for cs\<^sub>1' ctr\<^sub>1
            apply (cases ctr\<^sub>1, auto)
            using vn1(1) Van.validFromS_Cons_iff by auto
          .
        have trn\<^sub>1: \<open>validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1, cs\<^sub>1')\<close>
          using vn1(1) unfolding ctrr\<^sub>1 Van.validFromS_Cons_iff by auto
        hence cs\<^sub>1': "reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1'"
          apply (rule Van.reachNT.Step[OF r(1)])
          using Van.validFromS_def list_all_hd vn1 by auto
        have ctr\<^sub>1: "validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' (cs\<^sub>1' # ctr\<^sub>1)" "never T\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1' # ctr\<^sub>1)" \<open>completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' (cs\<^sub>1' # ctr\<^sub>1)\<close>
          using vn1 unfolding ctrr\<^sub>1 Van.validFromS_Cons_iff by auto
        obtain cvl\<^sub>1' where cvl\<^sub>1': "consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 cvl\<^sub>1 cvl\<^sub>1'" and Sctr1: "S\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1' # ctr\<^sub>1) = cvl\<^sub>1'"
          using Van.S_Cons_consume[OF `S\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>1 = cvl\<^sub>1`[unfolded ctrr\<^sub>1]] by blast
        hence nh\<^sub>1': "\<not> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1' cvl\<^sub>1'" 
          unfolding hopeless_def apply auto
          using ctr\<^sub>1(1) ctrr\<^sub>1 by (metis list_all_simps(1) vn1(2))        
        note actionL = IH.IH[OF _ cs\<^sub>1' _ _ _ _ _ _ _ _ _ ctr\<^sub>1 _ _ _ Sctr1, unfolded ctrr\<^sub>1, simplified] 
        show ?thesis
        proof(cases \<open>length ctrr\<^sub>2 \<le> 1\<close>)
          case True \<comment> \<open>No more right steps\<close>
          hence ctrr\<^sub>2: \<open>ctrr\<^sub>2 = [cs\<^sub>2]\<close>
            using vn2(1) by (cases ctrr\<^sub>2, auto)
          hence cfinal\<^sub>2: \<open>final\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
            using vn2(3) by auto
          have consume\<^sub>2: \<open>consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 []\<close>
            using S(2) unfolding ctrr\<^sub>2 apply -
            apply (drule Van.S_Cons_consume)
            by simp
          note iactionL = actionL[OF _ r(2) _ _ _ _ _ _ _ _ vn2 S(2)]
          show ?thesis 
          proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>)
            case isObs1: True
            hence isObs2: \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
            proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>)
              case False
              thus ?thesis 
              using O isObs1 unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp
            qed
            hence never: \<open>\<not>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1'\<close> \<open>never isObs\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1\<close>
              using isObs1 O unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp_all
            have getO: \<open>getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>
              using O isObs1 isObs2 unfolding ctrr\<^sub>1 ctrr\<^sub>2 by simp
            show ?thesis
              using never ial trn\<^sub>1 cvl\<^sub>1' isObs1 isObs2 getO unfolding iactionLeft_def apply -
              apply (erule allE[where x = cs\<^sub>1'], erule allE[where x = cvl\<^sub>1']) 
              apply (erule impE)
              subgoal by auto
              using nh\<^sub>1' consume\<^sub>2 apply simp
              unfolding unobservable_def
              apply (erule allE[where x = \<open>cs\<^sub>1' # ctr\<^sub>1\<close>])
              using ctr\<^sub>1 Van.O_Nil_list_ex by fastforce
          next
            case isObs1: False
            hence O: \<open>O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1' # ctr\<^sub>1) = O\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2\<close>
              using O unfolding ctrr\<^sub>1 by simp
            note iactionL = actionL[OF _ r(2) _ _ _ _ _ _ _ _ vn2 S(2) _ _ O]
            hence \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2 cvl\<^sub>2) trr\<^sub>1 trr\<^sub>2\<close>
              unfolding Opt.\<psi>_def apply (intro allI impI) 
              subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 
                by (rule iactionL[of _ _ _ s\<^sub>2], simp)
              .
            have uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
              using ial trn\<^sub>1 cvl\<^sub>1' isObs1 unfolding iactionLeft_def apply -
              apply (erule allE[where x = cs\<^sub>1'], erule allE[where x = cvl\<^sub>1']) 
              apply (erule impE)
              subgoal by auto
              using nh\<^sub>1' by simp
            show ?thesis by (rule Opt.unwind_via_\<psi>[OF uFor r(3-) \<psi> vnO1 vnO2 S(3-)])
          qed
        next
          case False
          then obtain cs\<^sub>2' ctr\<^sub>2 where ctrr\<^sub>2: \<open>ctrr\<^sub>2 = cs\<^sub>2 # cs\<^sub>2' # ctr\<^sub>2\<close>
            apply (cases ctrr\<^sub>2, auto)
            subgoal for cs\<^sub>2' ctr\<^sub>2
              apply (cases ctr\<^sub>2, auto)
              using vn2(1) Van.validFromS_Cons_iff by auto
              .
          have trn\<^sub>2: \<open>validTrans\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2, cs\<^sub>2')\<close>
            using vn2(1) unfolding ctrr\<^sub>2 Van.validFromS_Cons_iff by auto
          hence s2': "reachNT\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2'"
            apply (rule Van.reachNT.Step[OF r(2)])
            using Van.validFromS_def list_all_hd vn2 by auto
          have tr2: "validFromS\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' (cs\<^sub>2' # ctr\<^sub>2)" "never T\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2)" "completedFrom\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' (cs\<^sub>2' # ctr\<^sub>2)"
            using vn2 unfolding ctrr\<^sub>2 Van.validFromS_Cons_iff by auto
          obtain cvl\<^sub>2' where cvl\<^sub>2': "consume\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2 cvl\<^sub>2 cvl\<^sub>2'" and Vtr1: "S\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2) = cvl\<^sub>2'"
            using Van.S_Cons_consume[OF `S\<^sub>v\<^sub>a\<^sub>n ctrr\<^sub>2 = cvl\<^sub>2`[unfolded ctrr\<^sub>2]] by blast
          hence nh2': "\<not> hopeless\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2' cvl\<^sub>2'" 
            unfolding hopeless_def apply auto
            using tr2(1) ctrr\<^sub>2 
            by (metis list_all_simps(1) vn2(2))
          thus ?thesis
          proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1\<close>)
            case isObs1: True
            then show ?thesis 
            proof (cases \<open>isObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close>)
              case isObs2: True
              have O': \<open>getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1 = getObs\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2\<close> \<open>O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1' # ctr\<^sub>1) = O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2)\<close>
                using isObs1 isObs2 O ctrr\<^sub>1 ctrr\<^sub>2 by auto
              hence uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
                using sa trn\<^sub>1 trn\<^sub>2 cvl\<^sub>1' cvl\<^sub>2' isObs1 isObs2 unfolding saction_def apply -
                apply (erule allE[where x = cs\<^sub>1'], erule allE[where x = cvl\<^sub>1']) 
                apply (erule allE[where x = cs\<^sub>2'], erule allE[where x = cvl\<^sub>2']) 
                apply (erule impE)
                subgoal by auto
                subgoal using nh2' nh\<^sub>1' by blast
                .
              note saction = actionL[OF _ s2' _ _ _ _ _ _ _ _ tr2 Vtr1 _ _ O'(2), unfolded ctrr\<^sub>2, simplified]
              have \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2' cvl\<^sub>2') trr\<^sub>1 trr\<^sub>2\<close>
                unfolding Opt.\<psi>_def apply (intro impI allI)
                subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 
                  by (rule saction[of _ _ _ s\<^sub>2], simp)
                .
              show ?thesis by (rule Opt.unwind_via_\<psi>[OF uFor r(3-) \<psi> vnO1 vnO2 S(3-)])
            next
              case isObs2: False
              hence O': \<open>O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1 # cs\<^sub>1' # ctr\<^sub>1) = O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2' # ctr\<^sub>2)\<close>
                using O unfolding ctrr\<^sub>2 ctrr\<^sub>1 by simp
              have uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2' cvl\<^sub>2') s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
                using iar trn\<^sub>1 trn\<^sub>2 cvl\<^sub>1' cvl\<^sub>2' isObs1 isObs2 unfolding iactionRight_def apply -
                apply (erule allE[where x = cs\<^sub>2'], erule allE[where x = cvl\<^sub>2']) 
                apply (erule impE)
                subgoal by auto
                using nh2' by simp
              note iactionL = IH.IH[OF _ r(1) s2' _ _ _ _ _ _ _ _ vn1 tr2 S(1) Vtr1 _ _ O'[unfolded ctrr\<^sub>1[symmetric]], unfolded ctrr\<^sub>1 ctrr\<^sub>2, simplified]
              have \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2' cvl\<^sub>2') trr\<^sub>1 trr\<^sub>2\<close>
                unfolding Opt.\<psi>_def apply (intro impI allI)
                subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 
                  by (rule iactionL[of _ _ _ s\<^sub>2], simp)
                .
              show ?thesis
                by (rule Opt.unwind_via_\<psi>[OF uFor r(3-) \<psi> vnO1 vnO2 S(3-)])
            qed
          next
            case isObs1: False
            hence O': \<open>O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>1' # ctr\<^sub>1) = O\<^sub>v\<^sub>a\<^sub>n (cs\<^sub>2 # cs\<^sub>2' # ctr\<^sub>2)\<close>
              using O unfolding ctrr\<^sub>2 ctrr\<^sub>1 by simp
            have uFor: \<open>Opt.unwindFor (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2 cvl\<^sub>2) s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
              using ial trn\<^sub>1 trn\<^sub>2 cvl\<^sub>1' cvl\<^sub>2' isObs1 unfolding iactionLeft_def apply -
              apply (erule allE[where x = cs\<^sub>1'], erule allE[where x = cvl\<^sub>1'])
              apply (erule impE)
              subgoal by auto
              apply simp
              using nh\<^sub>1' by blast
            note iactionL = actionL[OF _ r(2) _ _ _ _ _ _ _ _ vn2 S(2) _ _ O'[unfolded ctrr\<^sub>2[symmetric]], unfolded ctrr\<^sub>1 ctrr\<^sub>2, simplified]
            have \<psi>: \<open>Opt.\<psi> (\<Delta> cs\<^sub>1' cvl\<^sub>1' cs\<^sub>2 cvl\<^sub>2) trr\<^sub>1 trr\<^sub>2\<close>
              unfolding Opt.\<psi>_def apply (intro impI allI)
              subgoal for _ _ s1 s\<^sub>2 vl\<^sub>1 vl\<^sub>2 
                by (rule iactionL[of _ _ _ s\<^sub>2], simp)
              .
            show ?thesis
              by (rule Opt.unwind_via_\<psi>[OF uFor r(3-) \<psi> vnO1 vnO2 S(3-)])
          qed
        qed
      qed
    qed
  qed
qed

theorem unwind_secure:
  assumes init: "\<And>cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2. \<lbrakk>
            B cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2; istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>1; istate\<^sub>v\<^sub>a\<^sub>n cs\<^sub>2; istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>1; istate\<^sub>o\<^sub>p\<^sub>t s\<^sub>2
        \<rbrakk> \<Longrightarrow> \<Delta> cs\<^sub>1 cvl\<^sub>1 cs\<^sub>2 cvl\<^sub>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
      and unwind: "unwind \<Delta>"
    shows ForAll_ForAll_CSecure
  unfolding ForAll_ForAll_CSecure_def apply clarify
  subgoal for ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2
    apply (rule unwind_trace[OF unwind Van.reachNT.Istate Van.reachNT.Istate Opt.reachNT.Istate Opt.reachNT.Istate init, 
          where cs\<^sub>2 = \<open>hd ctr\<^sub>2\<close> and s\<^sub>2 = \<open>hd tr\<^sub>2\<close>])
    apply assumption+
    by standard+
  .

end


end