theory Instantiate_OD
  imports "../Statewise/Statewise_OD"
begin

locale TempInstantiate =  System_Model istate validTrans final
  for istate :: \<open>'state \<Rightarrow> bool\<close> and validTrans :: \<open>'state \<times> 'state \<Rightarrow> bool\<close>
  and final :: \<open>'state \<Rightarrow> bool\<close>
+ 
fixes obsEq :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close>
  and speculating :: \<open>'state \<Rightarrow> bool\<close> and op\<^sub>\<L> :: \<open>'state \<Rightarrow> 'lowOp\<close>
  and bot :: \<open>'lowOp\<close>

assumes equivp_lowEquiv: \<open>equivp obsEq\<close>
(*assumes reflp_lowEquiv: \<open>reflp lowEquiv\<close>
    and symp_lowEquiv: \<open>symp lowEquiv\<close>*)
begin

definition
  isInter :: \<open>'state \<Rightarrow> bool\<close>
where
  \<open>isInter s = (\<not>speculating s \<and> \<not>final s)\<close>

definition
  lowEquiv :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close>
where
  \<open>lowEquiv s s' \<equiv> isInter s \<and> isInter s' \<and> op\<^sub>\<L> s \<noteq> bot \<and> op\<^sub>\<L> s' \<noteq> bot \<longrightarrow> obsEq s s'\<close>

sublocale asAbstract: Statewise_OD
  where istate = istate       
    and validTrans = validTrans
    and final = final
    and isInter = isInter
    and lowEquiv = lowEquiv
    and op\<^sub>\<L> = op\<^sub>\<L>
  apply standard
  subgoal unfolding isInter_def by auto
  subgoal 
    unfolding lowEquiv_def apply auto
    apply (metis (mono_tags) classes_eq_iff_equivp equivp_lowEquiv)
    by (metis classes_eq_iff_equivp equivp_lowEquiv)
  subgoal 
    apply (rule sympI)
    using equivp_lowEquiv 
    unfolding lowEquiv_def apply auto
    by (meson equivp_symp)
  .


thm  asAbstract.consume_def
definition \<open>consume s vl vl' \<equiv>
  if \<not>speculating s then vl \<noteq> [] \<and> op\<^sub>\<L> s = hd vl \<and> vl' = tl vl 
  else vl' = vl
\<close> 

lemma consume_asAbstract:
  assumes \<open>asAbstract.consume s vl vl'\<close> and \<open>\<not> final s\<close>
    shows \<open>consume s vl vl'\<close>
  using assms unfolding consume_def asAbstract.consume_def isInter_def
  by auto

(*abbreviation \<open>consume \<equiv> asAbstract.consume\<close> lemmas consume_def = asAbstract.consume_def*)
abbreviation \<open>hopeless \<equiv> asAbstract.hopeless\<close> 

lemma consume_finalE: \<open>final s \<Longrightarrow>
    consume s vl vl' \<Longrightarrow> (vl' = vl \<Longrightarrow> P) \<Longrightarrow> P\<close>
  unfolding consume_def isInter_def by auto

lemma consume_final_emptyE: \<open>final s \<Longrightarrow>
    consume s vl [] \<Longrightarrow> (vl = [] \<Longrightarrow> P) \<Longrightarrow> P\<close>
  apply (elim consume_finalE) by auto

(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft \<Delta> s vl s1 vl1 \<equiv>
 \<forall>s' vl'.
   validTrans (s, s') \<and> final s1 \<and> consume s vl vl' \<and> vl1 = [] \<longrightarrow> hopeless s' vl'"

lemma iactionLeft_asAbstract:
  assumes \<open>iactionLeft \<Delta> s vl s1 vl1\<close>
    shows \<open>asAbstract.iactionLeft (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
  using assms unfolding asAbstract.iactionLeft_def iactionLeft_def apply auto
  apply (elim consume_final_emptyE, assumption)
  by simp

(*
lemma \<open>final s \<Longrightarrow> iactionLeft \<Delta> s vl s1 vl1 \<longleftrightarrow> hopeless s vl\<close>
  unfolding iactionLeft_def apply auto
  subgoal
    apply (erule allE[where x = s],erule allE[where x = vl],elim conjE impE)
     apply (drule final_terminal)

  subgoal for s' vl'
    apply (erule allE[where x = s'],erule allE[where x = vl'],erule impE)
    apply simp
    apply (elim disjE, simp_all)
  apply (drule final_terminal, simp_all add: isInter_def)
  apply (elim consume_finalE, assumption)
  apply simp
*)

definition iactionRight where
"iactionRight \<Delta> s vl s1 vl1 \<equiv>
 \<forall>s1' vl1'.
   validTrans (s1, s1') \<and> final s \<and> consume s1 vl1 vl1' \<and> vl = [] \<longrightarrow> hopeless s1' vl1'"

lemma iactionRight_asAbstract:
  assumes \<open>iactionRight \<Delta> s vl s1 vl1\<close>
    shows \<open>asAbstract.iactionRight (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
  using assms unfolding asAbstract.iactionRight_def iactionRight_def apply auto
  apply (elim consume_finaconsume_asAbstractl_emptyE, assumption)
  by auto

(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> s' vl' s1' vl1'.
   validTrans (s, s') \<and> consume s vl vl' \<and> validTrans (s1, s1') \<and> consume s1 vl1 vl1' \<and>
   \<not>final s \<or> \<not>final s1
   \<longrightarrow>  
   hopeless s' vl' \<or> hopeless s1' vl1' \<or> 
   (\<Delta> s' vl' s1' vl1' \<and> lowEquiv s' s1')"

lemma saction_asAbstract:
  assumes \<open>saction \<Delta> s vl s1 vl1\<close> \<open>lowEquiv s s1\<close> \<open>\<Delta> s vl s1 vl1\<close>
    shows \<open>asAbstract.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
  using assms unfolding saction_def asAbstract.saction_def apply (intro allI impI)
  apply (elim conjE)
  apply (cases \<open>\<not> final s \<or> \<not> final s1\<close>)
  apply auto[1]
  unfolding de_Morgan_disj not_not apply (elim conjE)
  apply simp
  apply (drule final_terminal, assumption)
  apply (drule final_terminal, assumption)
  apply (erule consume_finalE, assumption)
  apply (erule consume_finalE, assumption)
  by simp


(* *)

abbreviation \<open>unwindFor \<Delta> s vl s1 vl1 \<equiv> 
   iactionLeft \<Delta> s vl s1 vl1 \<and>
   iactionRight \<Delta> s vl s1 vl1 \<and>
   saction \<Delta> s vl s1 vl1\<close>


lemma unwindFor_asAbstract:
  assumes \<open>unwindFor \<Delta> s vl s1 vl1\<close>  \<open>lowEquiv s s1\<close> \<open>\<Delta> s vl s1 vl1\<close>
    shows \<open>asAbstract.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
using assms proof (elim conjE,intro conjI)
  assume \<open>iactionRight \<Delta> s vl s1 vl1\<close>
    thus \<open>asAbstract.iactionRight (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
    by (rule iactionRight_asAbstract)
next
  assume \<open>iactionLeft \<Delta> s vl s1 vl1\<close>
    thus \<open>asAbstract.iactionLeft (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
      by (rule iactionLeft_asAbstract)
next
  assume \<open>saction \<Delta> s vl s1 vl1\<close> \<open>lowEquiv s s1\<close> \<open>\<Delta> s vl s1 vl1\<close>
    thus \<open>asAbstract.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
    by (rule saction_asAbstract)
qed

abbreviation \<open>reachNT \<equiv> asAbstract.reachNT\<close>

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reachNT s1 \<and> \<Delta> s vl s1 vl1 \<and> lowEquiv s s1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 \<or>
   unwindFor \<Delta> s vl s1 vl1"

abbreviation \<open>secure \<equiv> asAbstract.secure\<close>

lemma unwind_secure:
  assumes init: "(\<And>vl s s1 vl1. \<lbrakk>lowEquiv s s1; istate s; istate s1; vl = vl1\<rbrakk> \<Longrightarrow> \<Delta> s vl s1 vl1)"
      and unwind: "unwind \<Delta>"
    shows secure
proof (rule asAbstract.unwind_secure)
  fix vl :: \<open>'lowOp list\<close> and vl1 s s1 assume \<open>lowEquiv s s1\<close> \<open>istate s\<close> \<open>istate s1\<close> \<open>vl = vl1\<close>
  thus \<open>\<Delta> s vl s1 vl1\<close>
    by (rule init)
next
  show \<open>asAbstract.unwind (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1)\<close>
  unfolding asAbstract.unwind_def
  proof (intro allI impI; elim conjE)
    fix s vl s1 vl1
    assume r1: \<open>reachNT s\<close> and r2: \<open>reachNT s1\<close>
       and \<Delta>:  \<open>\<Delta> s vl s1 vl1\<close> and leq: \<open>lowEquiv s s1\<close>
    show \<open>hopeless s vl \<or> hopeless s1 vl1 \<or>
          asAbstract.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1) s vl s1 vl1\<close>
    proof (cases \<open>hopeless s vl\<close>)
      case hopeless: False
      show ?thesis 
      proof (cases \<open>hopeless s1 vl1\<close>)
        case hopeless1: False
        have \<open>unwindFor \<Delta> s vl s1 vl1\<close>
          using unwind[unfolded unwind_def] r1 r2 \<Delta> hopeless hopeless1 leq by auto
        thus ?thesis
          using \<Delta> leq by (intro disjI2 unwindFor_asAbstract)
      qed (rule disjI2, rule disjI1)
    qed (rule disjI1)
  qed
qed

end
end
