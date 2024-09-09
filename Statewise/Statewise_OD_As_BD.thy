theory Statewise_OD_As_BD
  imports Statewise_OD
begin

context Statewise_OD
begin


(* TODO - introduce later*)
interpretation lowEquivs: list_all2_lemmas \<open>(\<approx>\<^sub>\<L>)\<close> \<open>(\<approx>\<^sub>\<L>)\<close>
  by (rule list_all2_lemmas_lowEquivs)

text \<open>OD as instance of \<forall>\<forall> BD Security:\<close>

definition B :: "'state \<Rightarrow> 'lowOp list \<Rightarrow> 'state \<Rightarrow> 'lowOp list \<Rightarrow> bool"
where 
"B s lops s' lops' \<equiv> s \<approx>\<^sub>\<L> s' \<and> lops = lops'"
                            
sublocale asBD: BD_Security_STS 
    where istate = istate and validTrans = validTrans
      and isSec = isInter and getSec = op\<^sub>\<L> 
      and isObs = isObs and getObs = getObs
      and T = T and B = B
  ..

lemma S_eq_ops\<^sub>\<L>[simp]: \<open>asBD.S = ops\<^sub>\<L>\<close>
  unfolding asBD.S_def ops\<^sub>\<L>_def by auto


lemma O_Cons[simp]: "asBD.O (trn # tr) = getObs trn # asBD.O tr"
  by (auto simp add: isObs)

lemma O_length[simp]: "length (asBD.O tr) = length tr"
by(induct tr, auto)

lemma O_Nil_iff[simp]: "asBD.O tr = [] \<longleftrightarrow> tr = []"
by(induct tr, auto)

lemma O_eq_lengthD: \<open>asBD.O tr = asBD.O tr' \<Longrightarrow> length tr = length tr'\<close>
  using O_length by metis

lemma O_imp_lowEquivs:
  assumes O: \<open>asBD.O tr = asBD.O tr'\<close>
    shows \<open>tr \<approx>\<^sub>\<L> tr'\<close>
using assms proof -
  assume O: \<open>asBD.O tr = asBD.O tr'\<close>
  have len_tr: \<open>length tr = length tr'\<close>
    using O by (rule O_eq_lengthD)
  show \<open>tr \<approx>\<^sub>\<L> tr'\<close>
    using len_tr O apply (induct tr tr' rule: list_induct2)
    apply auto
    by (intro lowEquivs.ConsI getObs_imp_lowEquiv)    
qed

lemma ForAll_ForAll_Secure_imp_secure: "asBD.ForAll_ForAll_Secure \<Longrightarrow> secure"
  unfolding secure_alt_def asBD.ForAll_ForAll_Secure_def apply auto
  unfolding B_def apply (rule O_imp_lowEquivs)
  by auto
  
lemma lowEquivs_imp_O: 
  assumes \<open>tr \<approx>\<^sub>\<L> tr'\<close> \<open>ops\<^sub>\<L> tr = ops\<^sub>\<L> tr'\<close>
    shows \<open>asBD.O tr = asBD.O tr'\<close>
using assms proof (induct rule: lowEquivs.inducts)
  case (Cons x xs y ys)
  then show ?case 
    apply (elim low_equiv_interE)
    apply simp
    apply (intro conjI lowEquiv_imp_getObs)
    using ops\<^sub>\<L>_Cons_unfold list.inject
    apply force+
    using Cons.hyps(1) apply force+
    using ops\<^sub>\<L>_Cons_unfold by fastforce
qed simp

abbreviation \<open>consume \<equiv> asBD.consume\<close> lemmas consume_def = asBD.consume_def
abbreviation \<open>hopeless \<equiv> asBD.hopeless\<close> lemmas hopeless_def = asBD.hopeless_def 

lemma consume2_eqE:
  assumes \<open>isInter s \<longleftrightarrow> isInter s1\<close> \<open>consume s vl vl'\<close> \<open>consume s1 vl vl1'\<close> 
      and E: \<open>vl' = vl1' \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by auto

lemma isInter_consume2_eqE:
  assumes \<open>isInter s \<longleftrightarrow> isInter s\<^sub>1\<close> \<open>isInter s\<close> \<open>consume s vl vl'\<close> \<open>consume s\<^sub>1 vl vl1'\<close> 
      and E: \<open>\<lbrakk>op\<^sub>\<L> s = op\<^sub>\<L> s\<^sub>1; vl' = vl1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by auto

abbreviation
  interactable 
where
  \<open>interactable \<equiv> asBD.produces isInter\<close>
lemmas interactable_def = asBD.produces_def

lemma hopeless_empty_interactable: \<open>hopeless s [] \<longleftrightarrow> interactable s\<close>
  unfolding hopeless_def interactable_def ops\<^sub>\<L>_def asBD.S_Nil_list_ex not_not
  by auto

lemma neverInter_lops_emptyE: \<open>neverInter tr \<Longrightarrow> (ops\<^sub>\<L> tr = [] \<Longrightarrow> P) \<Longrightarrow> P\<close>
  unfolding ops\<^sub>\<L>_def
  by (metis asBD.Nil_S_never asBD.S_def)

lemma final_not_hopelessE: 
  assumes final: \<open>final s\<close> and notHopeless: \<open>\<not>hopeless s sl\<close>
      and E: \<open>sl = [] \<Longrightarrow> P\<close>
    shows P
  apply (rule E)
  using notHopeless[unfolded hopeless_def] apply auto
  by (elim asBD.final_allE[OF final] completed_neverInterE neverInter_lops_emptyE)

thm asBD.final_allE completed_neverInterE neverInter_lops_emptyE
(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft s vl s1 \<equiv>
 \<forall>s'.
   validTrans (s, s') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s1 \<and> vl = [] \<longrightarrow> interactable s'"

lemma final_consume_lastE:
  assumes f: \<open>final s\<close>
      and consume: \<open>consume s vl []\<close>
      and P: \<open>vl = [] \<Longrightarrow> P\<close>
    shows P
  using consume apply (rule asBD.consume_lastE)
  using isInter_not_final[OF f] apply auto
  by (rule P)

lemma iactionLeft_asBD:
  assumes \<open>iactionLeft s vl s1\<close> and eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    shows \<open>asBD.iactionLeft \<Delta> s vl s1 vl\<close>
  using assms(1) unfolding asBD.iactionLeft_def iactionLeft_def
  apply (auto simp add: isObs)
  apply (erule consume2_eqE[OF eqInter],assumption)
  apply (frule isInter_not_final)
  apply (erule final_consume_lastE)
  using hopeless_empty_interactable eqInter
  by blast+

definition iactionRight where
"iactionRight s vl s1 \<equiv>
 \<forall>s1'.
   validTrans (s1, s1') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s \<and> vl = [] \<longrightarrow> interactable s1'"

lemma iactionRight_asBD:
  assumes \<open>iactionRight s vl s1\<close> and eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    shows \<open>asBD.iactionRight \<Delta> s vl s1 vl\<close>
  using assms(1) unfolding asBD.iactionRight_def iactionRight_def
  apply (auto simp add: isObs)
  apply (erule consume2_eqE[OF eqInter[symmetric]],assumption)
  apply (frule isInter_not_final)
  apply (erule final_consume_lastE)
  apply assumption
  apply safe
  using hopeless_empty_interactable eqInter by blast+


(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 \<equiv>
 \<forall> s' vl' s1'.
   validTrans (s, s') \<and> consume s vl vl' \<and> validTrans (s1, s1') \<and> consume s1 vl vl' \<and>
   \<not>(final s \<and> final s1)
   \<longrightarrow>  
   asBD.hopeless s' vl' \<or> hopeless s1' vl' \<or> 
   (\<Delta> s' vl' s1' \<and> s' \<approx>\<^sub>\<L> s1')"


lemma consume_empty[simp]: "consume s [] vl \<longleftrightarrow> vl = [] \<and> \<not>isInter s"
  unfolding consume_def by auto

lemma final_saction:
  assumes final: \<open>final s\<close> \<open>final s1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
      and nh: \<open>\<not> hopeless s vl\<close> and nh1: \<open>\<not> hopeless s1 vl\<close> 
      and \<Delta>: \<open>\<Delta> s vl s1\<close>
    shows \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
  using final leq unfolding asBD.saction_def apply (intro allI impI)
  apply (elim conjE)
  apply (drule final_terminal, assumption)
  apply (drule final_terminal, assumption)
  apply (intro disjI2)
  apply (erule final_not_hopelessE[OF _ nh])
  apply (intro conjI lowEquiv_imp_getObs)
  using \<Delta> by simp_all

lemma saction_asBD:
  assumes \<open>saction \<Delta> s vl s1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
      and nh: \<open>\<not> hopeless s vl\<close> and nh1: \<open>\<not> hopeless s1 vl\<close> and \<Delta>: \<open>\<Delta> s vl s1\<close>
    shows \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
  using assms(2) unfolding asBD.saction_def apply (intro allI impI)
  apply (elim conjE)
  apply (cases \<open>final s \<and> final s1\<close>)
  subgoal
    apply (elim conjE)
    apply (drule final_terminal, assumption)
    apply (drule final_terminal, assumption)
    apply (intro disjI2)
    apply (erule final_not_hopelessE[OF _ nh])
    apply (intro conjI lowEquiv_imp_getObs)
    using \<Delta> by simp_all
  subgoal for s' vl' s1' vl1'
  proof -
    assume leq: "s \<approx>\<^sub>\<L> s1"
      and validTrans: "validTrans (s, s')" "validTrans (s1, s1')"
      and consume: "consume s vl vl'" "consume s1 vl vl1'"
      and "isObs s"
      and "isObs s1"
      and not_final: "\<not> (final s \<and> final s1)"
    have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
      using leq low_equiv_interE by blast
    have vls: \<open>vl' = vl1'\<close>
      using consume by (elim consume2_eqE[OF eqInter])
    hence consume': \<open>consume s1 vl vl'\<close>
      using consume(2) by clarify
    have nxt: \<open>hopeless s' vl' \<or> hopeless s1' vl' \<or> \<Delta> s' vl' s1' \<and> s' \<approx>\<^sub>\<L> s1'\<close>
      using validTrans consume(1) consume' not_final
      using assms(1) unfolding saction_def apply -
      apply (erule allE[where x = s'], erule allE[where x = vl'], 
             elim allE[where x = s1'] impE)
      by auto
    have obs: \<open>getObs s = getObs s1\<close>
      using leq apply (elim lowEquiv_imp_getObs[rotated])
      by (elim isInter_consume2_eqE[OF eqInter _ consume(1) consume'])
    thus "hopeless s' vl' \<or> hopeless s1' vl1' \<or> getObs s = getObs s1 \<and> \<Delta> s' vl' s1' \<and> s' \<approx>\<^sub>\<L> s1' \<and> 
          vl' = vl1'"
      using nxt vls by simp
  qed
  .

(* *)

abbreviation \<open>unwindFor \<Delta> s vl s1 \<equiv> 
   iactionLeft s vl s1 \<and>
   iactionRight s vl s1 \<and>
   saction \<Delta> s vl s1\<close>


lemma unwindFor_asBD:
  assumes \<open>unwindFor \<Delta> s vl s1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    and nh: \<open>\<not> hopeless s vl\<close> \<open>\<not> hopeless s1 vl\<close> and \<Delta>: \<open>\<Delta> s vl s1\<close>
  shows \<open>asBD.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
using assms(1) proof (elim conjE,intro conjI)
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  show \<open>asBD.finish s vl s1 vl\<close>
    using lowEquiv_imp_getObs[OF _ leq] unfolding asBD.finish_def asBD.eqObs_def apply (auto simp add: isObs)
    by (metis eqInter isInter_consume2_eqE)+
next
  assume iar: \<open>iactionRight s vl s1\<close>
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  show \<open>asBD.iactionRight (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
    using iar eqInter by (rule iactionRight_asBD)
next
  assume ial: \<open>iactionLeft s vl s1\<close>
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  show \<open>asBD.iactionLeft (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
    using ial eqInter by (rule iactionLeft_asBD)
next
  assume \<open>saction \<Delta> s vl s1\<close>
    thus \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1) s vl s1 vl\<close>
    using leq nh \<Delta> by (rule saction_asBD)
qed

abbreviation \<open>reachNT \<equiv> asBD.reachNT\<close>

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1.
   reachNT s \<and> reachNT s1 \<and> \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl \<or>
   unwindFor \<Delta> s vl s1"

lemma unwind_secure:
  assumes init: "(\<And>vl s s1. \<lbrakk>s \<approx>\<^sub>\<L> s1; istate s; istate s1\<rbrakk> \<Longrightarrow> \<Delta> s vl s1)"
      and unwind: "unwind \<Delta>"
  shows secure
proof (rule ForAll_ForAll_Secure_imp_secure[OF asBD.unwind_secure[where \<Delta> = \<open>\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1 \<and> vl = vl1\<close>], unfolded B_def])
  fix vl :: \<open>'lowOp list\<close> and vl1 s s1 assume \<open>s \<approx>\<^sub>\<L> s1 \<and> vl = vl1\<close> \<open>istate s\<close> \<open>istate s1\<close>
  thus \<open>\<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1  \<and> vl = vl1\<close>
    apply (elim conjE)
    apply (intro conjI)
    by (rule init)
next
  show \<open>asBD.unwind (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1  \<and> vl = vl1)\<close>
  unfolding asBD.unwind_def
  proof (simp add: isObs,intro allI impI; elim conjE)
    fix s vl s1 vl1
    assume r1: \<open>reachNT s\<close> and r2: \<open>reachNT s1\<close>
       and \<Delta>:  \<open>\<Delta> s vl s1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    show \<open>hopeless s vl \<or> hopeless s1 vl \<or>
          asBD.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1  \<and> vl = vl1) s vl s1 vl\<close>
    proof (cases \<open>hopeless s vl\<close>)
      case hopeless: False
      show ?thesis 
      proof (cases \<open>hopeless s1 vl\<close>)
        case hopeless1: False
        have \<open>unwindFor \<Delta> s vl s1\<close>
          using unwind[unfolded unwind_def] r1 r2 \<Delta> hopeless hopeless1 leq by auto
        thus ?thesis
          using leq hopeless hopeless1 \<Delta> by (intro disjI2 unwindFor_asBD)
      qed (rule disjI2, rule disjI1)
    qed (rule disjI1)
  qed
qed

end 
end
