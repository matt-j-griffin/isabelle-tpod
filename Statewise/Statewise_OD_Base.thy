theory Statewise_OD_Base
  imports "../ForAllForAllSecure/BD_Security_STS"
          "../OD"
          "HOL-ex.Sketch_and_Explore" (* TODO *)
begin


locale Statewise_OD_Base = System_Model istate validTrans final
  for istate :: \<open>'state \<Rightarrow> bool\<close> and validTrans :: \<open>'state \<times> 'state \<Rightarrow> bool\<close>
  and final :: \<open>'state \<Rightarrow> bool\<close>
+ 
  fixes isInter :: \<open>'state \<Rightarrow> bool\<close> 
    and op\<^sub>\<L> :: \<open>'state \<Rightarrow> 'lowOp\<close> 
    and low_equiv :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<close> 100)
    and op\<^sub>\<H> :: "'state \<Rightarrow> 'highOp"
    and u :: "'state \<Rightarrow> bool"

  assumes isInter_not_final: \<open>\<And>x. final x \<Longrightarrow> \<not> isInter x\<close>
      assumes equivp_lowEquiv: \<open>\<And>x y. \<lbrakk>isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y\<rbrakk> \<Longrightarrow> x \<approx>\<^sub>\<L> y = ((\<approx>\<^sub>\<L>) x = (\<approx>\<^sub>\<L>) y)\<close> (* Equivalence under assumptions *)

      and reflp_lowEquiv: \<open>reflp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>
      and symp_lowEquiv: \<open>symp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>

      and low_equiv_interE: \<open>\<And>x y. \<lbrakk>x \<approx>\<^sub>\<L> y; isInter x \<longleftrightarrow> isInter y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>

begin

abbreviation \<open>completed \<equiv> list_all final\<close>
abbreviation \<open>neverInter \<equiv> never isInter\<close>

lemma completed_neverInterE[elim]: \<open>completed tr \<Longrightarrow> (neverInter tr \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using isInter_not_final by (induct tr, auto)

definition \<open>ops\<^sub>\<L> = filtermap isInter op\<^sub>\<L>\<close> 



(* TODO filtermap lemma for interpretation? *)
lemma ops\<^sub>\<L>_Cons_unfold: "ops\<^sub>\<L> (trn # tr) = (if isInter trn then op\<^sub>\<L> trn # ops\<^sub>\<L> tr else ops\<^sub>\<L> tr)"
  unfolding ops\<^sub>\<L>_def by auto


abbreviation 
  \<open>validTrace \<pi> \<equiv> istate (hd \<pi>) \<and> validFromS (hd \<pi>) \<pi> \<and> completedFrom (hd \<pi>) \<pi> \<and> \<pi> \<noteq> []\<close>

sublocale OD
  where Tr = \<open>{\<pi>. validTrace \<pi>}\<close>
    and ops\<^sub>\<L> = ops\<^sub>\<L>
    (*and lowEquiv = lowEquiv*)
  .


lemma secure_alt_def: \<open>secure = 
    (\<forall>\<pi>\<^sub>1 \<pi>\<^sub>2. validTrace \<pi>\<^sub>1 \<and> validTrace \<pi>\<^sub>2 \<and> (hd \<pi>\<^sub>1) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>2) \<longrightarrow>
      secureFor \<pi>\<^sub>1 \<pi>\<^sub>2
)\<close>
  using secure_def by auto


(* TODO - introduce later*)
lemma list_all2_lemmas_lowEquivs: \<open>list_all2_lemmas (\<approx>\<^sub>\<L>\<^sub>s) (\<approx>\<^sub>\<L>)\<close>
  apply (standard)
  by blast

text \<open>OD as instance of \<forall>\<forall> BD Security:\<close>

definition isObs :: "'state \<Rightarrow> bool" where 
"isObs s \<equiv> True"

lemma isObs: "isObs s" unfolding isObs_def by auto

definition getObs :: "'state \<Rightarrow> 'state set" where 
"getObs s' \<equiv> {s . s \<approx>\<^sub>\<L> s'}"

lemma getObs_imp_lowEquiv: "getObs s = getObs s' \<Longrightarrow> s \<approx>\<^sub>\<L> s'"
  unfolding getObs_def Collect_eq 
  apply (erule allE[where x = s])
  by (meson reflpE reflp_lowEquiv)

lemma lowEquiv_eq:
  fixes s :: 'state assumes "(\<approx>\<^sub>\<L>) s = (\<approx>\<^sub>\<L>) s'" shows "{sa. sa \<approx>\<^sub>\<L> s} = {s. s \<approx>\<^sub>\<L> s'}"
  using assms unfolding Collect_eq apply auto
  by (metis sympE symp_lowEquiv)+

lemma lowEquiv_imp_getObs: "\<lbrakk>isInter s \<Longrightarrow>  op\<^sub>\<L> s = op\<^sub>\<L> s'; s \<approx>\<^sub>\<L> s'\<rbrakk> \<Longrightarrow> getObs s = getObs s'"
  apply (drule equivp_lowEquiv)
  unfolding getObs_def
  using lowEquiv_eq by blast
  
definition \<open>ops\<^sub>\<H> = filtermap isInter op\<^sub>\<H>\<close>

text \<open>OD with High Ops as instance of \<forall>\<forall> BD Security:\<close>

definition 
  getSec :: \<open>'state \<Rightarrow> ('lowOp \<times> 'highOp)\<close>
where
  \<open>getSec s = (op\<^sub>\<L> s, op\<^sub>\<H> s)\<close>

definition B :: "'state \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> 'state \<Rightarrow> ('lowOp \<times> 'highOp) list \<Rightarrow> bool"
where 
  "B s ops s' ops' \<equiv> s \<approx>\<^sub>\<L> s' \<and> unzipL ops = unzipL ops'"
                         
sublocale asBD: BD_Security_STS 
    where istate = istate and validTrans = validTrans
      and isSec = isInter and getSec = getSec 
      and isObs = isObs and getObs = getObs
      and T = \<open>Not o u\<close> and B = B
  ..

lemma S_eq_ops: \<open>asBD.S tr = zip (ops\<^sub>\<L> tr) (ops\<^sub>\<H> tr)\<close>
unfolding asBD.S_def unfolding getSec_def ops\<^sub>\<L>_def ops\<^sub>\<H>_def proof (induct tr)
  case (Cons s tr)
  thus ?case 
    by (cases \<open>isInter s\<close>, simp_all)
qed simp

lemma length_ops: \<open>length (ops\<^sub>\<L> tr) = length (ops\<^sub>\<H> tr)\<close>
  unfolding ops\<^sub>\<L>_def ops\<^sub>\<H>_def by (rule length_filtermap_eq)

lemma S_unzipL[simp]: \<open>unzipL (asBD.S tr) = ops\<^sub>\<L> tr\<close>
  unfolding S_eq_ops by (intro length_ops zip_unzip(1))

lemma O_Cons[simp]: "asBD.O (trn # tr) = getObs trn # asBD.O tr"
  by (auto simp add: isObs)

lemma O_length[simp]: "length (asBD.O tr) = length tr"
by(induct tr, auto)

lemma O_Nil_iff[simp]: "asBD.O tr = [] \<longleftrightarrow> tr = []"
by(induct tr, auto)

lemma O_eq_lengthD: \<open>asBD.O tr = asBD.O tr' \<Longrightarrow> length tr = length tr'\<close>
  using O_length by metis

interpretation lowEquivs: list_all2_lemmas \<open>(\<approx>\<^sub>\<L>\<^sub>s)\<close> \<open>(\<approx>\<^sub>\<L>)\<close>
  by (rule list_all2_lemmas_lowEquivs)

lemma O_imp_lowEquivs:
  assumes O: \<open>asBD.O tr = asBD.O tr'\<close>
    shows \<open>tr \<approx>\<^sub>\<L>\<^sub>s tr'\<close>
using assms proof -
  assume O: \<open>asBD.O tr = asBD.O tr'\<close>
  have len_tr: \<open>length tr = length tr'\<close>
    using O by (rule O_eq_lengthD)
  show \<open>tr \<approx>\<^sub>\<L>\<^sub>s tr'\<close>
    using len_tr O apply (induct tr tr' rule: list_induct2)
    apply auto
    by (intro lowEquivs.ConsI getObs_imp_lowEquiv)    
qed

lemma lowEquivs_imp_O:
  assumes \<open>tr \<approx>\<^sub>\<L>\<^sub>s tr'\<close> \<open>ops\<^sub>\<L> tr = ops\<^sub>\<L> tr'\<close>
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

abbreviation
  interactable 
where
  \<open>interactable \<equiv> asBD.produces isInter\<close>
lemmas interactable_def = asBD.produces_def

lemma hopeless_empty_interactable: \<open>hopeless s [] \<longleftrightarrow> interactable s\<close>
  unfolding hopeless_def interactable_def ops\<^sub>\<L>_def asBD.S_Nil_list_ex not_not
  by auto

lemma ops_emptyI:
  \<open>ops\<^sub>\<L> tr = [] \<Longrightarrow> ops\<^sub>\<H> tr = []\<close>
  \<open>ops\<^sub>\<H> tr = [] \<Longrightarrow> ops\<^sub>\<L> tr = []\<close>
  using length_ops[where tr = tr] by simp_all

lemma neverInter_lops_emptyE: 
  assumes major: \<open>neverInter tr\<close>
      and minor: \<open>\<lbrakk>ops\<^sub>\<L> tr = []; ops\<^sub>\<H> tr = []\<rbrakk> \<Longrightarrow> P\<close>
    shows P
proof -
  have \<open>zip (ops\<^sub>\<L> tr) (ops\<^sub>\<H> tr) = []\<close>
    using major unfolding asBD.Nil_S_never[unfolded S_eq_ops,symmetric] by order
  thus ?thesis
  unfolding zip_eq_Nil_iff proof (elim disjE)
    assume ops\<^sub>\<L>: "ops\<^sub>\<L> tr = []"
    thus P
      by (intro minor ops_emptyI(1)) 
  next
    assume ops\<^sub>\<H>: "ops\<^sub>\<H> tr = []"
    thus P
      by (intro minor ops_emptyI(2))
  qed
qed


lemma final_not_hopelessE:
  assumes final: \<open>final s\<close> and notHopeless: \<open>\<not>hopeless s sl\<close>
      and E: \<open>sl = [] \<Longrightarrow> P\<close>
    shows P
proof (rule E)
  show "sl = []"
  using notHopeless[unfolded hopeless_def] apply auto
  apply (elim asBD.final_allE[OF final] completed_neverInterE neverInter_lops_emptyE)
  apply simp
  unfolding S_eq_ops by simp
qed

(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft s vl s1 vl1 \<equiv>
 \<forall>s'.
   validTrans (s, s') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s1 \<and> vl = [] \<and> vl1 = [] \<longrightarrow> interactable s'"

lemma final_consume_lastE:
  assumes f: \<open>final s\<close>
      and consume: \<open>consume s vl []\<close>
      and P: \<open>vl = [] \<Longrightarrow> P\<close>
    shows P
  using consume apply (rule asBD.consume_lastE)
  using isInter_not_final[OF f] apply auto
  by (rule P)

lemma iactionLeft_asBD:
  assumes ial: \<open>iactionLeft s vl s1 vl1\<close>
      and length_vls: \<open>length vl = length vl1\<close>
    shows \<open>asBD.iactionLeft \<Delta> s vl s1 vl1\<close>
unfolding asBD.iactionLeft_def proof safe
  fix s' :: 'state and vl' :: "('lowOp \<times> 'highOp) list"
  assume vT: "validTrans (s, s')"
    and consume: "consume s vl vl'"
    and final1: "final s1"
    and consume1: "consume s1 vl1 []"
  note not_isInter1 = isInter_not_final[OF final1]
  have vl1_empty: \<open>vl1 = []\<close>
    using final1 consume1 by (rule final_consume_lastE)
  hence vl_empty: \<open>vl = []\<close>
    using length_vls by fastforce
  hence vl'_empty: \<open>vl' = []\<close>
    using consume by fastforce
  have not_isInter: \<open>\<not>isInter s\<close> 
    using consume vl_empty by force
  have \<open>interactable s'\<close>
    using ial unfolding iactionLeft_def apply (elim allE[where x = s'] impE)
    using vT not_isInter not_isInter1 final1 vl1_empty vl_empty by (intro conjI)
  thus "hopeless s' vl'"
    unfolding vl'_empty hopeless_empty_interactable .
qed (use isObs in blast)

definition iactionRight where
"iactionRight s vl s1 vl1 \<equiv>
 \<forall>s1'.
   validTrans (s1, s1') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s \<and> vl = [] \<and> vl1 = [] \<longrightarrow> interactable s1'"

lemma iactionRight_asBD:
  assumes iar: \<open>iactionRight s vl s1 vl1\<close>
      and length_vls: \<open>length vl = length vl1\<close>
    shows \<open>asBD.iactionRight \<Delta> s vl s1 vl1\<close>
unfolding asBD.iactionRight_def sketch safe
proof safe
  fix s1' :: 'state and vl1' :: "('lowOp \<times> 'highOp) list"
  assume vT: "validTrans (s1, s1')"
    and consume1: "consume s1 vl1 vl1'"
    and final: "final s"
    and consume: "consume s vl []"
  note not_isInter = isInter_not_final[OF final]
  have vl_empty: \<open>vl = []\<close>
    using final consume by (rule final_consume_lastE)
  hence vl1_empty: \<open>vl1 = []\<close>
    using length_vls by fastforce
  hence vl1'_empty: \<open>vl1' = []\<close>
    using consume1 by fastforce
  have not_isInter1: \<open>\<not>isInter s1\<close> 
    using consume1 vl1_empty by force
  have \<open>interactable s1'\<close>
    using iar unfolding iactionRight_def apply (elim allE[where x = s1'] impE)
    using vT not_isInter not_isInter1 final vl1_empty vl_empty by (intro conjI)
  thus "hopeless s1' vl1'"
    unfolding vl1'_empty hopeless_empty_interactable .
qed (use isObs in blast)

(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> s' vl' s1' vl1'.
   validTrans (s, s') \<and> consume s vl vl' \<and> validTrans (s1, s1') \<and> consume s1 vl1 vl1' \<and>
   \<not>(final s \<and> final s1)
   \<longrightarrow>  
   asBD.hopeless s' vl' \<or> hopeless s1' vl1' \<or> 
   (\<Delta> s' vl' s1' vl1' \<and> s' \<approx>\<^sub>\<L> s1')"

lemma final_saction:
  assumes final: \<open>final s\<close> \<open>final s1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
      and nh: \<open>\<not> hopeless s vl\<close> and nh1: \<open>\<not> hopeless s1 vl1\<close> 
      and \<Delta>: \<open>\<Delta> s vl s1 vl1\<close> and lops: \<open>unzipL vl = unzipL vl1\<close>
    shows \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
unfolding asBD.saction_def proof (intro allI impI , elim conjE)
  fix s' s1' :: 'state and vl' vl1' :: "('lowOp \<times> 'highOp) list"
  assume trans: "validTrans (s, s')" "validTrans (s1, s1')"
    and consume: "consume s vl vl'"  "consume s1 vl1 vl1'"
  note s_eq_s' = final_terminal[OF trans(1) final(1)]
  note s1_eq_s1' = final_terminal[OF trans(2) final(2)]
  note not_isInter = isInter_not_final[OF final(1)] isInter_not_final[OF final(2)]
  note consumeE = asBD.consume_notSecE[OF consume(1) not_isInter(1)] asBD.consume_notSecE[OF consume(2) not_isInter(2)]
  show "hopeless s' vl' \<or> hopeless s1' vl1' \<or> getObs s = getObs s1 \<and> \<Delta> s' vl' s1' vl1' \<and> s' \<approx>\<^sub>\<L> s1' \<and> unzipL vl' = unzipL vl1'"
    apply (intro disjI2)
    unfolding s_eq_s' s1_eq_s1'
    apply (rule consumeE(1), rule consumeE(2))
    using leq not_isInter lops
    apply (intro conjI lowEquiv_imp_getObs)
    apply simp_all
    using \<Delta> by simp_all
qed

lemma saction_asBD:
  assumes saction: \<open>saction \<Delta> s vl s1 vl1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
      and nh: \<open>\<not> hopeless s vl\<close> \<open>\<not> hopeless s1 vl1\<close> 
      and \<Delta>: \<open>\<lbrakk>final s; final s1; vl = []; vl1 = []\<rbrakk> \<Longrightarrow> \<Delta> s vl s1 vl1\<close>
      and lops: \<open>unzipL vl = unzipL vl1\<close>
    shows \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
proof (cases \<open>final s \<and> final s1\<close>)
  case True
  thus ?thesis
    using nh leq lops apply (elim conjE)
    apply (intro \<Delta> final_saction)
             apply assumption+
    by (erule final_not_hopelessE, blast+)+
next
  case False
  then show ?thesis 
  unfolding asBD.saction_def
  proof (intro allI impI, elim conjE)
  fix s' s1' :: 'state and vl' vl1' :: "('lowOp \<times> 'highOp) list"
  assume not_final: "\<not> (final s \<and> final s1)"
    and validTrans: "validTrans (s, s')" "validTrans (s1, s1')"
    and consume: "consume s vl vl'"  "consume s1 vl1 vl1'"
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
    have vls: \<open>unzipL vl' = unzipL vl1'\<close> (*TODO *)
      by (metis (no_types, lifting) consume(1) consume(2) consume_def eqInter list.collapse list.inject lops unzipL.simps(2))
    have nxt: \<open>hopeless s' vl' \<or> hopeless s1' vl1' \<or> \<Delta> s' vl' s1' vl1' \<and> s' \<approx>\<^sub>\<L> s1'\<close>
      using validTrans consume not_final
      using assms(1) unfolding saction_def apply -
      apply (erule allE[where x = s'], erule allE[where x = vl'], 
             elim allE[where x = s1'] impE)
      by auto
    have obs: \<open>getObs s = getObs s1\<close>
      using leq apply (elim lowEquiv_imp_getObs[rotated])
      using consume eqInter unfolding consume_def apply auto
      using lops unfolding getSec_def 
      by (metis S_unzipL asBD.S_Cons_unfold consume(1) consume(2) consume_def list.collapse list.inject ops\<^sub>\<L>_Cons_unfold unzipL.simps(2)) (* TODO *)
    show "hopeless s' vl' \<or> hopeless s1' vl1' \<or> getObs s = getObs s1 \<and> \<Delta> s' vl' s1' vl1' \<and> s' \<approx>\<^sub>\<L> s1' 
            \<and> unzipL vl' = unzipL vl1'"
      using obs vls nxt by simp
  qed
qed

(* *)

abbreviation \<open>unwindFor \<Delta> s vl s1 vl1 \<equiv> 
   iactionLeft s vl s1 vl1 \<and>
   iactionRight s vl s1 vl1 \<and>
   saction \<Delta> s vl s1 vl1\<close>

lemma unwindFor_asBD:
  assumes \<open>unwindFor \<Delta> s vl s1 vl1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    and nh: \<open>\<not> hopeless s vl\<close> \<open>\<not> hopeless s1 vl1\<close> 
    and \<Delta>: \<open>\<lbrakk>final s; final s1; vl = []; vl1 = []\<rbrakk> \<Longrightarrow> \<Delta> s vl s1 vl1\<close>
    and lops: \<open>unzipL vl = unzipL vl1\<close>
  shows \<open>asBD.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
using assms(1) proof (elim conjE,intro conjI)
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  show \<open>asBD.finish s vl s1 vl1\<close>
    using lowEquiv_imp_getObs[OF _ leq] unfolding asBD.finish_def asBD.eqObs_def apply (auto simp add: isObs)
    using isInter_not_final by force+
next
  assume iar: \<open>iactionRight s vl s1 vl1\<close>
  show \<open>asBD.iactionRight (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
    using iar unzipL_length[OF lops] by (rule iactionRight_asBD)
next
  assume ial: \<open>iactionLeft s vl s1 vl1\<close>
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  show \<open>asBD.iactionLeft (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
    using ial unzipL_length[OF lops] by (rule iactionLeft_asBD)
next
  assume \<open>saction \<Delta> s vl s1 vl1\<close>
    thus \<open>asBD.saction (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
    using leq nh \<Delta> lops by (rule saction_asBD)
qed

abbreviation \<open>reachNT \<equiv> asBD.reachNT\<close>

definition 
  unwind 
where
  "unwind \<Delta> \<equiv> \<forall> s vl s1 vl1.
     reachNT s \<and> reachNT s1 \<and> u s \<and> u s1 \<and> \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1
     \<longrightarrow>
    hopeless s vl \<or> hopeless s1 vl1 \<or> unwindFor \<Delta> s vl s1 vl1"

lemma unwind_ForAll_ForAll_Secure:
  assumes init: "(\<And>vl vl1 s s1. \<lbrakk>s \<approx>\<^sub>\<L> s1; unzipL vl = unzipL vl1; istate s; istate s1\<rbrakk> \<Longrightarrow> \<Delta> s vl s1 vl1)"
      and unwind: "unwind \<Delta>"
  shows asBD.ForAll_ForAll_Secure
proof (rule asBD.unwind_secure[where \<Delta> = \<open>\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1\<close>], unfold B_def, elim conjE)
  fix vl vl1 :: \<open>('lowOp \<times> 'highOp) list\<close> and s s1 assume \<open>s \<approx>\<^sub>\<L> s1\<close> \<open>unzipL vl = unzipL vl1\<close> \<open>istate s\<close> \<open>istate s1\<close>
  thus \<open>\<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1  \<and> unzipL vl = unzipL vl1\<close>
    by (intro conjI init)
next
  show \<open>asBD.unwind (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1)\<close>
  unfolding asBD.unwind_def Not_Not_comp  proof (intro allI impI; elim conjE)
    fix vl vl1 :: \<open>('lowOp \<times> 'highOp) list\<close> and s s1
    assume r1: \<open>reachNT s\<close> and r2: \<open>reachNT s1\<close>
       and lops: \<open>unzipL vl = unzipL vl1\<close> and u: \<open>u s\<close> \<open>u s1\<close>
       and \<Delta>:  \<open>\<Delta> s vl s1 vl1\<close> and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    show \<open>hopeless s vl \<or> hopeless s1 vl1 \<or>
          asBD.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<and> s \<approx>\<^sub>\<L> s1 \<and> unzipL vl = unzipL vl1) s vl s1 vl1\<close>
    proof (cases \<open>hopeless s vl\<close>)
      case hopeless: False
      show ?thesis 
      proof (cases \<open>hopeless s1 vl1\<close>)
        case hopeless1: False
        have \<open>unwindFor \<Delta> s vl s1 vl1\<close>
          using unwind[unfolded unwind_def] r1 r2 \<Delta> hopeless hopeless1 leq lops u by auto
        thus ?thesis
          using leq hopeless hopeless1 \<Delta> lops by (intro disjI2 unwindFor_asBD)
      qed (rule disjI2, rule disjI1)
    qed (rule disjI1)
  qed
qed

end 
end
