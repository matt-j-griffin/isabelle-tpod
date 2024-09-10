theory Statewise_OD
  imports
    Statewise_OD_Base
begin

locale Statewise_OD = System_Mod istate validTrans final
  for istate :: \<open>'state \<Rightarrow> bool\<close> and validTrans :: \<open>'state \<times> 'state \<Rightarrow> bool\<close>
  and final :: \<open>'state \<Rightarrow> bool\<close>
+ 
fixes isInter :: \<open>'state \<Rightarrow> bool\<close> and op\<^sub>\<L> :: \<open>'state \<Rightarrow> 'lowOp\<close>
    and low_equiv :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<close> 100)


  assumes isInter_not_final: \<open>\<And>x. final x \<Longrightarrow> \<not> isInter x\<close>
      assumes equivp_lowEquiv: \<open>\<And>x y. \<lbrakk>isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y\<rbrakk> \<Longrightarrow> x \<approx>\<^sub>\<L> y = ((\<approx>\<^sub>\<L>) x = (\<approx>\<^sub>\<L>) y)\<close> (* Equivalence under assumptions *)

      and reflp_lowEquiv: \<open>reflp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>
      and symp_lowEquiv: \<open>symp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>

      and low_equiv_interE: \<open>\<And>x y. \<lbrakk>x \<approx>\<^sub>\<L> y; isInter x \<longleftrightarrow> isInter y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>
(*
fixes TEST :: "'lowOp set"
*)
begin
(*
(*equivp TEST *) 
abbreviation "EXAMPLE x y \<equiv> ((isInter x \<longleftrightarrow> isInter y) \<and> ((isInter x \<longrightarrow> (op\<^sub>\<L> x \<in> TEST \<and> op\<^sub>\<L> y \<in> TEST)) \<longrightarrow> x = y)) "

lemma "EXAMPLE x y \<Longrightarrow> isInter x \<longleftrightarrow> isInter y"
  by auto

lemma reflp_E: \<open>reflp EXAMPLE\<close>
  unfolding reflp_def by auto

lemma symp_E: \<open>symp EXAMPLE\<close>
  unfolding symp_def by auto

lemma transp_asms: \<open>\<And>x y z. \<lbrakk>isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y\<rbrakk> \<Longrightarrow> 
       EXAMPLE x y \<longrightarrow>
       EXAMPLE y z \<longrightarrow> 
       EXAMPLE x z\<close>
  by auto
(* Equivalence under assumptions *)

lemma equivp_lowEquivQ:
  \<open>\<And>x y. \<lbrakk>(isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y)\<rbrakk> \<Longrightarrow> EXAMPLE x y = (EXAMPLE x = EXAMPLE y)\<close> 
  apply auto
  by metis+
*)

sublocale base: Statewise_OD_Base
  where istate = istate and validTrans = validTrans and final = final and isInter = isInter 
    and op\<^sub>\<L> = op\<^sub>\<L> and op\<^sub>\<H> = \<open>\<lambda>_. (1::nat)\<close> and u = \<open>\<lambda>_. True\<close>
    and low_equiv = low_equiv
proof standard
  fix x assume "final x" thus "\<not> isInter x" by (rule isInter_not_final)
next
  fix x y assume "isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y" 
  thus "x \<approx>\<^sub>\<L> y = ((\<approx>\<^sub>\<L>) x = (\<approx>\<^sub>\<L>) y)" by (rule equivp_lowEquiv)
next
  fix P x y assume "x \<approx>\<^sub>\<L> y"  "isInter x = isInter y \<Longrightarrow> P"
  thus P by (rule low_equiv_interE)
qed (rule reflp_lowEquiv symp_lowEquiv)+

abbreviation \<open>validTrace \<equiv> base.validTrace\<close>
abbreviation \<open>ops\<^sub>\<L> \<equiv> base.ops\<^sub>\<L>\<close> lemmas ops\<^sub>\<L>_def = base.ops\<^sub>\<L>_def
abbreviation \<open>interactable \<equiv> base.interactable\<close>
abbreviation \<open>reachNT \<equiv> base.reachNT\<close>

definition \<open>lops_only \<equiv> map (\<lambda>lop. (lop, 1))\<close>

definition \<open>hopeless s lops \<equiv> base.hopeless s (lops_only lops)\<close>
definition \<open>consume s lops lops' \<equiv> base.consume s (lops_only lops) (lops_only lops')\<close>


sublocale OD
  where Tr = \<open>{\<pi>. validTrace \<pi>}\<close>
    and ops\<^sub>\<L> = ops\<^sub>\<L>
    and low_equiv = low_equiv
  .

lemma secure_alt_def: \<open>secure = 
    (\<forall>\<pi>\<^sub>1 \<pi>\<^sub>2. validTrace \<pi>\<^sub>1 \<and> validTrace \<pi>\<^sub>2 \<and> (hd \<pi>\<^sub>1) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>2) \<longrightarrow>
      secureFor \<pi>\<^sub>1 \<pi>\<^sub>2
)\<close>
  using secure_def by auto

no_notation base.low_equivs (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<close> 100)

text \<open>OD as instance of \<forall>\<forall> BD Security:\<close>

lemma never_u[simp]: \<open>never (Not \<circ> (\<lambda>_. True)) \<pi>\<close>
  by auto

lemma S_ops\<^sub>\<L>: 
  assumes \<open>ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2\<close>
    shows \<open>unzipL (base.asBD.S \<pi>\<^sub>1) = unzipL (base.asBD.S \<pi>\<^sub>2)\<close>
using assms unfolding base.asBD.S_def base.getSec_def ops\<^sub>\<L>_def 
proof auto
  assume a1: "List_Filtermap.filtermap isInter op\<^sub>\<L> \<pi>\<^sub>1 = List_Filtermap.filtermap isInter op\<^sub>\<L> \<pi>\<^sub>2"
  have "base.getSec = (\<lambda>s. (op\<^sub>\<L> s, Suc 0))"
    using One_nat_def base.getSec_def by presburger
  then show "unzipL (List_Filtermap.filtermap isInter (\<lambda>s. (op\<^sub>\<L> s, Suc 0)) \<pi>\<^sub>1) = unzipL (List_Filtermap.filtermap isInter (\<lambda>s. (op\<^sub>\<L> s, Suc 0)) \<pi>\<^sub>2)"
    using a1 base.S_unzipL base.asBD.S_def ops\<^sub>\<L>_def by moura
qed

lemma bounds:
  assumes \<open>ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2\<close> \<open>hd \<pi>\<^sub>1 \<approx>\<^sub>\<L> hd \<pi>\<^sub>2\<close>
    shows \<open>base.B (hd \<pi>\<^sub>1) (base.asBD.S \<pi>\<^sub>1) (hd \<pi>\<^sub>2) (base.asBD.S \<pi>\<^sub>2)\<close>
  using assms unfolding base.B_def by (intro conjI S_ops\<^sub>\<L>)

lemma ForAll_ForAll_Secure_imp_secure: "base.asBD.ForAll_ForAll_Secure \<Longrightarrow> secure"
  unfolding secure_alt_def sketch safe
proof safe
  fix \<pi>\<^sub>1 \<pi>\<^sub>2 
  assume secure: base.asBD.ForAll_ForAll_Secure
    and i: "istate (hd \<pi>\<^sub>1)" "istate (hd \<pi>\<^sub>2)"
    and hd: "hd \<pi>\<^sub>1 \<approx>\<^sub>\<L> hd \<pi>\<^sub>2"
    and vT: "validFromS (hd \<pi>\<^sub>1) \<pi>\<^sub>1" "completedFrom (hd \<pi>\<^sub>1) \<pi>\<^sub>1" "\<pi>\<^sub>1 \<noteq> []"
            "validFromS (hd \<pi>\<^sub>2) \<pi>\<^sub>2" "completedFrom (hd \<pi>\<^sub>2) \<pi>\<^sub>2" "\<pi>\<^sub>2 \<noteq> []"
    and ops: "ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2"
  have \<open>base.asBD.ForAll_ForAll_Secure_For \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    using secure unfolding base.asBD.ForAll_ForAll_Secure_def by auto
  hence \<open> base.asBD.O \<pi>\<^sub>1 = base.asBD.O \<pi>\<^sub>2\<close>
    apply (elim impE conjE)
    apply clarify
    by (intro conjI never_u i hd vT bounds ops)
  thus "\<pi>\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>2"
    by (rule base.O_imp_lowEquivs)
qed
  
lemma getSec_op\<^sub>\<L>_eqI:
  assumes \<open>base.getSec s = base.getSec s\<^sub>1\<close>
    shows \<open>op\<^sub>\<L> s = op\<^sub>\<L> s\<^sub>1\<close>
  using assms unfolding base.getSec_def by auto

lemma isInter_consume2_eqE:
  assumes major: \<open>isInter s \<longleftrightarrow> isInter s\<^sub>1\<close> \<open>isInter s\<close> \<open>base.consume s vl vl'\<close> \<open>base.consume s\<^sub>1 vl vl1'\<close> 
      and minor: \<open>\<lbrakk>op\<^sub>\<L> s = op\<^sub>\<L> s\<^sub>1; vl' = vl1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  by (rule base.asBD.isSec_consume2_eqE[OF major], intro minor getSec_op\<^sub>\<L>_eqI)

(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft s vl s1 \<equiv>
 \<forall>s'.
   validTrans (s, s') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s1 \<and> vl = [] \<longrightarrow> interactable s'"

lemma iactionLeft_baseI: \<open>iactionLeft s (unzipL vl) s1 \<Longrightarrow> base.iactionLeft s vl s1 vl1\<close>
  unfolding base.iactionLeft_def iactionLeft_def by auto

definition iactionRight where
"iactionRight s vl s1 \<equiv>
 \<forall>s1'.
   validTrans (s1, s1') \<and> \<not> isInter s \<and> \<not> isInter s1 \<and> final s \<and> vl = [] \<longrightarrow> interactable s1'"

lemma iactionRight_baseI: \<open>iactionRight s (unzipL vl) s1 \<Longrightarrow> base.iactionRight s vl s1 vl1\<close>
  unfolding base.iactionRight_def iactionRight_def by auto

(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 \<equiv>
 \<forall> s' vl' s1'.
   validTrans (s, s') \<and> consume s vl vl' \<and> validTrans (s1, s1') \<and> consume s1 vl vl' \<longrightarrow>  
   hopeless s' vl' \<or> hopeless s1' vl' \<or> 
   (\<Delta> s' vl' s1' \<and> s' \<approx>\<^sub>\<L> s1')"

lemma lops_only_ops\<^sub>\<L>: \<open>base.asBD.S tr = lops_only (ops\<^sub>\<L> tr)\<close>
  unfolding lops_only_def ops\<^sub>\<L>_def map_filtermap base.asBD.S_def  base.getSec_def comp_apply ..

lemma lops_only_unzipL_S: \<open>lops_only (unzipL (base.asBD.S tr)) = base.asBD.S tr\<close>
  unfolding base.S_unzipL by (rule lops_only_ops\<^sub>\<L>[symmetric])

lemma base_consumeI: 
  assumes \<open>base.consume s vl vl'\<close>
    shows \<open>consume s (unzipL vl) (unzipL vl')\<close>
  using assms unfolding consume_def
  using base.S_unzipL base.asBD.S_def base.asBD.S_simps(1) base.asBD.S_single(2) base.asBD.filtermap_Nil_never_rhs base.consume_def base.getSec_def base.ops\<^sub>\<L>_Cons_unfold fst_conv list.collapse list.map_sel(1) list.sel(2) list.simps(9) lops_only_def map_tl ops\<^sub>\<L>_def
  by (smt (verit) ) (* TODO *)

lemma base_hopelessI: 
  assumes \<open>\<not>base.hopeless s' vl'\<close>
    shows \<open>\<not>hopeless s' (unzipL vl')\<close>
  using assms unfolding hopeless_def base.hopeless_def by (metis lops_only_unzipL_S)

lemma saction_baseI: 
  assumes saction: \<open>saction \<Delta> s (unzipL vl) s1\<close> and vl_eq: \<open>unzipL vl = unzipL vl1\<close>
      and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    shows \<open>base.saction (\<lambda>s vl s1 vl1. \<Delta> s (unzipL vl) s1) s vl s1 vl1\<close>
unfolding base.saction_def 
proof (intro allI impI disj_notI1 ; elim conjE)
  fix s' vl' s1' vl1'
  assume nh: "\<not> base.hopeless s' vl'" "\<not> base.hopeless s1' vl1'"
    and vT: "validTrans (s, s')" "validTrans (s1, s1')"
    and base_consume: "base.consume s vl vl'" "base.consume s1 vl1 vl1'"
  have eqInter: \<open>isInter s \<longleftrightarrow> isInter s1\<close>
    using leq low_equiv_interE by blast
  have vl'_eq: \<open>unzipL vl' = unzipL vl1'\<close>
    using base_consume eqInter vl_eq by (rule base.consume2_zip_eq)
  have consume: \<open>consume s (unzipL vl) (unzipL vl')\<close>
    using base_consume(1) by (rule base_consumeI)
  have consume1: \<open>consume s1 (unzipL vl) (unzipL vl')\<close> 
    unfolding vl_eq vl'_eq using base_consume(2) by (rule base_consumeI)
  have hopeless: \<open>\<not>hopeless s' (unzipL vl')\<close>
    using nh(1) by (rule base_hopelessI)
  have hopeless1: \<open>\<not>hopeless s1' (unzipL vl')\<close>
    using nh(2) unfolding vl'_eq by (rule base_hopelessI)
  show "\<Delta> s' (unzipL vl') s1' \<and> s' \<approx>\<^sub>\<L> s1'"
    using saction unfolding saction_def apply -
    apply (erule allE[where x = s'], erule allE[where x = \<open>unzipL vl'\<close>])
    apply (elim allE[where x = s1'] impE)
    using consume consume1 vT hopeless hopeless1 by simp_all
qed 

(* *)

abbreviation \<open>unwindFor \<Delta> s vl s1 \<equiv> 
   iactionLeft s vl s1 \<and>
   iactionRight s vl s1 \<and>
   saction \<Delta> s vl s1\<close>

lemma base_unwindForI: 
  assumes "unwindFor \<Delta> s (unzipL vl) s1" and vl_eq: \<open>unzipL vl = unzipL vl1\<close>
      and leq: \<open>s \<approx>\<^sub>\<L> s1\<close>
    shows "base.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s (unzipL vl) s1) s vl s1 vl1"  
  using assms by (elim conjE; intro conjI iactionLeft_baseI iactionRight_baseI saction_baseI)

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1.
   reachNT s \<and> reachNT s1 \<and> \<Delta> s vl s1 \<and> s \<approx>\<^sub>\<L> s1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl \<or>
   unwindFor \<Delta> s vl s1"

lemma base_unwindI:
  assumes unwind: \<open>unwind \<Delta>\<close>
    shows \<open>base.unwind (\<lambda>s vl s1 vl1. \<Delta> s (unzipL vl) s1)\<close>
unfolding base.unwind_def sketch (intro allI impI disj_notI1; elim conjE)
proof (intro allI impI disj_notI1 ; elim conjE)
  fix s vl s1 vl1 
  assume "\<not> base.hopeless s vl" "\<not> base.hopeless s1 vl1"
     "reachNT s"
     "reachNT s1"
     "\<Delta> s (unzipL vl) s1"
     and leq: "s \<approx>\<^sub>\<L> s1"
     and unzip: "unzipL vl = unzipL vl1"
  hence \<open>unwindFor \<Delta> s (unzipL vl) s1\<close> 
    using unwind unfolding unwind_def apply -
    apply (erule allE[where x = s], erule allE[where x = \<open>unzipL vl\<close>], elim disjE impE allE[where x = s1])
    subgoal by (intro conjI)
    apply (drule base_hopelessI, simp)
    by (drule base_hopelessI, drule base_hopelessI, simp)
  thus "base.unwindFor (\<lambda>s vl s1 vl1. \<Delta> s (unzipL vl) s1) s vl s1 vl1"
    using unzip leq by (rule base_unwindForI)
qed

lemma unwind_secure:
  assumes init: "(\<And>vl s s1. \<lbrakk>s \<approx>\<^sub>\<L> s1; istate s; istate s1\<rbrakk> \<Longrightarrow> \<Delta> s vl s1)"
      and unwind: "unwind \<Delta>"
  shows secure
  by (intro ForAll_ForAll_Secure_imp_secure base_unwindI init unwind
             base.unwind_ForAll_ForAll_Secure[where \<Delta> = \<open>\<lambda>s vl s1 vl1. \<Delta> s (unzipL vl) s1\<close>])

end 

end
