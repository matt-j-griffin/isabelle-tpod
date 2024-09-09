
definition toT :: "state list \<Rightarrow> trans list" where 
"toT sl \<equiv> zip (butlast sl) (tl sl)"

lemma toT_nth: "i < length sl-1 \<Longrightarrow> toT sl ! i = (sl!i, sl!(Suc i))"
unfolding toT_def by (auto simp: nth_butlast nth_tl) 

definition fromT :: "trans list \<Rightarrow> state list" where 
"fromT tr \<equiv> (fst (hd tr)) # map snd tr"

lemma toT_eq_Nil: "toT sl = [] \<longleftrightarrow> length sl \<le> Suc 0"
unfolding toT_def zip_eq_Nil_iff by (cases "sl") auto

lemma switch_istate2_validFrom2: 
"(sl = [] \<or> wfs (hd sl)) \<and> validSteps sl \<and> conformant sl \<longleftrightarrow> 
 (sl = [] \<or> istate2 (hd sl) \<and> validFrom2 (hd sl) (toT sl))"
unfolding conformant_piecewise
unfolding list_all_length
validTrans2.simps conformant_init_def
Aug.validFrom_nth toT_eq_Nil istate2_def conformant_step_def 
toT_def set_conv_nth validSteps_def apply auto 
	apply (auto simp add: hd_conv_nth) 
	unfolding srcOf_def tgtOf_def 
  apply (metis fst_conv length_greater_0_conv nth_butlast nth_zip zip_eq_Nil_iff)  
  apply (simp add: conformant_step_def nth_butlast nth_tl)
  apply (simp add: conformant_step_def nth_butlast nth_tl)
  apply (simp add: nth_butlast nth_tl)   
  using toT_def toT_eq_Nil apply auto[1] 
  using toT_def toT_eq_Nil apply force
  using toT_def toT_eq_Nil apply force
  apply (metis One_nat_def length_butlast length_tl nth_butlast nth_tl)
  apply (metis One_nat_def length_tl nth_tl s'_conformantStoreAddr)
  by (metis One_nat_def conformant_step_def length_butlast length_tl nth_butlast nth_tl)

thm conformant_def

lemma switch_istate1_validFrom1: 
"(sl = [] \<or> wfs (hd sl)) \<and> validSteps sl \<and> conformant sl \<and> \<not> mispredicts sl \<longleftrightarrow> 
 (sl = [] \<or> istate1 (hd sl) \<and> validFrom1 (hd sl) (toT sl))"
unfolding conformant_piecewise 
unfolding list_all_length
validTrans1.simps conformant_init_def
Orig.validFrom_nth toT_eq_Nil istate1_def conformant_step_def 
toT_def mispredicts_def set_conv_nth validSteps_def apply auto 
	apply (auto simp add: hd_conv_nth) 
	apply (metis length_greater_0_conv)
	unfolding srcOf_def tgtOf_def
	apply (metis fst_conv length_greater_0_conv nth_butlast nth_zip zip_eq_Nil_iff)  
  apply (simp add: conformant_step_def nth_butlast nth_tl)
  apply (simp add: conformant_step_def nth_butlast nth_tl)
  apply (metis One_nat_def diff_Suc_less length_greater_0_conv length_tl less_trans_Suc nth_tl)
  apply (simp add: nth_butlast nth_tl)
  apply (metis diff_is_0_eq' gr_implies_not_zero toT_def toT_eq_Nil)
  apply (metis diff_is_0_eq' less_nat_zero_code toT_def toT_eq_Nil)
  using toT_def toT_eq_Nil apply auto[1]
  apply (metis hd_conv_nth le_eq_less_or_eq length_0_conv less_Suc_eq_0_disj not_less_eq toT_def toT_eq_Nil)
  apply (metis One_nat_def length_butlast length_tl nth_butlast nth_tl)
  apply (metis One_nat_def length_tl nth_tl s'_conformantStoreAddr)
  apply (metis One_nat_def conformant_step_def length_butlast length_tl 
          nth_butlast nth_tl)
  by (smt (verit) Nitpick.size_list_simp(2) One_nat_def hd_conv_nth length_tl 
         less_Suc_eq_0_disj less_nat_zero_code nth_tl) 

lemma aux:
"((sl2 = [] \<or> wfs (hd sl2)) \<and> validSteps sl2 \<and> conformant sl2) \<and>
 ((sl2' = [] \<or> wfs (hd sl2')) \<and> validSteps sl2' \<and> conformant sl2') \<and>
 ((sl1 = [] \<or> wfs (hd sl1)) \<and> validSteps sl1 \<and> conformant sl1) \<and>
 ((sl1' = [] \<or> wfs (hd sl1')) \<and> validSteps sl1' \<and> conformant sl1') \<and> 
 \<not> mispredicts sl1 \<and> \<not> mispredicts sl1' 
 \<longleftrightarrow>
 (sl2 = [] \<or> istate2 (hd sl2) \<and> validFrom2 (hd sl2) (toT sl2)) \<and> 
 (sl2' = [] \<or> istate2 (hd sl2') \<and> validFrom2 (hd sl2') (toT sl2')) \<and>
 (sl1 = [] \<or> istate1 (hd sl1) \<and> validFrom1 (hd sl1) (toT sl1)) \<and> 
 (sl1' = [] \<or> istate1 (hd sl1') \<and> validFrom1 (hd sl1') (toT sl1'))" 
using switch_istate1_validFrom1 switch_istate2_validFrom2 by metis

lemma tpod_alt: 
"tpod \<longleftrightarrow>
(\<forall>tr2 tr2' tr1 tr1'.
   (tr2 = [] \<and> tr1 = [] \<or> counterpart (srcOf (hd tr2)) tr2 (srcOf (hd tr1)) tr1) \<and>
   (tr2' = [] \<and> tr1' = [] \<or> counterpart (srcOf (hd tr2')) tr2' (srcOf (hd tr1')) tr1') \<and>
   (tr1 = [] \<or> istate1 (srcOf (hd tr1)) \<and> validFrom1 (srcOf (hd tr1)) tr1) \<and>
   (tr1' = [] \<or> istate1 (srcOf (hd tr1')) \<and> validFrom1 (srcOf (hd tr1')) tr1') \<and>
   (tr1 = [] \<and> tr1' = [] \<or> tracesOK1 (srcOf (hd tr1)) tr1 (srcOf (hd tr1')) tr1') \<and>
   (tr2 = [] \<or> istate2 (srcOf (hd tr2)) \<and> validFrom2 (srcOf (hd tr2)) tr2) \<and> 
   (tr2' = [] \<or> istate2 (srcOf (hd tr2')) \<and> validFrom2 (srcOf (hd tr2')) tr2') \<longrightarrow>
   \<not> (tr2 = [] \<and> tr2' = [] \<or> tracesLeak2 (srcOf (hd tr2)) tr2 (srcOf (hd tr2')) tr2'))"
unfolding tpod_def sorry


(*************************************)
(* to add back to hopeless1 later: *)




(*************************************)
(* independent action: *)
definition Left where
"Left \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn s' vl'. validTrans trn \<and> s = srcOf trn \<and> s' = tgtOf trn \<and> 
   extend trn vl vl' \<and> \<not> \<gamma> trn
   \<longrightarrow>
   \<Delta> s' vl' s1 vl1"

definition Right where
"Right \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn1 s1' vl1'. validTrans trn1 \<and> s1 = srcOf trn1 \<and> s1' = tgtOf trn1 \<and> 
   extend trn1 vl1 vl1' \<and> \<not> \<gamma> trn1
   \<longrightarrow>
   \<Delta> s vl s1' vl1'"

definition Both where
"Both \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn s' vl' trn1 s1' vl1'. 
   validTrans trn \<and> s = srcOf trn \<and> s' = tgtOf trn \<and> 
   validTrans trn1 \<and> s1 = srcOf trn1 \<and> s1' = tgtOf trn1 \<and>
   extend trn vl vl' \<and> extend trn1 vl1 vl1' \<and> \<gamma> trn \<and> \<gamma> trn1
   \<longrightarrow>
   \<Delta> s' vl' s1' vl1' \<and> g trn = g trn1"

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   Left \<Delta> s vl s1 vl1 \<and> Right \<Delta> s vl s1 vl1 \<and> Both \<Delta> s vl s1 vl1"

lemma unwind_trace:
assumes unwind: "unwind \<Delta>" and "reachNT s" and "reach s1" and "\<Delta> s vl s1 vl1"
and "validFrom s tr" and "never T tr" 
and "validFrom s1 tr1" and "never T tr1" 
and "V tr = vl" and "V tr1 = vl1"
shows "O tr = O tr1"
proof-
  let ?f = "\<lambda> tr1 tr2. length tr1 + length tr2"
  show ?thesis using assms 
  proof(induct rule: measure_induct2[of ?f])
    case (IH trr1 trr2)
    show ?case


(* independent action: *)
definition iaction where
"iaction \<Delta> s vl s1 vl1 \<equiv>
 \<exists> al1 vl1'.
   let tr1 = traceOf s1 al1; s1' = tgtOf (last tr1) in
   list_ex \<phi> tr1 \<and> consumeList tr1 vl1 vl1' \<and>
   never \<gamma> tr1
   \<and>
   \<Delta> s vl s1' vl1'"

(* Multi-step intro, reflecting the improved def: *)
lemma iactionI_ms[intro?]:
assumes s: "sstep s1 al1 = (oul1, s1')" 
and l: "list_ex \<phi> (traceOf s1 al1)"
and "consumeList (traceOf s1 al1) vl1 vl1'"
and "never \<gamma> (traceOf s1 al1)" and "\<Delta> s vl s1' vl1'"
shows "iaction \<Delta> s vl s1 vl1"
proof-
  have "al1 \<noteq> []" using l by auto
  from sstep_tgtOf_traceOf[OF this s] assms 
  show ?thesis unfolding iaction_def by auto
qed

lemma sstep_eq_singleiff[simp]: "sstep s1 [a1] = ([ou1], s1') \<longleftrightarrow> step s1 a1 = (ou1, s1')"
using sstep_Cons by auto

(* The less expressive, single-step intro: *)
lemma iactionI[intro?]:
assumes "step s1 a1 = (ou1, s1')" and "\<phi> (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'"
and "\<not> \<gamma> (Trans s1 a1 ou1 s1')" and "\<Delta> s vl s1' vl1'"
shows "iaction \<Delta> s vl s1 vl1"
using assms 
by (intro iactionI_ms[of _ "[a1]" "[ou1]"]) (auto simp: consume_def consumeList_def)

definition match where
"match \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<exists> al1 vl1'.
    let trn = Trans s a ou s'; tr1 = traceOf s1 al1; s1' = tgtOf (last tr1) in
    al1 \<noteq> [] \<and> consumeList tr1 vl1 vl1' \<and>
    O tr1 = O [trn] \<and>
    \<Delta> s' vl' s1' vl1'"

lemma matchI_ms[intro?]:
assumes s: "sstep s1 al1 = (oul1, s1')" 
and l: "al1 \<noteq> []"
and "consumeList (traceOf s1 al1) vl1 vl1'"
and "O (traceOf s1 al1) = O [Trans s a ou s']"
and "\<Delta> s' vl' s1' vl1'"
shows "match \<Delta> s s1 vl1 a ou s' vl'"
proof-
  from sstep_tgtOf_traceOf[OF l s] assms 
  show ?thesis unfolding match_def by (intro exI[of _ al1]) auto
qed

lemma matchI[intro?]:
assumes "validTrans (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'" and "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a1 ou1 s1')"
and "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a1 ou1 s1')"
and "\<Delta> s' vl' s1' vl1'"
shows "match \<Delta> s s1 vl1 a ou s' vl'"
using assms by (intro matchI_ms[of s1 "[a1]" "[ou1]" s1'])
               (auto simp: consume_def consumeList_def split: if_splits)

definition ignore where
"ignore \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<not> \<gamma> (Trans s a ou s') \<and>
 \<Delta> s' vl' s1 vl1"

lemma ignoreI[intro?]:
assumes "\<not> \<gamma> (Trans s a ou s')" and "\<Delta> s' vl' s1 vl1"
shows "ignore \<Delta> s s1 vl1 a ou s' vl'"
unfolding ignore_def using assms by auto

(* reaction: *)
definition reaction where
"reaction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> a ou s' vl'.
   let trn = Trans s a ou s' in
   validTrans trn \<and> \<not> T trn \<and>
   consume trn vl vl'
   \<longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl'
   \<or>
   ignore \<Delta> s s1 vl1 a ou s' vl'"

lemma reactionI[intro?]:
assumes
"\<And>a ou s' vl'.
   \<lbrakk>step s a = (ou, s'); \<not> T (Trans s a ou s');
    consume (Trans s a ou s') vl vl'\<rbrakk>
   \<Longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'"
shows "reaction \<Delta> s vl s1 vl1"
using assms unfolding reaction_def by auto

definition "hopeless1" :: "'state \<Rightarrow> 'value \<Rightarrow> bool" where
"hopeless1 s v \<equiv> \<forall> tr trn. validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn \<longrightarrow> f trn \<noteq> v"

lemma hopeless1_coind:
assumes K: "K s"
and I: "\<And> trn. \<lbrakk>K (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
        \<Longrightarrow> (\<phi> trn \<longrightarrow> f trn \<noteq> v) \<and> K (tgtOf trn)"
shows "hopeless1 s v"
using K unfolding hopeless1_def proof(intro allI conjI impI)
  fix tr trn assume "K s" and "validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn"
  thus "f trn \<noteq> v"
  using I unfolding validFrom_def by (induction tr arbitrary: s trn)
  (auto, metis neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE)
qed

definition noVal where
"noVal K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal_disj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<or> Inv2 s) v"
using assms unfolding noVal_def by metis

lemma noVal_conj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<and> Inv2 s) v"
using assms unfolding noVal_def by blast

(* Often encountered sufficient criterion for noVal: *)
definition no\<phi> where
"no\<phi> K \<equiv> \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<longrightarrow> \<not> \<phi> (Trans s a ou s')"

lemma no\<phi>_noVal: "no\<phi> K \<Longrightarrow> noVal K v"
unfolding no\<phi>_def noVal_def by auto

(* intro rule for quick inline checks: *)
lemma hopeless1I[consumes 2, induct pred: "hopeless1"]:
assumes rs: "reachNT s" and K: "K s"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s'"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms by (intro hopeless1_coind[of ?K])
  (metis BD_Security_IO.reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* intro rule for more elaborate checks: *)
lemma hopeless1I2:
assumes rs: "reachNT s" and K: "K s"
and "invarNT K" and "noVal K v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms unfolding invarNT_def noVal_def apply(intro hopeless1_coind[of ?K])
  by metis (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)
qed

(* Binary version of the invariant: *)
definition noVal2 where
"noVal2 K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s v \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal2_disj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<or> Inv2 s v) v"
using assms unfolding noVal2_def by metis

lemma noVal2_conj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<and> Inv2 s v) v"
using assms unfolding noVal2_def by blast

lemma noVal_noVal2: "noVal K v \<Longrightarrow> noVal2 (\<lambda> s v. K s) v"
unfolding noVal_def noVal2_def by auto

lemma hopeless1I_noVal2[consumes 2, induct pred: "hopeless1"]:
assumes rs: "reachNT s" and K: "K s v"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s v\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s' v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms by (intro hopeless1_coind[of ?K])
  (metis BD_Security_IO.reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

lemma hopeless1I2_noVal2:
assumes rs: "reachNT s" and K: "K s v"
and "invarNT (\<lambda> s. K s v)" and "noVal2 K v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms unfolding invarNT_def noVal2_def
  by (intro hopeless1_coind[of ?K]) (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* end binary version *)

lemma hopeless1_validFrom:
assumes vl: "vl \<noteq> []" and i: "hopeless1 s (hd vl)" and v: "validFrom s tr" and V: "V tr = vl"
and T: "never T tr"
shows False
using i v V T proof(induction tr arbitrary: s)
  case Nil thus ?case by (metis V_simps(1) vl)
next
  case (Cons trn tr s)
  show ?case
  proof(cases "\<phi> trn")
    case True
    hence "f trn = hd vl" using Cons by (metis V_simps(3) hd_Cons_tl list.inject vl)
    moreover have "validFrom s [trn]" using \<open>validFrom s (trn # tr)\<close>
    unfolding validFrom_def by auto
    ultimately show ?thesis using Cons True unfolding hopeless1_def
    by (elim allE[of _ "[]"]) auto
  next
    case False
    hence "V tr = vl" using Cons by auto
    moreover have "never T tr" by (metis Cons.prems list_all_simps)
    moreover from \<open>validFrom s (trn # tr)\<close> have "validFrom (tgtOf trn) tr" and s: "s = srcOf trn"
    by (metis list.distinct(1) validFrom_def valid_ConsE Cons.prems(2) 
              IO_Automaton.validFrom_def list.discI list.sel(1))+    
    moreover have "hopeless1 (tgtOf trn) (hd vl)" using \<open>hopeless1 s (hd vl)\<close>
    unfolding hopeless1_def s by simp
    (metis (no_types) Cons.prems(2) Cons.prems(4) append_Cons list.sel(1)
           list.distinct list_all_simps valid.Cons validFrom_def valid_ConsE)
    ultimately show ?thesis using Cons(1) by auto
  qed
qed