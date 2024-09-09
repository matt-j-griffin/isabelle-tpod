(* Observational_Determinism, proved to be an instance of 
\<forall>\<forall> BD Security *)


theory Observational_Determinism
  imports 
    "../General_Preliminaries/Transition_System" 
    "../General_Preliminaries/Filtermap_Extensions" 
    "Bounded_Deducibility_Security"
    "Cheang_TPOD"
begin

(* Observational determinism (as in the Cheung paper): *)
locale OD = Transition_System istate validTrans srcOf tgtOf
(* we want sets *)
 for istate :: "'state \<Rightarrow> bool" and validTrans :: "'trans \<Rightarrow> bool"
 and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
+ 
fixes lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
  and lowOp :: "'trans \<Rightarrow> 'lowOp"

assumes reflp_lowEquiv: "reflp lowEquiv"
    and symp_lowEquiv: "symp lowEquiv"
begin

lemma lowEquiv_same: \<open>lowEquiv s s\<close>
  by (simp add: reflpD reflp_lowEquiv)
  

definition lowEquivTrans :: "'trans \<Rightarrow> 'trans \<Rightarrow> bool" where 
"lowEquivTrans trn1 trn2 \<equiv> 
 lowEquiv (srcOf trn1) (srcOf trn2) \<and> lowEquiv (tgtOf trn1) (tgtOf trn2)"


(* Unlike Cheung, we work with finite traces.  *)
definition lowEquivT :: "'trans list \<Rightarrow> 'trans list \<Rightarrow> bool" where 
"lowEquivT \<equiv> list_all2 lowEquivTrans"

lemma list_all2_lemmas_lowEquivT: \<open>list_all2_lemmas lowEquivT lowEquivTrans\<close>
  unfolding lowEquivT_def apply standard
  by blast

interpretation lowEquivT: list_all2_lemmas lowEquivT lowEquivTrans
  by (rule list_all2_lemmas_lowEquivT)


lemma lowEquivT_Cons[simp]: 
"lowEquivT (trn1 # tr1) (trn2 # tr2) \<longleftrightarrow>  
 lowEquiv (srcOf trn1) (srcOf trn2) \<and> lowEquiv (tgtOf trn1) (tgtOf trn2) \<and> 
 lowEquivT tr1 tr2" 
  by (simp add: lowEquivT.Cons lowEquivTrans_def)

lemma lowEquivT_def2: 
assumes "validFrom s1 tr1" "validFrom s2 tr2" "tr1 \<noteq> []"
shows "lowEquivT tr1 tr2 \<longleftrightarrow> 
  lowEquiv s1 s2 \<and> 
  list_all2 (\<lambda>trn1 trn2. lowEquiv (tgtOf trn1) (tgtOf trn2)) tr1 tr2"
proof(cases "length tr1 = length tr2")
  case False 
  thus ?thesis using assms 
  	by (meson list_all2_lengthD lowEquivT.lengthD)
next
  case True note l = True
  show ?thesis 
  proof(cases "tr1 = [] \<or> tr2 = []")
    case True
    hence [simp]: "tr1 = [] \<and> tr2 = []" using l by auto
    show ?thesis using assms by simp
  next
    case False
    thus ?thesis 
    using assms unfolding lowEquivT_def lowEquivTrans_def list_all2_conv_all_nth 
validFrom_def
apply auto 
		apply (simp add: hd_conv_nth) 
  subgoal for i apply(cases "i = 0") 
    apply (metis drop0 hd_drop_conv_nth)
    by simp (metis Suc_diff_1 Suc_lessD valid_validTrans_nth_srcOf_tgtOf) . 
  qed
qed

definition lowOpT :: "'trans list \<Rightarrow> 'lowOp list" where 
"lowOpT tr \<equiv> map lowOp tr"

lemma lowOpT_empty[simp]: \<open>lowOpT [] = []\<close>
  unfolding lowOpT_def by auto

(* It seems that this is the correct "secure for" for OD. 
For noninterference, there is no additional layer of "low operations" 
so only s1 and s2 are parameters.
*)
definition tracesLeakVia :: "'state \<Rightarrow> 'trans list \<Rightarrow> 'state \<Rightarrow> 'trans list \<Rightarrow> 'lowOp list \<Rightarrow> bool" where 
"tracesLeakVia s tr s' tr' lops \<equiv> 
 lowEquiv s s' \<and> lowOpT tr = lops \<and> lowOpT tr' = lops \<and> \<not> lowEquivT tr tr'"

lemma not_tracesLeakVia_Empty[simp]: \<open>\<not> tracesLeakVia s tr s' tr' []\<close>
  by (simp add: lowOpT_def tracesLeakVia_def)

definition tracesLeak :: "'state \<Rightarrow> 'trans list \<Rightarrow> 'state \<Rightarrow> 'trans list \<Rightarrow> bool" where 
"tracesLeak s tr s' tr' \<equiv> 
 lowEquiv s s' \<and> lowOpT tr = lowOpT tr' \<and> \<not> lowEquivT tr tr'"

lemma tracesLeak_empty[simp]: \<open>\<not>tracesLeak s [] s' []\<close>
  unfolding tracesLeak_def using lowEquivT.empty by simp

lemma tracesLeak_tracesLeakVia:
"tracesLeak s tr s' tr' \<longleftrightarrow> (\<exists>lops. tracesLeakVia s tr s' tr' lops)"
unfolding tracesLeak_def tracesLeakVia_def by auto

definition secureFor :: "'state \<Rightarrow> 'state \<Rightarrow> 'lowOp list \<Rightarrow> bool" where 
"secureFor s s' lops \<equiv> 
 \<forall>tr tr'. validFrom s tr \<and> validFrom s' tr' \<longrightarrow> \<not> tracesLeakVia s tr s' tr' lops"

lemma secureFor_Empty[simp]: \<open>secureFor s s' []\<close>
  unfolding secureFor_def by simp

definition secure :: bool where 
"secure \<equiv> \<forall>s s' lops. istate s \<and> istate s' \<longrightarrow> secureFor s s' lops"

lemma secure_alt: "secure \<longleftrightarrow> 
(\<forall>s tr s' tr'. 
   istate s \<and> istate s' \<and> 
   validFrom s tr \<and> validFrom s' tr' \<longrightarrow> \<not> tracesLeak s tr s' tr')"
unfolding secure_def secureFor_def tracesLeakVia_def tracesLeak_tracesLeakVia by auto


(* The familiar formulation of (low) observational determinism: *)
lemma secure_alt': "secure \<longleftrightarrow> 
(\<forall>s tr s' tr'. 
   istate s \<and> istate s' \<and> lowEquiv s s' \<and> 
   validFrom s tr \<and> validFrom s' tr' \<and> lowOpT tr = lowOpT tr' 
   \<longrightarrow> lowEquivT tr tr')"
unfolding secure_def secureFor_def tracesLeakVia_def by auto


lemma not_tracesLeakVia_NilL[simp]: "\<not> tracesLeakVia s [] s' tr' lops"
unfolding tracesLeakVia_def using lowOpT_def by auto

lemma not_tracesLeakVia_NilR[simp]: "\<not> tracesLeakVia s tr s' [] lops"
unfolding tracesLeakVia_def using lowOpT_def by auto

lemma not_tracesLeak_NilL[simp]: "\<not> tracesLeak s [] s' tr"
unfolding tracesLeak_def using lowOpT_def by auto

lemma not_tracesLeak_NilR[simp]: "\<not> tracesLeak s tr s' []"
unfolding tracesLeak_def using lowOpT_def by auto

(* OD as instance of \<forall>\<forall> BD Security: *)

definition isSec :: "'trans \<Rightarrow> bool" where 
"isSec trn \<equiv> True"

definition getSec :: "'trans \<Rightarrow> 'lowOp" where 
"getSec trn \<equiv> lowOp trn" 

definition isObs :: "'trans \<Rightarrow> bool" where 
"isObs trn \<equiv> True"

definition getObs :: "'trans \<Rightarrow> 'state set" where 
"getObs trn \<equiv> {s . lowEquiv s (tgtOf trn)}"

definition T :: "'trans \<Rightarrow> bool" where 
"T trn \<equiv> False"

lemma not_T[simp]: "\<not> T trn" unfolding T_def by auto

definition B :: "'state \<Rightarrow> 'lowOp list \<Rightarrow> 'state \<Rightarrow> 'lowOp list \<Rightarrow> bool"
where 
"B s lops s' lops' \<equiv> lowEquiv s s' \<and> lops = lops'"
                         
sublocale asBD: BD_Security_TS where 
istate = istate and validTrans = validTrans
and srcOf = srcOf and tgtOf = tgtOf 
(* *)
and isSec = isSec and getSec = getSec 
and isObs = isObs and getObs = getObs
and T = T and B = B
done

lemma isSec: "isSec trn" unfolding isSec_def by auto

lemma isObs: "isObs trn" unfolding isObs_def by auto

lemma [simp,intro!]: "never T tr" unfolding T_def list_all_def by simp

lemma S_Cons[simp]: "asBD.S (trn # tr) = getSec trn # asBD.S tr"
by (auto simp: isSec)

lemma S_length[simp]: "length (asBD.S tr) = length tr"
by(induct tr, auto)

lemma S_Nil_iff[simp]: "asBD.S tr = [] \<longleftrightarrow> tr = []"
by(induct tr, auto)

lemma O_Cons[simp]: "asBD.O (trn # tr) = getObs trn # asBD.O tr"
by (auto simp: isObs)

lemma O_length[simp]: "length (asBD.O tr) = length tr"
by(induct tr, auto)

lemma O_Nil_iff[simp]: "asBD.O tr = [] \<longleftrightarrow> tr = []"
by(induct tr, auto)
 
lemma S_map: "asBD.S tr = map lowOp tr"
apply(induct tr) unfolding asBD.S_def unfolding getSec_def by (auto simp: isSec)

lemma B_S_iff_lowOpT:
"B s1 (asBD.S tr1) s2 (asBD.S tr2) \<longleftrightarrow> lowEquiv s1 s2 \<and> lowOpT tr1 = lowOpT tr2" 
unfolding B_def lowOpT_def S_map validFrom_def by auto

lemma lowEquiv_classes_eq_imp_low_equiv: 
  assumes \<open>{s. lowEquiv s s1} = {s. lowEquiv s s2}\<close> 
    shows \<open>lowEquiv s1 s2\<close>
  using assms by (metis mem_Collect_eq reflp_def reflp_lowEquiv)
  
lemma classes_eq_iff_equivp: 
  assumes \<open>equivp P\<close>
    shows "{s. P s s\<^sub>1} = {s. P s s\<^sub>2} \<longleftrightarrow> P s\<^sub>1 s\<^sub>2"
  using assms apply (intro iffI)
  using equivp_reflp apply fastforce
  by (simp add: equivp_def)



(*
definition
  init_lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
where
  \<open>init_lowEquiv s1 s2 \<equiv> istate s1 \<and> istate s2 \<and> lowEquiv s1 s2\<close>

lemma init_lowEquiv_classes_eq_iff_low_equiv: 
  assumes \<open>equivp init_lowEquiv\<close>
      and \<open>istate s\<^sub>1\<close> and \<open>istate s\<^sub>2\<close>
    shows "{s. lowEquiv s s\<^sub>1} = {s. lowEquiv s s\<^sub>2} \<longleftrightarrow> lowEquiv s\<^sub>1 s\<^sub>2"
  using assms apply (frule_tac s\<^sub>1=s\<^sub>1 and s\<^sub>2=s\<^sub>2 in classes_eq_iff_equivp)
  unfolding init_lowEquiv_def apply safe
  using equivp_reflp apply fastforce
  using equivp_reflp apply fastforce
  by blast+

definition
  trans_lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
where
  \<open>trans_lowEquiv s\<^sub>1' s\<^sub>2' \<equiv> lowEquiv s\<^sub>1' s\<^sub>2' \<and> 
      (\<exists>trn\<^sub>1 trn\<^sub>2. tgtOf trn\<^sub>1 = s\<^sub>1' \<and> tgtOf trn\<^sub>2 = s\<^sub>2' \<and>
      validTrans trn\<^sub>1 \<and> validTrans trn\<^sub>2 \<and> lowOp trn\<^sub>1 = lowOp trn\<^sub>2)\<close>

lemma equivp_lowOp: \<open>equivp (\<lambda>trn\<^sub>1 trn\<^sub>2. lowOp trn\<^sub>1 = lowOp trn\<^sub>2)\<close>
  unfolding equivp_def by metis


lemma trans_lowEquiv_classes_eq_iff_low_equiv:
  assumes \<open>equivp trans_lowEquiv\<close>
      and \<open>validTrans trn\<^sub>1\<close> and \<open>validTrans trn\<^sub>2\<close>
      and \<open>lowOp trn\<^sub>1 = lowOp trn\<^sub>2\<close>
    shows "{s. lowEquiv s (tgtOf trn\<^sub>1)} = {s. lowEquiv s (tgtOf trn\<^sub>2)} \<longleftrightarrow> lowEquiv (tgtOf trn\<^sub>1) (tgtOf trn\<^sub>2)"
  using assms apply (intro iffI)
  using lowEquiv_classes_eq_imp_low_equiv apply blast
  apply (drule_tac s\<^sub>1=\<open>tgtOf trn\<^sub>1\<close> and s\<^sub>2=\<open>tgtOf trn\<^sub>2\<close> in classes_eq_iff_equivp)
  apply (elim iffE impE)
  using trans_lowEquiv_def apply auto[1]
  using trans_lowEquiv_def apply auto[1]
  using trans_lowEquiv_def apply auto[1]
  apply (drule Collect_eqE)
  apply (intro Collect_cong)
  apply (erule_tac x=s in allE)
  unfolding trans_lowEquiv_def 
  apply clarify

  sledgehammer


  using Collect_eqI Collect_cong

   apply safe

  unfolding trans_lowEquiv_def Collect_ex_eq apply safe
  sledgehammer
     apply (metis assms(1) classes_eq_iff_equivp trans_lowEquiv_def)+
  done
 *)
lemma O_eq_iff_lowEquivT_length_neq:
  assumes "validFrom s1 tr1" "validFrom s2 tr2" 
      and "lowEquiv s1 s2"
      and \<open>length tr1 \<noteq> length tr2\<close>
    shows "asBD.O tr1 = asBD.O tr2 \<longleftrightarrow> lowEquivT tr1 tr2"
  using assms by (metis asBD.O_list_all asBD.O_simps(1) isObs_def list.map_disc_iff 
              list_all2_lengthD list_all_append list_all_simps(1) lowEquivT_def map_eq_imp_length_eq 
                rev_induct)

lemma O_eq_imp_lowEquivT:
  assumes \<open>validFrom s\<^sub>1 tr\<^sub>1\<close> \<open>validFrom s\<^sub>2 tr\<^sub>2\<close>
      and \<open>lowEquiv s\<^sub>1 s\<^sub>2\<close>
      and \<open>asBD.O tr\<^sub>1 = asBD.O tr\<^sub>2\<close>
    shows \<open>lowEquivT tr\<^sub>1 tr\<^sub>2\<close>
proof(cases \<open>length tr\<^sub>1 = length tr\<^sub>2\<close>)
  case False thus ?thesis 
    using O_eq_iff_lowEquivT_length_neq assms by blast
next
  case True note l = True
  show ?thesis 
  proof(cases \<open>tr\<^sub>1 = []\<close>)
    case True
    thus ?thesis using l by auto
  next
    case False
    show ?thesis using l False assms unfolding lowEquivT_def2[OF assms(1,2) False] 
    apply (induct tr\<^sub>1 tr\<^sub>2 arbitrary: s\<^sub>1 s\<^sub>2 rule: list_nonempty_induct2)
    apply (simp add: getObs_def)
    apply (frule lowEquiv_classes_eq_imp_low_equiv, blast) 
    subgoal for trn1 tr1 trn2 tr2
    apply (simp add: getObs_def)
    using lowEquiv_classes_eq_imp_low_equiv
    unfolding validFrom_Cons
    by blast
    . 
  qed
qed
(*
lemma lowEquivT_imp_O_eq:
  assumes \<open>validFrom s\<^sub>1 tr\<^sub>1\<close> \<open>validFrom s\<^sub>2 tr\<^sub>2\<close>
      and \<open>lowEquiv s\<^sub>1 s\<^sub>2\<close>
      and \<open>lowEquivT tr\<^sub>1 tr\<^sub>2\<close>
      and \<open>equivp trans_lowEquiv\<close>
    shows \<open>asBD.O tr\<^sub>1 = asBD.O tr\<^sub>2\<close>
proof(cases \<open>length tr\<^sub>1 = length tr\<^sub>2\<close>)
  case False thus ?thesis 
    using O_eq_iff_lowEquivT_length_neq assms by blast
next
  case True note l = True
  show ?thesis 
  proof(cases \<open>tr\<^sub>1 = []\<close>)
    case True
    thus ?thesis using l by auto
  next
    case False
    show ?thesis using l False assms unfolding lowEquivT_def2[OF assms(1,2) False] 
    apply (induct tr\<^sub>1 tr\<^sub>2 arbitrary: s\<^sub>1 s\<^sub>2 rule: list_nonempty_induct2)
    apply (simp add: getObs_def validFrom_def)
    apply (elim conjE)  
    apply (simp add: trans_lowEquiv_classes_eq_iff_low_equiv valid_Cons_iff)
    using getObs_def trans_lowEquiv_classes_eq_iff_low_equiv validFrom_Cons by auto[1]
  qed
qed 


lemma O_eq_iff_lowEquivT:
  assumes \<open>validFrom s\<^sub>1 tr\<^sub>1\<close> \<open>validFrom s\<^sub>2 tr\<^sub>2\<close>
      and \<open>lowEquiv s\<^sub>1 s\<^sub>2\<close>
      and \<open>equivp trans_lowEquiv\<close>
    shows \<open>asBD.O tr\<^sub>1 = asBD.O tr\<^sub>2 \<longleftrightarrow> lowEquivT tr\<^sub>1 tr\<^sub>2\<close>
  using assms by (meson O_eq_imp_lowEquivT lowEquivT_imp_O_eq)
*)

(* Observational determinism is a particular case of BD security *)
lemma implies_secureFor:
"vl = [] \<or> vl' = [] \<or> vl \<noteq> vl' \<or> \<not> lowEquiv s s' \<Longrightarrow> asBD.secureFor s vl s' vl'"
unfolding asBD.secureFor_alt by (auto simp: B_def)


lemma isLeak_imp_asBD_isleak: 
  assumes \<open>\<exists>tr tr'. validFrom s tr \<and> validFrom s' tr' \<and> tracesLeakVia s tr s' tr' lops\<close>
    shows \<open>lowEquiv s s' \<and> asBD.isLeak s lops s' lops\<close>
  using assms unfolding asBD.isLeak_def tracesLeakVia_def apply safe 
  apply (simp add: B_def S_map lowOpT_def) 
  by (metis O_eq_imp_lowEquivT list.pred_True)
(*
lemma asBD_isleak_imp_isLeak:
  assumes \<open>equivp trans_lowEquiv\<close>
      and \<open>lowEquiv s s' \<and> asBD.isLeak s lops s' lops\<close>
    shows \<open>\<exists>tr tr'. validFrom s tr \<and> validFrom s' tr' \<and> tracesLeakVia s tr s' tr' lops\<close>
  using assms unfolding asBD.isLeak_def tracesLeakVia_def apply safe 
  apply (rule_tac x=tr in exI)
  apply (rule_tac x=tr' in exI)
  unfolding S_map B_def lowOpT_def apply safe
  by (frule_tac s\<^sub>1=s and s\<^sub>2=s' in lowEquivT_imp_O_eq, blast+)

lemma isLeak_iff_asBD_isleak: 
  assumes \<open>equivp trans_lowEquiv\<close>
    shows \<open>(\<exists>tr tr'. validFrom s tr \<and> validFrom s' tr' \<and> tracesLeakVia s tr s' tr' lops) 
              \<longleftrightarrow> lowEquiv s s' \<and> asBD.isLeak s lops s' lops\<close>
  using assms isLeak_imp_asBD_isleak asBD_isleak_imp_isLeak by blast
*)

lemma secureFor_imp_asBD_secureFor: 
  assumes \<open>asBD.secureFor s lops s1 lops\<close>
    shows \<open>secureFor s s1 lops\<close>
  using assms unfolding asBD.secureFor_alt secureFor_def apply clarify 
  apply (erule_tac x=tr in allE)
  apply (erule_tac x=tr' in allE)
  unfolding tracesLeakVia_def apply safe
  apply (simp add: S_map lowOpT_def)
  apply (simp add: S_map lowOpT_def)
  using B_def apply blast
  using O_eq_imp_lowEquivT by blast

(*
lemma asBD_secureFor_imp_secureFor: 
  assumes \<open>equivp trans_lowEquiv\<close>
      and \<open>secureFor s s' lops\<close>
    shows \<open>asBD.secureFor s lops s' lops\<close>
  using assms unfolding asBD.secureFor_alt secureFor_def apply clarify 
  apply (erule_tac x=tr in allE)
  apply (erule_tac x=tr' in allE)
  unfolding tracesLeakVia_def apply safe
  unfolding B_def apply blast
  apply (simp add: S_map lowOpT_def)
  apply (simp add: S_map lowOpT_def)
  by (drule lowEquivT_imp_O_eq, blast+)

theorem secureFor_iff_asBD_secureFor: 
  assumes \<open>equivp trans_lowEquiv\<close>
    shows \<open>asBD.secureFor s lops s1 lops \<longleftrightarrow> secureFor s s1 lops\<close>
  using assms secureFor_imp_asBD_secureFor asBD_secureFor_imp_secureFor by blast
*)
theorem secure_imp_asBD_secure:
  assumes asBD.secure
    shows secure
  using assms unfolding asBD.secure_def secure_def 
  by (metis secureFor_imp_asBD_secureFor)
(*
theorem secure_iff_asBD_secure:
  assumes \<open>equivp trans_lowEquiv\<close>
    shows \<open>asBD.secure \<longleftrightarrow> secure\<close>
  unfolding asBD.secure_def secure_def 
  by (metis assms implies_secureFor secureFor_iff_asBD_secureFor)
*)

(* Unwinding for OD: *)
 
(* TODO: Prove that these are equivalent to the BD-unwinding conditions: *)

definition initCond :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where 
"initCond \<Delta> \<equiv> \<forall>s s'. istate s \<and> istate s' \<and> lowEquiv s s' \<longrightarrow> \<Delta> s s'"

definition unwindCond :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where 
"unwindCond \<Delta> \<equiv> \<forall>s s'. \<Delta> s s' \<and> lowEquiv s s'  \<longrightarrow> 
 (\<forall>trn ss trn' ss'. 
    srcOf trn = s \<and> tgtOf trn = ss \<and> srcOf trn' = s' \<and> tgtOf trn' = ss' \<and> 
    lowOp trn = lowOp trn' 
    \<longrightarrow> lowEquiv ss ss' \<and> \<Delta> ss ss')"

lemma unwindCond_secureFor: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> s s'"
shows "secureFor s s' lops"
using \<Delta> proof(induction lops arbitrary: s s')
  case (Nil s s')
  thus ?case unfolding secureFor_def tracesLeakVia_def  
  	by (simp add: lowOpT_def)
next
  case (Cons lop lops s s')
  show ?case unfolding secureFor_def proof(intro allI impI, elim conjE)
    fix tr tr'
    assume v: "validFrom s tr" "validFrom s' tr'"
    {assume l: "lowEquiv s s'" "lowOpT tr = lop # lops" "lowOpT tr' = lop # lops"
     from l obtain trn trr trn' trr' where 
     tr:  "tr = trn # trr" "lowOp trn = lop" "lowOpT trr = lops" and 
     tr': "tr' = trn' # trr'" "lowOp trn' = lop" "lowOpT trr' = lops"
     by (auto simp add: lowOpT_def)
     obtain ss ss' where ss: "srcOf trn = s" "tgtOf trn = ss" "validFrom ss trr"
     and ss': "srcOf trn' = s'" "tgtOf trn' = ss'" "validFrom ss' trr'"
     using v unfolding tr(1) tr'(1) by (meson validFrom_Cons)
     have lss: "lowEquiv ss ss'" and d: "\<Delta> ss ss'" 
     using `\<Delta> s s'` unwind l(1) ss'(1) ss'(2) ss(1) ss(2) tr'(2) tr(2) 
     unfolding unwindCond_def by blast+
     have "secureFor ss ss' lops" using Cons.IH[OF d] .
     hence "lowEquivT trr trr'" 
     by (simp add: tr'(3) lss secureFor_def ss'(3) ss(3) tr(3) tracesLeakVia_def)
     hence "lowEquivT tr tr'" unfolding tr(1) tr'(1)  
     	 by (simp add: l(1) lss ss'(1) ss'(2) ss(1) ss(2))
    }
    thus "\<not> tracesLeakVia s tr s' tr' (lop # lops)" unfolding tracesLeakVia_def by auto
  qed
qed


definition unwindSteps :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where 
"unwindSteps \<Delta> \<equiv> \<forall>s s'. \<Delta> s s' \<longrightarrow> 
 (\<forall>trn ss trn' ss'. 
    srcOf trn = s \<and> tgtOf trn = ss \<and> srcOf trn' = s' \<and> tgtOf trn' = ss' \<and> 
    lowOp trn = lowOp trn' 
    \<longrightarrow> \<Delta> ss ss')"

lemma unwindSteps_not_secureFor: 
  assumes "lops \<noteq> []" 
      and \<open>\<exists>tr tr'. validFrom s tr \<and> validFrom s' tr' \<and> \<not> lowEquivT tr tr' \<and> lowOpT tr = lops \<and> lowOpT tr' = lops\<close>
      and \<open>lowEquiv s s'\<close>
    shows "\<not>secureFor s s' lops"
using assms proof(induction lops arbitrary: s s' rule: list_nonempty_induct)
  case (single lop)
  thus ?case     
    unfolding secureFor_def unwindSteps_def tracesLeakVia_def apply safe
    apply (erule_tac x=tr in allE)
    apply (erule_tac x=tr' in allE)
    by simp_all
next
  case (cons lop lops)
  then show ?case 
    by (metis OD.tracesLeakVia_def OD_axioms secureFor_def)
qed

theorem unwind_secure: 
assumes \<open>initCond \<Delta>\<close> and \<open>unwindCond \<Delta>\<close>
shows secure
unfolding secure_def  
by (metis assms initCond_def secureFor_def tracesLeakVia_def unwindCond_secureFor)



(*
sublocale Cheang_OD 
  where Tr = \<open>{tr. istate (srcOf (hd tr)) \<and> validFrom (srcOf (hd tr)) tr}\<close>
    and op_low = lowOpT
    and low_equiv = lowEquivTrans
  .

lemma \<open>secure \<longleftrightarrow> OD\<close>
unfolding secure_alt' OD_def lowEquivT_def proof (intro iffI allI ballI impI; elim conjE)
  fix \<pi>\<^sub>1 \<pi>\<^sub>2 assume \<open>\<forall>s tr s' tr'. istate s \<and> istate s' \<and>
          lowEquiv s s' \<and> validFrom s tr \<and> validFrom s' tr' \<and> lowOpT tr = lowOpT tr' \<longrightarrow>
          low_equivs tr tr'\<close>
       \<open>\<pi>\<^sub>1 \<in> {tr. istate (srcOf (hd tr)) \<and> validFrom (srcOf (hd tr)) tr}\<close>
       \<open>\<pi>\<^sub>2 \<in> {tr. istate (srcOf (hd tr)) \<and> validFrom (srcOf (hd tr)) tr}\<close>
       \<open>lowEquivTrans (hd \<pi>\<^sub>1) (hd \<pi>\<^sub>2)\<close>
       \<open>lowOpT \<pi>\<^sub>1 = lowOpT \<pi>\<^sub>2\<close>
  thus \<open>low_equivs \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    apply -
    apply (erule allE[of _ \<open>srcOf (hd \<pi>\<^sub>1)\<close>], erule allE[of _ \<pi>\<^sub>1], 
           erule allE[of _ \<open>srcOf (hd \<pi>\<^sub>2)\<close>], erule allE[of _ \<pi>\<^sub>2])
    apply (erule impE)
    apply (intro conjI)
    using lowEquivTrans_def by simp_all
next
  fix s\<^sub>1 \<pi>\<^sub>1 s\<^sub>2 \<pi>\<^sub>2 
  assume \<open>\<forall>\<pi>\<^sub>1\<in>{tr. istate (srcOf (hd tr)) \<and> validFrom (srcOf (hd tr)) tr}.
          \<forall>\<pi>\<^sub>2\<in>{tr. istate (srcOf (hd tr)) \<and> validFrom (srcOf (hd tr)) tr}. OD_Tr \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
         \<open>istate s\<^sub>1\<close> \<open>istate s\<^sub>2\<close> \<open>lowEquiv s\<^sub>1 s\<^sub>2\<close> \<open>validFrom s\<^sub>1 \<pi>\<^sub>1\<close> \<open>validFrom s\<^sub>2 \<pi>\<^sub>2\<close>
         \<open>lowOpT \<pi>\<^sub>1 = lowOpT \<pi>\<^sub>2\<close>
  thus \<open>low_equivs \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    apply (cases \<pi>\<^sub>1)
    apply (cases \<pi>\<^sub>2)
    apply simp
    apply (metis lowEquivT_def not_tracesLeak_NilL tracesLeak_def)
    apply (cases \<pi>\<^sub>2)
    apply (simp add: lowOpT_def)
    apply (erule ball_inE[of _ _ \<pi>\<^sub>1])
    apply (simp add: validFrom_Cons)
    apply (erule ball_inE[of _ _ \<pi>\<^sub>2])
    apply (simp add: validFrom_Cons)
    apply (erule impE)
    unfolding lowEquivTrans_def apply (intro conjI)
    apply (simp add: validFrom_Cons)
    apply auto
    sorry
qed
*)

end (* context OD *)

(*
(* Strict Observational determinism, a variant of Observational Determinism where lowEquiv is an
   equivalence relation  *)
locale Strict_OD = OD istate validTrans srcOf tgtOf lowEquiv lowOp adversary
  for istate :: "'state \<Rightarrow> bool" and validTrans :: "'trans \<Rightarrow> bool"
  and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
  and lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
  and lowOp :: "'trans \<Rightarrow> 'lowOp"
  and adversary :: "'adversary_state"
+
  assumes equivp_lowEquiv: "equivp lowEquiv"

begin


lemma lowEquiv_classes_equal: 
"{s. lowEquiv s s1} = {s. lowEquiv s s2} \<longleftrightarrow> lowEquiv s1 s2"
  apply (rule iffI)
  using lowEquiv_classes_eq_imp_low_equiv apply blast
  using equivp_lowEquiv by (simp add: equivp_def)

lemma lowEquivT_imp_O_eq:
  assumes "validFrom s1 tr1" "validFrom s2 tr2" 
      and "lowEquiv s1 s2"
      and "lowEquivT tr1 tr2"
    shows "asBD.O tr1 = asBD.O tr2"
proof(cases "length tr1 = length tr2")
  case False thus ?thesis 
    using O_eq_iff_lowEquivT_length_neq assms by blast    
next
  case True note l = True
  show ?thesis 
  proof(cases "tr1 = []")
    case True
    thus ?thesis using l by auto
  next
    case False
    show ?thesis using l False assms unfolding lowEquivT_def2[OF assms(1,2) False] 
    apply(induct tr1 tr2 arbitrary: s1 s2 rule: list_nonempty_induct2)
    apply (simp add: getObs_def)
      using equivp_lowEquiv equivp_def apply (simp add: lowEquiv_classes_equal)
    subgoal for trn1 tr1 trn2 tr2
    apply(cases "tr1 = []")
      subgoal by simp
      subgoal apply (simp add: getObs_def)        
        using lowEquiv_classes_equal
        unfolding validFrom_Cons
        by blast
    . . 
  qed
qed 


lemma O_eq_iff_lowEquivT:
  assumes "validFrom s1 tr1" "validFrom s2 tr2" 
      and "lowEquiv s1 s2"
    shows "asBD.O tr1 = asBD.O tr2 \<longleftrightarrow> lowEquivT tr1 tr2"
  using assms apply (intro iffI)
  apply (frule_tac s\<^sub>2=s2 in O_eq_imp_lowEquivT, blast+)
  by (simp add: Strict_OD.lowEquivT_imp_O_eq Strict_OD_axioms)

lemma isLeak_iff_asBD_isleak: 
"(\<exists>tr tr'. validFrom s tr \<and> validFrom s' tr' \<and> tracesLeakVia s tr s' tr' lops) \<longleftrightarrow>
  lowEquiv s s' \<and> asBD.isLeak s lops s' lops"
  apply (rule iffI)
  using isLeak_imp_asBD_isleak apply blast
  unfolding asBD.isLeak_def tracesLeakVia_def apply safe
  apply (simp add: B_def O_eq_iff_lowEquivT S_map lowOpT_def) 
  by (metis O_eq_iff_lowEquivT list.pred_True) 

theorem secureFor_iff_asBD_secureFor: 
"asBD.secureFor s lops s1 lops \<longleftrightarrow> secureFor s s1 lops"
  apply (rule iffI)
  apply (simp add: secureFor_imp_asBD_secureFor)
  unfolding asBD.secureFor_alt secureFor_def apply clarify
  apply (erule_tac x=tr in allE)
  apply (erule_tac x=tr' in allE)
  apply (elim impE conjE)
  unfolding tracesLeakVia_def apply safe
  using B_S_iff_lowOpT apply auto[1]
  using S_map lowOpT_def apply presburger
  apply (simp add: S_map lowOpT_def)
  by (meson B_def lowEquivT_imp_O_eq)

theorem secure_iff_asBD_secure:
"asBD.secure \<longleftrightarrow> secure"
unfolding asBD.secure_def by (metis implies_secureFor secureFor_iff_asBD_secureFor secure_def)

end
*)


end
