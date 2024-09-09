(* Observational determinism based on simple transition 
systems, with transitions being just pairs of states: *)

theory Simple_Observational_Determinism 
imports Observational_Determinism
begin 

locale Simple_OD = Simple_Transition_System istate validTrans 
      for istate :: "'state \<Rightarrow> bool" 
      and validTrans :: "('state \<times> 'state) \<Rightarrow> bool"
  + fixes lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
      and lowOp :: "'state \<Rightarrow> 'lowOp" 
(* we assume, like Cheang, that the low operation to be executed 
   is already known in the source state *)
  assumes "reflp lowEquiv" 
      and "symp lowEquiv" 
(* should not name this equivp_lowEquiv, since then at interpretation 
I'd get a clash with the equivp_lowEquiv obtained from OD via the 
sublocale OD command. *)

begin


sublocale OD 
  where istate = istate and validTrans = validTrans 
and srcOf = fst and tgtOf = snd and lowEquiv = lowEquiv and lowOp = "\<lambda>(_,s). lowOp s" 
  apply standard using Simple_OD_axioms Simple_OD_def by blast+

(* Low equivalence for "simple traces" (again, the suffix "S" for "simple" )  *)
definition lowEquivTS :: "'state list \<Rightarrow> 'state list \<Rightarrow> bool" where 
"lowEquivTS \<equiv> list_all2 lowEquiv"

lemma list_all2_lemmas_lowEquivTS: \<open>list_all2_lemmas lowEquivTS lowEquiv\<close>
  unfolding lowEquivTS_def apply standard
  by blast

interpretation lowEquivTS: list_all2_lemmas lowEquivTS lowEquiv
  by (rule list_all2_lemmas_lowEquivTS)

interpretation lowEquivT: list_all2_lemmas lowEquivT lowEquivTrans
  by (rule list_all2_lemmas_lowEquivT)

lemma lowEquivTS_intermediary:
  assumes \<open>length tr = length tr'\<close> 
      and \<open>valid tr\<close> and \<open>valid tr'\<close>
      and \<open>lowEquivTS (fst (hd tr) # map snd tr) (fst (hd tr') # map snd tr')\<close>
    shows \<open>lowEquivT tr tr'\<close>
proof (cases \<open>tr = []\<close>)
  case True
  then show ?thesis using assms(1) by auto
next
  case a: False
  then show ?thesis 
    proof (cases \<open>tr' = []\<close>)
      case True
      then show ?thesis 
        using a assms(1) by auto
    next
      case False
      show ?thesis 
        using assms(1) a False assms(2-) proof (induct rule: rev_nonempty_induct2)
        case (single x y)
        then show ?case 
          using lowEquivTS.hd lowEquivTS.tl by fastforce
      next
        case (snoc x xs y ys)
        show ?case 
          apply (subgoal_tac \<open>length (map snd xs) = length (map snd ys)\<close>) defer
          apply (simp add: snoc.hyps(1))
          using snoc.prems snoc.hyps(1-3)
          apply (frule_tac snoc.hyps(4))
          using valid_valid2 apply auto[1]
          using valid_valid2 apply auto[1]
          unfolding hd_append2  map_append lowEquivTS.Cons
          using lowEquivTS.appendE(1) apply metis
          apply (rule lowEquivT.append1I)
          apply blast
          apply (elim conjE)
          apply simp
          unfolding lowEquivTrans_def apply (intro conjI)
          apply (frule_tac lowEquivTS.append1E(1))
          apply (metis list.distinct(1) list.sel(1) lowEquivT.last lowEquivTrans_def valid_append)
          apply (rule lowEquivTS.append1E(2), simp)
          done
      qed
   qed
qed


(* Transfer: *)
lemma lowEquivTS_toS_valid[simp]: 
"valid tr \<Longrightarrow> valid tr' \<Longrightarrow> 
 lowEquivTS (toS tr) (toS tr') \<longleftrightarrow> lowEquivT tr tr'"
  apply (rule iffI)
  subgoal 
    apply (case_tac \<open>tr = []\<close>, auto)
    apply (case_tac \<open>tr' = []\<close>, auto)
    apply (frule lowEquivTS.lengthD)
    apply (frule length_toS_length)
    apply simp
    unfolding toS_def apply auto
    using lowEquivTS_intermediary by blast
  subgoal
    apply (rule lowEquivT.inducts, blast)
    apply simp
    unfolding lowEquivTrans_def
    unfolding toS_def apply auto
    apply (case_tac \<open>xs = []\<close>, auto)
    apply (rule lowEquivTS.ConsI, blast)
    unfolding lowEquivTS.single apply blast
    apply (rule lowEquivTS.ConsI, blast)
    apply (rule lowEquivTS.ConsI, blast)
    apply (case_tac \<open>ys = []\<close>, auto)
    apply (rule lowEquivTS.ConsE)
    by simp
  .


lemma lowEquivTS_toS_validFrom[simp]: 
"validFrom s tr \<Longrightarrow> validFrom s' tr' \<Longrightarrow> 
 lowEquivTS (toS tr) (toS tr') \<longleftrightarrow> lowEquivT tr tr'"
unfolding validFrom_def 
using lowEquivTS_def lowEquivTS_toS_valid lowEquivT_def by auto

lemma lowEquivT_fromS[simp]: 
assumes 1: "length sl > Suc 0 \<or> length sl' > Suc 0"
shows "lowEquivT (fromS sl) (fromS sl') \<longleftrightarrow> lowEquivTS sl sl'"
proof(cases "length sl' \<le> Suc 0")
  case True thus ?thesis using 1
  unfolding lowEquivT_def lowEquivTS_def list_all2_conv_all_nth 
  by (metis fromS_eq_Nil length_0_conv not_less) 
next
  case False 
  hence 2: "length sl' > Suc 0" by auto
  thus ?thesis using 1 
  unfolding lowEquivT_def lowEquivTS_def lowEquivTrans_def list_all2_conv_all_nth 
  apply safe
    subgoal 
    	by (metis toS_fromS_nonSingl fromS_eq_Nil length_toS nat_neq_iff not_le)
    subgoal for i apply(cases i)
      subgoal by (metis False fromS_eq_Nil length_greater_0_conv nat_neq_iff toS_fromS_nonSingl toS_nth_0)
      subgoal for j apply(elim allE[of _ j]) 
      	 by (metis length_fromS_notNil length_toS Suc_lessD Suc_less_eq fromS_eq_Nil fromS_nth leD 
        length_greater_0_conv nat_neq_iff snd_conv toS_fromS_nonSingl) .
    subgoal by (metis length_0_conv length_fromS_notNil)
    subgoal by (metis False Nitpick.size_list_simp(2) fromS_nth le_0_eq length_fromS_notNil 
       length_tl less_SucI less_imp_le_nat prod.exhaust_sel prod.inject)
    subgoal by (smt (verit, ccfv_threshold) Ex_less_Suc length_fromS_notNil 
        length_toS Suc_lessD fromS_nth length_greater_0_conv 
       less_trans_Suc nat_neq_iff snd_conv toS_fromS_nonSingl) 
    apply (metis False Nitpick.size_list_simp(2) Simple_Transition_System.fromS_eq_Nil 
         Simple_Transition_System.length_fromS_notNil fromS_Nil length_tl)
    apply (metis (no_types, opaque_lifting) Simple_Transition_System.fromS_eq_Nil \<open>\<And>i. \<lbrakk>Suc 0 < length sl'; Suc 0 < length sl; length (fromS sl) = length (fromS sl'); \<forall>i<length (fromS sl). lowEquiv (fst (fromS sl ! i)) (fst (fromS sl' ! i)) \<and> lowEquiv (snd (fromS sl ! i)) (snd (fromS sl' ! i)); i < length sl\<rbrakk> \<Longrightarrow> lowEquiv (sl ! i) (sl' ! i)\<close> 
      length_0_conv not_le)
    using \<open>\<lbrakk>Suc 0 < length sl'; Suc 0 < length sl; length sl = length sl'; \<forall>i<length sl. lowEquiv (sl ! i) (sl' ! i)\<rbrakk> \<Longrightarrow> length (fromS sl) = length (fromS sl')\<close> apply presburger    
    using \<open>\<And>i. \<lbrakk>Suc 0 < length sl'; Suc 0 < length sl; length sl = length sl'; \<forall>i<length sl. lowEquiv (sl ! i) (sl' ! i); i < length (fromS sl)\<rbrakk> \<Longrightarrow> lowEquiv (fst (fromS sl ! i)) (fst (fromS sl' ! i))\<close> apply presburger
    using \<open>\<And>i. \<lbrakk>Suc 0 < length sl'; Suc 0 < length sl; length sl = length sl'; \<forall>i<length sl. lowEquiv (sl ! i) (sl' ! i); i < length (fromS sl)\<rbrakk> \<Longrightarrow> lowEquiv (snd (fromS sl ! i)) (snd (fromS sl' ! i))\<close> by presburger
qed 

(* We should not assume the same operation for the last state in the 
trace -- this seems to be the correct (stronger) notion of TPOD for the 
finite case. (Recall: Cheung uses infinite traces, so does not worry about this.)
*)
definition lowOpTS :: "'state list \<Rightarrow> 'lowOp list" where 
"lowOpTS sl \<equiv> if sl = [] then [] else map lowOp (tl sl)"

lemma lowOpTS_Empty[simp]: \<open>lowOpTS [] = []\<close>
  unfolding lowOpTS_def by auto

lemma lowOpTS_toS_valid[simp]: 
"valid tr \<Longrightarrow> lowOpTS (toS tr) = lowOpT tr"
unfolding lowOpTS_def lowOpT_def apply(rule nth_equalityI)
  subgoal by simp
  subgoal for i 
    apply (cases \<open>toS tr = []\<close>, simp_all)
    unfolding case_prod_beta' toS_def by simp
  .

lemma lowOpTS_toS_validFrom[simp]: 
"validFrom s tr \<Longrightarrow> lowOpTS (toS tr) = lowOpT tr"
using lowOpTS_def lowOpTS_toS_valid lowOpT_def validFrom_def by fastforce

lemma lowOpTS_fromS[simp]: 
"lowOpT (fromS sl) = lowOpTS sl"
unfolding lowOpT_def lowOpTS_def apply(rule nth_equalityI)
  subgoal by simp
  subgoal for i 
    using fromS_nth nth_butlast
    unfolding fromS_def by fastforce 
  .
    
definition tracesLeakViaS :: "'state \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> 'state list \<Rightarrow> 'lowOp list \<Rightarrow> bool" where 
"tracesLeakViaS s sl s' sl' lops \<equiv> 
 lowEquiv s s' \<and> (sl = [] \<longleftrightarrow> sl' = []) \<and> 
 lowOpTS sl = lops \<and> lowOpTS sl' = lops \<and> \<not> lowEquivTS sl sl'"

lemma tracesLeakVia_fromS[simp]: 
assumes "length sl \<noteq> Suc 0" "length sl' \<noteq> Suc 0"
shows "tracesLeakVia s (fromS sl) s' (fromS sl') lops \<longleftrightarrow> tracesLeakViaS s sl s' sl' lops"
proof(cases "length sl > Suc 0 \<or> length sl' > Suc 0")
  case False
  thus ?thesis 
  unfolding tracesLeakVia_def tracesLeakViaS_def apply simp
  apply(cases sl)
   subgoal apply(cases sl')
     using assms by (simp_all add: lowEquivT_def)
   subgoal apply(cases sl')
     using assms by auto 
   .
next
  case True
  thus ?thesis 
  unfolding tracesLeakVia_def tracesLeakViaS_def 
  by simp (metis assms lowOpTS_def lowOpTS_fromS lowOpT_def 
     map_is_Nil_conv toS_fromS_nonSingl)
qed

lemma tracesLeakViaS_toS_valid[simp]: 
"valid tr \<Longrightarrow> valid tr' \<Longrightarrow> 
 tracesLeakViaS s (toS tr) s' (toS tr') lops \<longleftrightarrow> 
 tracesLeakVia s tr s' tr' lops"
unfolding tracesLeakVia_def tracesLeakViaS_def by auto

lemma tracesLeakViaS_toS_validFrom[simp]: 
"validFrom s tr \<Longrightarrow> validFrom s' tr' \<Longrightarrow> 
 tracesLeakViaS s (toS tr) s' (toS tr') lops \<longleftrightarrow> 
 tracesLeakVia s tr s' tr' lops"
unfolding tracesLeakVia_def tracesLeakViaS_def using lowOpT_def by auto

definition tracesLeakS :: "'state \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> 'state list \<Rightarrow> bool" where 
"tracesLeakS s sl s' sl' \<equiv> 
 lowEquiv s s' \<and> (sl = [] \<longleftrightarrow> sl' = []) \<and> 
 lowOpTS sl = lowOpTS sl' \<and> \<not> lowEquivTS sl sl'"

lemma not_tracesLeakS_empty[simp]: 
  \<open>\<not>tracesLeakS s [] s' sl'\<close>
  \<open>\<not>tracesLeakS s sl s' []\<close>
  unfolding tracesLeakS_def by auto

lemma tracesLeakS_tracesLeakViaS:
"tracesLeakS s sl s' sl' \<longleftrightarrow> (\<exists>lops. tracesLeakViaS s sl s' sl' lops)"
unfolding tracesLeakS_def tracesLeakViaS_def by auto

lemma tracesLeak_fromS[simp]: 
assumes "length sl \<noteq> Suc 0" "length sl' \<noteq> Suc 0"
shows "tracesLeak s (fromS sl) s' (fromS sl') \<longleftrightarrow> tracesLeakS s sl s' sl'"
using assms unfolding tracesLeakS_tracesLeakViaS tracesLeak_tracesLeakVia by auto
 
lemma tracesLeakS_toS_valid[simp]: 
"valid tr \<Longrightarrow> valid tr' \<Longrightarrow> 
 tracesLeakS s (toS tr) s' (toS tr') \<longleftrightarrow> tracesLeak s tr s' tr'"
unfolding tracesLeakS_tracesLeakViaS tracesLeak_tracesLeakVia by auto

lemma tracesLeakS_toS_validFrom[simp]: 
"validFrom s tr \<Longrightarrow> validFrom s' tr' \<Longrightarrow> 
 tracesLeakS s (toS tr) s' (toS tr') \<longleftrightarrow> tracesLeak s tr s' tr'"
unfolding tracesLeakS_tracesLeakViaS tracesLeak_tracesLeakVia by auto

lemma secureFor_altS: 
"secureFor s s' lops \<longleftrightarrow> 
 (\<forall>sl sl'. validFromS s sl \<and> validFromS s' sl' \<longrightarrow> 
           \<not> tracesLeakViaS s sl s' sl' lops)"
unfolding secureFor_def apply safe
  subgoal for sl sl'
  apply(erule allE[of _ "fromS sl"]) apply(erule allE[of _ "fromS sl'"]) 
  apply(cases "length sl = Suc 0 \<or> length sl' = Suc 0")
    subgoal apply (cases sl)
      subgoal apply(cases sl')
        subgoal by auto
        subgoal for s ssl unfolding tracesLeakViaS_def lowEquivTS_def by simp .
      subgoal for s' ssl' apply(cases sl')
        subgoal unfolding tracesLeakViaS_def lowEquivTS_def by simp 
        subgoal apply simp
          using lowEquivTS.Cons 
        length_fromS_notNil validFromS_def diff_Suc_1 fromS_singl 
       length_0_conv length_Cons list.sel(1) list.size(3) lowEquivTS.Nil 
        lowOpTS_fromS nat.simps(3) 
       not_tracesLeakVia_NilR tracesLeakViaS_def tracesLeakVia_def
          by (smt (verit, del_insts) Suc_mono lowEquivT_fromS neq0_conv validFrom_Nil validFrom_fromS)
         . .
    subgoal by simp .
  subgoal for tr tr'
  apply(erule allE[of _ "toS tr"]) apply(erule allE[of _ "toS tr'"]) by simp .


sublocale Cheang_OD 
  where Tr = \<open>{tr. istate (hd tr) \<and> validFromS (hd tr) tr}\<close>
    and op_low = lowOpTS
    and low_equiv = lowEquiv
  .

lemma secure_altS: \<open>secure \<longleftrightarrow> (\<forall>s tr s' tr'. istate s \<and> istate s' \<and> lowEquiv s s' \<and> 
    validFromS s tr \<and> validFromS s' tr' \<and> lowOpTS tr = lowOpTS tr' \<and> (tr = [] \<longleftrightarrow> tr' = [])
      \<longrightarrow> lowEquivTS tr tr')\<close>
  unfolding secure_alt' apply (intro iff_allI iffI allI impI; elim conjE)
  subgoal for s tr s' tr'
    apply (erule allE[of _ \<open>fromS tr\<close>], erule allE[of _ s'], erule allE[of _ \<open>fromS tr'\<close>])
    apply (erule impE)
    apply (intro conjI validFrom_fromS_impI, assumption+)
    apply simp
    apply (elim validFromSE)
    apply simp_all
    using lowEquivT_fromS 
    by (metis Suc_lessI length_greater_0_conv less_Suc0E list.discI lowEquivTS.conv_all_nth nth_Cons_0)
  subgoal for s tr s' tr'
    apply (erule allE[of _ "toS tr"])
    apply (erule allE[of _ s'])
    apply (erule allE[of _ "toS tr'"])
    apply (elim impE)
    apply simp_all
    apply auto
    using not_tracesLeak_NilR tracesLeak_def apply force
    using not_tracesLeak_NilL tracesLeak_def apply force
    done
  .


lemma \<open>secure \<longleftrightarrow> OD\<close>
unfolding secure_altS OD_def proof (intro iffI allI ballI impI; elim conjE)
  fix \<pi>\<^sub>1 \<pi>\<^sub>2 assume \<open>\<forall>s tr s' tr'. istate s \<and> istate s' \<and> lowEquiv s s' \<and>
          validFromS s tr \<and> validFromS s' tr' \<and> lowOpTS tr = lowOpTS tr' \<and>
          (tr = []) = (tr' = []) \<longrightarrow> lowEquivTS tr tr'\<close>
       \<open>\<pi>\<^sub>1 \<in> {tr. istate (hd tr) \<and> validFromS (hd tr) tr}\<close>
       \<open>\<pi>\<^sub>2 \<in> {tr. istate (hd tr) \<and> validFromS (hd tr) tr}\<close>
       \<open>lowEquiv (hd \<pi>\<^sub>1) (hd \<pi>\<^sub>2)\<close>
       \<open>lowOpTS \<pi>\<^sub>1 = lowOpTS \<pi>\<^sub>2\<close>
  thus \<open>low_equivs \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    apply -
    apply (erule allE[of _ \<open>hd \<pi>\<^sub>1\<close>], erule allE[of _ \<pi>\<^sub>1], 
           erule allE[of _ \<open>hd \<pi>\<^sub>2\<close>], erule allE[of _ \<pi>\<^sub>2])
    apply (cases \<open>lowEquivTS \<pi>\<^sub>1 \<pi>\<^sub>2\<close>, auto)
    apply (simp add: lowEquivTS_def)
    sledgehammer  
    sorry
next
  fix s\<^sub>1 \<pi>\<^sub>1 s\<^sub>2 \<pi>\<^sub>2 
  assume \<open>\<forall>\<pi>\<^sub>1\<in>{tr. istate (hd tr) \<and> validFromS (hd tr) tr}.
          \<forall>\<pi>\<^sub>2\<in>{tr. istate (hd tr) \<and> validFromS (hd tr) tr}. OD_Tr \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
         \<open>istate s\<^sub>1\<close> \<open>istate s\<^sub>2\<close> \<open>lowEquiv s\<^sub>1 s\<^sub>2\<close> \<open>validFromS s\<^sub>1 \<pi>\<^sub>1\<close> \<open>validFromS s\<^sub>2 \<pi>\<^sub>2\<close>
         \<open>lowOpTS \<pi>\<^sub>1 = lowOpTS \<pi>\<^sub>2\<close> \<open>(\<pi>\<^sub>1 = []) = (\<pi>\<^sub>2 = [])\<close>
  thus \<open>lowEquivTS \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    apply (cases \<pi>\<^sub>1)
    apply (cases \<pi>\<^sub>2)
    apply simp
    apply blast
    apply (cases \<pi>\<^sub>2)
    apply blast
    apply simp
    apply (erule allE[of _ \<pi>\<^sub>1], erule impE)
    apply (simp add: validFromS_def)
    apply (erule allE[of _ \<pi>\<^sub>2], erule impE)
    apply (simp add: validFromS_def)
    by (simp add: lowEquivTS_def validFromS_def)
qed

end (* context Simple_OD *)


(* *)

locale Simple_Cond_OD = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: Simple_OD istate1 validTrans1  
          lowEquiv lowOp1 
+   
(* Augmented semantics (same lowEquiv) : *)
 Aug: Simple_OD istate2 validTrans2 
          lowEquiv lowOp2
for
  istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
and
  validTrans1 :: "'state \<times> 'state \<Rightarrow> bool" and validTrans2 :: "'state \<times> 'state \<Rightarrow> bool"
and 
 lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
and lowOp1 :: "'state \<Rightarrow> 'lowOp" and lowOp2 :: "'state \<Rightarrow> 'lowOp"

begin

sublocale Cond_OD where 
istate1 = istate1 and istate2 = istate2 
and
  validTrans1 = validTrans1 and validTrans2 = validTrans2
and
  srcOf1 = fst and srcOf2 = fst and tgtOf1 = snd and tgtOf2 = snd
and 
 lowEquiv = lowEquiv
and lowOp1 = "\<lambda>(_,s). lowOp1 s" and lowOp2 = "\<lambda>(_,s). lowOp2 s"
  by standard 

abbreviation "fromS1 \<equiv> Orig.fromS"
abbreviation "toS1 \<equiv> Orig.toS"
abbreviation "fromS2 \<equiv> Aug.fromS"
abbreviation "toS2 \<equiv> Aug.toS"

abbreviation "validS1 \<equiv> Orig.validS"
abbreviation "validFromS1 \<equiv> Orig.validFromS"
(* *)
abbreviation "validS2 \<equiv> Aug.validS"
abbreviation "validFromS2 \<equiv> Aug.validFromS"

thm condSecure_def
thm Orig.secureFor_altS
thm Aug.secureFor_altS

end (* context Simple_Cond_OD *)


locale Simple_OD_plus_highOps = Simple_OD istate validTrans lowEquiv lowOp
for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" 
and lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
and lowOp :: "'state  \<Rightarrow> 'lowOp"
+
fixes highOp :: "'state  \<Rightarrow> 'highOp"
begin

sublocale OD_plus_highOps where istate = istate and validTrans = validTrans 
and srcOf = fst and tgtOf = snd and lowEquiv = lowEquiv 
and lowOp = "\<lambda>(_,s). lowOp s"
and highOp = "\<lambda>(_,s). highOp s" 
apply standard . 

definition highOpTS :: "'state list \<Rightarrow> 'highOp list" where 
"highOpTS sl \<equiv> if sl = [] then [] else map highOp (tl sl)"

lemma highOpTS_toS_valid[simp]: 
"valid tr \<Longrightarrow> highOpTS (toS tr) = highOpT tr"
unfolding highOpTS_def highOpT_def apply(rule nth_equalityI)
  subgoal by simp
  subgoal for i apply(cases i)
    subgoal 
      using case_prod_unfold nth_butlast toS_nth_0 
      by (smt (verit) length_greater_0_conv length_map list.sel(3) nth_map toS_def)
    subgoal for j 
      using case_prod_beta' nth_butlast toS_nth_Suc valid_validTrans_nth_srcOf_tgtOf 
      by (smt (verit) length_map less_nat_zero_code list.sel(3) list.size(3) nth_map toS_def)
  . .

lemma highOpTS_toS_validFrom[simp]: 
"validFrom s tr \<Longrightarrow> highOpTS (toS tr) = highOpT tr"
using highOpTS_def highOpTS_toS_valid highOpT_def validFrom_def by fastforce

lemma highOpTS_fromS[simp]: 
"highOpT (fromS sl) = highOpTS sl"
unfolding highOpT_def highOpTS_def apply(rule nth_equalityI)
  subgoal by simp
  subgoal for i using fromS_nth nth_butlast nth_tl by fastforce 
  .


end (* context Simple_OD_plus_highOps *)


locale Simple_TPOD = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: Simple_OD_plus_highOps istate1 validTrans1  
          lowEquiv lowOp1 highOp1
+   
(* Augmented semantics (same lowEquiv) : *)
 Aug: Simple_OD_plus_highOps istate2 validTrans2 
          lowEquiv lowOp2 highOp2

  for istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
    and validTrans1 :: "'state \<times> 'state \<Rightarrow> bool" and validTrans2 :: "'state \<times> 'state \<Rightarrow> bool"
    and  lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
    and lowOp1 :: "'state \<Rightarrow> 'lowOp" and lowOp2 :: "'state \<Rightarrow> 'lowOp"
    and highOp1 :: "'state \<Rightarrow> 'highOp" and highOp2 :: "'state \<Rightarrow> 'highOp"
+
  fixes speculating :: "'state \<Rightarrow> bool"
(*  assumes equivp_validTrans1_lowEquiv:
    \<open>equivp (\<lambda>s\<^sub>1' s\<^sub>2'. \<exists>s\<^sub>1 s\<^sub>2. validTrans1 (s\<^sub>1, s\<^sub>1') \<and> validTrans1 (s\<^sub>2, s\<^sub>2') \<and> lowEquiv s\<^sub>1' s\<^sub>2')\<close>*)
begin

sublocale TPOD 
  where istate1 = istate1 and istate2 = istate2 
    and validTrans1 = validTrans1 and validTrans2 = validTrans2
    and srcOf1 = fst and srcOf2 = fst and tgtOf1 = snd and tgtOf2 = snd
    and lowEquiv = lowEquiv
    and lowOp1 = "\<lambda>(_,s). lowOp1 s" and lowOp2 = "\<lambda>(_,s). lowOp2 s"
    and highOp1 = "\<lambda>(_,s). highOp1 s" and highOp2 = "\<lambda>(_,s). highOp2 s"
    and speculating = "\<lambda>(s,_). speculating s"
  by standard 

sublocale Simple_Cond_OD where 
 istate1 = istate1 and istate2 = istate2
and
 validTrans1 = validTrans1 and validTrans2 = validTrans2
and 
 lowEquiv = lowEquiv
and lowOp1 = lowOp1 and lowOp2 = lowOp2 
  by standard 

abbreviation "lowEquivTS1 \<equiv> Orig.lowEquivTS"
abbreviation "lowOpTS1 \<equiv> Orig.lowOpTS"  
abbreviation "highOpTS1 \<equiv> Orig.highOpTS" 
abbreviation "tracesLeakViaS1 \<equiv> Orig.tracesLeakViaS" 
abbreviation "tracesLeakS1 \<equiv> Orig.tracesLeakS"

interpretation lowEquivTS: list_all2_lemmas lowEquivTS1 lowEquiv
  by (rule Orig.list_all2_lemmas_lowEquivTS)

abbreviation "lowEquivTS2 \<equiv> Aug.lowEquivTS"
abbreviation "lowOpTS2 \<equiv> Aug.lowOpTS"  
abbreviation "highOpTS2 \<equiv> Aug.highOpTS" 
abbreviation "tracesLeakViaS2 \<equiv> Aug.tracesLeakViaS" 
abbreviation "tracesLeakS2 \<equiv> Aug.tracesLeakS" 

definition tracesOKS1 :: "'state list \<Rightarrow> 'state list \<Rightarrow> bool" where 
"tracesOKS1 sl sl' \<equiv> 
 (sl = [] \<longleftrightarrow> sl' = []) \<and> 
 lowOpTS1 sl = lowOpTS1 sl' \<and> lowEquivTS1 sl sl'"

lemma tracesOKS1_empty[simp]: \<open>tracesOKS1 [] []\<close>
  unfolding tracesOKS1_def by auto

lemma tracesOKS1_lengthD:
  assumes \<open>tracesOKS1 sl sl'\<close>
    shows \<open>length sl = length sl'\<close>
  using assms lowEquivTS.lengthD unfolding tracesOKS1_def by auto 


lemma tracesOK_fromS[simp]: 
assumes "length sl \<noteq> Suc 0" "length sl' \<noteq> Suc 0"
shows "tracesOK1 (fromS1 sl) (fromS1 sl') \<longleftrightarrow> tracesOKS1 sl sl'"
proof(cases "length sl > Suc 0 \<or> length sl' > Suc 0")
  case False
  thus ?thesis 
  unfolding tracesOK1_def tracesOKS1_def apply simp
  apply(cases sl)
   subgoal apply(cases sl')
     using assms by (simp_all add: Orig.lowEquivT_def)
   subgoal apply(cases sl')
     using assms by auto 
   .
next
  case True
  thus ?thesis 
  unfolding tracesOK1_def tracesOKS1_def assms
  apply (simp add: Orig.lowOpTS_def Orig.lowOpT_def)
  by (metis (no_types, lifting) Orig.Simple_OD_axioms Orig.lowOpTS_fromS Orig.lowOpT_def Simple_OD.lowOpTS_def)
qed

lemma tracesOKS1_toS_valid[simp]: 
"valid1 tr \<Longrightarrow> valid1 tr' \<Longrightarrow> 
 tracesOKS1 (toS1 tr) (toS1 tr') \<longleftrightarrow> tracesOK1 tr tr'"
  unfolding tracesOK1_def tracesOKS1_def by auto

lemma tracesOKS1_toS_validFrom[simp]: 
"validFrom1 s tr \<Longrightarrow> validFrom1 s' tr' \<Longrightarrow> 
 tracesOKS1 (toS1 tr) (toS1 tr') \<longleftrightarrow> tracesOK1 tr tr'"
unfolding tracesOK1_def tracesOKS1_def using Orig.lowOpT_def by auto


thm counterpart_def[no_vars]

fun 
  stutterS :: \<open>'state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool\<close>
where
  \<open>stutterS s2 s1 s1' = (
    if speculating s2 
      then s1' = s1
      else s1' \<noteq> s1
  )\<close>

lemma stutterTS_equiv: \<open>stutterT (s2, s2') (s1, s1') \<longleftrightarrow> stutterS s2 s1 s1'\<close>
  using stutterT_def by auto

lemma stutter_eq: \<open>stutterT = (\<lambda>(s2, s2') (s1, s1'). stutterS s2 s1 s1')\<close>
  unfolding stutterT_def stutterS.simps
  unfolding case_prod_beta
  by metis


definition
  counterpart_stutterS :: "'state list \<Rightarrow> 'state list \<Rightarrow> bool" 
where
  \<open>counterpart_stutterS = list_step_all2 (\<lambda>s2 s1 s2'. stutterS s2 s1)\<close>

lemma list_step_all2_lemmas_counterpart_stutterS: 
  \<open>list_step_all2_lemmas counterpart_stutterS (\<lambda>s2 s1 s2' s1'. stutterS s2 s1 s1')\<close>
  unfolding counterpart_stutterS_def apply standard
  by blast

interpretation counterpart_stutterT: list_all2_lemmas counterpart_stutterT stutterT  
  by (rule list_all2_lemmas_counterpart_stutterT)

interpretation counterpart_stutterS: list_step_all2_lemmas counterpart_stutterS 
  \<open>(\<lambda>s2 s1 s2' s1'. stutterS s2 s1 s1')\<close>
  by (rule list_step_all2_lemmas_counterpart_stutterS)

lemma counterpart_stutterT_fromS:
  assumes \<open>Suc 0 < length sl2 \<or> Suc 0 < length sl1\<close>
    shows \<open>counterpart_stutterT (fromS2 sl2) (fromS1 sl1) \<longleftrightarrow> counterpart_stutterS sl2 sl1\<close>
  unfolding counterpart_stutterT_def counterpart_stutterS_def stutter_eq apply safe
  subgoal
    using assms by (rule_tac Orig.fromS_list_step_all2I, blast+)
  subgoal
    by (rule_tac Orig.fromS_list_step_all2E, blast)
  .

lemma counterpart_stutterT_toS_valid:
  assumes \<open>valid2 tr2\<close> and \<open>valid1 tr1\<close>
    shows \<open>counterpart_stutterT tr2 tr1 \<longleftrightarrow> counterpart_stutterS (toS2 tr2) (toS1 tr1)\<close>
  using counterpart_stutterT_fromS assms Simple_Transition_System.fromS_toS_valid 
  by (metis Orig.Nil_not_valid Orig.length_toS Suc_less_eq2 length_greater_0_conv)

lemma counterpart_stutterT_toS_validFrom:
  assumes \<open>validFrom2 s2 tr2\<close> and \<open>validFrom1 s1 tr1\<close>
    shows \<open>counterpart_stutterT tr2 tr1 \<longleftrightarrow> counterpart_stutterS (toS2 tr2) (toS1 tr1)\<close>
  using assms apply (cases "tr2 = [] \<or> tr1 = []")
  subgoal
    apply auto
    using Orig.validFrom_def Simple_Transition_System.fromS_Nil Simple_Transition_System.fromS_list_step_all2E Simple_Transition_System.fromS_toS_valid counterpart_stutterS_def counterpart_stutterT_def list_all2_Nil by fastforce+
  subgoal
    apply (rule_tac counterpart_stutterT_toS_valid)
    unfolding Orig.validFrom_def Aug.validFrom_def by safe
  .

definition 
  counterpartS :: "'state \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> 'state list \<Rightarrow> bool" 
where 
  "counterpartS s2 sl2 s1 sl1 \<equiv>
    (sl2 = [] \<longleftrightarrow> sl1 = []) \<and> 
    lowOpTS2 sl2 = lowOpTS1 sl1 \<and> highOpTS2 sl2 = highOpTS1 sl1 \<and>
    counterpart_stutterS sl2 sl1"

lemma counterpart_fromS[simp]: 
assumes "length sl2 \<noteq> Suc 0" "length sl1 \<noteq> Suc 0"
shows "counterpart s2 (fromS2 sl2) s1 (fromS1 sl1) \<longleftrightarrow> counterpartS s2 sl2 s1 sl1"
proof(cases "length sl2 > Suc 0 \<or> length sl1 > Suc 0")
  case False
  thus ?thesis 
  unfolding counterpart_def counterpartS_def apply simp
  apply(cases sl2)
   subgoal apply(cases sl1)
     using assms by auto
   subgoal apply(cases sl1)
     using assms by auto .
next
  case True
  thus ?thesis 
    unfolding counterpart_def counterpartS_def apply auto
    by (simp_all add: counterpart_stutterT_fromS)
qed

lemma counterpartS_toS_valid[simp]: 
"valid2 tr2 \<Longrightarrow> valid1 tr1 \<Longrightarrow> 
 counterpartS s2 (toS2 tr2) s1 (toS1 tr1) \<longleftrightarrow> 
 counterpart s2 tr2 s1 tr1"
unfolding counterpart_def counterpartS_def 
  using counterpart_stutterT_toS_valid by auto

lemma counterpartS_toS_validFrom[simp]: 
"validFrom2 s2 tr2 \<Longrightarrow> validFrom1 s1 tr1 \<Longrightarrow> 
 counterpartS s2 (toS2 tr2) s1 (toS1 tr1) \<longleftrightarrow> 
 counterpart s2 tr2 s1 tr1"
unfolding counterpart_def counterpartS_def 
  using counterpart_stutterT_toS_validFrom by auto

lemma tpod_altS: 
"tpod \<longleftrightarrow> 
 (\<forall>s2 sl2 s2' sl2' s1 sl1 s1' sl1'.
   counterpartS s2 sl2 s1 sl1 \<and>
   counterpartS s2' sl2' s1' sl1' \<and>
   istate1 s1 \<and>
   istate1 s1' \<and>
   validFromS1 s1 sl1 \<and>
   validFromS1 s1' sl1' \<and>
   tracesOKS1 sl1 sl1' \<and>
   istate2 s2 \<and> istate2 s2' \<and> validFromS2 s2 sl2 \<and> validFromS2 s2' sl2' \<longrightarrow>
   \<not> tracesLeakS2 s2 sl2 s2' sl2')"
proof-
note myDefs = 
  Orig.tracesLeakS_def Orig.lowEquivTS_def 
  Aug.tracesLeakS_def Aug.lowEquivTS_def 
tracesOKS1_def counterpart_def counterpartS_def
show ?thesis 
unfolding tpod_def apply safe
  subgoal for s2 sl2 s2' sl2' s1 sl1 s1' sl1'
  apply(erule allE[of _ "s2"], erule allE[of _ "fromS2 sl2"]) 
  apply(erule allE[of _ "s2'"], erule allE[of _ "fromS2 sl2'"])
  apply(erule allE[of _ "s1"], erule allE[of _ "fromS2 sl1"]) 
  apply(erule allE[of _ "s1'"], erule allE[of _ "fromS2 sl1'"]) 
  apply(cases "length sl2 = Suc 0 \<or> length sl2' = Suc 0 \<or> 
               length sl1 = Suc 0 \<or> length sl1' = Suc 0")
    subgoal apply (cases sl2) 
      subgoal apply(cases sl2')
        subgoal apply(cases sl1)
          subgoal apply(cases sl1')
            subgoal by auto
            subgoal for s1' ssl1' 
            unfolding myDefs by simp .
          subgoal for s1 ssl1 
            subgoal unfolding myDefs by simp . .
        subgoal unfolding myDefs by simp .
      subgoal unfolding myDefs apply simp  
        using Aug.lowOpTS_def Orig.lowOpTS_def 
       Orig.validFromS_def Aug.validFromS_def diff_Suc_1 length_Cons 
        length_butlast length_greater_0_conv length_map list.distinct(1) 
          list.exhaust list.rel_inject(2) list.sel(1) list.size(3)
        by (metis Orig.length_fromS_less1 Orig.lowOpTS_fromS Orig.lowOpT_def list.rel_sel)
     .
   subgoal apply (simp add: myDefs) 
     by (metis Suc_lessI counterpart_stutterT_fromS length_greater_0_conv)
     .
  subgoal for s2 tr2 s2' tr2' s1 tr1 s1' tr1'
    apply(erule allE[of _ s2], erule allE[of _ "toS2 tr2"]) 
    apply(erule allE[of _ s2'], erule allE[of _ "toS2 tr2'"]) 
    apply(erule allE[of _ s1], erule allE[of _ "toS2 tr1"]) 
    apply(erule allE[of _ s1'], erule allE[of _ "toS2 tr1'"]) 
    by simp . 
qed

(* This is the definition of TPOD to work with: *)
lemma tpod_altS_stateFree: 
"tpod \<longleftrightarrow> 
 (\<forall>sl2 sl2' sl1 sl1'.
   sl2 = [] \<and> sl2' = [] \<and> sl1 = [] \<and> sl1' = [] 
   \<or>  
   istate1 (hd sl1) \<and> istate1 (hd sl1') \<and> istate2 (hd sl2) \<and> istate2 (hd sl2') \<and> 
   validS1 sl1 \<and> validS1 sl1' \<and> validS2 sl2 \<and> validS2 sl2' \<and> 
   counterpartS (hd sl2) sl2 (hd sl1) sl1 \<and>
   counterpartS (hd sl2') sl2' (hd sl1') sl1' \<and>
   tracesOKS1 sl1 sl1' 
   \<longrightarrow>
   \<not> tracesLeakS2 (hd sl2) sl2 (hd sl2') sl2')"
  unfolding tpod_altS  
  apply safe
  using Aug.not_tracesLeakS_empty(2) apply blast
  subgoal for sl2 sl2' sl1 sl1'
    apply (erule allE[of _ \<open>hd sl2\<close>], erule allE[of _ sl2]) 
    apply (erule allE[of _ \<open>hd sl2'\<close>], erule allE[of _ sl2']) 
    apply (erule allE[of _ \<open>hd sl1\<close>], erule allE[of _ sl1]) 
    apply (erule allE[of _ \<open>hd sl1'\<close>], erule allE[of _ sl1']) 
    unfolding Orig.validFromS_def Aug.validFromS_def by safe
  subgoal for s2 sl2 s2' sl2' s1 sl1 s1' sl1'
    apply (erule allE[of _ sl2]) 
    apply (erule allE[of _ sl2']) 
    apply (erule allE[of _ sl1]) 
    apply (erule allE[of _ sl1']) 
    apply (elim impE)
    apply (metis (no_types, lifting) Simple_TPOD.counterpartS_def Simple_TPOD.tracesOKS1_def Simple_TPOD_axioms Simple_Transition_System.validFromS_def)
    by (metis Aug.not_tracesLeakS_empty(1) Aug.not_tracesLeakS_empty(2) Simple_Transition_System.validFromS_def)
  .

(*  *)

(* The unwinding theorem for TPOD: *)

thm initCond_def

(* NB: The definition of initCond is already OK, no point in an alternative definition. *)

lemma unwindCond_altS: "unwindCond \<Delta> \<longleftrightarrow> (\<forall>s2 s2' s1 s1'. 
 \<Delta> s2 s2' s1 s1' \<and> lowEquiv s2 s2' \<and> lowEquiv s1 s1' \<longrightarrow> 
 (\<forall>ss2 ss2' ss1 ss1'. 
   validTrans2 (s2,ss2) \<and> validTrans2 (s2',ss2') \<and> lowOp2 ss2 = lowOp2 ss2' 
   \<and>
   validTrans1 (s1,ss1) \<and> validTrans1 (s1',ss1') \<and> lowOp1 ss1 = lowOp1 ss1' 
   \<and> 
   lowOp1 ss1 = lowOp2 ss2 \<and> 
   highOp1 ss1 = highOp2 ss2 \<and> highOp1 ss1' = highOp2 ss2' \<and>
   stutterS s2 s1 ss1 \<and> stutterS s2' s1' ss1'
   \<and> 
   lowEquiv ss1 ss1'
   \<longrightarrow> 
   \<Delta> ss2 ss2' ss1 ss1' \<and> lowEquiv ss2 ss2'))"
  unfolding unwindCond_def by (simp add: stutterTS_equiv)


(*
is still the right theorem for the correctness of unwinding. 
*)

(* Compositional version: *)
(*
lemma unwindIntoCond_altS: 
"unwindIntoCond PC first next \<Delta>s \<longleftrightarrow> (\<forall>pc\<in>PC. \<forall>s2 s2' s1 s1'. 
 \<Delta>s pc s2 s2' s1 s1' \<and> lowEquiv s2 s2' \<and> lowEquiv s1 s1' \<longrightarrow> 
 (\<forall>ss2 ss2' ss1 ss1'. 
   validTrans2 (s2,ss2) \<and> validTrans2 (s2',ss2') \<and> lowOp2 s2 = lowOp2 s2' 
   \<and>
   validTrans1 (s1,ss1) \<and> validTrans1 (s1',ss1') \<and> lowOp1 s1 = lowOp1 s1' \<and> 
   lowOp1 s1 = lowOp2 s2 \<and> highOp1 s1 = highOp2 s2 \<and> highOp1 s1' = highOp2 s2' 
   \<and> 
   lowEquiv ss1 ss1'
   \<longrightarrow> 
   \<Delta>s (next pc) ss2 ss2' ss1 ss1' \<and> lowEquiv ss2 ss2'))"
unfolding unwindIntoCond_def by auto
*)

lemma unwindIntoCond_altS: 
"unwindIntoCond PC first next \<Delta>s \<longleftrightarrow> (\<forall>pc\<in>PC. \<forall>sm sm' s s'. 
 \<Delta>s pc sm sm' s s' \<and> lowEquiv sm sm' \<and> lowEquiv s s' \<longrightarrow> 
 (\<forall>ssm ssm' ss ss'. 
   validTrans2 (sm,ssm) \<and> validTrans2 (sm',ssm') \<and> lowOp2 ssm = lowOp2 ssm' 
   \<and>
   validTrans1 (s,ss) \<and> validTrans1 (s',ss') \<and> lowOp1 ss = lowOp1 ss' \<and> 
   lowOp1 ss = lowOp2 ssm \<and> highOp1 ss = highOp2 ssm \<and> highOp1 ss' = highOp2 ssm'
   \<and> 
   stutterS sm s ss \<and> stutterS sm' s' ss' \<and>
   lowEquiv ss ss'
   \<longrightarrow> 
   \<Delta>s (next pc) ssm ssm' ss ss' \<and> lowEquiv ssm ssm'))"
unfolding unwindIntoCond_def by (simp add: stutterTS_equiv)


 

(* So *)
thm compositional_unwind_secure
(*
is still the right theorem for the correctness of unwinding. 
*)

thm compositional_unwind_secure[no_vars]

thm unwindIntoCond_altS[no_vars]

definition  "unwindIntoCond2 \<Delta>1 \<Delta>2 =
(\<forall>sm sm' s s'.
       \<Delta>1 sm sm' s s' \<and> lowEquiv sm sm' \<and> lowEquiv s s' \<longrightarrow>
       (\<forall>ssm ssm' ss ss'.
           validTrans2 (sm, ssm) \<and>
           validTrans2 (sm', ssm') \<and>
           lowOp2 ssm = lowOp2 ssm' \<and>
           validTrans1 (s, ss) \<and>
           validTrans1 (s', ss') \<and>
           lowOp1 ss = lowOp1 ss' \<and>
           lowOp1 ss = lowOp2 ssm \<and> highOp1 ss = highOp2 ssm \<and> highOp1 ss' = highOp2 ssm' \<and> 
           lowEquiv ss ss' \<and>
           stutterS sm s ss \<and> stutterS sm' s' ss'
           \<longrightarrow>
           \<Delta>2 ssm ssm' ss ss' \<and> lowEquiv ssm ssm'))"

corollary unwind2_secure: 
  assumes \<open>initCond (\<Delta>s 0)\<close>
      and \<open>(\<And>i. i < m \<Longrightarrow> unwindIntoCond2 (\<Delta>s i) (\<Delta>s (Suc i)))\<close>
      and \<open>unwindIntoCond2 (\<Delta>s m) (\<Delta>s m)\<close>
    shows tpod
apply(rule compositional_unwind_secure[of \<Delta>s 0 "{i . i \<le> m}" 
  "\<lambda>i. if i < m then Suc i else m"])
using assms unfolding unwindIntoCond2_def unwindIntoCond_altS apply safe 
  subgoal for pc sm sm' s s' ssm ssm' ss ss' by (smt (z3) le_eq_less_or_eq)
  subgoal for pc sm sm' s s' ssm ssm' ss ss' using nat_less_le by blast
  subgoal by (metis (mono_tags) Suc_leI order_refl) .


(*    *)
(* The more natural (but less effective) version of tpod. 
It is closer in spirit to conditional security:
*)
(*
lemma tpod'_altS: 
"tpod' \<longleftrightarrow> 
 (\<forall>s2 sl2 s2' sl2'.
   (\<forall>s1 sl1 s1' sl1'. 
      counterpartS s2 sl2 s1 sl1 \<and> counterpartS s2' sl2' s1' sl1' \<and>     
      istate1 s1 \<and> istate1 s1' \<and> validFromS1 s1 sl1 \<and> validFromS1 s1' sl1'
      \<longrightarrow>  
      \<not> tracesLeakS1 s1 sl1 s1' sl1')
   \<and> 
   istate2 s2 \<and> istate2 s2' \<and> validFromS2 s2 sl2 \<and> validFromS2 s2' sl2' 
   \<longrightarrow> 
   \<not> tracesLeakS2 s2 sl2 s2' sl2')"
unfolding tpod'_def apply safe
  subgoal for s2 sl2 s2' sl2'
    apply(erule allE[of _ "s2"], erule allE[of _ "fromS2 sl2"]) 
    apply(erule allE[of _ "s2'"], erule allE[of _ "fromS2 sl2'"])
    apply (subgoal_tac \<open>length sl2 \<noteq> Suc 0 \<and> length sl2' \<noteq> Suc 0\<close>, elim conjE)
    apply (elim impE) defer
    apply (drule_tac Aug.tracesLeak_fromS, blast+)

    using Aug.tracesLeakS_def Orig.tracesLeakS_toS_validFrom

    using Aug.lowOpTS_def Aug.validFrom_fromS One_nat_def Orig.lowEquivTS_def 
Orig.not_tracesLeak_NilR Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.length_fromS_notNil 
Simple_Transition_System.toS_fromS_nonSingl Simple_Transition_System.validFromS_def 
Simple_Transition_System.validFromS_toS  
   counterpartS_toS_valid counterpart_length hd_conv_nth length_butlast less_one list.size(3) 
list_all2_conv_all_nth map_is_Nil_conv not_le
    apply (smt (verit, best) Suc_pred length_greater_0_conv n_not_Suc_n)

    using Aug.lowOpTS_def Aug.validFrom_fromS One_nat_def Orig.fromS_Nil Orig.lowEquivTS_def 
Orig.not_tracesLeak_NilR Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.length_fromS_notNil 
Simple_Transition_System.toS_fromS_nonSingl Simple_Transition_System.validFromS_def 
Simple_Transition_System.validFromS_toS Transition_System.validFrom_def 
   counterpartS_toS_valid counterpart_length hd_conv_nth length_butlast less_one list.size(3) 
list_all2_conv_all_nth map_is_Nil_conv not_le
   
    by (smt (z3) Aug.tracesLeakS_def Orig.fromS_toS_validFrom Orig.tracesLeakS_toS_validFrom counterpartS_toS_validFrom diff_Suc_1 length_0_conv)
  subgoal
    using Aug.lowOpTS_def Aug.validFrom_fromS One_nat_def Orig.fromS_Nil Orig.lowEquivTS_def 
Orig.not_tracesLeak_NilR Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.length_fromS_notNil 
Simple_Transition_System.toS_fromS_nonSingl Simple_Transition_System.validFromS_def 
Simple_Transition_System.validFromS_toS Transition_System.validFrom_def 
   counterpartS_toS_valid counterpart_length hd_conv_nth length_butlast less_one list.size(3) 
list_all2_conv_all_nth map_is_Nil_conv not_le Aug.lowOpTS_def Aug.tracesLeakS_toS_validFrom Orig.lowEquivTS_def Orig.lowOpTS_def Orig.lowOpTS_fromS Orig.lowOpT_def Orig.toS_def Orig.tracesLeakS_def Orig.tracesLeak_fromS Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.fromS_toS_validFrom Simple_Transition_System.validFromS_toS Simple_Transition_System.validFrom_fromS counterpartS_def counterpart_fromS le_eq_less_or_eq length_greater_0_conv 
     length_map list_all2_Nil2

    using Aug.lowOpTS_def Aug.tracesLeakS_toS_validFrom Orig.lowEquivTS_def Orig.lowOpTS_def Orig.lowOpTS_fromS Orig.lowOpT_def Orig.toS_def Orig.tracesLeakS_def Orig.tracesLeak_fromS Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.fromS_toS_validFrom Simple_Transition_System.validFromS_toS Simple_Transition_System.validFrom_fromS counterpartS_def counterpart_fromS le_eq_less_or_eq length_greater_0_conv 
     length_map list_all2_Nil2 (* TODO *)
 	by (smt (verit) Aug.lowOpTS_def Aug.tracesLeakS_toS_validFrom Orig.lowEquivTS_def Orig.lowOpTS_def Orig.lowOpTS_fromS Orig.lowOpT_def Orig.toS_def Orig.tracesLeakS_def Orig.tracesLeak_fromS Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.fromS_toS_validFrom Simple_Transition_System.validFromS_toS Simple_Transition_System.validFrom_fromS counterpartS_def counterpart_fromS le_eq_less_or_eq length_greater_0_conv 
     length_map list_all2_Nil2) .
*)
thm tpod_altS_stateFree

lemma counterpartS_length: "counterpartS s\<^sub>2 sl\<^sub>1 s\<^sub>1 sl\<^sub>2 \<Longrightarrow> length sl\<^sub>2 = length sl\<^sub>1"
unfolding counterpartS_def Aug.lowOpT_def Orig.lowOpT_def Aug.lowOpTS_def 
Orig.lowOpTS_def diff_Suc_1 length_Cons length_butlast length_map list.exhaust
  by (metis Nitpick.size_list_simp(2) length_map)

(*
lemma tpod'_altS_stateFree: 
"tpod' \<longleftrightarrow> (\<forall>sl2 sl2'.  
    sl2 = [] \<and> sl2' = [] \<or>    
   (\<forall>sl1 sl1'.   
      counterpartS (hd sl2) sl2 (hd sl1) sl1 \<and> counterpartS (hd sl2') sl2' (hd sl1') sl1' \<and>     
      validS1 sl1 \<and> validS1 sl1' 
      \<longrightarrow>  
      \<not> tracesLeakS1 (hd sl1) sl1 (hd sl1') sl1')
   \<and> 
   validS2 sl2 \<and> validS2 sl2' 
   \<longrightarrow> 
   \<not> tracesLeakS2 (hd sl2) sl2 (hd sl2') sl2')"
unfolding tpod'_altS apply safe 
sorry
*)

lemma unsecure:
  assumes \<open>\<exists>sl1 sl1' sl2 sl2'. 
            istate1 (hd sl1) \<and> istate1 (hd sl1') \<and> istate2 (hd sl2) \<and> istate2 (hd sl2') \<and> 
            validS1 sl1 \<and> validS1 sl1' \<and> validS2 sl2 \<and> validS2 sl2' \<and>
            lowEquiv (hd sl2) (hd sl2') \<and> \<not> lowEquivTS2 (tl sl2) (tl sl2') \<and>
            lowOpTS1 sl1 = lowOpTS1 sl1' \<and> lowEquivTS2 sl1 sl1' \<and>
            lowOpTS2 sl2 = lowOpTS1 sl1 \<and> highOpTS2 sl2 = highOpTS1 sl1 \<and> counterpart_stutterS sl2 sl1 \<and>
            lowOpTS2 sl2' = lowOpTS1 sl1' \<and> highOpTS2 sl2' = highOpTS1 sl1' \<and> counterpart_stutterS sl2' sl1'\<close>
    shows \<open>\<not>tpod\<close>
  using assms unfolding tpod_altS
  apply (intro notI)
  apply (elim exE conjE)
  subgoal for sl1 sl1' sl2 sl2' 
    apply (erule allE[of _ \<open>hd sl2\<close>])
    apply (erule allE[of _ sl2])
    apply (erule allE[of _ \<open>hd sl2'\<close>])
    apply (erule allE[of _ sl2'])
    apply (erule allE[of _ \<open>hd sl1\<close>])
    apply (erule allE[of _ sl1])
    apply (erule allE[of _ \<open>hd sl1'\<close>])
    apply (erule allE[of _ sl1'])
    apply (elim impE, intro conjI)
    subgoal
      unfolding counterpartS_def apply (intro conjI)
      using Aug.lowOpTS_def Orig.lowOpTS_def list.sel(2) list_all2_lemmas.Nil list_all2_lemmas.intro lowEquivTS.f_list_all2_eq map_is_Nil_conv apply (metis)
      by blast+
    subgoal
      unfolding counterpartS_def apply (intro conjI)
      using Aug.lowOpTS_def Orig.lowOpTS_def list.sel(2) list_all2_Nil2 lowEquivTS.f_list_all2_eq map_is_Nil_conv apply (metis)
      by blast+
    apply blast+
    subgoal
      unfolding Orig.validFromS_def apply (rule disjI2)
      by blast+
    subgoal
      unfolding Orig.validFromS_def apply (rule disjI2)
      by blast+
    subgoal
      unfolding tracesOKS1_def apply (intro conjI)
      by blast+
    apply blast+
    subgoal
      unfolding Aug.validFromS_def apply (rule disjI2)
      by blast+
    subgoal
      unfolding Aug.validFromS_def apply (rule disjI2)
      by blast+
    subgoal
      unfolding Aug.tracesLeakS_def apply clarify
      apply (intro conjI)
      using Aug.lowOpTS_def Orig.lowOpTS_def list.sel(2) list_all2_Nil2 lowEquivTS.f_list_all2_eq map_is_Nil_conv apply (metis)
       apply fastforce
      using lowEquivTS.tl by blast
    .
  .

end (* context Simple_TPOD *)



end 