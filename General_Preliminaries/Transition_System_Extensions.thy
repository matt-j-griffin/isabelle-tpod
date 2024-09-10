theory Transition_System_Extensions
  imports Trivia_Extensions 
          Relative_Security.Transition_System
begin

\<comment> \<open>These are just abbreviations so will not impact proofs.\<close>

no_notation Trivia.Rcons (infix "##" 70)
no_notation Trivia.lmember ("(_/ \<in>\<in> _)" [50, 51] 50)
(*no_notation Trivia.LNil_abbr ("[[]]")*)

locale System_Model = 
  Simple_Transition_System istate validTrans   
    for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state  \<Rightarrow> bool"
+
  fixes final :: "'state \<Rightarrow> bool"
  assumes final_terminal: \<open>\<And>s1 s2. \<lbrakk>validTrans (s1,s2); final s1\<rbrakk> \<Longrightarrow> s2 = s1\<close>

context Simple_Transition_System
begin

(* todo *)
lemma list_step_all_lemmas_validS: \<open>list_step_all_lemmas validS (\<lambda>a b. validTrans (a, b))\<close>
  apply standard
  unfolding validS_def list_step_all_length by simp

interpretation validS: list_step_all_lemmas validS \<open>\<lambda>a b. validTrans (a, b)\<close>
  by (rule list_step_all_lemmas_validS) 

(* First inconsistency *)
(*
definition validFromS :: "'state \<Rightarrow> 'state list \<Rightarrow> bool" where
"validFromS s sl \<equiv> sl \<noteq> [] \<and> (hd sl = s \<and> validS sl)"

lemma validFromS[simp,intro!]: 
"validFromS s [s]"
unfolding validFromS_def by auto

lemma validFromS_empty[simp]: \<open>\<not>validFromS s []\<close>
  unfolding validFromS_def by auto

lemma validFromS_Cons_iff:
"validFromS s (s' # sl) \<longleftrightarrow> s = s' \<and> (sl = [] \<or> (validTrans (s,hd sl) \<and> validFromS (hd sl) sl))"
unfolding validFromS_def validS_def apply auto  
  apply (metis hd_conv_nth length_greater_0_conv nth_Cons_0) 
  apply (metis Suc_less_eq Suc_pred length_greater_0_conv nth_Cons_Suc)
  by (metis One_nat_def Suc_pred hd_conv_nth length_0_conv less_Suc_eq_0_disj not_less_eq nth_Cons')

lemma validFromS_Cons[intro]:
"validTrans (s,s') \<Longrightarrow> validFromS s' sl \<Longrightarrow> validFromS s (s # sl)"
by (cases "sl", auto simp: validFromS_Cons_iff)
*)
lemma validFromSE: 
  assumes major: \<open>validFromS s sl\<close> \<open>sl \<noteq> []\<close>
      and emptyE: \<open>sl = [] \<Longrightarrow> P\<close> 
      and ConsE: \<open>\<And>x xs. \<lbrakk>sl = (x # xs); x = s; validS (x # xs)\<rbrakk> \<Longrightarrow> P\<close> 
  shows P
  using major apply (cases sl)
  apply simp
  apply simp
  unfolding validFromS_def apply auto
  apply (erule ConsE)
  by simp_all

(* *)


(* Switching between traces and simple traces: *)

(* TODO not needed? *)
lemma list_all_fromS_list_step_all: 
    \<open>list_all (\<lambda>(x, y). P x y) (fromS xs) \<longleftrightarrow> list_step_all P xs\<close>
  by (simp add: fromS_def list_step_all_def)

lemma fromS_length_eqI: 
  assumes \<open>length xs = length ys\<close>
    shows \<open>length (fromS xs) = length (fromS ys)\<close>
  using assms by (simp add: length_fromS_less1)

lemma fromS_length_eqE: 
  assumes \<open>length xs > Suc 0 \<or> length ys > Suc 0\<close>
      and \<open>length (fromS xs) = length (fromS ys)\<close>
    shows \<open>length xs = length ys\<close>
  using assms unfolding length_fromS_less1 by (metis One_nat_def eq_diff_iff order_less_imp_le zero_less_diff)

lemma fromS_list_step_all2E:
  assumes \<open>list_step_all2 P xs ys\<close>
    shows \<open>list_all2 (\<lambda>(x, y) (z, w). P x z y w) (fromS xs) (fromS ys)\<close>
  using assms
  unfolding list_step_all2_length list_all2_conv_all_nth apply safe
  unfolding length_fromS_less1 apply (simp_all add: fromS_nth)
  by blast

lemma fromS_list_step_all2I:
  assumes \<open>length xs > Suc 0 \<or> length ys > Suc 0\<close>
      and \<open>list_all2 (\<lambda>(x, y) (z, w). P x z y w) (fromS xs) (fromS ys)\<close>
    shows \<open>list_step_all2 P xs ys\<close>
  using assms apply (drule_tac fromS_length_eqE)
  apply (drule list_all2_lengthD, blast)
  unfolding list_step_all2_length list_all2_conv_all_nth length_fromS_less1 apply safe
  by (simp_all add: fromS_nth)

(*

definition toS :: "('state \<times> 'state) list \<Rightarrow> 'state list" where 
"toS tr \<equiv> if tr = [] then [] else (fst (hd tr)) # map snd tr"

lemma toS_Nil[simp]: "toS [] = []"
unfolding toS_def by auto

lemma toS_eq_Nil[simp]: "toS tr = [] \<longleftrightarrow> tr = []"
unfolding toS_def by auto

lemma length_toS[simp]: 
"tr \<noteq> [] \<Longrightarrow> length (toS tr) = Suc (length tr)"
unfolding toS_def by auto

lemma length_toS_length:
  assumes \<open>length (toS tr) = length (toS tr')\<close>
    shows \<open>length tr = length tr'\<close>
  using assms by (metis add_left_cancel length_greater_0_conv length_toS plus_1_eq_Suc toS_eq_Nil)
  
lemma toS_nth_0: "tr \<noteq> [] \<Longrightarrow> toS tr ! 0 = fst (tr!0)"
unfolding toS_def by (simp add: hd_conv_nth)

lemma toS_nth_Suc: "i < length tr-1 \<Longrightarrow> toS tr ! (Suc i) = snd (tr!i)"
unfolding toS_def by auto 

lemma toS_last: "tr \<noteq> [] \<Longrightarrow> last (toS tr) = snd (last tr)"
unfolding toS_def by (simp add: last_map)

lemma toS_nth_valid: "valid tr \<Longrightarrow> i < length tr-1 \<Longrightarrow> toS tr ! i = fst (tr!i)"
unfolding toS_def by (simp add: hd_conv_nth nth_Cons' valid_nth)

lemma toS_length_gt_eq: \<open>length tr \<le> length (toS tr)\<close>
  by (cases \<open>tr = []\<close>, simp_all)

(* *)

lemma fromS_toS_valid[simp]: "valid tr \<Longrightarrow> fromS (toS tr) = tr"
apply(rule nth_equalityI)
  subgoal by (cases tr, auto)
  subgoal apply (cases tr)
    subgoal by simp
    subgoal 
    	by (smt (verit, best) fromS_nth length_fromS_notNil toS_eq_Nil 
       toS_last \<open>valid tr \<Longrightarrow> length (fromS (toS tr)) = length tr\<close> 
        diff_Suc_1 last_conv_nth le_eq_less_or_eq le_zero_eq length_Cons 
        less_Suc_eq_le not_less 
       prod.collapse toS_nth_0 toS_nth_Suc valid_nth zero_induct) . . 

lemma fromS_toS_validFrom[simp]: "validFrom s tr \<Longrightarrow> fromS (toS tr) = tr"
unfolding validFrom_def by auto
  
lemma toS_fromS_singl[simp]: "toS (fromS [s]) = []"
by simp
 
lemma toS_fromS_nonSingl[simp]: 
"length sl \<noteq> Suc 0 \<Longrightarrow> toS (fromS sl) = sl"
apply(rule nth_equalityI)  
  subgoal by (cases sl, auto)
  subgoal for i apply(cases "sl = []")
    subgoal by auto
    subgoal apply (cases i)
      subgoal by simp (metis toS_nth_0 fromS_eq_Nil fromS_nth fst_eqD 
           length_fromS_notNil length_greater_0_conv)
      subgoal for j apply simp 
      	by (metis (no_types, lifting) toS_def Suc_less_eq2 
        \<open>\<lbrakk>length sl \<noteq> Suc 0\<rbrakk> \<Longrightarrow> length (toS (fromS sl)) = length sl\<close> 
          diff_Suc_1 fromS_nth 
           length_fromS_notNil list.size(3) nth_Cons_Suc nth_map snd_conv) . . .


lemma list_step_all_toS: 
  \<open>valid xs \<Longrightarrow> list_step_all P (toS xs) \<longleftrightarrow> list_all (\<lambda>(x, y). P x y) xs\<close>
    by (metis fromS_toS_valid list_all_fromS_list_step_all)

(* Transfer: *)
lemma valid_fromS[simp]: 
"length sl > Suc 0 \<Longrightarrow> valid (fromS sl) \<longleftrightarrow> validS sl" 
unfolding valid_nth validS_def list_all_length  apply(cases sl)
  subgoal by auto
  subgoal for s ssl apply(cases ssl)
    subgoal by auto
    subgoal by (simp add: fromS_nth) . .

lemma validFrom_fromS_impI[intro]: 
"validFromS s sl \<Longrightarrow> validFrom s (fromS sl)"
  unfolding validFrom_def validFromS_def apply(cases sl)
  apply simp 
  by (metis fromS_eq_Nil hd_conv_nth length_greater_0_conv nat_less_le 
    not_less not_less_eq toS_fromS_nonSingl toS_nth_0 valid_fromS)

lemma validFrom_fromS[simp]: 
"length sl \<noteq> Suc 0 \<Longrightarrow> validFrom s (fromS sl) \<longleftrightarrow> validFromS s sl"
  apply (rule iffI)
  defer
  apply (rule validFrom_fromS_impI, assumption)
  by (metis Suc_lessI length_greater_0_conv toS_def toS_fromS_nonSingl validFromS_Cons_iff validFromS_def validFrom_def valid_fromS)

lemma validS_toS[simp]: 
"valid tr \<Longrightarrow> validS (toS tr)" 
by (metis fromS_eq_Nil fromS_toS_valid not_less valid_fromS valid_nth)

lemma validFromS_toS[simp]: 
"validFrom s tr \<Longrightarrow> validFromS s (toS tr)" 
by (metis validFrom_def list.sel(1) toS_def validFromS_def validS_toS)
*)


end (* context Simple_Transition_System *)

context System_Model
begin 

lemma validFromS_length_le_1: 
  assumes \<open>validFromS s sl\<close>
    shows \<open>length sl \<le> Suc 0 \<longleftrightarrow> sl = [] \<or> sl = [s]\<close>
using assms unfolding le_Suc_eq le_zero_eq length_0_conv apply (intro iffI)
  subgoal
    using validFromS_singl_iff
    by (metis Suc_length_conv length_0_conv)
  subgoal
    apply (elim disjE)
    unfolding Suc_length_conv le_Suc_eq
    by simp_all
  .
(*
lemma validFromS_all_final: 
  assumes \<open>validFromS s tr\<close> and \<open>final s\<close> shows \<open>list_all final tr\<close>
using assms proof (induct tr)
  case (Cons a tr4)
  show ?case 
    using Cons(2-)
    unfolding validFromS_Cons_iff list_all_simps apply (elim conjE)
    apply simp
    apply (elim disjE conjE)
    apply simp
    apply (rule Cons(1))
    using final_terminal by auto
qed auto
*)

lemma validFromS_alwaysE: (* might not be needed *)
  assumes \<open>final s\<close> and \<open>validFromS s tr\<close> and \<open>Q s\<close> and \<open>list_all Q tr \<Longrightarrow> P\<close>
      and \<open>tr \<noteq> []\<close>
    shows P
using assms unfolding validFromS_def 
proof auto
  assume "tr \<noteq> []"  "final (hd tr)" "Q (hd tr)" "list_all Q tr \<Longrightarrow> P" "validS tr" "s = hd tr"
    thus ?thesis
      apply (induct tr rule: list_nonempty_induct, auto)
      by (metis validFromS_Cons_iff validFromS_def final_terminal list.distinct(1))
  qed

end (*context System_Model *)


context Simple_Transition_System
begin

(*

lemma lfromS_llength_eqI: 
  assumes \<open>llength xs = llength ys\<close>
    shows \<open>llength (lfromS xs) = llength (lfromS ys)\<close>
  using assms by (simp add: llength_lfromS_less1)

lemma lfromS_llength_eqE: 
  assumes \<open>llength xs > Suc 0 \<or> llength ys > Suc 0\<close>
      and \<open>llength (lfromS xs) = llength (lfromS ys)\<close>
    shows \<open>llength xs = llength ys\<close>
  using assms unfolding llength_lfromS_less1  
  by (smt (verit) eSuc_minus_1 eSuc_minus_eSuc epred_0 epred_1 epred_minus_epred i0_less idiff_enat_0_right ldropn_Suc_conv_ldropn llength_LCons llength_ldropn llength_lfromS_less1 one_eSuc)


(* Switcing between finite and infinite validity: *)
lemma lfinite_lvalidFromS_validFromS: "lfinite tr \<Longrightarrow> lvalidFromS s tr \<longleftrightarrow> validFromS s (list_of tr)"
apply(induct arbitrary: s rule: lfinite.induct)
  apply auto 
  apply (metis hd_list_of list_of_LNil lvalidFromS_Cons_iff validFromS_Cons_iff validFromS_def)
  by (metis Simple_Transition_System.validFromS_Cons_iff hd_list_of llist_of.simps(1) llist_of_list_of lvalidFromS_Cons_iff)

lemma lvalidFromS_llist_of_validFromS: "lvalidFromS s (llist_of tr) \<longleftrightarrow> validFromS s tr"
by (simp add: lfinite_lvalidFromS_validFromS)

lemma validS_append: 
assumes tr1: "validS tr1" and tr12: "validTrans (last tr1, hd tr2)" 
and tr2: "validS tr2"
shows "validS (append tr1 tr2)" 
using list_step_all_lemmas.appendI list_step_all_lemmas_validS tr1 tr12 tr2 by blast

lemma lvalidS_lappend: 
assumes tr1: "lvalidS tr1" and tr12: "validTrans (llast tr1, lhd tr2)" 
and tr2: "lvalidS tr2"
shows "lvalidS (lappend tr1 tr2)" 
unfolding lvalidS_def proof safe
  fix i assume i: "enat i < llength (lappend tr1 tr2) - 1"
  show "validTrans (lnth (lappend tr1 tr2) i, lnth (lappend tr1 tr2) (Suc i))"
  proof(cases "Suc i < llength tr1")
    case True
    hence l: "lnth (lappend tr1 tr2) i = lnth tr1 i"
    and l': "lnth (lappend tr1 tr2) (Suc i) = lnth tr1 (Suc i)"
    using lnth_lappend1 by (metis Suc_ile_eq order_less_le)+
    show ?thesis unfolding l l' using tr1 True unfolding lvalidS_def  
      by (metis Suc_ile_eq diff_Suc_1 enat_llength_ldropn llength_ldropn one_enat_def)
  next
    case False note s = False
    show ?thesis proof(cases "i < llength tr1")
      case True
      have si: "Suc i = llength tr1" using s True 
        by (simp add: Suc_ile_eq order_less_le)
      hence l: "lnth (lappend tr1 tr2) i = llast tr1"
      and l': "lnth (lappend tr1 tr2) (Suc i) = lhd tr2"     
      apply (metis True eSuc_enat llast_conv_lnth lnth_lappend1)  
        by (metis diff_Suc_1 diff_self_eq_0 i idiff_enat_enat lappend_lnull2 lhd_conv_lnth 
       linorder_neq_iff lnth_lappend one_enat_def si the_enat.simps) 
      show ?thesis using tr12 unfolding l l'  .
    next
      case False  
      then obtain n1 where n1: "llength tr1 = enat n1"  
        by fastforce
      hence l: "lnth (lappend tr1 tr2) i = lnth tr2 (i - n1)"
      and l': "lnth (lappend tr1 tr2) (Suc i) = lnth tr2 (Suc (i - n1))" 
      apply (metis False lnth_lappend the_enat.simps) 
      by (metis False Suc_diff_le enat_ord_simps(2) linorder_le_less_linear lnth_lappend n1 s the_enat.simps)
      have nn1: "i - n1 < llength tr2 - 1" using i n1 apply simp 
      apply(cases "llength tr2", auto simp: algebra_simps) 
        by (metis False add_diff_cancel_right' diff_commute diff_diff_left enat_ord_simps(2) idiff_enat_enat 
       linordered_semidom_class.add_diff_inverse one_enat_def zero_less_diff) 
      show ?thesis using tr2 nn1 unfolding l l' unfolding lvalidS_def by auto
    qed
  qed
qed

lemma validS_append1: 
assumes "validS (append tr1 tr2)" "tr1 \<noteq> []"
shows "validS tr1"
using assms apply(induct tr1, auto)
by (metis Simple_Transition_System.validFromS_Cons_iff append_Cons neq_Nil_conv validFromS_def)

lemma lvalidS_lappend1: 
assumes "lvalidS (lappend tr1 tr2)"
shows "lvalidS tr1"
using assms unfolding lvalidS_def apply clarify subgoal for i apply simp
apply(erule allE[of _ i])
apply(subst (asm) lnth_lappend1)
  subgoal by (metis co.enat.exhaust dual_order.strict_trans1 eSuc_minus_1 enat_le_plus_same(1) idiff_0 plus_1_eSuc(2))
  subgoal apply(subst (asm) lnth_lappend1)
    subgoal by (metis \<open>enat i < llength tr1 - 1 \<Longrightarrow> enat i < llength tr1\<close> eSuc_enat eSuc_minus_1 ileI1 order_less_le)
    subgoal by (meson dual_order.strict_trans1 enat_le_plus_same(1) enat_minus_mono1) . . .

lemma validS_append2: 
assumes "validS (append tr1 tr2)" "tr2 \<noteq> []"
shows "validS tr2"
using assms apply(induct tr1, auto)
by (metis validFromS_def validS_Nil validFromS_Cons_iff)

lemma lvalidS_lappend2: 
assumes "lfinite tr1" "lvalidS (lappend tr1 tr2)"
shows "lvalidS tr2"
using assms unfolding lvalidS_def apply clarify subgoal for i apply simp
apply(cases "llength tr1")
  subgoal for n1 
  apply(erule allE[of _ "n1+i"])
  apply(subst (asm) lnth_lappend2[of _ n1])
    subgoal by simp
    subgoal by simp
    subgoal apply simp apply(subst (asm) lnth_lappend2[of _ n1])
      subgoal by simp
      subgoal by simp
      subgoal by simp (metis add_diff_assoc_enat enat_less_enat_plusI2 ldropn_eq_LNil 
       llength_LNil llength_ldropn nle_le not_less_zero one_enat_def) . .
  subgoal using llength_eq_infty_conv_lfinite by blast . . 

lemma validS_validTrans: 
assumes "tr1 \<noteq> []" "tr2 \<noteq> []" "validS (append tr1 tr2)"
shows "validTrans (last tr1, hd tr2)"
by (smt (verit, del_insts) Nil_is_append_conv append.assoc append.right_neutral 
  append_Cons append_Nil2 append_butlast_last_id append_eq_Cons_conv append_eq_append_conv2 
  assms list.collapse list.simps(3) list_step_all_lemmas.Cons2E list_step_all_lemmas_validS same_append_eq validS_append2)

lemma lvalidS_validTrans: 
assumes "tr1 \<noteq> [[]]" "tr2 \<noteq> [[]]" "lfinite tr1" "lvalidS (lappend tr1 tr2)"
shows "validTrans (llast tr1, lhd tr2)"
apply(cases "llength tr1")
  subgoal for n1 
  using assms unfolding lvalidS_def apply(elim allE[of _ "n1-1"])
  apply simp apply(subst (asm) lnth_lappend1)
    subgoal apply simp 
     by (metis diff_less llength_eq_0 lnull_def not_gr_zero zero_enat_def zero_less_Suc)
    subgoal apply(subst (asm) lnth_lappend2[of _ n1])
      subgoal by simp
      subgoal by simp
      subgoal 
        by (metis One_nat_def Suc_ile_eq Suc_pred add_diff_assoc_enat 
       cancel_comm_monoid_add_class.diff_cancel eSuc_enat enat_le_plus_same(1) 
      enat_ord_simps(2) i0_less lhd_conv_lnth llast_conv_lnth llength_eq_0 lnull_def one_enat_def zero_enat_def) . .
  subgoal using assms(3) llength_eq_infty_conv_lfinite by blast .

(* *)

lemma validS_reach: 
assumes "istate (hd tr)" "validS tr" 
shows "reach (last tr)"
by (metis (no_types, lifting) Istate fromS_eq_Nil hd_Nil_eq_last 
 hd_conv_nth assms last_conv_nth length_fromS_less1 linorder_not_less list.size(3) 
 nat_neq_iff toS_fromS_nonSingl toS_last toS_nth_0 valid_fromS valid_reach_src_tgt)

lemma validFromS_reach: 
assumes "istate s" "validFromS s tr" "tr \<noteq> []"
shows "reach (last tr)"
using assms unfolding validFromS_def using validS_reach by blast

lemma reach_validFromS_reach: 
assumes "reach s" "validFromS s tr" "tr \<noteq> []"
shows "reach (last tr)"
by (metis (no_types, lifting) Simple_Transition_System.validFromS_reach 
  Transition_System.reach_init_valid assms valid_reach_src_tgt)

lemma lvalidFromS_reach: 
assumes i: "istate s" and l: "lvalidFromS s tr" and s': "s' \<in> lset tr"
shows "reach s'"
proof-
  obtain tr1 tr2 where tr1: "lfinite tr1" "llast tr1 = s'" "tr1 \<noteq> [[]]" "tr = lappend tr1 tr2"
  using s'  
  by (metis LNil_eq_lappend_iff lappend_snocL1_conv_LCons2 lfinite_LConsI lfinite_lappend 
  llast_lappend_LCons llast_singleton llist.distinct(1) split_llist_first)

  hence "lvalidFromS s tr1" 
   by (metis LNil_eq_lappend_iff l lhd_lappend lnull_def lvalidFromS_def lvalidS_lappend1)
  hence "validFromS s (list_of tr1) \<and> last (list_of tr1) = s'" using tr1
  by (metis lfinite_lvalidFromS_validFromS llast_llist_of llist_of_list_of)
  thus ?thesis 
  by (metis i llist_of.simps(1) llist_of_list_of tr1(1) tr1(3) validFromS_reach)
qed

(* *)

lemma validFromS_append: 
"tr1 \<noteq> [] \<Longrightarrow> tr1' \<noteq> [] \<Longrightarrow> validFromS s1 tr1 \<Longrightarrow> validFromS (lastt s1 tr1) tr1' \<Longrightarrow> 
 validFromS s1 (butlast tr1 @ tr1')"
apply(cases "butlast tr1 = []")
  subgoal apply simp by(cases tr1, auto split: if_splits simp: lastt_def)
  subgoal unfolding validFromS_def apply(rule disjI2)
  apply(rule conjI)
    subgoal by (metis append_butlast_last_id hd_append2)
    subgoal apply(rule validS_append) apply auto  
      apply (metis validS_append1 append_butlast_last_id)  
      by (metis validS_validTrans append_butlast_last_id hd_Cons lastt_def list.distinct(1)) 
. . 


(* *)

lemma lprefix_lvalidS: "lvalidS tr \<Longrightarrow> lprefix tr' tr \<Longrightarrow> lvalidS tr'"
by (metis lvalidS_lappend1 lprefix_conv_lappend)

lemma lprefix_lvalidFromS: "lvalidFromS s tr \<Longrightarrow> lprefix tr' tr \<Longrightarrow> lvalidFromS s tr'"
by (metis lvalidFromS_def lhd_LCons llist.distinct(1) lprefix.cases lprefix_lvalidS)

lemma lprefix_lvalidFrom_validFrom: "lvalidFromS s tr \<Longrightarrow> lprefix (llist_of tr') tr \<Longrightarrow> validFromS s tr'"
using lprefix_lvalidFromS lvalidFromS_llist_of_validFromS by blast

lemma lsublist_lvalidS: "lvalidS tr \<Longrightarrow> lsublist tr' tr \<Longrightarrow> lvalidS tr'"
by (metis lvalidS_lappend1 lvalidS_lappend2 lsublist_def)

lemma lsublist_lvalidromS: "lvalidFromS s tr \<Longrightarrow> lsublist tr' tr \<Longrightarrow> tr' \<noteq> LNil \<Longrightarrow> lvalidFromS (lhd tr') tr'"
using lsublist_lvalidS lvalidFromS_def by auto

find_theorems valid append

thm valid_append[no_vars]

thm lvalid_LCons_iff[no_vars]

lemma lvalidS_LCons_iff: 
"lvalidS (s $ tr) = (validTrans (s,lhd tr) \<and> lvalidS tr \<or> tr = [[]])"
using lvalidFromS_Cons_iff lvalidFromS_def by auto

lemma lvalidS_lappend_finite: 
"tr \<noteq> [] \<Longrightarrow> tr1 \<noteq> [[]] \<Longrightarrow> 
 lvalidS (lappend (llist_of tr) tr1) = (validS tr \<and> lvalidS tr1 \<and> validTrans (last tr,lhd tr1))"
apply (induct tr)   
apply (simp_all add: lvalidS_LCons_iff)  
by (metis list_step_all_lemmas.ConsE list_step_all_lemmas.ConsI list_step_all_lemmas_validS)

lemma lvalidS_llist_of[simp]: "lvalidS (llist_of tr) \<longleftrightarrow> validS tr"
by (metis Simple_Transition_System.lvalidFromS_def Simple_Transition_System.lvalidFromS_llist_of_validFromS 
Simple_Transition_System.lvalidS_LNil Simple_Transition_System.validFromS_def Simple_Transition_System.validS_Nil)

lemma lvalidFromS_lappend_finite: 
"lvalidFromS s (lappend (llist_of tr) tr1) \<longleftrightarrow> 
 validFromS s tr \<and> 
 (tr1 = [[]] \<or> 
  lvalidFromS (lhd tr1) tr1 \<and>
  (tr = [] \<and> s = lhd tr1 \<or> (tr \<noteq> [] \<and> validTrans (last tr, lhd tr1))))"
apply(cases "tr \<noteq> [] \<and> tr1 \<noteq> [[]]")
  subgoal unfolding validFromS_def lvalidFromS_def lastt_def apply(subst lvalidS_lappend_finite) by auto
  subgoal apply simp apply(elim disjE)
    subgoal apply simp apply(cases "tr1 = [[]]", auto) 
      unfolding lvalidFromS_def by auto 
    subgoal unfolding lvalidFromS_def validFromS_def by auto . .

lemma lvalidFromS_lappend_finite': 
"tr1 \<noteq> [[]] \<Longrightarrow> 
 lvalidFromS s (lappend (llist_of tr) tr1) \<longleftrightarrow> 
 validFromS s tr \<and> 
 lvalidFromS (lhd tr1) tr1 \<and>
 (tr = [] \<and> s = lhd tr1 \<or> 
  tr \<noteq> [] \<and> validTrans (last tr, lhd tr1))"
unfolding lvalidFromS_lappend_finite by auto

lemma lvalidFromS_lappend_LCons: 
"lvalidFromS s (lappend (llist_of tr) (s' $ tr1)) \<longleftrightarrow> 
 validFromS s tr \<and> 
 lvalidFromS s' ((s' $ tr1)) \<and>
 (tr = [] \<and> s = s' \<or> 
  tr \<noteq> [] \<and> validTrans (last tr, s'))"
apply(subst lvalidFromS_lappend_finite') by auto

*)
end (*context Simple_Transition_System *)




context System_Model
begin


definition completedFrom :: "'state \<Rightarrow> 'state list \<Rightarrow> bool" where 
"completedFrom s sl \<equiv> (sl = [] \<and> final s) \<or> (sl \<noteq> [] \<and> final (last sl))"

lemma completed_Nil[simp,intro]: "completedFrom s [] \<longleftrightarrow> final s"
unfolding completedFrom_def by auto

lemma completed_Cons[simp]: "completedFrom s' (s # sl) \<longleftrightarrow> (sl = [] \<and> final s) \<or> (sl \<noteq> [] \<and> completedFrom s sl)"
unfolding completedFrom_def by auto

(*
lemma lcompletedFrom_singl: "llength tr = enat (Suc 0) \<Longrightarrow> 
    lvalidFromS s tr \<Longrightarrow> 
    lcompletedFrom s tr \<longleftrightarrow> tr = [[s]] \<and> final s"
apply(cases tr)
  subgoal by (simp add: enat_0_iff(1)) 
  subgoal for s' tr' unfolding lcompletedFrom_def  
  by simp (metis lvalidFromS_Cons_iff One_nat_def eSuc_inject 
   lfinite_LNil list_of_LNil llength_eq_0 lnull_def one_eSuc one_enat_def) .
*)

end (* context System_Model *)



end


