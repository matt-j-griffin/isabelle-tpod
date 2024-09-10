theory Attic 
  imports Main
begin



(*

(*  THE CONCRETE FILTERMAP_CHARACTERISING PREDICATES 
(used in the relative security unwinding proof soundness)  *)


(*
context TwoFuncPred
begin

coinductive sssameL :: "turn \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"sssameL trn wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> sssameL trn wL wR [[a]] [[a']]"
|
lappend: 
"xs \<noteq> [] \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameL trn' vL vR as as'
 \<Longrightarrow> sssameL trn wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayL: 
"vL < wL \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameL L vL vR as as'
 \<Longrightarrow> sssameL L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayR: 
"vR < wR \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameL R vL vR as as'
 \<Longrightarrow> sssameL R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
RL: 
"map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameL L vL vR as as'
 \<Longrightarrow> sssameL R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"

thm sssameL.coinduct

lemmas sssameL_selectLNil = disjI1
lemmas sssameL_selectSingl = disjI2[OF disjI1]
lemmas sssameL_selectlappend = disjI2[OF disjI2[OF disjI1]]
lemmas sssameL_selectDelayL = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas sssameL_selectDelayR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas sssameL_selectRL = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]

(* *)
proposition sssameL_lmap_lfilter: 
assumes "sssameL trn wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  define P where "P \<equiv> \<lambda>(trn,wL,wR) as as'. sssameL trn wL wR as as'"
  show ?thesis 
  apply(rule lmap_lfilter_lappend_coind_wf[OF wf_TWW, of P "(trn,wL,wR)"])
    subgoal using assms unfolding P_def by simp
    subgoal for w lxs lxs' apply (cases w) subgoal for trn wL wR 
    unfolding P_def apply clarsimp apply (erule sssameL.cases)
    apply (auto simp: TWW_def less_turn_def)+ by blast . .
qed


(* *)

coinductive sssameR :: "turn \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"sssameR trn wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> sssameR trn wL wR [[a]] [[a']]"
|
lappend: 
"xs \<noteq> [] \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameR trn' vL vR as as'
 \<Longrightarrow> sssameR trn wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayL: 
"vL < wL \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameR L vL vR as as'
 \<Longrightarrow> sssameR L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
DelayR: 
"vR < wR \<Longrightarrow> map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameR R vL vR as as'
 \<Longrightarrow> sssameR R wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
LR: 
"map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 sssameR R vL vR as as'
 \<Longrightarrow> sssameR L wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"

thm sssameR.coinduct

lemmas sssameR_selectLNil = disjI1
lemmas sssameR_selectSingl = disjI2[OF disjI1]
lemmas sssameR_selectlappend = disjI2[OF disjI2[OF disjI1]]
lemmas sssameR_selectDelayL = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas sssameR_selectDelayR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas sssameR_selectLR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]

lemma switch: "switch trn = (if trn = L then R else L)"
by(cases trn, auto)

lemma sssameR_lmap_lfilter: 
assumes "sssameR trn wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  define P where "P \<equiv> \<lambda>(trn,wR,wL) as as'. sssameR (switch trn) wL wR as as'"
  show ?thesis 
  apply(rule lmap_lfilter_lappend_coind_wf[OF wf_TWW, of P "(switch trn,wR,wL)"])
    subgoal using assms unfolding P_def  apply(auto simp: switch)  
      using switch.cases by blast
    subgoal for w lxs lxs' apply (cases w) subgoal for trn wL wR 
    unfolding P_def apply clarsimp apply (erule sssameR.cases)
    apply (auto simp: TWW_def less_turn_def switch split: if_splits)+  
    apply (metis (full_types) turn.exhaust) apply (metis (full_types) turn.exhaust)
    apply (metis (full_types) switch.cases)+ .
    . .
qed

(* *)

coinductive ssssame :: "enat \<Rightarrow> enat \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
LNil: 
"ssssame wL wR [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> ssssame wL wR [[a]] [[a']]"
|
lappend: 
"(xs \<noteq> [] \<or> vL < wL) \<Longrightarrow> (xs' \<noteq> [] \<or> vR < wR) \<Longrightarrow> 
 map func (filter pred xs) = map func' (filter pred' xs') \<Longrightarrow> 
 ssssame vL vR as as'
 \<Longrightarrow> ssssame wL wR (lappend (llist_of xs) as) (lappend (llist_of xs') as')"
|
lmap_lfilter: 
"lmap func (lfilter pred as) = lmap func' (lfilter pred' as') \<Longrightarrow> 
 ssssame wL wR as as'"


thm ssssame.coinduct

lemmas ssssame_selectLNil = disjI1
lemmas ssssame_selectSingl = disjI2[OF disjI1]
lemmas ssssame_selectlappend = disjI2[OF disjI2[OF disjI1]] 
lemmas ssssame_selectlmap_lfilter = disjI2[OF disjI2[OF disjI2]] 

lemma ssssame_lmap_lfilter: 
assumes "ssssame wL wR as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  define P where "P \<equiv> \<lambda>(trn::turn,wL,wR) as as'. trn = L \<and> ssssame wL wR as as'"
  show ?thesis  
  apply(rule lmap_lfilter_lappend_coind_wf2[OF wf wf, of ssssame wL wR])
    subgoal using assms unfolding P_def by simp
    subgoal for wL wR lxs lxs'  
    unfolding P_def apply clarsimp apply (erule ssssame.cases)
    apply (auto simp: TWW_def less_turn_def) 
    by blast+  .
qed

end (* context TwoFuncPred *)
*)


(* Abstract filtermap locale, applicable to several operators: *)
(* TODO quite messy might need work *)
locale if_filtermap_def =
  fixes pred and func and def
  assumes if_filtermap_def: \<open>def tr = (if tr = [] then [] else filtermap pred func (butlast tr))\<close>
begin

lemma map_filter: "def tr =  (if tr = [] then [] else map func (filter pred (butlast tr)))" 
  unfolding if_filtermap_def filtermap_map_filter ..

lemma simps[simp]:
"def [] = []"  "\<not> pred s \<Longrightarrow> def (s # tr) = def tr"  
"pred s \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> def (s # tr) = func s # def tr"
"def [s] = []"
unfolding if_filtermap_def by auto

lemma imp_Nil: "def (s # tr) = [] \<Longrightarrow> def tr = []"
  by (metis simps list.distinct)

lemma iff_Nil[simp]: "def (s # tr) = [] \<longleftrightarrow> (\<not> pred s \<or> tr = []) \<and> def tr = []"
unfolding if_filtermap_def by (cases "pred s", auto)

lemma Nil_iff: "[] = def (s # tr) \<longleftrightarrow> (\<not> pred s \<or> tr = []) \<and> def tr = []"
unfolding if_filtermap_def by (cases "pred s", auto)

lemma Cons_unfold: "def (s # tr) = (if pred s then (if tr = [] then [] else func s # def tr) else def tr)"
  by auto


lemma doubleI: "(pred s \<Longrightarrow> X = [func s]) \<Longrightarrow> 
    (\<not>pred s \<Longrightarrow> X = []) \<Longrightarrow> X = def [s, s']"
  unfolding Cons_unfold
  by auto

lemma double_predI': "pred s \<Longrightarrow> X = [func s] \<Longrightarrow> def [s, s'] = X"
  unfolding Cons_unfold
  by auto

lemma double_predI: "pred s \<Longrightarrow> def [s, s'] = [func s]"
  by (rule double_predI'[rotated], blast)

lemma double_not_predI: "\<not>pred s \<Longrightarrow> def [s, s'] = []"
  unfolding Cons_unfold
  by auto

lemma Cons2I: "(pred s \<Longrightarrow> (func s # def (s' # tr)) = X) \<Longrightarrow> 
    (\<not>pred s \<Longrightarrow> def (s' # tr) = X) \<Longrightarrow> def (s # s' # tr) = X"
  unfolding Cons_unfold
  by auto

lemma Cons_pred2I: "pred s \<Longrightarrow> func s = x \<Longrightarrow> def (s' # tr) = xs \<Longrightarrow> def (s # s' # tr) = (x # xs)"
  by (rule Cons2I, simp_all)

lemma Cons_not_pred2I: "\<not>pred s \<Longrightarrow> def (s' # tr) = X \<Longrightarrow> def (s # s' # tr) = X"
  by (rule Cons2I, simp_all)


lemma Cons_single:
  assumes \<open>tr = []\<close>
    shows \<open>def (s # tr) = []\<close>
  unfolding iff_Nil apply (intro conjI)
  apply (intro disjI2)
  apply (rule assms)
  using assms by simp

lemma Cons'_single:
  assumes \<open>tr = []\<close>
    shows \<open>[] = def (s # tr)\<close>
  unfolding Nil_iff apply (intro conjI)
  apply (intro disjI2)
  apply (rule assms)
  using assms by simp

lemma Cons'_not_pred:
  assumes \<open>\<not>pred s\<close> and \<open>def tr = []\<close>
    shows \<open>[] = def (s # tr)\<close>
  unfolding Nil_iff apply (intro conjI)
  apply (intro disjI1)
  apply (rule assms(1))
  by (rule assms(2))

lemma Cons_not_pred:
  assumes \<open>\<not>pred s\<close> and \<open>def tr = []\<close>
    shows \<open>def (s # tr) = []\<close>
  unfolding iff_Nil apply (intro conjI)
  apply (intro disjI1)
  apply (rule assms(1))
  by (rule assms(2))

lemma length: "length (def tr) \<le> length tr" 
  unfolding if_filtermap_def apply (auto simp: length_filtermap)  
by (metis diff_le_self dual_order.trans length_butlast length_filtermap)

lemma iff_non_pred[simp]: "def (s # tr) = def tr \<longleftrightarrow> \<not> pred s \<or> tr = []"
apply(cases "pred s") 
by auto (metis Cons_unfold not_Cons_self)

lemma imp_pred: "def (s # tr) = sec # def tr \<Longrightarrow> pred s"
by (cases "pred s") auto

lemma length_Nil[simp]: "length tr \<le> Suc 0 \<Longrightarrow> def tr = []"
unfolding if_filtermap_def by (cases tr, auto)

lemma eq_empty_ConsE:
  assumes \<open>def (x # xs) = def (y # ys)\<close> and \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
    shows \<open>(pred y \<and> pred x \<longrightarrow> func x = func y \<and> def xs = def ys)
         \<and> (pred y \<and> \<not>pred x \<longrightarrow> def xs = (func y # def ys))
         \<and> (\<not>pred y \<and> pred x \<longrightarrow> (func x # def xs) = def ys)
         \<and> (\<not>pred y \<and> \<not>pred x \<longrightarrow> def xs = def ys)\<close>
  using assms unfolding Cons_unfold
  by (simp split: if_splits)

lemma eq_ConsE: 
  assumes \<open>def (x # xs) = def (y # ys)\<close>
      and \<open>pred x \<longleftrightarrow> pred y\<close>
    shows \<open>def xs = def ys \<and> ((pred x \<and> pred y \<and> ys \<noteq> [] \<and> xs \<noteq> []) \<longrightarrow> func x = func y)\<close>
  using assms unfolding Cons_unfold   
  by (auto split: if_splits)
  
lemma def_eq_NilE: 
  \<open>(def tr = []) = ((\<not> pred (hd tr) \<or> tl tr = []) \<and> def (tl tr) = [])\<close>
proof (induct tr)
  case (Cons a tr)
  then show ?case by fastforce
qed simp_all

lemma eq_ConsI: 
  assumes \<open>(xs = [] \<longleftrightarrow> ys = [])\<close>
      and \<open>\<lbrakk>pred x; xs \<noteq> []; pred y; ys \<noteq> []\<rbrakk> \<Longrightarrow> func x = func y\<close>
      and \<open>\<lbrakk>xs \<noteq> []; ys \<noteq> []\<rbrakk> \<Longrightarrow> def xs = def ys\<close>
      and \<open>pred x \<longleftrightarrow> pred y\<close>
    shows \<open>def (x # xs) = def (y # ys)\<close>
  using assms(1,2,4) unfolding Cons_unfold if_splits apply auto
  using assms(3) by blast+

lemma eq_Cons2I: 
  assumes both: \<open>\<lbrakk>pred x; pred y\<rbrakk> \<Longrightarrow> func y = func x \<and> def (y' # ys) = def (x' # xs)\<close>
      and left: \<open>\<lbrakk>pred x; \<not>pred y\<rbrakk> \<Longrightarrow> def (y' # ys) = func x # def (x' # xs)\<close>
      and right: \<open>\<lbrakk>\<not>pred x; pred y\<rbrakk> \<Longrightarrow> func y # def (y' # ys) = def (x' # xs)\<close>
      and neither: \<open>\<lbrakk>\<not>pred x; \<not>pred y\<rbrakk> \<Longrightarrow> def (y' # ys) = def (x' # xs)\<close>
    shows \<open>def (x # x' # xs) = def (y # y' # ys)\<close>
  apply (intro Cons2I Cons2I[symmetric])
  unfolding list.simps using assms by blast+

lemma eq_both_Cons2I: 
  assumes \<open>pred x\<close> \<open>pred y\<close> and \<open>func y = func x\<close> and \<open>def (y' # ys) = def (x' # xs)\<close>
    shows \<open>def (x # x' # xs) = def (y # y' # ys)\<close>
  apply (intro eq_Cons2I)
  using assms by blast+

lemma eq_left_Cons2I: 
  assumes \<open>pred x\<close> \<open>\<not>pred y\<close> and \<open>def (y' # ys) = func x # def (x' # xs)\<close>
    shows \<open>def (x # x' # xs) = def (y # y' # ys)\<close>
  apply (intro eq_Cons2I)
  using assms by blast+

lemma eq_right_Cons2I: 
  assumes \<open>\<not>pred x\<close> \<open>pred y\<close> and \<open>func y # def (y' # ys) = def (x' # xs)\<close>
    shows \<open>def (x # x' # xs) = def (y # y' # ys)\<close>
  apply (intro eq_Cons2I)
  using assms by blast+

lemma eq_neither_Cons2I: 
  assumes \<open>\<not>pred x\<close> \<open>\<not>pred y\<close> and \<open>def (y' # ys) = def (x' # xs)\<close>
    shows \<open>def (x # x' # xs) = def (y # y' # ys)\<close>
  apply (intro eq_Cons2I)
  using assms by blast+


lemma eq_singleI: 
  assumes \<open>pred x \<longleftrightarrow> pred y\<close>
    shows \<open>def [x] = def [y]\<close>
  using assms apply (rule eq_ConsI[rotated,rotated,rotated])
  by simp_all

lemma neq_nextI:
  assumes \<open>def xs \<noteq> def ys\<close>
      and \<open>pred x \<longleftrightarrow> pred y\<close>
    shows \<open>def (x # xs) \<noteq> def (y # ys)\<close>
  using assms unfolding Cons_unfold if_splits by auto

lemma neq_leftI:
  assumes \<open>def xs \<noteq> def ys\<close>
      and \<open>\<not>pred x\<close>
    shows \<open>def (x # xs) \<noteq> def ys\<close>
  using assms unfolding Cons_unfold if_splits by auto

lemma neq_rightI:
  assumes \<open>def xs \<noteq> def ys\<close>
      and \<open>\<not>pred y\<close>
    shows \<open>def xs \<noteq> def (y # ys)\<close>
  using assms unfolding Cons_unfold if_splits by auto

lemma neq_firstI:
  assumes \<open>pred x\<close> and \<open>pred y\<close> and \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
      and \<open>func x \<noteq> func y\<close>
    shows \<open>def (x # xs) \<noteq> def (y # ys)\<close>
  using assms unfolding Cons_unfold if_splits by auto

lemma single[simp]: \<open>def [x] = def [y]\<close>
  by simp

lemma func_2: 
  assumes \<open>\<lbrakk>pred x \<and> pred y\<rbrakk> \<Longrightarrow> func x = func y\<close>
      and \<open>pred x \<longleftrightarrow> pred y\<close>
    shows \<open>def [x, x'] = def [y, y']\<close>
proof (rule eq_ConsI)
  show \<open>def [x'] = def [y']\<close>
    using single by assumption
  show \<open>([x'] = []) = ([y'] = [])\<close>
    by simp
  show \<open>pred x \<Longrightarrow>
    [x'] \<noteq> [] \<Longrightarrow> pred y \<Longrightarrow> [y'] \<noteq> [] \<Longrightarrow> func x = func y\<close>
    using assms(1) by simp
  show \<open>pred x \<longleftrightarrow> pred y\<close>
    using assms(2) by assumption
qed

lemma def2: "def xs = map func (filter pred (butlast xs))"
unfolding if_filtermap_def by (induct xs, auto)

lemma eq_Nil_iff:
  "def tr = [] \<longleftrightarrow> never pred (butlast tr)"
  "[] = def tr \<longleftrightarrow> never pred (butlast tr)"
by (metis def2 filtermap_Nil_never filtermap_map_filter) +

lemma eq_Cons: 
assumes 1: "def tr = Cons obs obsl'"
shows "\<exists>tr1 s tr'. tr = append tr1 (Cons s tr') \<and> never pred tr1 \<and> 
   pred s \<and> func s = obs \<and> def tr' = obsl'"
proof-
  have "tr \<noteq> []" using 1 by auto
  note 1 = this 1 
  have "\<not> never pred (butlast tr)"  
    by (metis eq_Nil_iff 1(2) list.distinct(1))   

  then obtain ii where ii: "ii < length (butlast tr) \<and> pred (nth (butlast tr) ii)"  
  unfolding list_all_nth by auto
  define i where "i = (LEAST ii. ii < length (butlast tr) \<and> pred (nth (butlast tr) ii))"
  have i: "i < length (butlast tr)" "pred (nth (butlast tr) i)"
  and min_i: "\<And>j. j < i \<Longrightarrow> \<not> pred (nth (butlast tr) j)"
  unfolding i_def  
  by (smt (verit, ccfv_SIG) LeastI_ex dual_order.strict_trans enat_ord_simps(2) ii not_less_Least)+
  hence isInt: "pred (nth tr i)" by (simp add: nth_butlast)

  have [simp]: "\<not> length tr \<le> Suc i" 
      using i(1) by auto

  show ?thesis 
  apply(rule exI[of _ "take i tr"]) 
  apply(rule exI[of _ "nth tr i"])
  apply(rule exI[of _ "drop (Suc i) tr"])
  proof(intro conjI)  
    show 2: "tr = take i tr @ tr ! i # drop (Suc i) tr" 
    apply(rule sym) apply(rule append_take_nth_drop)
    using i(1) by auto
    have "butlast tr = take i tr @ (butlast (tr ! i # drop (Suc i) tr))" 
    by (metis "2" butlast_append list.distinct(1))
    hence 22: "butlast tr = take i tr @ (tr ! i # butlast (drop (Suc i) tr))" by simp

    show 3: "never pred (take i tr)" 
     unfolding list_all_nth apply simp 
     by (metis i(1) min_i nth_butlast order_less_trans) 
    have 33: "map func (filter pred (take i tr)) = []" apply simp 
      by (metis "3" never_Nil_filter)
   
    show 4: "pred (nth tr i)" by fact
    show "func (nth tr i) = obs" 
    using 1 4 unfolding def2 unfolding 22 apply simp unfolding 33 by simp
    show "def (drop (Suc i) tr) = obsl'" 
    using 1 4 unfolding def2 unfolding 22 apply simp unfolding 33 by simp
  qed
qed

end (* context if_filtermap_def *)
*)


end
