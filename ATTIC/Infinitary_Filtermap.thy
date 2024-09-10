theory Infinitary_Filtermap
  imports Bounded_Deducibility_Security.Filtermap
    Trivia_Extensions
begin

(*************************)
(* THE INFINITARY VERSION *)

definition lfiltermap ::
"('trans \<Rightarrow> bool) \<Rightarrow> ('trans \<Rightarrow> 'a) \<Rightarrow> 'trans llist \<Rightarrow> 'a llist"
where
"lfiltermap pred func tr = lmap func (lfilter pred tr)"

lemmas lfiltermap_lmap_lfilter = lfiltermap_def


lemma lfiltermap_lappend: "lfinite tr \<Longrightarrow> lfiltermap pred func (lappend tr tr1) = 
  lappend (lfiltermap pred func tr) (lfiltermap pred func tr1)"
unfolding lfiltermap_def by (simp add: lmap_lappend_distrib)


(* 
lemma lfiltermap_LNil_llist_ex: "lfiltermap pred func tr = [[]] \<longleftrightarrow> \<not> llist_ex pred tr"
proof(induction tr)
  case (LCons trn tr)
  thus ?case by (cases "pred trn") auto
qed auto
*)

lemma lfiltermap_LNil_never: "lfiltermap pred func tr = [[]] \<longleftrightarrow> lnever pred tr"
by (simp add: lfilter_empty_conv lfiltermap_lmap_lfilter llist.pred_set lmap_eq_LNil)

lemma llength_lfiltermap: "llength (lfiltermap pred func tr) \<le> llength tr"
by (simp add: lfiltermap_lmap_lfilter llength_lfilter_ile)

lemma lfiltermap_llist_all[simp]: "lfinite tr \<Longrightarrow> lfiltermap pred func tr = lmap func tr \<longleftrightarrow> llist_all pred tr"
apply (induction "list_of tr" arbitrary: tr)
  subgoal using llist_of_list_of apply auto 
    apply fastforce
    by (metis lfiltermap_LNil_never llist.pred_inject(1) llist.simps(12) llist_of.simps(1) llist_of_list_of) 
  subgoal for a x tr apply(cases tr, auto)  
    apply (metis iless_Suc_eq length_list_of lfilter_LCons lfiltermap_lmap_lfilter 
    lfinite_LConsI linorder_not_less llength_LCons llength_lfiltermap llength_lmap)
    apply (metis Suc_ile_eq eSuc_enat length_list_of lfilter_LCons lfiltermap_lmap_lfilter linorder_not_less 
      llength_LCons llength_lfiltermap llength_lmap llist.sel(3) ltl_lmap)
    by (simp add: lfiltermap_lmap_lfilter) .

(*
lemma lfiltermap_eq_LCons:
assumes "lfiltermap pred func tr = a $ al1"
shows "\<exists> trn tr2 tr1.
   tr = lappend tr2 (trn $ tr1) \<and> lnever pred tr2 \<and> pred trn \<and> func trn = a \<and> lfiltermap pred func tr1 = al1"
(* using assms proof(induction tr arbitrary: a al1)
  case (LCons trn tr a al1)
  show ?case
  proof(cases "pred trn")
    case False
    hence "lfiltermap pred func tr = a # al1" using LCons by simp
    from LCons(1)[OF this] obtain trnn tr2 tr1 where
    1: "tr = tr2 @ [trnn] @ tr1 \<and> never pred tr2 \<and> pred trnn \<and> func trnn = a \<and>
     lfiltermap pred func tr1 = al1" by blast
    show ?thesis apply(rule exI[of _ trnn], rule exI[of _ "trn # tr2"], rule exI[of _ tr1])
    using LCons(2) 1 False by simp
  next
    case True
    hence "lfiltermap pred func tr = al1" using LCons by simp
    show ?thesis apply(rule exI[of _ trn], rule exI[of _ "[]"], rule exI[of _ tr])
    using LCons(2) True by simp
  qed
qed auto
*)
oops
*)


lemma lfilter_LNil_lnever: "[[]] = lfilter pred xs \<Longrightarrow> lnever pred xs"
by (metis lfiltermap_LNil_never lfiltermap_lmap_lfilter llist.simps(12))

lemma lnever_LNil_lfilter: "lnever pred xs \<longleftrightarrow> [[]] = lfilter pred xs"
by (metis lfilter_empty_conv llist.pred_set)

lemma lfilter_LNil_lnever': "lfilter pred xs = [[]] \<Longrightarrow> lnever pred xs"
by (metis lfiltermap_LNil_never lfiltermap_lmap_lfilter llist.simps(12))

lemma lnever_LNil_lfilter': "lnever pred xs \<longleftrightarrow> lfilter pred xs = [[]]"
by (metis lfilter_empty_conv llist.pred_set)

lemma lfiltermap_LCons2_eq:
     "lfiltermap pred func [[x, x']] = lfiltermap pred func [[y, y']]
  \<Longrightarrow> lfiltermap pred func (x $ x' $ zs) = lfiltermap pred func (y $ y' $ zs)"
by (metis lappend_code(1) lappend_code(2) lfiltermap_lappend lfinite_LCons lfinite_LNil)

lemma lfiltermap_LCons_cong:
   "lfiltermap pred func xs = lfiltermap pred func ys
\<Longrightarrow> lfiltermap pred func (x $ xs) = lfiltermap pred func (x $ ys)"
by (simp add: lfiltermap_lmap_lfilter)

lemma lfiltermap_LCons_eq:
   "lfiltermap pred func xs = lfiltermap pred func ys
\<Longrightarrow> pred x \<longleftrightarrow> pred y
\<Longrightarrow> pred x \<longrightarrow> func x = func y
\<Longrightarrow> lfiltermap pred func (x $ xs) = lfiltermap pred func (y $ ys)"
by (simp add: lfiltermap_lmap_lfilter)

lemma set_lfiltermap:
"lset (lfiltermap pred func xs) \<subseteq> {func x | x . x \<in> lset xs \<and> pred x}"
unfolding lfiltermap_def by auto

(* *)

(* *)

lemma lfinite_lfiltermap_filtermap: 
"lfinite xs \<Longrightarrow> lfiltermap pred func xs = llist_of (filtermap pred func (list_of xs))" 
by (induct rule: lfinite.induct, auto simp: lfiltermap_lmap_lfilter) 

lemma lfiltermap_llist_of_filtermap: 
"lfiltermap pred func(llist_of xs) = llist_of (filtermap pred func xs)"
by (simp add: lfinite_lfiltermap_filtermap)

lemma filtermap_butlast: "xs \<noteq> [] \<Longrightarrow>
    \<not> pred (last xs) \<Longrightarrow>
    filtermap pred func xs = filtermap pred func (butlast xs)"
by (metis append_butlast_last_id not_holds_filtermap_RCons)

lemma filtermap_butlast': 
"xs \<noteq> [] \<Longrightarrow> pred (last xs) \<Longrightarrow> 
 filtermap pred func xs = filtermap pred func (butlast xs) @ [func (last xs)]"
by (metis append_butlast_last_id holds_filtermap_RCons)

lemma lfinite_lfiltermap_butlast: "xs \<noteq> [[]] \<Longrightarrow> (lfinite xs \<Longrightarrow> \<not> pred (llast xs)) \<Longrightarrow> 
lfiltermap pred func xs = lfiltermap pred func (lbutlast xs)"
unfolding lbutlast_def apply (auto simp: lfinite_lfiltermap_filtermap) 
by (metis butlast.simps(1) filtermap_butlast llast_llist_of llist_of_list_of)

(* *)

lemma last_filtermap: "xs \<noteq> [] \<Longrightarrow> pred (last xs) \<Longrightarrow> 
  filtermap pred func xs \<noteq> [] \<and> last (filtermap pred func xs) = func (last xs)"
by (metis holds_filtermap_RCons snoc_eq_iff_butlast)

(* *)

lemma filtermap_ltakeUntil[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> filtermap pred func (ltakeUntil pred xs) = [func (last (ltakeUntil pred xs))]"
unfolding filtermap_map_filter   
  by (smt (verit, del_insts) Cons_eq_map_conv append_butlast_last_id append_self_conv2 filter.simps(1) 
filter_eq_Cons_iff ltakeUntil_ex_butlast ltakeUntil_last ltakeUntil_not_Nil map_append)

lemma last_ltakeUntil_filtermap[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> func (last (ltakeUntil pred xs)) = lhd (lfiltermap pred func xs)"
unfolding lfiltermap_lmap_lfilter apply simp  
  by (metis (no_types, lifting) ldropWhile_cong lfinite_LConsI lfinite_LNil lfinite_lappend 
lfinite_ltakeWhile llast_lappend_LCons llast_llist_of llast_singleton llist_of_list_of ltakeUntil_def)

lemma lfiltermap_lmap_filtermap_lsplit:
assumes "lfiltermap pred func xs = lfiltermap pred func ys"
shows "lmap (filtermap pred func) (lsplit pred xs) = lmap (filtermap pred func) (lsplit pred ys)"
using assms apply(coinduction arbitrary: xs ys) apply auto
  subgoal by (simp add: LNil_eq_lmap lfilter_empty_conv lfiltermap_lmap_lfilter)
  subgoal by (metis lfiltermap_LNil_never llist.pred_set)
  subgoal by (smt (verit, ccfv_threshold) LCons_lfilter_ldropUntil lfiltermap_lmap_lfilter llist.set_sel(1) 
     lnull_lfilter lset_cases ltl_lmap ltl_simps(2)) .

lemma lfiltermap_lfinite_lsplit:
assumes "lfiltermap pred func xs = lfiltermap pred func ys"
shows "lfinite (lsplit pred xs) \<longleftrightarrow> lfinite (lsplit pred ys)" 
by (metis assms lfiltermap_lmap_filtermap_lsplit llength_eq_infty_conv_lfinite llength_lmap)

lemma lfiltermap_lsplitEnd[simp]: "lfiltermap pred func (lsplitEnd pred xs) = [[]]"
by (metis lfiltermap_LNil_never llist.pred_set lset_lsplitEnd)

lemma lfiltermap_lconcat_lsplit: 
"lfiltermap pred func xs = 
 lfiltermap pred func (lconcat (lmap llist_of (lsplit pred xs)))"
apply(subst lsplit_lsplitEnd[of xs pred])
apply(cases "lfinite (lconcat (lmap llist_of (lsplit pred xs)))")
  subgoal apply(subst lfiltermap_lappend) by auto
  subgoal apply(subst lappend_inf) by auto .

lemma lfilter_lconcat_lfinite': "(\<And>i. i < llength yss \<Longrightarrow> lfinite (lnth yss i)) 
\<Longrightarrow> lfilter pred (lconcat yss) = lconcat (lmap (lfilter pred) yss)" 
by (metis in_lset_conv_lnth lfilter_lconcat_lfinite)

lemma lfilter_lconcat_llist_of: 
"lfilter pred (lconcat (lmap llist_of yss)) = lconcat (lmap (lfilter pred) (lmap llist_of yss))" 
apply(rule lfilter_lconcat_lfinite) by auto

find_theorems lconcat lmap

lemma lfiltermap_lconcat_lmap_llist_of: 
"lfiltermap pred func (lconcat (lmap llist_of yss)) = 
 lconcat (lmap (llist_of o filtermap pred func) yss)" 
unfolding lfiltermap_def lfilter_lconcat_llist_of 
unfolding lmap_lconcat filtermap_map_filter apply simp  
by (smt (verit, best) in_lset_conv_lnth lfilter_llist_of 
 llength_lmap llist.map_comp llist.map_cong lmap_llist_of lnth_lmap)

find_theorems llength lsplit

lemma filtermap_noteq_imp_lsplit:
assumes len: "llength (lsplit pred xs) = llength (lsplit pred xs')"
and l: "lfiltermap pred func xs \<noteq> lfiltermap pred func xs'"
shows "\<exists>i0<llength (lsplit pred xs). 
   filtermap pred func (lnth (lsplit pred xs) i0) \<noteq> 
   filtermap pred func (lnth (lsplit pred xs') i0)"
proof-
  define yss where yss: "yss \<equiv> lsplit pred xs" 
  define yss' where yss': "yss' \<equiv> lsplit pred xs'" 
  define u where u: "u = lmap (llist_of o filtermap pred func) yss"
  define u' where u': "u' = lmap (llist_of o filtermap pred func) yss'"
  have "lfiltermap pred func (lconcat (lmap llist_of yss)) \<noteq> 
           lfiltermap pred func (lconcat (lmap llist_of yss'))" 
  using l[unfolded lfiltermap_lconcat_lsplit[of pred func xs]
                   lfiltermap_lconcat_lsplit[of pred func xs']]
  unfolding yss yss' .
  hence "lconcat u \<noteq> lconcat u'" 
  unfolding lfiltermap_lconcat_lmap_llist_of u u' .
  hence "u \<noteq> u'" by auto
  moreover have "llength u = llength u'"  
    by (simp add: u u' len yss yss')
  ultimately obtain i0 where 0: "i0 < llength u" "lnth u i0 \<noteq> lnth u' i0" 
  by (metis llist.rel_eq llist_all2_all_lnthI)

  show ?thesis unfolding yss[symmetric] yss'[symmetric] apply(rule exI[of _ i0])
  using 0 len unfolding u u'  
  by simp (metis lnth_lmap yss yss')
qed


(* SOME COINDUCTION INFRASTRUCTURE FOR REASONING ABOUT FILTERMAP *)

(* Multi-step coinduction for lazy-list equality: *)
 
proposition llist_lappend_coind: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lxs = lxs' \<or>  
   (\<exists>ys llxs llxs'. ys \<noteq> [] \<and> 
    lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys) llxs' \<and> 
    P llxs llxs')" 
shows "lxs = lxs'"
proof-
  have l1: "llength lxs \<le> llength lxs'"
  proof(cases "lfinite lxs'")
    case False thus ?thesis by (simp add: not_lfinite_llength)
  next
    case True
    then obtain xs' where lxs': "lxs' = llist_of xs'"
    by (metis llist_of_list_of)
    show ?thesis using P unfolding lxs' proof(induct xs' arbitrary: lxs rule: length_induct)
      case (1 xs' lxs)
      show ?case using lappend[OF 1(2)] apply(elim disjE exE conjE)
        subgoal by simp
        subgoal for ys llxs llxs' using 1(1)[rule_format, of "list_of llxs'" llxs] 
        by simp (metis length_append length_greater_0_conv less_add_same_cancel2 
        lfinite_lappend lfinite_llist_of list_of_lappend list_of_llist_of llength_llist_of llist_of_list_of) .
    qed
  qed
  (* *)
  have l2: "llength lxs' \<le> llength lxs"
  proof(cases "lfinite lxs")
    case False thus ?thesis by (simp add: not_lfinite_llength)
  next
    case True
    then obtain xs where lxs: "lxs = llist_of xs"
    by (metis llist_of_list_of)
    show ?thesis using P unfolding lxs proof(induct xs arbitrary: lxs' rule: length_induct)
      case (1 xs lxs')
      show ?case using lappend[OF 1(2)] apply(elim disjE exE conjE)
        subgoal by simp
        subgoal for ys llxs llxs' using 1(1)[rule_format, of "list_of llxs" llxs'] 
        by simp (metis length_append length_greater_0_conv less_add_same_cancel2 
        lfinite_lappend lfinite_llist_of list_of_lappend list_of_llist_of llength_llist_of llist_of_list_of) .
    qed
  qed
  from l1 l2 have l: "llength lxs = llength lxs'" by simp
  show ?thesis proof(rule llist_eq_lnth)
    show "llength lxs = llength lxs'" by fact
  next
    fix i assume i: "enat i < llength lxs"
    
    show "lnth lxs i = lnth lxs' i"  
    using P l i proof(induct i arbitrary: lxs lxs' rule: less_induct)
    case (less i lxs lxs')
    show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
      fix ys llxs llxs'
      assume ys: "ys \<noteq> []" and P: " P llxs llxs'"
      and lxs: "lxs = lappend (llist_of ys) llxs"
      and lxs': "lxs' = lappend (llist_of ys) llxs'" 
      
      show "lnth lxs i = lnth lxs' i"
      proof(cases "i < length ys")
        case True
        hence "lnth lxs i = ys ! i" "lnth lxs' i = ys ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
        thus ?thesis by simp
      next
        case False
        then obtain j where i: "i = length ys + j" 
        using le_Suc_ex not_le_imp_less by blast
        hence j: "j < llength lxs" "j < llength lxs'"  
        by (metis dual_order.strict_trans enat_ord_simps(2) 
           length_greater_0_conv less.prems(2,3) less_add_same_cancel2 ys)+
        hence 0: "lnth lxs i = lnth llxs j" "lnth lxs' i = lnth llxs' j" unfolding lxs lxs'  
        unfolding i   by (auto simp: lnth_lappend_llist_of)
        show ?thesis unfolding 0 apply(rule less(1)[rule_format, of j llxs llxs'])
          unfolding i apply auto
        using ys P lappend[OF less(2)] less.prems apply auto  
        apply (metis enat_add1_eq llength_lappend llength_llist_of lxs lxs') 
        apply (metis enat_add1_eq llength_lappend llength_llist_of lxs lxs')      
        by (metis enat_add_mono i llength_lappend llength_llist_of lxs plus_enat_simps(1))+
      qed
    qed auto
  qed
qed 
qed


(******************************************)
(* Characterisation of filtermap-equality *)

locale TwoFuncPred = 
fixes pred :: "'a \<Rightarrow> bool" and pred' :: "'a' \<Rightarrow> bool" 
and func :: "'a \<Rightarrow> 'b" and func' :: "'a' \<Rightarrow> 'b"
begin

lemma LCons_eq_lmap_lfilter: 
assumes "LCons b bss = lmap func (lfilter pred as)" 
shows "\<exists>as1 a ass. 
   as = lappend (llist_of as1) (LCons a ass) \<and> 
   never pred as1 \<and> pred a \<and> func a = b \<and> 
   bss = lmap func (lfilter pred ass)"
proof-
  obtain a ass' where 1: "lfilter pred as = LCons a ass'" "b = func a" "bss = lmap func ass'"
  using assms by (metis lmap_eq_LCons_conv)
  obtain us vs where 2: "as = lappend us (a $ vs)" "lfinite us"
  "\<forall>u\<in>lset us. \<not> pred u" "pred a" "ass' = lfilter pred vs"
  using lfilter_eq_LConsD[OF 1(1)] by auto
  show ?thesis apply(rule exI[of _ "list_of us"]) apply(rule exI[of _ a]) apply(rule exI[of _ "vs"]) 
  using 1 2 apply simp
  using lmember_equiv_list_all set_list_of by blast
qed

lemma LCons_eq_lmap_lfilter': 
assumes "LCons b bss = lmap func' (lfilter pred' as)" 
shows "\<exists>as1 a ass. 
   as = lappend (llist_of as1) (LCons a ass) \<and> 
   never pred' as1 \<and> pred' a \<and> func' a = b \<and> 
   bss = lmap func' (lfilter pred' ass)"
proof-
  obtain a ass' where 1: "lfilter pred' as = LCons a ass'" "b = func' a" "bss = lmap func' ass'"
  using assms by (metis lmap_eq_LCons_conv)
  obtain us vs where 2: "as = lappend us (a $ vs)" "lfinite us"
  "\<forall>u\<in>lset us. \<not> pred' u" "pred' a" "ass' = lfilter pred' vs"
  using lfilter_eq_LConsD[OF 1(1)] by auto
  show ?thesis apply(rule exI[of _ "list_of us"]) apply(rule exI[of _ a]) apply(rule exI[of _ "vs"]) 
  using 1 2 apply simp
  using lmember_equiv_list_all set_list_of by blast
qed

(*
context 
fixes W :: "'w rel"
assumes W: "wf W"
begin 

coinductive same :: "'w \<Rightarrow> 'a llist \<Rightarrow> 'a' llist \<Rightarrow> bool" where
Demote: 
"same v as as' \<Longrightarrow> (v,w) \<in> W \<Longrightarrow> same w as as'" 
| 
LNil: 
"same w [[]] [[]]"
|
Singl: 
"(pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') \<Longrightarrow> same w [[a]] [[a']]"
|
LConsBoth: 
"same w as as' \<Longrightarrow> (pred a \<longleftrightarrow> pred' a') \<Longrightarrow> (pred a \<longrightarrow> func a = func' a') 
 \<Longrightarrow> same v (a $ as) (a' $ as')"
|
LConsL: 
"same v as as' \<Longrightarrow> \<not> pred a \<Longrightarrow> as' = [[]] \<or> (v,w) \<in> W \<Longrightarrow> same w (a $ as) as'"
|
LConsR: 
"same v as as' \<Longrightarrow> \<not> pred' a' \<Longrightarrow> as = [[]] \<or> (v,w) \<in> W \<Longrightarrow> same w as (a' $ as')"

lemmas same_selectDemote = disjI1
lemmas same_selectLNil = disjI2[OF disjI1]
lemmas same_selectSingl = disjI2[OF disjI2[OF disjI1]]
lemmas same_selectLConsBoth = disjI2[OF disjI2[OF disjI2[OF disjI1]]]
lemmas same_selectLConsL = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI1]]]]
lemmas same_selectLConsR = disjI2[OF disjI2[OF disjI2[OF disjI2[OF disjI2]]]]


lemma same_LCons_holds: 
assumes "same v (LCons a ass) (LCons a' ass')" and "pred a" and "pred' a'"
shows "\<exists>w. func a = func' a' \<and> same w ass ass'"
using W assms proof(induct v rule: wf_induct_rule)
  case (less v)
  from `same v (a $ ass) (a' $ ass')` show ?case 
  apply cases using less apply auto  
    by (meson TwoFuncPred.LNil W)
qed

lemma same_lappend_not_hold1: 
assumes same: "same w (lappend (llist_of as1) (LCons a ass)) (LCons a' ass')" 
and n: "never pred as1" and p: "pred a" "pred' a'"
shows "\<exists>v. same v (LCons a ass) (LCons a' ass')" 
using W same n proof (induct w arbitrary: as1 rule: wf_induct_rule)
  case (less w)
  show ?case 
  apply(cases "as1 = []")
    subgoal using less(2-) by auto
    subgoal using less(2) apply-apply(erule same.cases)
      subgoal using less.hyps less.prems(2) by blast
      subgoal by auto
      subgoal using p(2) 
        by (metis lappend_simps(1) less.prems(2) lhd_LCons lhd_llist_of list_all_hd lnull_llist_of)
      subgoal for as as' aa aa'  
      using p less(2-) 
      by (metis lhd_LCons lhd_lappend lhd_llist_of list_all_hd lnull_llist_of) 
      subgoal for v as as' aa w' using less(1)[rule_format] using less(2-) p 
      apply(cases "as' = [[]]")
        subgoal using less(2-) p by force
        subgoal by (metis LConsBoth lappend_code(2) list.collapse list_all_simps(1) 
         llist.sel(3) llist_of.simps(2) order_less_imp_le same_LCons_holds) . 
      subgoal for w as aa using less(2-) p by force . .
qed

lemma same_lappend_not_hold2: 
assumes same: "same w (LCons a ass) (lappend (llist_of as1') (LCons a' ass'))" 
and n: "never pred' as1'" and p: "pred a" "pred' a'"
shows "\<exists>v. same v (LCons a ass) (LCons a' ass')" 
using W same n proof (induct w arbitrary: as1' rule: wf_induct_rule)
  case (less w)
  show ?case 
  apply(cases "as1' = []")
    subgoal using less(2-) by auto
    subgoal using less(2) apply-apply(erule same.cases)
      subgoal using less.hyps less.prems(2) by blast
      subgoal by auto
      subgoal using p(1)  
        by (metis lappend_simps(1) less.prems(2) lhd_LCons lhd_llist_of list_all_hd lnull_llist_of)
      subgoal for as as' aa aa'  
      using p less(2-) 
      by (metis lhd_LCons lhd_lappend lhd_llist_of list_all_hd lnull_llist_of) 
      subgoal using less(2-) p by blast
      subgoal for v as as' a'a w apply (cases "as' = [[]]")
        subgoal using less(2-) p apply simp 
        by (metis lappend_eq_LNil_iff lbutlast_lappend lbutlast_singl llist_of_eq_LNil_conv)
        subgoal using less(1)[rule_format] using less(2-) p apply simp 
        by (metis list.collapse list_all_simps(1) llist.distinct(1) llist.sel(3) 
         lnull_llist_of ltl_lappend ltl_llist_of) . . .
qed 

lemma same_lappend_not_hold: 
assumes same: "same w (lappend (llist_of as1) (LCons a ass)) (lappend (llist_of as1') (LCons a' ass'))" 
and n: "never pred as1" "never pred' as1'" and p: "pred a" "pred' a'"
shows "\<exists>v. same v (LCons a ass) (LCons a' ass')" 
using W same n proof(induct "length as1 + length as1'" w arbitrary: as1 as1' rule: less2_induct'')
  case (less w as1 as1')
  then show ?case  apply-apply(erule same.cases)
    subgoal for v as as' w by auto 
    subgoal using p by auto
    subgoal by (metis lappend_lnull1 less.prems(1) llist.disc(1) llist.discI(2) llist.sel(3) lnull_lappend ltl_lappend)
    subgoal for as as' aa a'a w' using less(2-) p apply(cases as1) 
      subgoal by (cases as1', auto)
      subgoal for a1 ass1 apply(cases as1')
        subgoal by auto
        subgoal for a1' ass1' 
        apply(rule less(1)[rule_format, of ass1 ass1' _, simplified]) by auto . . 
    subgoal for v as as' aa w' using less(2-) p apply(cases as1) 
      subgoal by auto
      subgoal for a1 ass1 apply(rule less(1)[rule_format, of ass1 as1' v, simplified]) by auto .
    subgoal for v as as' aa' w' using less(2-) p apply(cases as1') 
      subgoal by auto
      subgoal for a1' ass1' apply(rule less(1)[rule_format, of as1 ass1' v, simplified]) by auto . .
qed

lemma same_lappend_never_LCons: 
assumes same: "same w (lappend (llist_of as1) (LCons a ass)) (lappend (llist_of as1') (LCons a' ass'))" 
and n: "never pred as1" "never pred' as1'" and p: "pred a" "pred' a'"
shows "\<exists>w1. func a = func' a' \<and> same w1 ass ass'" 
using n(1) n(2) p(1) p(2) same same_LCons_holds same_lappend_not_hold by blast 

(* *)
         
lemma same_LCons_lset: 
assumes s: "same w (a $ as) as'" and p: "pred a"
shows "func a \<in> func' ` {a'. a' \<in> lset as' \<and> pred' a'}"
using W s proof(induct w arbitrary: as' rule: wf_induct_rule)
  case (less n)
  from `same n (a $ as) as'` 
  show ?case apply-apply(erule same.cases)
  using p unfolding image_def using "less.hyps" by auto    
qed

lemma same_LCons_lset2: 
assumes s: "same w' (a $ as) as'"
shows "\<exists>w'' as''. lset as'' \<subseteq> lset as' \<and> same w'' as as''"
using W s proof(induct w' arbitrary: as' rule: wf_induct_rule)
  case (less w)
  from `same w (a $ as) as'` 
  show ?case apply-apply(erule same.cases)
  unfolding image_def using "less.hyps"  
  apply simp_all 
  apply (metis lset_LNil same.LNil singleton_insert_inj_eq) by blast+  
qed
 
lemma lset_same_image: "a \<in> lset as \<Longrightarrow> same w as as' \<Longrightarrow> pred a \<Longrightarrow> 
   func a \<in> func' ` {a'. a' \<in> lset as' \<and> pred' a'}"
proof(induct arbitrary: w as' rule: lset_induct)
  case (find as w as') 
  then show ?case using same_LCons_lset by auto
next
  case (step a1 as w as')
  thus ?case using same_LCons_lset2 by force
qed  

lemma same_LCons_lset': 
assumes s: "same w as (a' $ as')" and p: "pred' a'"
shows "func' a' \<in> func ` {a. a \<in> lset as \<and> pred a}"
using W s proof(induct w arbitrary: as rule: wf_induct_rule)
  case (less w)
  from `same w as (a' $ as')` 
  show ?case apply-apply(erule same.cases)
  using p unfolding image_def using "less.hyps" by auto
qed

lemma same_LCons_lset2': 
assumes s: "same w' as (a' $ as')"
shows "\<exists>w'' as''. lset as'' \<subseteq> lset as \<and> same w'' as'' as'"
using W s proof(induct w' arbitrary: as rule: wf_induct_rule)
  case (less w)
  from `same w as (a' $ as')` 
  show ?case apply-apply(erule same.cases)
  unfolding image_def using "less.hyps" 
  apply simp_all 
  apply (metis lset_LNil same.LNil singleton_insert_inj_eq) by blast+   
qed
 
lemma lset_same_image': "a' \<in> lset as' \<Longrightarrow> same w as as' \<Longrightarrow> pred' a' \<Longrightarrow> 
   func' a' \<in> func ` {a. a \<in> lset as \<and> pred a}"
proof(induct arbitrary: w as rule: lset_induct)
  case (find as w as') 
  then show ?case using same_LCons_lset' by auto
next
  case (step a1 as w as')
  thus ?case using same_LCons_lset2' by force
qed   

lemma same_lnever_iff: "same w as as' \<Longrightarrow> lnever pred as \<longleftrightarrow> lnever pred' as'"
using lset_same_image[of _ as w as'] lset_same_image'[of _ as' w as]   
unfolding llist.pred_set image_def by auto

(* *)
theorem same_lmap_lfilter: 
assumes "same w as as'"
shows "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')"
proof-
  {fix bs bs'
   assume "\<exists>w as as'. bs = lmap func (lfilter pred as) \<and> 
                      bs' = lmap func' (lfilter pred' as') \<and> 
                      same w as as'"
   hence "bs = bs'"
   proof(coinduct rule: llist.coinduct)
     case (Eq_llist bs bs')
     then obtain w as as' where bs: "bs = lmap func (lfilter pred as)" 
     and bs': "bs' = lmap func' (lfilter pred' as')" 
     and same: "same w as as'" by auto
     show ?case proof(intro conjI impI)
       show ln: "lnull bs \<longleftrightarrow> lnull bs'" unfolding lnull_def bs bs'  find_theorems lmap LNil 
       apply simp unfolding lnever_LNil_lfilter'[symmetric] using same_lnever_iff[OF same] .
       assume nln: "\<not> lnull bs" "\<not> lnull bs'"
       then obtain b bss b' bss' where 
       bs0: "bs = LCons b bss" and bs0': "bs' = LCons b' bss'"
       by (metis lhd_LCons_ltl)
       obtain as1 a ass where as: "as = lappend (llist_of as1) (LCons a ass)" 
       and as1: "never pred as1" and a: "pred a" "func a = b"
       and bss: "bss = lmap func (lfilter pred ass)"
       using LCons_eq_lmap_lfilter[OF bs[unfolded bs0]] by auto 
       obtain as1' a' ass' where as': "as' = lappend (llist_of as1') (LCons a' ass')" 
       and as1': "never pred' as1'" and a': "pred' a'" "func' a' = b'"
       and bss': "bss' = lmap func' (lfilter pred' ass')" 
       using LCons_eq_lmap_lfilter'[OF bs'[unfolded bs0']] by auto 
        
       then obtain w1 where aa': "func a = func' a'" and sas: "same w1 ass ass'" 
       using same_lappend_never_LCons[OF same[unfolded as as'] as1 as1' a(1) a'(1)] 
       by auto
     
       show "lhd bs = lhd bs'"
       unfolding bs0 bs0' using a(2) a'(2) aa' by simp
 
       show "\<exists>w as as'. ltl bs = lmap func (lfilter pred as) \<and> 
                        ltl bs' = lmap func' (lfilter pred' as') \<and> local.same w as as'"
       apply(rule exI[of _ w1]) apply(rule exI[of _ ass]) apply(rule exI[of _ ass']) 
       unfolding bs0 bs0' apply(intro conjI)
         subgoal unfolding bss by simp 
         subgoal unfolding bss' by simp 
         subgoal using sas . .   
    qed    
   qed
  }
  thus ?thesis using assms by blast
qed

(* The converse is also true, butwe do not need it: 
lemma same_lmap_lfilter: 
assumes "lmap func (lfilter pred as) = lmap func (lfilter pred as')" 
and "need an invaiant about w: never the difference between 
the lengths of corresponding non-pred blocks in as and as' is > w"
shows "same w as as'"
using assms apply(coinduct rule: same.coinduct)
  apply auto

corollary
assumes "lmap func (lfilter pred as) = lmap func' (lfilter pred' as')" 
shows "same \<infinity> as as'"
*)

end (* context *)
*)

(*
We want the following to be a sufficient criterion for the filter-map equality 
of two lazy lists:

(C) "\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 

But the lazy-list multistep induction for equality would only give us a criterion (C')
*weaker* than the above, which replaces "ys \<noteq> [] \<and> ys' \<noteq> []" by the *stronger* assumption 
"map func (filter pred ys) \<noteq> []". 

As it turns out, we *can* obtain the above stronger criterion from the weaker one as follows:
-- we first prove (C) implies "lnever pred lxs = lnever pred' lxs'"
-- from this, we prove (C') by doing, in the case when "lnever pred lxs" holds, induction on 
"theN pred lxs", which gives the first index of lxs where pred holds. 

Now, by well-founded induction, we can prove the following refinement (Cwf) of (C): 

(Cwf) "\<And>w lxs lxs'. P w lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v llxs llxs') \<or> 
   (\<exists>v ys llxs ys' llxs'.        
       (v,w) \<in> W \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v llxs llxs')"   for W well-founded

So, compared to (C), (Cwf) adds to the predicate P parameter w form a well-founded set
and allows an alternative (third) disjoint where "ys \<noteq> [] \<and> ys' \<noteq> []" is replaced 
with that extra parameter decreasing ((v,w) \<in> W). (Cwf) can be preved from (C) by well-fouded induction. 

 
A variation of (Cwf) is also possible, which considers two well-founded relations

(Cwf2)
"\<And>w1 w2 lxs lxs'. P w1 w2 lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v1 v2 ys llxs ys' llxs'.        
       ((v1,w1) \<in> W1 \<or> ys \<noteq> []) \<and> ((v2,w2) \<in> W2 \<or> ys' \<noteq> []) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v1 v2 llxs llxs')"  for W1 W2 well-fouded relations. 

(Cwf) is slightly more insightful than (Cwf), as it allows the alternative wf-decrease 
to be componentwise. It can be reduced to (Cwf) by well-founded induction on one of the arguments. 


(Cwf) and (Cwf2) act as the mothers of all the "same" predicates used for infinitary 
relative security -- they immdiately yield their soundness for proving filtermap equality. 
In sssameL and sssameR cases, som ingenuity is required in order to phrase the trn,wfL,wfR 
situation as well-founded descent -- this is captured in the relation TWW. 
*)

lemma lmap_lfilter_lappend_lnever: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
shows "lnever pred lxs = lnever pred' lxs'"
proof safe
  assume ln: "lnever pred lxs"
  show "lnever pred' lxs'"
  unfolding llist_all_lnth using P ln apply (intro allI impI)
  subgoal for i proof(induct i arbitrary: lxs lxs' rule: less_induct)
    case (less i lxs lxs')
    show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
      fix ys llxs ys' llxs'
      assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
      and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'" 
      and P: "P llxs llxs'" 
      have lnys: "never pred ys" and lnllxs: "lnever pred llxs" using `lnever pred lxs` unfolding lxs 
        by (auto simp add: list_all_iff llist.pred_set) 
      hence lnys': "never pred' ys'" using yss'(2)  
        by (metis Nil_is_map_conv never_Nil_filter yss'(3))
      show "\<not> pred' (lnth lxs' i)" 
      proof(cases "i < length ys'")
        case True note i = True
        hence 0: "lnth lxs' i = ys' ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
        show ?thesis using lnys' i unfolding 0 list_all_nth by simp
      next
        case False note i = False
        then obtain j where i: "i = length ys' + j" 
        using le_Suc_ex not_le_imp_less by blast
        hence j: "j < llength llxs'" using `i < llength lxs'` unfolding lxs' 
        using enat_add_mono by fastforce 
        hence 0: "lnth lxs' i = lnth llxs' j" unfolding lxs lxs'  
        unfolding i  by (auto simp: lnth_lappend_llist_of)
        show ?thesis unfolding 0 apply(rule less(1)[rule_format, OF _ P])
        using j P yss' less.prems lnllxs unfolding i by auto 
      qed
    qed(metis less.prems(2) less.prems(3) llist_all_lnth lmap_eq_LNil lnever_LNil_lfilter')
  qed .
next
  assume ln': "lnever pred' lxs'"
  show "lnever pred lxs"
  unfolding llist_all_lnth using P ln' apply (intro allI impI)
  subgoal for i proof(induct i arbitrary: lxs lxs' rule: less_induct)
    case (less i lxs lxs')
    show ?case using lappend[OF less(2)] proof(elim disjE exE conjE)
      fix ys llxs ys' llxs'
      assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
      and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'" 
      and P: "P llxs llxs'" 
      have lnys': "never pred' ys'" and lnllxs: "lnever pred' llxs'" using `lnever pred' lxs'` unfolding lxs' 
        by (auto simp add: list_all_iff llist.pred_set) 
      hence lnys: "never pred ys" using yss'(2)  
        by (metis Nil_is_map_conv never_Nil_filter yss'(3))
      show "\<not> pred (lnth lxs i)" 
      proof(cases "i < length ys")
        case True note i = True
        hence 0: "lnth lxs i = ys ! i" unfolding lxs lxs'  
          by (auto simp: lnth_lappend_llist_of)
        show ?thesis using lnys i unfolding 0 list_all_nth by simp
      next
        case False note i = False
        then obtain j where i: "i = length ys + j" 
        using le_Suc_ex not_le_imp_less by blast
        hence j: "j < llength llxs" using `i < llength lxs` unfolding lxs
        using enat_add_mono by fastforce 
        hence 0: "lnth lxs i = lnth llxs j" unfolding lxs lxs'  
        unfolding i  by (auto simp: lnth_lappend_llist_of)
        show ?thesis unfolding 0 apply(rule less(1)[rule_format, OF _ P])
        using j P yss' less.prems lnllxs unfolding i by auto 
      qed
    qed(metis less.prems(2) less.prems(3) llist_all_lnth lmap_eq_LNil lnever_LNil_lfilter')
  qed .
qed

lemma lmap_lfilter_lappend_makeStronger: 
assumes lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
and P: "P lxs lxs'" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       map func (filter pred ys) \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')"
using P proof(induct "theN pred lxs" arbitrary: lxs lxs' rule: less_induct)
  case (less lxs lxs')
  show ?case using lappend[OF less(2)] proof(elim disjE allE conjE exE)
    fix ys llxs ys' llxs'
    assume yss': "ys \<noteq> []" "ys' \<noteq> []" "map func (filter pred ys) = map func' (filter pred' ys')"
    and lxs: "lxs = lappend (llist_of ys) llxs" and lxs': "lxs' = lappend (llist_of ys') llxs'"
    and P: "P llxs llxs'"
    show ?thesis
    proof(cases "lnever pred lxs")
      case True note ln = True
      hence ln': "lnever pred' lxs'" 
      using lappend less.prems lmap_lfilter_lappend_lnever by blast
      show ?thesis apply(rule disjI1)
      using ln ln' by (simp add: lnever_LNil_lfilter')
    next
      case False note ln = False
      hence ln': "\<not> lnever pred' lxs'" 
      using lappend less.prems lmap_lfilter_lappend_lnever by blast
      have "\<not> never pred ys \<or> (never pred ys \<and> \<not> lnever pred llxs)" using ln unfolding lxs
      unfolding llist_all_lappend_llist_of by simp
      thus ?thesis proof(elim disjE conjE)
        assume ys: "\<not> never pred ys"
        show ?thesis apply(rule disjI2)
        apply(rule exI[of _ ys]) apply(rule exI[of _ llxs]) apply(rule exI[of _ ys']) apply(rule exI[of _ llxs'])
        using yss' lxs lxs' P ys by (auto simp:  never_Nil_filter)
      next
        assume ys: "never pred ys" and llxs: "\<not> lnever pred llxs"
        hence ys': "never pred' ys'" and llxs': "\<not> lnever pred' llxs'"      
        apply (metis Nil_is_map_conv never_Nil_filter yss'(3)) 
        using P lappend llxs lmap_lfilter_lappend_lnever by blast

        have theN: "theN pred llxs < theN pred lxs"
        unfolding lxs theN_append[OF llxs ys] using yss' by simp 
      
        show ?thesis proof(cases "lmap func (lfilter pred llxs) = lmap func' (lfilter pred' llxs')")
          case True
          hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
          unfolding lxs lxs' using ys ys' 
          by (simp add: lmap_lappend_distrib yss'(3))
          thus ?thesis by simp
        next
          case False
          then obtain yys lllxs yys' lllxs' where yyss': "map func (filter pred yys) \<noteq> []" 
          "map func (filter pred yys) = map func' (filter pred' yys')"
          and llxs: "llxs = lappend (llist_of yys) lllxs" and llxs': "llxs' = lappend (llist_of yys') lllxs'" 
          and "P lllxs lllxs'" using less(1)[OF theN P] by blast
        
          show ?thesis apply(rule disjI2) 
          apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
          apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
          apply(intro conjI)
            subgoal using yyss'(1) by simp
            subgoal apply simp unfolding yss'(3) yyss'(2) ..
            subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
            subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
            subgoal by fact .   
        qed
      qed 
    qed
  qed simp
qed


lemma lmap_lfilter_lappend_coind: 
assumes P: "P lxs lxs'"
and lappend: 
"\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  have lappend: 
  "\<And>lxs lxs'. P lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>ys llxs ys' llxs'.               
       map func (filter pred ys) \<noteq> [] \<and> 
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P llxs llxs')" 
  using lmap_lfilter_lappend_makeStronger[OF lappend] by auto
  show ?thesis apply(rule llist_lappend_coind[where P = "\<lambda>as as'. 
    \<exists>lxs lxs'. as = lmap func (lfilter pred lxs) \<and> 
               as' = lmap func' (lfilter pred' lxs') \<and> 
               P lxs lxs'"])
    subgoal using P by auto
    subgoal for lxs lxs' using lappend  
    by (smt (verit, ccfv_SIG) lfilter_lappend_llist_of list.map_disc_iff lmap_lappend_distrib lmap_llist_of) .
qed 

proposition lmap_lfilter_lappend_coind_wf: 
assumes W: "wf W" and P: "P w lxs lxs'"
and lappend: 
"\<And>w lxs lxs'. P w lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v llxs llxs') \<or> 
   (\<exists>v ys llxs ys' llxs'.        
       (v,w) \<in> W \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  define Q where "Q \<equiv> \<lambda> llxs llxs'. \<exists>w. P w llxs llxs'"
  have Q: "Q lxs lxs'" using P unfolding Q_def by auto
  {fix lxs lxs' assume "Q lxs lxs'"
   then obtain w where "P w lxs lxs'" using Q_def by auto
   hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
     (\<exists>ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> ys' \<noteq> [] \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       Q llxs llxs')" 
   proof(induct w arbitrary: lxs lxs' rule: wf_induct_rule[OF W])
     case (1 w lxs lxs')
     show ?case using lappend[OF 1(2)] apply(elim disjE)
       subgoal by simp
       subgoal unfolding Q_def by blast
       subgoal proof(elim exE conjE)
         fix v ys llxs ys' llxs' assume vw: "(v, w) \<in> W"
         and yss': "map func (filter pred ys) = map func' (filter pred' ys')"
         and lxs: "lxs = lappend (llist_of ys) llxs"
         and lxs': "lxs' = lappend (llist_of ys') llxs'"
         and P: "P v llxs llxs'"
         show ?thesis
         proof(cases "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')")
           case True
           thus ?thesis by simp
         next
           case False
           hence "lmap func (lfilter pred llxs) \<noteq> lmap func' (lfilter pred' llxs')"
           using yss' unfolding lxs lxs' by (auto simp: lmap_lappend_distrib)
           then obtain yys lllxs yys' lllxs' where yyss': "yys \<noteq> []" "yys' \<noteq> []"
           "map func (filter pred yys) = map func' (filter pred' yys')"
           and llxs: "llxs = lappend (llist_of yys) lllxs"
           and llxs': "llxs' = lappend (llist_of yys') lllxs'"
           and "Q lllxs lllxs'"using 1(1)[OF vw P] by auto
           show ?thesis apply(rule disjI2)
           apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
           apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
           apply(intro conjI)
            subgoal using yyss'(1) by simp
            subgoal using yyss'(2) by simp
            subgoal apply simp unfolding yss' yyss' ..
            subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
            subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
            subgoal by fact . 
       qed 
     qed .
   qed 
  } note lappend = this
  show ?thesis apply(rule lmap_lfilter_lappend_coind[of Q, OF Q lappend]) by auto
qed

proposition lmap_lfilter_lappend_coind_wf2: 
assumes W1: "wf (W1::'a1 rel)" and W2: "wf (W2::'a2 rel)" 
and P: "P w1 w2 lxs lxs'"
and lappend: 
"\<And>w1 w2 lxs lxs'. P w1 w2 lxs lxs' \<Longrightarrow> 
   lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
   (\<exists>v1 v2 ys llxs ys' llxs'.        
       ((v1,w1) \<in> W1 \<or> ys \<noteq> []) \<and> ((v2,w2) \<in> W2 \<or> ys' \<noteq> []) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v1 v2 llxs llxs')" 
shows "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')"
proof-
  {fix w1 w2  lxs lxs' assume "P w1 w2 lxs lxs'" 
   hence "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs') \<or>  
     (\<exists>v1 v2 ys llxs ys' llxs'.        
       ys \<noteq> [] \<and> (ys' \<noteq> [] \<or> (v2,w2) \<in> trancl W2) \<and>  
       map func (filter pred ys) = map func' (filter pred' ys') \<and> 
       lxs = lappend (llist_of ys) llxs \<and> lxs' = lappend (llist_of ys') llxs' \<and> 
       P v1 v2 llxs llxs')" 
   proof(induct w1 arbitrary: w2 lxs lxs' rule: wf_induct_rule[OF W1])
     case (1 w1 w2 lxs lxs')
     show ?case using lappend[OF 1(2)] apply(elim disjE)
       subgoal by simp 
       subgoal proof(elim exE conjE)
         fix v1 v2 ys llxs ys' llxs' assume vw1: "(v1, w1) \<in> W1 \<or> ys \<noteq> []"
         and vw2: "(v2, w2) \<in> W2 \<or> ys' \<noteq> []"
         and yss': "map func (filter pred ys) = map func' (filter pred' ys')"
         and lxs: "lxs = lappend (llist_of ys) llxs"
         and lxs': "lxs' = lappend (llist_of ys') llxs'"
         and P: "P v1 v2 llxs llxs'"
         show ?thesis 
         proof(cases "ys \<noteq> []")
           case True
           thus ?thesis using vw2 yss' lxs lxs' P by blast
         next
           case False note ys = False         
           hence vw1: "(v1, w1) \<in> W1" using vw1 by auto
           show ?thesis
           proof(cases "lmap func (lfilter pred lxs) = lmap func' (lfilter pred' lxs')")
             case True
             thus ?thesis by simp
           next
             case False
             hence "lmap func (lfilter pred llxs) \<noteq> lmap func' (lfilter pred' llxs')"
             using yss' unfolding lxs lxs' by (auto simp: lmap_lappend_distrib)
             then obtain v1 vv2 yys lllxs yys' lllxs' where yyss': "yys \<noteq> []" "yys' \<noteq> [] \<or> (vv2,v2) \<in> trancl W2"
             "map func (filter pred yys) = map func' (filter pred' yys')"
             and llxs: "llxs = lappend (llist_of yys) lllxs"
             and llxs': "llxs' = lappend (llist_of yys') lllxs'"
             and "P v1 vv2 lllxs lllxs'"using 1(1)[OF vw1 P] by blast
             show ?thesis apply(rule disjI2)
             apply(rule exI[of _ v1]) apply(rule exI[of _ vv2])
             apply(rule exI[of _ "ys @ yys"]) apply(rule exI[of _ lllxs])
             apply(rule exI[of _ "ys' @ yys'"]) apply(rule exI[of _ lllxs'])
             apply(intro conjI)
               subgoal using yyss'(1) by simp
               subgoal using yyss'(2) vw2 by auto
               subgoal apply simp unfolding yss' yyss' ..
               subgoal unfolding lxs llxs lappend_assoc lappend_llist_of_llist_of[symmetric] ..
               subgoal unfolding lxs' llxs' lappend_assoc lappend_llist_of_llist_of[symmetric] .. 
               subgoal by fact . 
         qed 
       qed 
     qed . 
   qed
  } note lappend = this
  (* *)
  define Q where "Q \<equiv> \<lambda> w2 llxs llxs'. \<exists>w1. P w1 w2 llxs llxs'" 
  have W2p: "wf (W2\<^sup>+)"  
    using W2 wf_trancl by blast
  have Q: "Q w2 lxs lxs'" using P unfolding Q_def by auto
  show ?thesis apply(rule lmap_lfilter_lappend_coind_wf[OF W2p, of Q, OF Q])
  using lappend unfolding Q_def by meson
qed

end (* context TwoFuncPred *)


end
