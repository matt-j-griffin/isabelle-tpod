
(* TODO TPOD Trivia *)
theory Trivia_Extensions
  imports 
    "Bounded_Deducibility_Security.Trivia"
    More_LazyLists.List_Filtermap
    (*"Relative_Security.RS_Trivia" *)
(*    "Coinductive.Coinductive_List"*)
    "HOL-ex.Sketch_and_Explore" (* TODO *)
begin

no_notation Trivia.Rcons (infix "##" 70)
(*no_notation Trivia.LNil_abbr ("[[]]")*)


lemma length_filtermap_eq: \<open>length (filtermap pred func1 xs) = length (filtermap pred func2 xs)\<close>
proof (induct xs)
  fix a xs
  assume IH: "length (filtermap pred func1 xs) = length (filtermap pred func2 xs)"
    thus "length (filtermap pred func1 (a # xs)) = length (filtermap pred func2 (a # xs))"
    by (cases \<open>pred a\<close>, simp_all)
qed simp


(* TODO check a lot of this for unused/duplicate theorems *)

lemma All_commute2: "(\<forall>x y a b. P x y a b) = (\<forall>a b x y. P x y a b)"
by auto

lemma True_not_False: \<open>True = (\<not> False)\<close>
  by simp

lemma all_ex_P:
  assumes "\<forall>s. P s" "\<And>s. P s = Q s" shows "\<exists>s. Q s"
  using assms by auto
(*
instantiation option :: (type) bot
begin

definition
  bot_option :: \<open>'a option\<close>
where
  \<open>\<bottom> \<equiv> None\<close>

instance ..

end

lemma Some_bot_simps[simp]: \<open>Some x \<noteq> \<bottom>\<close> \<open>\<bottom> \<noteq> Some y\<close>
  unfolding bot_option_def by simp_all
*)
lemma ball_inE:
  assumes major: "\<forall>x\<in>S. P x" and "x\<in>S"
      and minor: "P x \<Longrightarrow> R"
    shows R
  using assms by blast

lemma map_neq_updI: \<open>x \<noteq> y \<Longrightarrow> P (m y) \<Longrightarrow> P ((m(x \<mapsto> v)) y)\<close>
  by simp

lemmas map_neq_upd_the_valI = map_neq_updI[rotated, where P=\<open>\<lambda>m. the m = _\<close>]

lemma map_upd_current: \<open>(m(k \<mapsto> v)) k = Some v\<close>
  by simp

lemma map_upd_next: \<open>m k\<^sub>2 = Some v \<Longrightarrow> k\<^sub>1 \<noteq> k\<^sub>2 \<Longrightarrow> (m(k\<^sub>1 \<mapsto> v)) k\<^sub>2 = Some v\<close>
  by simp

lemma map_upd_k_neq_eqI:
  assumes \<open>m\<^sub>1 k\<^sub>2 = m\<^sub>2 k\<^sub>2\<close> and \<open>k\<^sub>1 \<noteq> k\<^sub>2\<close>
    shows \<open>(m\<^sub>1(k\<^sub>1 \<mapsto> v\<^sub>1)) k\<^sub>2 = (m\<^sub>2(k\<^sub>1 \<mapsto> v\<^sub>2)) k\<^sub>2\<close>
  using assms by auto

lemma not_insertI:
  assumes \<open>a \<notin> C\<close> and \<open>a \<noteq> b\<close> 
    shows \<open>a \<notin> insert b C\<close>
  using assms by auto

lemma not_in_emptyI[simp]: \<open>a \<notin> {}\<close>
  by auto

lemma last_Cons2: \<open>last (y # (x # xs)) = last (x # xs)\<close>
  by simp

lemma last_single: \<open>last [x] = x\<close>
  by simp

lemma the_key1: \<open>the ([x \<mapsto> y] x) = y\<close>
  by simp

lemma the_key2_1: \<open>x \<noteq> z \<Longrightarrow> the ([x \<mapsto> y, z \<mapsto> w] x) = y\<close>
  by simp

lemma the_key2_2: \<open>the ([x \<mapsto> y, z \<mapsto> w] z) = w\<close>
  by simp

(* lemmas the_key2 = the_key2_1 the_key2_2 *)


lemma fst_comp_pair: \<open>(fst \<circ> (\<lambda>s. (P s, Q s))) = P\<close>
  by auto

lemma snd_comp_pair: \<open>(snd \<circ> (\<lambda>s. (P s, Q s))) = Q\<close>
  by auto

lemma comp_snd_fun: "(snd \<circ> (\<lambda>x. (P x, Q x))) x = Q x"
  by simp

lemma map_upd_k_eq_eqI: \<open>(m\<^sub>1(k \<mapsto> v)) k = (m\<^sub>2(k \<mapsto> v)) k\<close>
  by auto

lemma [simp]: \<open>\<exists>x::nat. x < 8\<close>
  by (rule exI[of _ 1], auto)

lemma insert_inE: assumes \<open>x \<in> insert y Y\<close> shows \<open>x \<in> Y \<or> x = y\<close>
  using assms by auto

lemma upds_eqI[intro]:
  assumes \<open>m x = m' x\<close>
    shows \<open>(m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals)) x\<close>
proof -
  show \<open>(m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals)) x\<close>
    using assms apply -
    unfolding map_upds_def apply (cases \<open>x \<in> dom (map_of (rev (zip addrs vals)))\<close>)
    unfolding map_add_dom_app_simps(1) map_add_dom_app_simps(3) by blast+ 
qed

lemma upds_all_eqI:
  assumes \<open>\<forall>x\<in>A. m x = m' x\<close> and \<open>x \<in> A\<close>
    shows \<open>(m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals)) x\<close>
proof (rule upds_eqI)
  show \<open>m x = m' x\<close>
    using assms by (rule ball_inE[of A _ x])
qed

lemma upds_all_eqI':
  assumes \<open>\<forall>x\<in>A. m x = m' x\<close> and \<open>x \<in> A\<close> and \<open>vals = vals'\<close>
    shows \<open>(m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals')) x\<close>
  by (subst assms(3), use assms(1,2) in \<open>rule upds_all_eqI[of A]\<close>)


lemma allI_upds:
  assumes \<open>\<forall>x\<in>A. m x = m' x\<close> and \<open>vals = vals'\<close>
    shows \<open>\<forall>x\<in>A. (m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals')) x\<close>
proof (intro ballI)
  fix x assume inA: \<open>x \<in> A\<close> show \<open>(m(addrs [\<mapsto>] vals)) x = (m'(addrs [\<mapsto>] vals')) x\<close>
    using assms(1) inA assms(2) by (rule upds_all_eqI')
qed



lemma nested_imageI:
  assumes \<open>x \<in> f ` A\<close>
    shows \<open>g x \<in> (\<lambda>a. g (f a)) ` A\<close>
  using assms by blast

lemma less2_induct[case_names less]: 
assumes "(\<And>(x::nat) (a::nat). (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. b < a \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::nat,b::nat),(x,a)) . y < x \<or> y = x \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . x < y}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed

(*
lemma less2_induct'[case_names less]: 
assumes "(\<And>(x::nat) (a::enat). (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. b < a \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::nat,b::enat),(x,a)) . y < x \<or> y = x \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . x < y}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed
*)

lemma less2_induct'[case_names less]: 
assumes "(\<And>(x::'a::wellorder) (a::'w::wellorder). (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. b < a \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::'a::wellorder,b::'w::wellorder),(x,a)) . y < x \<or> y = x \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . x < y}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed


lemma less2_induct''[consumes 1, case_names less]: 
assumes W: "wf (W::'w rel)" and 
"(\<And>(x::'a::wellorder) a. (\<And>y b. y < x \<Longrightarrow> P y b) \<Longrightarrow> (\<And>b. (b,a) \<in> W \<Longrightarrow> P x b) \<Longrightarrow> P x a)"
shows "P x a"
proof-
  define R where "R = {((y::'a::wellorder,b::'w),(x,a)) . y < x \<or> y = x \<and> (b,a) \<in> W}"
  have 0: "R = lex_prod {(x,y) . x < y} {(x,y) . (x,y) \<in> W}"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 using W by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,a). P x a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by auto
  }
  thus ?thesis unfolding Q_def by auto
qed

lemma less3_induct[case_names less]: 
assumes "(\<And>(x::'a::wellorder) (x'::'a'::wellorder) (a::'w::wellorder). 
   (\<And>y y' b. y < x \<Longrightarrow> P y y' b) \<Longrightarrow> 
   (\<And>y' b. y' < x' \<Longrightarrow> P x y' b) \<Longrightarrow> 
   (\<And>b. b < a \<Longrightarrow> P x x' b) \<Longrightarrow> 
   P x x' a)"
shows "P x x' a"
proof-
  define R where "R = {((y::'a::wellorder,y'::'a'::wellorder,b::'w::wellorder),(x,x',a)) . 
     y < x \<or> 
     y = x \<and> y' < x' \<or> 
     y = x \<and> y' = x' \<and> b < a}"
  have 0: "R = lex_prod {(x,y) . x < y} (lex_prod {(x,y) . x < y} {(x,y) . x < y})"
  unfolding R_def by auto
  have 1: "wf R" unfolding 0 by (simp add: wf wf_lex_prod)
  define Q where "Q \<equiv> \<lambda>(x,x',a). P x x' a"  
  {fix xa have "Q xa" apply(rule wf_induct[OF 1])
   using assms unfolding Q_def R_def by (auto split: prod.splits)
  }
  thus ?thesis unfolding Q_def by auto
qed



 
lemma drop_Suc: "n < length xs \<Longrightarrow> drop n xs = Cons (nth xs n) (drop (Suc n) xs)" 
by (simp add: Cons_nth_drop_Suc)

lemma append_take_nth_drop: "n < length xs \<Longrightarrow>
  append (take n xs) (Cons (nth xs n) (drop (Suc n) xs)) = xs"
by (metis append_take_drop_id drop_Suc)   

lemmas list_all_nth = list_all_length
(*
(* *)
(* Lazy list notations: *)

abbreviation LNil_abbr ("[[]]") where "LNil_abbr \<equiv> LNil"

abbreviation LCons_abbr (infixr "$" 65) where "x $ xs \<equiv> LCons x xs"
  
syntax
  \<comment> \<open>llist Enumeration\<close>
  "_llist" :: "args => 'a llist"    ("[[(_)]]")

translations
  "[[x, xs]]" == "x $ [[xs]]"
  "[[x]]" == "x $ [[]]"

(* *)


definition lbutlast :: "'a llist \<Rightarrow> 'a llist" where 
"lbutlast sl \<equiv> if lfinite sl then llist_of (butlast (list_of sl)) else sl"

lemma llength_lbutlast_lfinite[simp]: 
"sl \<noteq> [[]] \<Longrightarrow> lfinite sl \<Longrightarrow> llength (lbutlast sl) = llength sl - 1"
unfolding lbutlast_def apply auto 
by (metis One_nat_def idiff_enat_enat length_list_of one_enat_def)

lemma llength_lbutlast_not_lfinite[simp]: 
"\<not> lfinite sl \<Longrightarrow> llength (lbutlast sl) = \<infinity>"
unfolding lbutlast_def using not_lfinite_llength by auto

lemma lbutlast_LNil[simp]:
"lbutlast [[]] = [[]]"
unfolding lbutlast_def by auto

lemma lbutlast_singl[simp]:
"lbutlast [[s]] = [[]]"
unfolding lbutlast_def by auto

lemma lbutlast_lfinite[simp]:
"lfinite sl \<Longrightarrow> lbutlast sl = llist_of (butlast (list_of sl))"
unfolding lbutlast_def by auto

lemma lbutlast_Cons[simp]: "tr \<noteq> [[]] \<Longrightarrow> lbutlast (s $ tr) = s $ lbutlast tr"
unfolding lbutlast_def using llist_of_list_of by fastforce

(* *)
definition "lsublist xs ys \<equiv> \<exists>us vs. lfinite us \<and> ys = lappend us (lappend xs vs)"

lemma lsublist_refl: "lsublist xs xs"  
  by (metis lappend_LNil2 lappend_code(1) lfinite_LNil lsublist_def)

lemma lsublist_trans:
  assumes "lsublist xs ys" and "lsublist ys zs" shows "lsublist xs zs"
using assms unfolding lsublist_def proof (elim exE conjE)
  fix us usa vs vsa :: \<open>'a llist\<close>
  assume finite: \<open>lfinite us\<close> \<open>lfinite usa\<close>
  assume append: \<open>ys = lappend us (lappend xs vs)\<close> \<open>zs = lappend usa (lappend ys vsa)\<close>
  have append_finite: \<open>lfinite (lappend usa us)\<close>
    using finite unfolding lfinite_lappend by (intro conjI)
  thus \<open>\<exists>us vs. lfinite us \<and> zs = lappend us (lappend xs vs)\<close>
    using append apply clarify
    apply (rule exI[of _ \<open>lappend usa us\<close>])
    apply (rule exI[of _ \<open>lappend vs vsa\<close>])
    using append_finite apply (intro conjI)
    unfolding lappend_assoc by blast+
qed

lemma lnth_lconcat_lsublist: 
assumes xs: "xs = lconcat (lmap llist_of xss)" and "i < llength xss"
shows "lsublist (llist_of (lnth xss i)) xs"
unfolding lsublist_def 
apply(rule exI[of _ "lconcat (lmap llist_of (ltake i xss))"])
apply(rule exI[of _ "lconcat (lmap llist_of (ldrop (Suc i) xss))"])
apply simp  
  by (metis (no_types, lifting) assms lappend_inf 
    lappend_ltake_ldrop lconcat_lappend lconcat_simps(2) ldrop_enat ldrop_lmap 
    ldropn_Suc_conv_ldropn linorder_neq_iff llength_lmap llength_ltake lmap_lappend_distrib 
   lnth_lmap min_def order_less_imp_le)

lemma lnth_lconcat_lsublist2: 
assumes xs: "xs = lconcat (lmap llist_of xss)" and "Suc i < llength xss"
shows "lsublist (llist_of (append (lnth xss i) (lnth xss (Suc i)))) xs"
proof -
  have llen_Suc: \<open>enat (Suc i) < llength xss\<close>
    by (simp add: assms(2))
  then have unfold_Suc_llist_of: \<open>llist_of (lnth xss (Suc i)) = lnth (lmap llist_of xss) (Suc i)\<close>
    by (rule lnth_lmap[symmetric])
  have ldropn_Suc_complex:\<open>(llist_of (lnth xss (Suc i)) $ ldrop (enat (Suc (Suc i))) (lmap llist_of xss)) = ldropn (Suc i) (lmap llist_of xss)\<close>
    unfolding unfold_Suc_llist_of
    unfolding ldrop_enat lconcat_simps(2)[symmetric]
    apply (rule ldropn_Suc_conv_ldropn)
    by (simp add: llen_Suc)

  have llen: \<open>enat i < llength xss\<close>
    using llen_Suc  Suc_ile_eq nless_le by auto
  then have unfold_llist_of: \<open>llist_of (lnth xss i) = lnth (lmap llist_of xss) i\<close>
    by (rule lnth_lmap[symmetric])
  have ldropn_complex:\<open>(llist_of (lnth xss i) $ ldropn (Suc i) (lmap llist_of xss)) = ldropn i (lmap llist_of xss)\<close>
    unfolding unfold_llist_of
    unfolding ldrop_enat lconcat_simps(2)[symmetric]
    apply (rule ldropn_Suc_conv_ldropn)
    by (simp add: llen)

  show ?thesis
    unfolding lsublist_def
    apply(rule exI[of _ "lconcat (lmap llist_of (ltake i xss))"])
    apply(rule exI[of _ "lconcat (lmap llist_of (ldrop (Suc (Suc i)) xss))"])
    apply simp
    unfolding xs
    unfolding ltake_lmap[symmetric] ldrop_lmap[symmetric]

    unfolding lappend_llist_of_llist_of[symmetric]
    unfolding lappend_assoc

    unfolding lconcat_simps(2)[symmetric, of \<open>llist_of (lnth xss (Suc i))\<close>]
    unfolding ldropn_Suc_complex

    unfolding lconcat_simps(2)[symmetric, of "llist_of (lnth xss i)"]
    unfolding ldropn_complex

    apply (cases \<open>lfinite (ltake (enat i) (lmap llist_of xss))\<close>)
    defer
    apply simp
    unfolding lconcat_lappend[symmetric, of _ "ldropn i (lmap llist_of xss)"]
    unfolding ldrop_enat[symmetric] lappend_ltake_ldrop by blast
qed

lemma lnth_lconcat_lconcat_lsublist: 
assumes xs: "xs = lappend (lconcat (lmap llist_of xss)) ys" and "i < llength xss"
shows "lsublist (llist_of (lnth xss i)) xs"
by (metis assms lappend_assoc lnth_lconcat_lsublist lsublist_def xs)

lemma lnth_lconcat_lconcat_lsublist2: 
assumes xs: "xs = lappend (lconcat (lmap llist_of xss)) ys" and "Suc i < llength xss"
shows "lsublist (llist_of (append (lnth xss i) (lnth xss (Suc i)))) xs"
by (metis assms lappend_assoc lnth_lconcat_lsublist2 lsublist_def xs)

(* *)

lemma llist_of_butlast: "llist_of (butlast xs) = lbutlast (llist_of xs)"
 by simp

lemma lprefix_lbutlast: "lprefix xs ys \<Longrightarrow> lprefix (lbutlast xs) (lbutlast ys)"
apply(cases "lfinite xs") 
  subgoal apply(cases "lfinite ys")
  apply simp_all 
    apply (smt (verit, ccfv_threshold) butlast_append lfinite_lappend 
   list_of_lappend lprefix_conv_lappend prefix_append prefix_order.eq_iff prefixeq_butlast)
  by (metis lbutlast_def llist_of_list_of lprefix_llist_of lprefix_trans prefixeq_butlast)
  by (simp add: not_lfinite_lprefix_conv_eq)

lemma su_lset_lconcat_llist_of: 
assumes "xs \<in> lset xss"
shows "set xs \<subseteq> lset (lconcat (lmap llist_of xss))"
using in_lset_lappend_iff
by (metis assms in_lset_conv_lnth lnth_lconcat_lsublist lset_llist_of lsublist_def subsetI)

(* *)

lemma lnth_lconcat: 
assumes "i < llength (lconcat xss)"
shows "\<exists>j<llength xss. \<exists>k<llength (lnth xss j). lnth (lconcat xss) i = lnth (lnth xss j) k"
using assms lnth_lconcat_conv by blast

lemma lsublist_lnth_lconcat: "i < llength tr1s \<Longrightarrow> lsublist (llist_of (lnth tr1s i)) (lconcat (lmap llist_of tr1s))"
by (meson lnth_lconcat_lsublist)

lemma lsublist_lset: 
"lsublist xs ys \<Longrightarrow> lset xs \<subseteq> lset ys"
by (metis in_lset_lappend_iff lsublist_def subsetI)

lemma lsublist_LNil: 
"lsublist xs ys \<Longrightarrow> ys = LNil \<Longrightarrow> xs = LNil"
by (metis LNil_eq_lappend_iff lsublist_def)

(* *)

primcorec betw :: "nat \<Rightarrow> enat \<Rightarrow> nat llist" where 
"betw i n = (if i \<ge> n then LNil else i $ betw (Suc i) n)"


lemma betw_more_simps: 
"\<not> n \<le> i \<Longrightarrow> betw i n = i $ betw (Suc i) n"
using betw.ctr(2) enat_ord_simps(1) by blast


lemma lhd_betw: "i < n \<Longrightarrow> lhd (betw i n) = i"
by fastforce

lemma not_lfinite_betw_infty: "\<not> lfinite (betw i \<infinity>)"
proof-
  {fix js assume "lfinite js" "js = betw i \<infinity>" 
   hence False
   apply (induct arbitrary: i)
     subgoal by (metis betw.disc(2) enat_ord_code(5) llist.disc(1))
     subgoal by (metis betw.sel(2) enat_ord_code(5) llist.sel(3)) .
  }
  thus ?thesis by auto
qed

lemma llength_betw_infty[simp]: "llength (betw i \<infinity>) = \<infinity>"
using not_lfinite_betw_infty not_lfinite_llength by blast

lemma llength_betw: "llength (betw i n) = n - i"
apply(cases n)
  subgoal for nn apply simp apply(induct "nn-i" arbitrary: i, auto)
    apply (simp add: zero_enat_def)  
    by (metis betw.ctr(2) diff_Suc_1 diff_Suc_eq_diff_pred diff_commute 
    eSuc_enat enat_ord_simps(1) less_le_not_le llength_LCons zero_less_Suc zero_less_diff)
  subgoal by simp .

lemma lfinite_betw_not_infty: "n < \<infinity> \<Longrightarrow> lfinite (betw i n)"
using lfinite_conv_llength_enat llength_betw by fastforce

lemma lfinite_betw_enat: "lfinite (betw i (enat n))"
using lfinite_conv_llength_enat llength_betw by fastforce
  
lemma lnth_betw: "enat j < n - i \<Longrightarrow> lnth (betw i n) j = i + j"
apply(induct j arbitrary: i, auto)  
  apply (metis betw.ctr(1) betw.disc_iff(1) betw.simps(3) enat_0 llength_LNil 
       llength_betw lnth_0_conv_lhd zero_less_iff_neq_zero)
  by (metis Suc_ile_eq add_Suc betw.ctr(1) betw.ctr(2) betw.disc(2) betw.sel(2) iless_Suc_eq 
  llength_LCons llength_LNil llength_betw lnth_ltl not_less_zero)

definition "build n f \<equiv> lmap f (betw 0 n)"

lemma llength_build[simp]: "llength (build n f) = n" 
by (simp add: build_def llength_betw)

lemma lnth_build[simp]: "i < n \<Longrightarrow> lnth (build n f) i = f i" 
by (simp add: build_def llength_betw lnth_betw)

lemma build_lnth[simp]: "build (llength xs) (lnth xs) = xs"
by (metis (mono_tags, lifting) llength_build llist.rel_eq llist_all2_all_lnthI lnth_build)

lemma build_eq_LNil[simp]: "build n f = [[]] \<longleftrightarrow> n = 0"
  by (metis llength_build llength_eq_0 lnull_def)

(* *)

definition "nextNotNil xss i \<equiv> LEAST j. i < j \<and> j < llength xss \<and> lnth xss j \<noteq> Nil"

lemma nextNotNil: 
assumes "\<exists>j. i < j \<and> j < llength xss \<and> lnth xss j \<noteq> Nil"
shows "i < nextNotNil xss i \<and> nextNotNil xss i < llength xss \<and> 
  lnth xss (nextNotNil xss i) \<noteq> Nil"
using LeastI_ex[OF assms] unfolding nextNotNil_def .

lemma nextNotNil_least: 
assumes "i < j" "j < llength xss" "lnth xss j \<noteq> Nil"
shows "nextNotNil xss i \<le> j" 
  unfolding nextNotNil_def apply (rule Least_le)
  using assms by (intro conjI)

lemma nextNotNil_Suc: 
assumes "Suc i < llength xss"  "lnth xss (Suc i) \<noteq> Nil"
shows "nextNotNil xss i = Suc i"
by (metis assms le_antisym linorder_neq_iff nextNotNil nextNotNil_least not_less_eq_eq order_less_imp_le)

lemma nextNotNil_Suc2: 
assumes "\<exists>j. i < j \<and> j < llength xss \<and> lnth xss j \<noteq> Nil" "lnth xss (Suc i) = Nil" 
shows "nextNotNil xss i = nextNotNil xss (Suc i)" 
apply(rule antisym)
  subgoal apply(rule nextNotNil_least)
    apply (metis Suc_lessD Suc_lessI assms nextNotNil)
    apply (metis assms linorder_neqE_nat nextNotNil not_less_eq)
    using Suc_lessI assms nextNotNil by blast
  subgoal apply(rule nextNotNil_least)
    apply (metis Suc_lessI assms nextNotNil)
    using assms(1) nextNotNil apply blast
    using assms(1) nextNotNil by blast . 

(* *)

lemma lnth_0_lset:  "xs \<noteq> [[]] \<Longrightarrow> lnth xs 0 \<in> lset xs"
by (metis llist.set_sel(1) lnth_0_conv_lhd lnull_def)

lemma lconcat_eq_LNil_iff[simp]: "lconcat xss = LNil \<longleftrightarrow> (\<forall>xs\<in>lset xss. xs = LNil)"
by (metis lnull_def lnull_lconcat mem_Collect_eq subset_eq)

(* *)


lemma lbutlast_lappend: 
assumes "(ys::'a llist) \<noteq> [[]]" shows "lbutlast (lappend xs ys) = lappend xs (lbutlast ys)"
proof-
  {fix us vs :: "'a llist"
   assume "\<exists> xs ys. ys \<noteq> [[]] \<and> us = lbutlast (lappend xs ys) \<and> vs = lappend xs (lbutlast ys)"
   hence "us = vs"
   apply(coinduct rule: llist.coinduct)
   apply (auto simp: lappend_lnull1)
   apply (metis lappend.ctr(2) lappend.simps(4) lbutlast_Cons llist.collapse(1) llist.distinct(1) 
       ltl_lappend)
   apply (metis lappend_code(2) lappend_lnull1 lbutlast_Cons lhd_LCons_ltl lstrict_prefix_code(2) lstrict_prefix_def)
   apply (metis lappend_code(2) lbutlast_Cons lbutlast_singl lhd_LCons lnull_def not_lnull_conv)
   apply (metis lappend_code(2) lbutlast_Cons lbutlast_singl lhd_LCons lnull_def not_lnull_conv)
   apply (smt (verit, ccfv_SIG) lappend.ctr(2) lappend_eq_LNil_iff lbutlast_Cons ltl_lappend ltl_simps(2))
   apply (metis lappend_code(1) lappend_lnull2 lbutlast_Cons lbutlast_singl llist.exhaust_sel ltl_simps(2))
   by (metis (no_types, lifting) lappend.ctr(2) lappend_eq_LNil_iff lappend_ltl lbutlast_Cons ltl_simps(2))
  }
  thus ?thesis using assms by blast
qed

lemma lbutlast_llist_of: "lbutlast (llist_of xs) = llist_of (butlast xs)"
by auto

lemma butlast_list_of: "lfinite xs \<Longrightarrow> butlast (list_of xs) = list_of (lbutlast xs)"
  by simp
*)
lemma not_allI: "(\<exists>x. \<not>R x) \<Longrightarrow> \<not>(\<forall>x. R x)"
  by simp

lemma prodI: "x = y \<Longrightarrow> z = w \<Longrightarrow> (x, z) = (y, w)"
  by simp

lemma list_all_hd:
  assumes \<open>list_all P xs\<close>
      and \<open>xs \<noteq> []\<close>
    shows \<open>P (hd xs)\<close>
  using assms by (metis list.collapse list_all_simps(1))

lemma lmember_equiv_list_all: "(\<forall>x. x \<in>\<in> xs \<longrightarrow> P x) \<longleftrightarrow> list_all P xs"
  by (induct xs, auto)

lemma lmember_implies_list_all_butlast: 
  assumes "(\<forall>x. x \<in>\<in> xs \<longrightarrow> P x)"
    shows "list_all P (butlast xs)"
  using assms lmember_equiv_list_all by (metis in_set_butlastD)


lemma map_eq_all_keys: 
  assumes \<open>\<forall>k. (m::(('a,'b) map)) k = m' k\<close>
    shows \<open>m = m'\<close>
  using assms by blast

lemma butlast_nth_lt_length: 
  assumes "n < length xs"
      and "ys \<noteq> []"
    shows "butlast (xs @ ys) ! n = xs ! n"
  using assms apply (auto simp add: butlast_append)
  by (metis nth_append)

lemma butlast2_nth_lt_length: 
  assumes "n < length xs"
    shows "butlast (xs @ [x, x']) ! n = xs ! n"
  using assms by (frule_tac ys=\<open>[x, x']\<close> in butlast_nth_lt_length, blast+)

lemma butlast_nth_length: \<open>length ys > 1 \<Longrightarrow> butlast (xs @ ys) ! length xs = hd ys\<close>
  apply (auto simp add: butlast_append)
  by (metis One_nat_def append_is_Nil_conv butlast.simps(2) length_gt_1_Cons_snoc list.collapse list.inject not_Cons_self2 nth_append_length)

lemma butlast2_nth_length: \<open>butlast (xs @ [x, x']) ! length xs = x\<close>
  by (simp add: butlast_append)

lemma tl2_nth_length: \<open>tl (xs @ [x, x']) ! length xs = x'\<close>
  apply (cases \<open>xs = []\<close>, auto)
  using cancel_comm_monoid_add_class.diff_cancel diff_less diff_right_commute length_greater_0_conv length_tl list.sel(2) list.size(3) nth_Cons_0 nth_Cons_pos nth_append zero_less_diff zero_less_one
  by (smt (verit))

lemma list_nonempty_induct4[consumes 4, case_names single cons]:
  assumes \<open>length xs = length ys\<close> and \<open>length ys = length zs\<close> and \<open>length zs = length ws\<close>
      and \<open>xs \<noteq> []\<close>
      and \<open>\<And>x y z w. P [x] [y] [z] [w]\<close>
      and \<open>\<And>x xs y ys z zs w ws. \<lbrakk>xs \<noteq> []; ys \<noteq> []; zs \<noteq> []; ws \<noteq> []; P xs ys zs ws;
            length xs = length ys; length ys = length zs; length zs = length ws
            \<rbrakk> \<Longrightarrow> P (x # xs) (y # ys) (z # zs) (w # ws)\<close>
    shows \<open>P xs ys zs ws\<close>
using assms proof (induct xs ys zs ws rule: list_induct4)
  case (Cons x xs y ys z zs w ws)
  then show ?case
    apply (cases \<open>xs \<noteq> []\<close>)
    apply auto
    apply (subgoal_tac \<open>ys \<noteq> []\<close>)
    apply (subgoal_tac \<open>zs \<noteq> []\<close>)
    apply (subgoal_tac \<open>ws \<noteq> []\<close>)
    by auto
qed auto

lemma rev_induct2 [consumes 1, case_names Nil snoc]:
  assumes \<open>length xs = length ys\<close>
      and nil: \<open>P [] []\<close>
      and snoc: \<open>(\<And>x xs y ys. \<lbrakk>length xs = length ys; P xs ys\<rbrakk> \<Longrightarrow> P (xs ## x) (ys ## y))\<close>
    shows \<open>P xs ys\<close>
using assms proof (induct xs arbitrary: ys rule: rev_induct)
  case (snoc x xs ys)
  thus ?case
    by (induct ys rule: rev_induct) simp_all
qed simp

lemma rev_nonempty_induct2 [consumes 2, case_names single snoc]:
  assumes \<open>length xs = length ys\<close>
      and \<open>xs \<noteq> []\<close>
      and single: \<open>\<And>x y. P [x] [y]\<close>
      and snoc: \<open>(\<And>x xs y ys. \<lbrakk>length xs = length ys; xs \<noteq> []; ys \<noteq> []; P xs ys\<rbrakk> 
                    \<Longrightarrow> P (xs ## x) (ys ## y))\<close>
    shows \<open>P xs ys\<close>
using assms proof (induct xs ys rule: rev_induct2)
  case (snoc x xs y ys)
  then show ?case 
    apply (cases xs, auto)
    apply (cases ys, auto)
    by (metis append_Cons list.distinct(1) snoc.hyps(1))
qed simp

lemma rev_induct4 [consumes 3, case_names Nil snoc]:
  assumes \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length zs = length ws\<close>
      and nil: \<open>P [] [] [] []\<close>
      and snoc: \<open>(\<And>x xs y ys z zs w ws. \<lbrakk>
                  length xs = length ys; length xs = length zs; length xs = length ws;
                  P xs ys zs ws
                 \<rbrakk> \<Longrightarrow> P (xs ## x) (ys ## y) (zs ## z) (ws ## w))\<close>
    shows \<open>P xs ys zs ws\<close>
using assms proof (induct xs ys arbitrary: zs ws rule: rev_induct2)
  case (snoc x xs y ys)
  show ?case 
    using snoc.prems(2) snoc by (induct zs ws rule: rev_induct2) auto
qed simp

lemma rev_nonempty_induct4 [consumes 4, case_names single snoc]:
  assumes \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length zs = length ws\<close>
      and \<open>xs \<noteq> []\<close>
      and single: \<open>\<And>x y z w. P [x] [y] [z] [w]\<close>
      and snoc: \<open>(\<And>x xs y ys z zs w ws. \<lbrakk>
                  length xs = length ys; length xs = length zs; length xs = length ws;
                  xs \<noteq> []; ys \<noteq> []; zs \<noteq> []; ws \<noteq> []; P xs ys zs ws
                 \<rbrakk> \<Longrightarrow> P (xs ## x) (ys ## y) (zs ## z) (ws ## w))\<close>
    shows \<open>P xs ys zs ws\<close>
using assms proof (induct xs ys zs ws rule: rev_induct4)
  case (snoc x xs y ys z zs w ws)
  then show ?case 
    apply (cases \<open>xs \<noteq> []\<close>)
    apply auto
    apply (subgoal_tac \<open>ys \<noteq> []\<close>)
    apply (subgoal_tac \<open>zs \<noteq> []\<close>)
    apply (subgoal_tac \<open>ws \<noteq> []\<close>)
    by auto
qed auto


lemma allP_lastP:
  assumes \<open>\<forall>i<length \<pi>\<^sub>1. P (\<pi>\<^sub>3 ! i) (\<pi>\<^sub>4 ! i) (\<pi>\<^sub>1 ! i) (\<pi>\<^sub>2 ! i)\<close>
      and \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close> and \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>3\<close> and \<open>length \<pi>\<^sub>3 = length \<pi>\<^sub>4\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>P (last \<pi>\<^sub>3) (last \<pi>\<^sub>4) (last \<pi>\<^sub>1) (last \<pi>\<^sub>2)\<close>
  using assms apply (subgoal_tac \<open>P (\<pi>\<^sub>3 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>4 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>1 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>2 ! (length \<pi>\<^sub>1 - 1))\<close>)
  apply (metis last_conv_nth length_0_conv)
  by (meson diff_less length_greater_0_conv less_numeral_extra(1))

lemma allNotP_lastNotP:
  assumes \<open>\<forall>i<length \<pi>\<^sub>1. \<not>P (\<pi>\<^sub>3 ! i) (\<pi>\<^sub>4 ! i) (\<pi>\<^sub>1 ! i) (\<pi>\<^sub>2 ! i)\<close>
      and \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close> and \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>3\<close> and \<open>length \<pi>\<^sub>3 = length \<pi>\<^sub>4\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>\<not>P (last \<pi>\<^sub>3) (last \<pi>\<^sub>4) (last \<pi>\<^sub>1) (last \<pi>\<^sub>2)\<close>
  using assms apply (subgoal_tac \<open>\<not>P (\<pi>\<^sub>3 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>4 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>1 ! (length \<pi>\<^sub>1 - 1)) (\<pi>\<^sub>2 ! (length \<pi>\<^sub>1 - 1))\<close>)
  apply (metis last_conv_nth length_0_conv)
  by (meson diff_less length_greater_0_conv less_numeral_extra(1))

(* *)

lemma list_nonempty_induct2[consumes 2, case_names single cons]:
  assumes \<open>length xs = length ys\<close>
      and \<open>xs \<noteq> []\<close>
      and \<open>\<And>x y. P [x] [y]\<close>
      and \<open>\<And>x xs y ys. \<lbrakk>xs \<noteq> []; ys \<noteq> []; P xs ys; length xs = length ys
            \<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)\<close>
    shows \<open>P xs ys\<close>
using assms proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)
  then show ?case
    apply (cases \<open>xs \<noteq> []\<close>)
    apply auto
    apply (subgoal_tac \<open>ys \<noteq> []\<close>)
    by auto
qed auto


(* *)

locale list_all_lemmas =
    fixes f :: \<open>'a list \<Rightarrow> bool\<close>
      and g :: \<open>'a \<Rightarrow> bool\<close>
  assumes f_eq: \<open>f = list_all g\<close>
begin

lemma empty[simp]: \<open>f []\<close>
  using f_eq by (metis list.pred_inject(1))

lemma single[simp]: \<open>f [s] \<longleftrightarrow> g s\<close>
  unfolding f_eq by auto

lemma hd:
  assumes \<open>f \<pi>\<close>
      and \<open>\<pi> \<noteq> []\<close>
    shows \<open>g (hd \<pi>)\<close>
  using assms unfolding f_eq by (rule list_all_hd)

lemma nth0:
  assumes \<open>\<pi> \<noteq> []\<close>
      and \<open>f \<pi>\<close>
    shows \<open>g (\<pi> ! 0)\<close>
  using assms unfolding f_eq by (simp add: list_all_length) 

lemma nth_lt_length:
  assumes \<open>i < length \<pi>\<close>
      and \<open>f \<pi>\<close>
    shows \<open>g (\<pi> ! i)\<close>
  using assms unfolding f_eq by (simp add: list_all_length) 

lemma append: \<open>f \<pi> \<and> f \<pi>' \<longleftrightarrow> f (\<pi> @ \<pi>')\<close>
  unfolding f_eq by simp

lemma appendI:
  assumes \<open>f \<pi>\<close>
      and \<open>f \<pi>'\<close>
    shows \<open>f (\<pi> @ \<pi>')\<close>
  using assms unfolding f_eq by simp

lemma append1I:
  assumes \<open>f \<pi>\<close>
      and \<open>g s\<close>
    shows \<open>f (\<pi> ## s)\<close>
  using assms unfolding f_eq by simp

lemma appendE:
  assumes \<open>f (\<pi> @ \<pi>')\<close>
    shows \<open>f \<pi>\<close> and \<open>f \<pi>'\<close>
  using assms unfolding f_eq by simp_all

lemma last:
  assumes \<open>f \<pi>\<close>
      and \<open>\<pi> \<noteq> []\<close>
    shows \<open>g (last \<pi>)\<close>
  using assms f_eq by (meson last_in_set lmember_equiv_list_all)

lemma Cons: \<open>f (s # \<pi>) \<longleftrightarrow> g s \<and> f \<pi>\<close>
  using f_eq by simp

lemma ConsI:
  assumes \<open>g s\<close>
      and \<open>f \<pi>\<close>
    shows \<open>f (s # \<pi>)\<close>
  using assms f_eq by auto

lemma ConsE:
  assumes \<open>f (s # \<pi>)\<close>
    shows \<open>g s\<close> and \<open>f \<pi>\<close>
  using assms f_eq by auto


lemma all_length: \<open>f xs \<longleftrightarrow> (\<forall>i < length xs. g (xs ! i))\<close>
  using f_eq by (simp add: list_all_length) 

lemma hd_tlI:
  assumes \<open>g (hd xs)\<close>
      and \<open>f (tl xs)\<close>
    shows \<open>f xs\<close>
  using assms f_eq ConsI empty list.exhaust_sel by (metis )

lemma hd_nth_joinI:
  assumes \<open>xs \<noteq> []\<close>
      and \<open>g (hd xs)\<close>
      and \<open>\<forall>i < length xs - 1. g (xs ! Suc i)\<close>
    shows \<open>f xs\<close>
  apply (rule hd_tlI)
  using assms(1,2) apply blast
  using nth_tl assms(1,3) less_Suc_eq nth_tl by (metis all_length length_tl)

lemma nth_joinI:
  assumes \<open>xs \<noteq> []\<close>
      and \<open>g (xs ! 0)\<close>
      and \<open>\<forall>i < length xs - 1. g (xs ! Suc i)\<close>
    shows \<open>f xs\<close>
  apply (rule hd_nth_joinI)
  using assms(1) apply blast
  using assms(1,2) apply (simp add: hd_conv_nth)
  using assms(3) by blast

end

lemma list_all2_last:
  assumes \<open>list_all2 P \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>P (last \<pi>\<^sub>1) (last \<pi>\<^sub>2)\<close>
  using assms by (metis diff_less last_conv_nth length_greater_0_conv list_all2_conv_all_nth zero_less_one)

lemma list_all2_map_eq: \<open>map P xs = map P ys \<longleftrightarrow> list_all2 (\<lambda>s s'. P s = P s') xs ys\<close>
  apply auto
  subgoal
    apply (frule map_eq_imp_length_eq)
    apply (simp add: list_all2_conv_all_nth)
    using nth_map by (metis )
  subgoal
    apply (auto simp add: list_all2_conv_all_nth)
    using length_map nth_equalityI nth_map
    by (metis (mono_tags, lifting))
  .

primrec 
  unzipL :: "('a \<times> 'b) list \<Rightarrow> 'a list" 
where
  "unzipL [] = []" |
  "unzipL (x # xs) = fst x # unzipL xs"

lemma unzipL_empty[simp]: 
    \<open>unzipL vl = [] \<longleftrightarrow> vl = []\<close>
    \<open>[] = unzipL vl \<longleftrightarrow> vl = []\<close>
  by (induct vl, auto)

lemma unzipL_length: 
  assumes \<open>unzipL vl = unzipL vl1\<close>
    shows \<open>length vl = length vl1\<close>
using assms proof (induct vl1 arbitrary: vl)
  case Nil then show ?case by simp
next
  case (Cons y ys) then obtain z zs where xs: "vl = z # zs"
    by (metis list.exhaust list.simps(3) unzipL_empty(2))
  from Cons xs have "unzipL zs = unzipL ys" by simp
  with Cons have "length zs = length ys" by blast
  with xs show ?case by simp
qed

lemma unzipL_no_tl:
  assumes unzip: \<open>unzipL vl\<^sub>1 = unzipL vl\<^sub>2\<close>
    shows \<open>vl\<^sub>1 \<noteq> [] \<Longrightarrow> unzipL (tl vl\<^sub>1) \<noteq> unzipL vl\<^sub>2\<close> \<open>vl\<^sub>2 \<noteq> [] \<Longrightarrow> unzipL vl\<^sub>1 \<noteq> unzipL (tl vl\<^sub>2)\<close>
  using unzipL_length[OF unzip] unzip by (induct vl\<^sub>1 vl\<^sub>2 rule: list_induct2, simp_all)

primrec 
  unzipR :: "('a \<times> 'b) list \<Rightarrow> 'b list" 
where
  "unzipR [] = []" |
  "unzipR (x # xs) = snd x # unzipR xs"

definition \<open>unzip xs \<equiv> (unzipL xs,  unzipR xs)\<close>

lemma unzip_zip: \<open>zip (unzipL xs) (unzipR xs) = xs\<close>
  by (induct xs, auto)

lemma zip_unzip:
  assumes \<open>length xs = length ys\<close>
    shows \<open>unzipL (zip xs ys) = xs\<close> \<open>unzipR (zip xs ys) = ys\<close>
  using assms by (induct xs ys rule: list_induct2, simp_all)

lemma length_unzip: \<open>length (unzipL list) = length (unzipR list)\<close>
  by (induct list, auto)  

lemma zip2: "(zip [s\<^sub>1, s\<^sub>1'] [s\<^sub>2, s\<^sub>2']) = [(s\<^sub>1, s\<^sub>2), (s\<^sub>1', s\<^sub>2')]"
  by auto

lemma tl_zip: 
  assumes \<open>length xs = length ys\<close>
    shows \<open>(tl (zip xs ys)) = zip (tl xs) (tl ys)\<close>
  using assms by (induct xs ys rule : list_induct2, auto)

lemma last_zip:   
  assumes \<open>length xs = length ys\<close>
      and \<open>xs \<noteq> []\<close>
    shows \<open>last (zip xs ys) = (last xs, last ys)\<close>
  using assms by (induct xs ys rule : list_induct2, auto)  

lemma list_all2_hd:
  assumes \<open>list_all2 P \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>P (hd \<pi>\<^sub>1) (hd \<pi>\<^sub>2)\<close>
  using assms list.rel_sel by blast

lemma list_all2_tl:
  assumes \<open>list_all2 P \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    shows \<open>list_all2 P (tl \<pi>\<^sub>1) (tl \<pi>\<^sub>2)\<close>
  using assms by (metis list.rel_sel list.sel(2))

lemma list_all2_appendE:
  assumes \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close>
      and \<open>list_all2 P (\<pi>\<^sub>1 @ \<pi>\<^sub>1') (\<pi>\<^sub>2 @ \<pi>\<^sub>2')\<close>
    shows \<open>list_all2 P \<pi>\<^sub>1 \<pi>\<^sub>2\<close> and \<open>list_all2 P \<pi>\<^sub>1' \<pi>\<^sub>2'\<close>
  using assms list_all2_append by blast+

locale list_all2_lemmas =
    fixes f2 :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> bool\<close>
      and g2 :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes f_list_all2_eq: \<open>f2 = list_all2 g2\<close>
begin

sublocale pair: list_all_lemmas \<open>\<lambda>xs. f2 (unzipL xs) (unzipR xs)\<close> \<open>\<lambda>x. g2 (fst x) (snd x)\<close>
  apply standard
  unfolding f_list_all2_eq 
  apply (subgoal_tac "\<And>xs. (\<lambda>xs. list_all2 g2 (unzipL xs) (unzipR xs)) xs =
    list_all (\<lambda>x. g2 (fst x) (snd x)) xs")
  apply simp
  apply (induct_tac xs)
  apply simp
  by simp

lemma empty[simp]: \<open>f2 [] []\<close>
  using pair.empty by auto

lemma single[simp]: \<open>f2 [s] [s'] \<longleftrightarrow> g2 s s'\<close>
  using pair.single
  by (simp add: f_list_all2_eq)

lemma hd:
  assumes \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>g2 (hd \<pi>\<^sub>1) (hd \<pi>\<^sub>2)\<close>
  using assms f_list_all2_eq list.rel_sel by blast

lemma tl:
  assumes \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    shows \<open>f2 (tl \<pi>\<^sub>1) (tl \<pi>\<^sub>2)\<close>
  using assms by (metis f_list_all2_eq list_all2_tl)

lemma lengthD[intro?]:
  assumes \<open>f2 xs ys\<close>
    shows \<open>length xs = length ys\<close>
  using assms by (simp add: f_list_all2_eq list_all2_lengthD) 

lemma nth0:
  assumes \<open>\<pi>\<^sub>1 \<noteq> []\<close>
      and \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    shows \<open>g2 (\<pi>\<^sub>1 ! 0) (\<pi>\<^sub>2 ! 0)\<close>
  using assms by (metis f_list_all2_eq length_greater_0_conv list_all2_nthD)

lemma nth_lt_length:
  assumes \<open>i < length \<pi>\<^sub>1\<close>
      and \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    shows \<open>g2 (\<pi>\<^sub>1 ! i) (\<pi>\<^sub>2 ! i)\<close>
  using assms by (simp add: f_list_all2_eq list_all2_conv_all_nth)

lemma append:
  assumes \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close>
    shows \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> f2 \<pi>\<^sub>1' \<pi>\<^sub>2' \<longleftrightarrow> f2 (\<pi>\<^sub>1 @ \<pi>\<^sub>1') (\<pi>\<^sub>2 @ \<pi>\<^sub>2')\<close>
  using assms using list_all2_append f_list_all2_eq by blast
  
lemma appendI:
  assumes \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>f2 \<pi>\<^sub>1' \<pi>\<^sub>2'\<close>
    shows \<open>f2 (\<pi>\<^sub>1 @ \<pi>\<^sub>1') (\<pi>\<^sub>2 @ \<pi>\<^sub>2')\<close>
  using assms using list_all2_appendI f_list_all2_eq by blast

lemma append1I:
  assumes \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>g2 s\<^sub>1 s\<^sub>2\<close>
    shows \<open>f2 (\<pi>\<^sub>1 ## s\<^sub>1) (\<pi>\<^sub>2 ## s\<^sub>2)\<close>
  using assms using list_all2_appendI f_list_all2_eq by blast

lemma appendE:
  assumes \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close>
      and \<open>f2 (\<pi>\<^sub>1 @ \<pi>\<^sub>1') (\<pi>\<^sub>2 @ \<pi>\<^sub>2')\<close>
    shows \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close> and \<open>f2 \<pi>\<^sub>1' \<pi>\<^sub>2'\<close>
  using assms f_list_all2_eq list_all2_append by blast+

lemma append1E:
  assumes \<open>f2 (\<pi>\<^sub>1 ## s\<^sub>1) (\<pi>\<^sub>2 ## s\<^sub>2)\<close>
    shows \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close> and \<open>g2 s\<^sub>1 s\<^sub>2\<close>
  using assms unfolding f_list_all2_eq 
  apply (metis appendE(1) butlast_snoc f_list_all2_eq length_butlast list_all2_lengthD)
  by (metis assms f_list_all2_eq list_all2_last snoc_eq_iff_butlast)

lemma tl_appendI:
  assumes \<open>f2 (tl \<pi>\<^sub>1) (tl \<pi>\<^sub>2)\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close> and \<open>\<pi>\<^sub>2 \<noteq> []\<close>
      and \<open>f2 \<pi>\<^sub>1' \<pi>\<^sub>2'\<close>
    shows \<open>f2 (tl (\<pi>\<^sub>1 @ \<pi>\<^sub>1')) (tl (\<pi>\<^sub>2 @ \<pi>\<^sub>2'))\<close>
  using assms by (simp add: appendI list.case_eq_if)

lemma last:
  assumes \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close>
    shows \<open>g2 (last \<pi>\<^sub>1) (last \<pi>\<^sub>2)\<close>
  using assms f_list_all2_eq list_all2_last by blast

lemma Cons: \<open>f2 (s\<^sub>1 # \<pi>\<^sub>1) (s\<^sub>2 # \<pi>\<^sub>2) \<longleftrightarrow> g2 s\<^sub>1 s\<^sub>2 \<and> f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
  using f_list_all2_eq list_all2_Cons by blast

lemma ConsI:
  assumes \<open>g2 s\<^sub>1 s\<^sub>2\<close>
      and \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
    shows \<open>f2 (s\<^sub>1 # \<pi>\<^sub>1) (s\<^sub>2 # \<pi>\<^sub>2)\<close>
  using assms by (simp add: local.Cons)

lemma ConsE:
  assumes \<open>f2 (s\<^sub>1 # \<pi>\<^sub>1) (s\<^sub>2 # \<pi>\<^sub>2)\<close>
    shows \<open>g2 s\<^sub>1 s\<^sub>2\<close> and \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
  using assms by (simp_all add: local.Cons) 

lemma conv_all_nth: \<open>f2 xs ys \<longleftrightarrow> (length xs = length ys \<and> (\<forall>i < length xs. g2 (xs ! i) (ys ! i)))\<close>
  using list_all2_conv_all_nth f_list_all2_eq by auto

lemma conv_all_nth': 
  assumes \<open>length xs = length ys\<close>
    shows \<open>f2 xs ys = (\<forall>i . i < length xs \<longrightarrow> g2 (xs ! i) (ys ! i))\<close>
  using assms conv_all_nth by simp

lemma hd_tlI:
  assumes \<open>g2 (hd \<pi>\<^sub>1) (hd \<pi>\<^sub>2)\<close>
      and \<open>length \<pi>\<^sub>1 = length \<pi>\<^sub>2\<close>
      and \<open>f2 (tl \<pi>\<^sub>1) (tl \<pi>\<^sub>2)\<close>
    shows \<open>f2 \<pi>\<^sub>1 \<pi>\<^sub>2\<close>
  using assms apply (frule_tac lengthD)
  apply simp
  apply (simp add: f_list_all2_eq)
  by (metis length_0_conv list.rel_sel)


lemma Nil [iff, code]: 
  \<open>f2 [] ys = (ys = [])\<close>
  by (simp add: f_list_all2_eq)

lemma Nil2 [iff, code]: 
  \<open>f2 xs [] = (xs = [])\<close>
  by (simp add: f_list_all2_eq)

lemma inducts[consumes 1, case_names Nil Cons]:
  assumes \<open>f2 xs ys\<close>
      and \<open>R [] []\<close>
      and \<open>(\<And>x xs y ys. \<lbrakk>g2 x y; f2 xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys))\<close>
    shows \<open>R xs ys\<close>
  apply (rule list_all2_induct)
  using assms(1) apply (simp add: f_list_all2_eq)
  using assms(2) apply blast
  using assms(3) by (simp add: f_list_all2_eq)

end

definition
  list_all4 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> bool\<close>
where
  \<open>list_all4 P xs ys zs ws \<equiv> list_all2 (\<lambda>(x,y) (z,w). P x y z w) (zip xs ys) (zip zs ws)
    \<and> length xs = length ys \<and> length zs = length ws\<close>

lemma list_all4_empty[simp]: 
  \<open>list_all4 P [] [] [] []\<close>
  unfolding list_all4_def by auto

lemma list_all4_lengthD:
  assumes \<open>list_all4 P xs ys zs ws\<close>
    shows \<open>length xs = length ys \<and> length xs = length zs  \<and> length xs = length ws\<close>
  using assms unfolding list_all4_def apply clarify 
  apply (drule_tac list_all2_lengthD)
  by auto

lemma list_all4_Nil:
  \<open>list_all4 g4 [] ys zs ws \<Longrightarrow> ys = [] \<and> zs = [] \<and> ws = []\<close>
  \<open>list_all4 g4 xs [] zs ws \<Longrightarrow> xs = [] \<and> zs = [] \<and> ws = []\<close>
  \<open>list_all4 g4 xs ys [] ws \<Longrightarrow> xs = [] \<and> ys = [] \<and> ws = []\<close>
  \<open>list_all4 g4 xs ys zs [] \<Longrightarrow> xs = [] \<and> ys = [] \<and> zs = []\<close>
  subgoal by (drule list_all4_lengthD, force)
  subgoal by (drule list_all4_lengthD, force)
  subgoal by (drule list_all4_lengthD, force)
  subgoal by (drule list_all4_lengthD, force)
  .

lemma list_all4_nthD:
  assumes \<open>list_all4 P xs ys zs ws\<close>
      and \<open>p < length xs\<close>  
    shows \<open>P (xs ! p) (ys ! p) (zs ! p) (ws ! p)\<close>
  using assms apply (frule_tac list_all4_lengthD)
  unfolding list_all4_def apply clarify
  apply (drule list_all2_nthD)
  by auto

lemma list_all4_conv_all_nth:
  \<open>list_all4 P xs ys zs ws \<longleftrightarrow> (length xs = length ys \<and> length xs = length zs \<and> length xs = length ws \<and> (\<forall>i < length xs. P (xs ! i) (ys ! i) (zs ! i) (ws ! i)))\<close>
  unfolding list_all4_def list_all2_conv_all_nth by auto

lemma list_all4_appendI:
  assumes \<open>list_all4 P xs ys zs ws\<close> and \<open>list_all4 P xs' ys' zs' ws'\<close>
    shows \<open>list_all4 P (xs @ xs') (ys @ ys') (zs @ zs') (ws @ ws')\<close>
  using assms apply (frule_tac list_all4_lengthD)
  apply (frule_tac xs=xs' in list_all4_lengthD)
  unfolding list_all4_def apply safe
  using zip_append apply simp
  apply (rule list_all2_appendI, blast+)
  by (metis length_append)+

lemma list_all4_appendE:
  assumes \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length xs = length ws\<close>
      and \<open>list_all4 P (xs @ xs') (ys @ ys') (zs @ zs') (ws @ ws')\<close>
    shows \<open>list_all4 P xs ys zs ws \<and> list_all4 P xs' ys' zs' ws'\<close>
  using assms apply (frule_tac list_all4_lengthD)
  unfolding list_all4_def 
  using zip_append apply auto
  apply (rule list_all2_appendE(1), simp_all)
  apply (rule list_all2_appendE(2), simp_all)
  done

locale list_all4_lemmas =
    fixes f4 :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> bool\<close>
      and g4 :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool\<close>
  assumes f_list_all4_eq: \<open>f4 = list_all4 g4\<close>
begin

lemma empty[simp]: \<open>f4 [] [] [] []\<close>
  using f_list_all4_eq by auto

lemma single[simp]: \<open>f4 [x] [y] [z] [w] \<longleftrightarrow> g4 x y z w\<close>
  unfolding f_list_all4_eq list_all4_def by auto

lemma lengthD[intro?]:
  assumes \<open>f4 xs ys zs ws\<close>
    shows \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length xs = length ws\<close>
  using assms unfolding f_list_all4_eq
  by (drule_tac list_all4_lengthD, blast)+

lemma hd:
  assumes \<open>f4 xs ys zs ws\<close>
      and \<open>xs \<noteq> []\<close>
    shows \<open>g4 (hd xs) (hd ys) (hd zs) (hd ws)\<close>
  using assms apply (frule_tac lengthD(2))
  unfolding f_list_all4_eq list_all4_def apply clarify
  apply (drule list_all2_hd)
  apply auto
  apply (frule hd_zip[of xs ys])
  apply auto
  apply (subgoal_tac \<open>zs \<noteq> []\<close>)
  apply (frule hd_zip[of zs ws])
  by auto

lemma tl:
  assumes \<open>f4 xs ys zs ws\<close>
    shows \<open>f4 (tl xs) (tl ys) (tl zs) (tl ws)\<close>
  using assms unfolding f_list_all4_eq list_all4_def
  apply auto
  apply (frule list_all2_tl)
  apply (drule tl_zip)+
  by simp

lemma nth0:
  assumes \<open>xs \<noteq> []\<close>
      and \<open>f4 xs ys zs ws\<close>
    shows \<open>g4 (xs ! 0) (ys ! 0) (zs ! 0) (ws ! 0)\<close>
  using assms unfolding f_list_all4_eq apply (frule_tac p=0 in list_all4_nthD)
  by auto

lemma nth_lt_length:
  assumes \<open>i < length xs\<close>
      and \<open>f4 xs ys zs ws\<close>
    shows \<open>g4 (xs ! i) (ys ! i) (zs ! i) (ws ! i)\<close>
  using assms unfolding f_list_all4_eq apply (frule_tac p=i in list_all4_nthD)
  by auto
  
lemma appendI:
  assumes \<open>f4 xs ys zs ws\<close>
      and \<open>f4 xs' ys' zs' ws'\<close>
    shows \<open>f4 (xs @ xs') (ys @ ys') (zs @ zs') (ws @ ws')\<close>
  using assms using list_all4_appendI f_list_all4_eq by blast

lemma append1I:
  assumes \<open>f4 xs ys zs ws\<close>
      and \<open>g4 x y z w\<close>
    shows \<open>f4 (xs ## x) (ys ## y) (zs ## z) (ws ## w)\<close>
  apply (rule appendI)
  using assms(1) apply blast
  using assms(2) by simp

lemma appendE:
  assumes \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length xs = length ws\<close>
      and \<open>f4 (xs @ xs') (ys @ ys') (zs @ zs') (ws @ ws')\<close>
    shows \<open>f4 xs ys zs ws \<and> f4 xs' ys' zs' ws'\<close>
  using assms f_list_all4_eq list_all4_appendE by blast+

lemma append1E:
  assumes \<open>f4 (xs ## x) (ys ## y) (zs ## z) (ws ## w)\<close>
    shows \<open>f4 xs ys zs ws \<and> g4 x y z w\<close>
proof -
  have \<open>length xs = length ys\<close> \<open>length xs = length zs\<close> \<open>length xs = length ws\<close>
    using assms(1) apply (drule_tac lengthD, simp)
    using assms(1) apply (drule_tac lengthD(2), simp)
    using assms(1) apply (drule_tac lengthD(3), simp)
    done
  then show ?thesis
    using assms(1) apply (drule_tac appendE, blast+)
    by simp
qed

lemma append:
  assumes \<open>length xs = length ys\<close> and \<open>length xs = length zs\<close> and \<open>length xs = length ws\<close>
    shows \<open>f4 xs ys zs ws \<and> f4 xs' ys' zs' ws' \<longleftrightarrow> f4 (xs @ xs') (ys @ ys') (zs @ zs') (ws @ ws')\<close>
  using assms appendE appendI by blast

(*
lemma tl_appendI:
  assumes \<open>f4 (tl \<pi>\<^sub>1) (tl \<pi>\<^sub>2) (tl \<pi>\<^sub>1) (tl ws)\<close>
      and \<open>\<pi>\<^sub>1 \<noteq> []\<close> and \<open>\<pi>\<^sub>2 \<noteq> []\<close>
      and \<open>f4 \<pi>\<^sub>1' \<pi>\<^sub>2'\<close>
    shows \<open>f4 (tl (\<pi>\<^sub>1 @ \<pi>\<^sub>1')) (tl (\<pi>\<^sub>2 @ \<pi>\<^sub>2'))\<close>
  using assms by (simp add: appendI list.case_eq_if)
*)

lemma last:
  assumes \<open>f4 xs ys zs ws\<close>
      and \<open>xs \<noteq> []\<close>
    shows \<open>g4 (last xs) (last ys) (last zs) (last ws)\<close>
  using assms apply (subgoal_tac \<open>zs \<noteq> []\<close>) defer  
  apply (frule_tac lengthD(2), auto)
  unfolding f_list_all4_eq list_all4_def apply clarify
  apply (frule list_all2_last)
  apply auto[1]
  apply (drule last_zip, simp_all)
  apply (drule last_zip[of zs ws])
  by auto

lemma ConsI:
  assumes \<open>g4 x y z w\<close>
      and \<open>f4 xs ys zs ws\<close>
    shows \<open>f4 (x # xs) (y # ys) (z # zs) (w # ws)\<close>
  using assms appendI single by fastforce

lemma ConsE:
  assumes \<open>f4 (x # xs) (y # ys) (z # zs) (w # ws)\<close>
    shows \<open>g4 x y z w \<and> f4 xs ys zs ws\<close>
  using assms unfolding f_list_all4_eq list_all4_def by auto

lemma Cons: \<open>f4 (x # xs) (y # ys) (z # zs) (w # ws) \<longleftrightarrow> g4 x y z w \<and> f4 xs ys zs ws\<close>
  using ConsI ConsE by blast

lemma conv_all_nth: \<open>f4 xs ys zs ws \<longleftrightarrow> (length xs = length ys \<and> length xs = length zs \<and> length xs = length ws \<and> (\<forall>i < length xs. g4 (xs ! i) (ys ! i) (zs ! i) (ws ! i)))\<close>
  unfolding f_list_all4_eq using list_all4_conv_all_nth by blast

lemma conv_all_nth': 
  assumes \<open>length xs = length ys \<and> length xs = length zs \<and> length xs = length ws\<close>
    shows \<open>f4 xs ys zs ws \<longleftrightarrow> (\<forall>i < length xs. g4 (xs ! i) (ys ! i) (zs ! i) (ws ! i))\<close>
  using assms conv_all_nth by simp

lemma Nil:
  \<open>f4 [] ys zs ws \<Longrightarrow> ys = [] \<and> zs = [] \<and> ws = []\<close>
  \<open>f4 xs [] zs ws \<Longrightarrow> xs = [] \<and> zs = [] \<and> ws = []\<close>
  \<open>f4 xs ys [] ws \<Longrightarrow> xs = [] \<and> ys = [] \<and> ws = []\<close>
  \<open>f4 xs ys zs [] \<Longrightarrow> xs = [] \<and> ys = [] \<and> zs = []\<close>
  unfolding f_list_all4_eq
  subgoal by (drule list_all4_Nil, force)
  subgoal by (drule list_all4_Nil, force)
  subgoal by (drule list_all4_Nil, force)
  subgoal by (drule list_all4_Nil, force)
  .
end


definition 
  list_step_all :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool\<close>
where
  \<open>list_step_all P xs \<longleftrightarrow> list_all (\<lambda>(a, b). P a b) (zip (butlast xs) (tl xs))\<close>

lemma list_step_all_empty[simp]: \<open>list_step_all P []\<close>
  unfolding list_step_all_def by auto

lemma list_step_all_single[simp]: \<open>list_step_all P [s]\<close>
  unfolding list_step_all_def by auto

lemma list_step_all_two: \<open>g s s' \<longleftrightarrow> list_step_all g [s, s']\<close>
  unfolding list_step_all_def by auto

lemma list_step_all_length:
  \<open>list_step_all P \<pi> \<longleftrightarrow> (\<forall>i<length \<pi> - Suc 0. P (\<pi> ! i) (\<pi> ! Suc i))\<close>
  unfolding list_step_all_def by (auto simp add: list_all_length nth_butlast nth_tl)

lemma list_step_all_nth_lt_length:
  assumes \<open>list_step_all g \<pi>\<close>
      and \<open>i < length \<pi> - Suc 0\<close>
    shows \<open>g (\<pi> ! i) (\<pi> ! Suc i)\<close>
  using assms by (auto simp add: list_step_all_length)

lemma XY: "i < length (xs @ xs') - 1 
  \<Longrightarrow> i < length xs - 1 \<or> 
      i = length xs - 1 \<or> 
      (i \<ge> length xs \<and> i < length xs + length xs' - 1)"  
  by auto

lemma appendI: 
  assumes \<open>i < length (xs @ xs') - 1\<close>
      and \<open>\<And>i. i < length xs - 1 \<Longrightarrow> P (xs ! i) (xs ! Suc i)\<close>
      and \<open>\<And>i. i < length xs' - 1 \<Longrightarrow> P (xs' ! i) (xs' ! Suc i)\<close>
      and \<open>P (last xs) (hd xs')\<close>
    shows \<open>P ((xs @ xs') ! i) ((xs @ xs') ! Suc i)\<close>
  using assms(1) apply (drule_tac XY)
  apply (elim disjE)
  subgoal 
    unfolding nth_append apply (frule assms(2))    
    using Suc_lessI diff_Suc_1 less_imp_diff_less not_less_eq
    by fastforce
  subgoal
    using assms(4) apply clarify
    using One_nat_def Suc_diff_Suc append.right_neutral append_self_conv2 assms(1) assms(3) 
          cancel_comm_monoid_add_class.diff_cancel diff_zero hd_conv_nth last_conv_nth 
          length_greater_0_conv lessI nat_neq_iff nth_append
    by metis
  subgoal
    unfolding nth_append 
    using assms(3)
    apply auto
    using One_nat_def Suc_diff_le Suc_leI add_diff_inverse_nat less_Suc_eq less_nat_zero_code 
          nat_add_left_cancel_less nat_diff_split_asm not_less_eq_eq plus_1_eq_Suc
          Nat.add_diff_assoc diff_0_eq_0 diff_Suc_diff_eq1
    by (metis (no_types, lifting))
  .

lemma list_step_all_append2E:
  assumes \<open>list_step_all g (xs @ [x, x'])\<close>
    shows \<open>list_step_all g (xs @ [x])\<close> and \<open>g x x'\<close>
  using assms apply (auto simp add: list_step_all_length)
  subgoal for n
    apply (erule_tac x=n in allE, simp)
    by (metis Nat.lessE Suc_less_eq nth_append nth_append_length)

  subgoal
    by (metis append.assoc length_append_singleton lessI nth_append_length two_singl_Rcons)
  done

lemma list_step_all_append1E:
  assumes \<open>list_step_all g (\<pi> ## s)\<close>
    shows \<open>list_step_all g \<pi>\<close> and \<open>\<pi> \<noteq> [] \<longrightarrow> g (last \<pi>) s\<close>
  using assms apply (cases \<pi> rule: rev_cases, auto)
  apply (meson list_step_all_append2E(1))
  apply (cases \<pi> rule: rev_cases, auto)
  apply (meson list_step_all_append2E(2))
  done

lemma list_step_all_appendI:
  assumes \<open>list_step_all P xs\<close>
      and \<open>P (last xs) (hd xs')\<close>
      and \<open>list_step_all P xs'\<close>
    shows \<open>list_step_all P (xs @ xs')\<close>
  using assms apply (cases \<open>xs = [] \<or> xs' = []\<close>, simp_all)
  apply (auto simp add: list_step_all_length)
  apply (rule appendI)
  apply simp
  using One_nat_def by presburger+  

lemma list_step_all_append2I:
  assumes \<open>list_step_all P (xs ## x)\<close>
      and \<open>P x s\<close> 
    shows \<open>list_step_all P (xs @ [x, s])\<close>
  apply (cases \<open>xs = []\<close>)
  subgoal
    by (metis assms(2) eq_Nil_appendI list_step_all_two)
  subgoal
    apply (rule list_step_all_appendI)
    subgoal
      using assms(1) by (rule list_step_all_append1E(1))
    subgoal    
      using assms(1) apply simp    
      by (metis list_step_all_append1E(2))
    subgoal
      using assms(2) unfolding list_step_all_two by simp
    .
  .

lemma list_step_all_append1I:
  assumes \<open>list_step_all P xs\<close>
      and \<open>P (last xs) x\<close>
    shows \<open>list_step_all P (xs ## x)\<close>
using assms proof (induct xs rule: rev_induct)
  case (snoc x' xs)
  then show ?case     
    using list_step_all_append2I
    apply (drule_tac s=x in list_step_all_append2I)
    by auto    
qed simp

lemma list_step_all_Cons2I:
  assumes \<open>P (x) (x')\<close> and \<open>list_step_all P (x' # xs)\<close>
    shows \<open>list_step_all P (x # x' # xs)\<close>
  using assms list_step_all_appendI append_Cons append_Nil last_snoc list.sel(1)  list_step_all_single
  by (metis (mono_tags, opaque_lifting) )

lemma list_step_all_ConsI:
  assumes \<open>P (x) (hd xs)\<close> and \<open>list_step_all P xs\<close>
    shows \<open>list_step_all P (x # xs)\<close>
  using assms list_step_all_appendI append_Cons append_Nil last_snoc list.sel(1)  list_step_all_single
  by (metis (mono_tags, opaque_lifting) )

lemma list_step_all_Cons2E:
  assumes \<open>list_step_all P (x # x' # xs)\<close>
    shows \<open>P (x) (x') \<and> list_step_all P (x' # xs)\<close>
  using assms unfolding list_step_all_length by auto

lemma list_step_all_ConsE:
  assumes \<open>list_step_all P (x # xs)\<close>
    shows \<open>(xs \<noteq> [] \<longrightarrow> P (x) (hd xs)) \<and> list_step_all P xs\<close>
  using assms apply (cases xs) 
  apply simp
  using assms unfolding list_step_all_length by auto


locale list_step_all_lemmas =
    fixes f :: \<open>'b list \<Rightarrow> bool\<close>
      and g :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes f_list_step_all_g: \<open>f = list_step_all g\<close>
begin

lemma length:
  \<open>f \<pi> \<longleftrightarrow> (\<forall>i<length \<pi> - Suc 0. g (\<pi> ! i) (\<pi> ! Suc i))\<close>
  using f_list_step_all_g by (simp add: list_step_all_length)

lemma empty[simp]: \<open>f []\<close>
  using f_list_step_all_g by simp

lemma single[simp]: \<open>f [s]\<close>
  using f_list_step_all_g by simp

lemma two: \<open>g s s' \<longleftrightarrow> f [s, s']\<close>
  unfolding f_list_step_all_g using list_step_all_two by metis

lemma appendI:
  assumes \<open>f xs\<close> and \<open>f ys\<close>
      and \<open>g (last xs) (hd ys)\<close> 
    shows \<open>f (xs @ ys)\<close>
  using assms list_step_all_appendI f_list_step_all_g by fastforce

lemma append2I:
  assumes \<open>f (xs ## x)\<close>
      and \<open>g x s\<close> 
    shows \<open>f (xs @ [x, s])\<close>
  using assms list_step_all_append2I f_list_step_all_g by fastforce

lemma append1I:
  assumes \<open>f xs\<close>
      and \<open>g (last xs) x\<close>
    shows \<open>f (xs ## x)\<close>
  using assms list_step_all_append1I f_list_step_all_g by fastforce

lemma append2E:
  assumes \<open>f (xs @ [x, x'])\<close>
    shows \<open>f (xs @ [x])\<close> and \<open>g x x'\<close>
  using assms list_step_all_append2E(1) f_list_step_all_g apply metis
  by (metis assms f_list_step_all_g list_step_all_append2E(2))  

lemma append1E:
  assumes \<open>f (\<pi> ## s)\<close>
    shows \<open>f \<pi>\<close> and \<open>\<pi> \<noteq> [] \<longrightarrow> g (last \<pi>) s\<close>
  using assms list_step_all_append1E(1) f_list_step_all_g apply metis
  by (metis assms f_list_step_all_g list_step_all_append1E(2))  

lemma nth_lt_length:
  assumes \<open>f \<pi>\<close>
      and \<open>i < length \<pi> - Suc 0\<close>
    shows \<open>g (\<pi> ! i) (\<pi> ! Suc i)\<close>
  using assms f_list_step_all_g list_step_all_nth_lt_length by blast

lemma Cons2E:
  assumes \<open>f (x # x' # xs)\<close>
    shows \<open>g (x) (x') \<and> f (x' # xs)\<close>
  using assms unfolding f_list_step_all_g by (rule list_step_all_Cons2E)

lemma ConsE:
  assumes \<open>f (x # xs)\<close>
    shows \<open>(xs \<noteq> [] \<longrightarrow> g (x) (hd xs)) \<and> f xs\<close>
  using assms unfolding f_list_step_all_g by (rule list_step_all_ConsE)

lemma Cons2I:
  assumes \<open>g (x) (x')\<close> and \<open>f (x' # xs)\<close>
  shows \<open>f (x # x' # xs)\<close>
  unfolding f_list_step_all_g apply (rule list_step_all_Cons2I)
  apply (rule assms(1))
  using assms(2) unfolding f_list_step_all_g by clarify

lemma ConsI:
  assumes \<open>g (x) (hd xs)\<close> and \<open>f xs\<close>
    shows \<open>f (x # xs)\<close>
  unfolding f_list_step_all_g apply (rule list_step_all_ConsI)
  apply (rule assms(1))
  using assms(2) unfolding f_list_step_all_g by clarify

end

definition 
  list_step_all2 :: \<open>('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
where
  \<open>list_step_all2 P xs ys \<longleftrightarrow> length xs = length ys \<and> 
    list_step_all (\<lambda>(a, b) (a', b'). P a b a' b') (zip xs ys)\<close>

lemma list_step_all2_empty[simp]: 
  \<open>list_step_all2 g2 [] []\<close>
  unfolding list_step_all2_def by auto

lemma list_step_all2_single[simp]: 
  \<open>list_step_all2 g2 [x] [y]\<close>
  unfolding list_step_all2_def by simp

lemma list_step_all2_pair:
  \<open>g2 s\<^sub>1 s\<^sub>2 s\<^sub>1' s\<^sub>2' \<longleftrightarrow> list_step_all2 g2 [s\<^sub>1, s\<^sub>1'] [s\<^sub>2, s\<^sub>2']\<close>
  unfolding list_step_all2_def apply safe
  apply simp
  unfolding zip2 apply (metis list_step_all_two old.prod.case)
  by (metis list_step_all_two old.prod.case)

lemma list_step_all2_length:
    \<open>list_step_all2 P xs ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i<length xs - Suc 0. P (xs ! i) (ys ! i) (xs ! Suc i) (ys ! Suc i))\<close>
  unfolding list_step_all2_def list_step_all_length by auto

lemma list_step_all2_lengthD:
  assumes \<open>list_step_all2 P xs ys\<close>
    shows \<open>length xs = length ys\<close>
  using assms unfolding list_step_all2_length by simp  

lemma list_step_all2_nth_lt_length:
  assumes \<open>list_step_all2 P xs ys\<close>
      and \<open>i < length xs - Suc 0\<close>
    shows \<open>P (xs ! i) (ys ! i) (xs ! Suc i) (ys ! Suc i)\<close>
  using assms unfolding list_step_all2_def apply clarify
  apply (frule_tac list_step_all_nth_lt_length)
  by auto

lemma list_step_all2_appendI:
  assumes \<open>list_step_all2 P xs ys\<close>
      and \<open>P (last xs) (last ys) (hd xs') (hd ys')\<close>
      and \<open>list_step_all2 P xs' ys'\<close>
    shows \<open>list_step_all2 P (xs @ xs') (ys @ ys')\<close>
  using assms(1) apply (drule_tac list_step_all2_lengthD)
  using assms(3) apply (drule_tac list_step_all2_lengthD)
  apply (cases \<open>xs = [] \<or> ys = []\<close>)
  subgoal 
    using assms(1,3) by fastforce
  subgoal
    apply (cases \<open>xs' = [] \<or> ys' = []\<close>)
    subgoal
      using assms(1) by fastforce
    subgoal
      unfolding list_step_all2_def apply safe
      subgoal by simp
      subgoal
        using assms unfolding list_step_all2_def apply auto
        apply (rule list_step_all_appendI)
        unfolding hd_zip last_zip by blast+
      .
    .
  .

lemma list_step_all2_append2I:
  assumes \<open>list_step_all2 P (xs @ [x]) (ys @ [y])\<close>
      and \<open>P x y x' y'\<close> 
    shows \<open>list_step_all2 P (xs @ [x, x']) (ys @ [y, y'])\<close>
  using assms unfolding list_step_all2_def apply auto
  by (frule_tac list_step_all_append2I, blast+)

lemma list_step_all2_append1I:
  assumes \<open>list_step_all2 P xs ys\<close>
      and \<open>P (last xs) (last ys) x y\<close>
    shows \<open>list_step_all2 P (xs ## x) (ys ## y)\<close>
  using assms unfolding list_step_all2_def apply (cases \<open>xs = []\<close>, auto)
  apply (rule_tac list_step_all_append1I, blast)
  by (simp add: last_zip)

lemma list_step_all2_append2E:
  assumes \<open>list_step_all2 P (xs @ [x, x']) (ys @ [y, y'])\<close>
    shows \<open>list_step_all2 P (xs @ [x]) (ys @ [y])\<close> and \<open>P x y x' y'\<close>
  using assms unfolding list_step_all2_def apply auto
  apply (frule_tac list_step_all_append2E, blast)
  apply (frule_tac list_step_all_append2E(2))
  by (simp add: last_zip)

lemma list_step_all2_append1E:
  assumes \<open>list_step_all2 P (xs @ [x]) (ys @ [y])\<close>
    shows \<open>list_step_all2 P xs ys\<close> and \<open>xs \<noteq> [] \<longrightarrow> P (last xs) (last ys) x y\<close>
  using assms unfolding list_step_all2_def apply auto
  apply (frule_tac list_step_all_append1E, blast)
  apply (frule_tac list_step_all_append1E(2))
  using last_zip by fastforce

lemma list_step_all2_inducts[consumes 1, case_names Empty Single Next]:
  assumes \<open>list_step_all2 P xs ys\<close>
      and Q_empty: \<open>Q [] []\<close>
      and Q_single: \<open>Q [hd xs] [hd ys]\<close>
      and Q_next: \<open>\<And>x y xs ys. \<lbrakk>length xs = length ys; xs \<noteq> []; ys \<noteq> []; Q xs ys; list_step_all2 P xs ys; P (last xs) (last ys) x y\<rbrakk> \<Longrightarrow> Q (xs ## x) (ys ## y)\<close>
    shows \<open>Q xs ys\<close>
proof -
  have length: \<open>length xs = length ys\<close>
    using assms(1) by (drule_tac list_step_all2_lengthD, linarith)
  show ?thesis 
    proof (cases \<open>xs = []\<close>)
      case True
      then show ?thesis using length Q_empty by simp
    next
      case False
      show ?thesis 
        using length False assms proof (induct rule: rev_nonempty_induct2)
          case (snoc x xs y ys)
          then show ?case 
            apply (frule_tac list_step_all2_append1E)
            apply (frule_tac list_step_all2_append1E(2))
            by auto
        qed simp
    qed
qed

lemma list_step_all2_impI:
  assumes \<open>list_step_all2 P xs ys\<close>
      and \<open>(\<And>x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2. P x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2 \<Longrightarrow> Q x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2)\<close>
    shows \<open>list_step_all2 Q xs ys\<close>
  using assms by (metis list_step_all2_length)

locale list_step_all2_lemmas =
    fixes f2 :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
      and g2 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes f_list_step_all2_g: \<open>f2 = list_step_all2 g2\<close>
begin

sublocale pair: list_step_all_lemmas \<open>\<lambda>xs. f2 (unzipL xs) (unzipR xs)\<close> \<open>\<lambda>x y. g2 (fst x) (snd x) (fst y) (snd y)\<close>
  apply standard
  unfolding f_list_step_all2_g 
  apply (subgoal_tac "\<And>xs. (\<lambda>xs. list_step_all2 g2 (unzipL xs) (unzipR xs)) xs =
    list_step_all (\<lambda>x y. g2 (fst x) (snd x) (fst y) (snd y)) xs")
  apply simp
  unfolding list_step_all2_def unzip_zip
  apply (induct_tac xs)
  apply (simp_all add: length_unzip)
  by (simp_all add: case_prod_beta' )

lemma empty[simp]: 
  \<open>f2 [] []\<close>
  unfolding f_list_step_all2_g by auto

lemma single[simp]: 
  \<open>f2 [x] [y]\<close>
  unfolding f_list_step_all2_g by auto

lemma pair: \<open>g2 s\<^sub>1 s\<^sub>2 s\<^sub>1' s\<^sub>2' \<longleftrightarrow> f2 [s\<^sub>1, s\<^sub>1'] [s\<^sub>2, s\<^sub>2']\<close>
  unfolding f_list_step_all2_g list_step_all2_pair by meson

lemma lengthD:
  assumes \<open>f2 xs ys\<close>
    shows \<open>length xs = length ys\<close>
  using assms unfolding f_list_step_all2_g list_step_all2_length by simp  

lemma appendI:
  assumes \<open>f2 xs ys\<close>
      and \<open>g2 (last xs) (last ys) (hd xs') (hd ys')\<close>
      and \<open>f2 xs' ys'\<close>
    shows \<open>f2 (xs @ xs') (ys @ ys')\<close>
  using assms list_step_all2_appendI f_list_step_all2_g by fastforce

lemma append2I:
  assumes \<open>f2 (xs @ [x]) (ys @ [y])\<close>
      and \<open>g2 x y x' y'\<close> 
    shows \<open>f2 (xs @ [x, x']) (ys @ [y, y'])\<close>
  using assms list_step_all2_append2I f_list_step_all2_g by fastforce

lemma append1I:
  assumes \<open>f2 xs ys\<close>
      and \<open>g2 (last xs) (last ys) x y\<close>
    shows \<open>f2 (xs ## x) (ys ## y)\<close>
  using assms list_step_all2_append1I f_list_step_all2_g by fastforce

lemma append2E:
  assumes \<open>f2 (xs @ [x, x']) (ys @ [y, y'])\<close>
    shows \<open>f2 (xs @ [x]) (ys @ [y])\<close> and \<open>g2 x y x' y'\<close>
  using assms unfolding f_list_step_all2_g
  using list_step_all2_append2E(1)  apply metis
  by (metis assms f_list_step_all2_g list_step_all2_append2E(2))  

lemma append1E:
  assumes \<open>f2 (xs ## x) (ys ## y)\<close>
    shows \<open>f2 xs ys\<close> and \<open>xs \<noteq> [] \<longrightarrow> g2 (last xs) (last ys) x y\<close>
  using assms list_step_all2_append1E(1) f_list_step_all2_g apply metis
  by (metis assms f_list_step_all2_g list_step_all2_append1E(2))  

lemma nth_lt_length:
  assumes \<open>f2 xs ys\<close>
      and \<open>i < length xs - Suc 0\<close>
    shows \<open>g2 (xs ! i) (ys ! i) (xs ! Suc i) (ys ! Suc i)\<close>
  using assms unfolding f_list_step_all2_g 
  using list_step_all2_nth_lt_length by blast


lemma length:
  \<open>f2 xs ys \<longleftrightarrow> (\<forall>i<length xs - Suc 0. g2 (xs ! i) (ys ! i) (xs ! Suc i) (ys ! Suc i)) \<and> length xs = length ys\<close>
  using f_list_step_all2_g list_step_all2_length by blast

lemma inducts[consumes 1, case_names Empty Single Next]:
  assumes \<open>f2 xs ys\<close>
      and \<open>Q [] []\<close>
      and \<open>Q [hd xs] [hd ys]\<close>
      and \<open>\<And>x y xs ys. \<lbrakk>length xs = length ys; xs \<noteq> []; ys \<noteq> []; Q xs ys; f2 xs ys; g2 (last xs) (last ys) x y\<rbrakk> \<Longrightarrow> Q (xs ## x) (ys ## y)\<close>
    shows \<open>Q xs ys\<close>
  apply (rule_tac P=g2 in list_step_all2_inducts)
  using assms unfolding f_list_step_all2_g by auto

end



lemma hd_single_0th: \<open>hd [a] = [a] ! 0\<close>
  by auto

lemma length_single_0: \<open>i < length [a] \<Longrightarrow> i = 0\<close>
  by auto

lemma trunc_length: \<open>i < length (\<pi>\<^sub>1 ## s\<^sub>1) \<Longrightarrow> i \<noteq> length \<pi>\<^sub>1 \<Longrightarrow> i < length \<pi>\<^sub>1\<close>
  by auto



lemma map_swapI:
  assumes \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>1' x\<close>
      and k_not_in: \<open>k \<notin> X\<close>
      and \<open>P (\<mu>1' k)\<close>
    shows \<open>P (\<mu>1 k)\<close>
  apply (insert assms)
  apply (erule ball_inE[of _ _ k])
  unfolding mem_Collect_eq apply assumption
  by simp

lemma map_eq_swapI:
  assumes \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>1' x\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>2 x = \<mu>2' x\<close>
      and k_not_in: \<open>k \<notin> X\<close>
      and \<open>\<mu>1' k = \<mu>2' k\<close>
    shows \<open>\<mu>1 k = \<mu>2 k\<close>
  apply (insert assms)
  apply (erule ball_inE[of _ _ k])
  unfolding mem_Collect_eq apply assumption
  apply (erule ball_inE[of _ _ k])
  unfolding mem_Collect_eq apply assumption
  by simp

lemma all_in_nested_image_eqI:
  assumes \<open>x \<in> g ` A\<close>
      and \<open>\<forall>x\<in>A. f1 (g x) = f2 (g x)\<close>
    shows \<open>f1 x = f2 x\<close>
  apply (insert assms)
  apply (erule imageE)
  subgoal for y
    apply (erule ball_inE[of _ _ y], assumption)
    by simp
  .

lemma Collect_eqE:
  \<open>{x. P x} = {x. Q x} \<Longrightarrow> \<forall>x. P x = Q x\<close>
  by auto


lemma append1_is_2: "[x] ## x' = [x, x']"
  by simp

lemma Cons1_is_2: "x # [x'] = [x, x']"
  by simp

lemmas hd_Cons = List.list.sel(1)

lemma hd_single_append1[simp]: \<open>hd ([x] ## x') = x\<close>
  unfolding append1_is_2 hd_Cons by clarify

lemma butlast_append2[simp]: "butlast (ys @ [y, y']) = (ys @ [y])"
  by (metis butlast_append butlast_snoc list.discI two_singl_Rcons)


(*
(* *)
abbreviation lnever :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" where "lnever U \<equiv> llist_all (\<lambda> a. \<not> U a)"

(* *)

lemma llast_last_llist_of: "lfinite xs \<Longrightarrow> llast xs = last (list_of xs)"
by (metis llast_llist_of llist_of_list_of)
*)
(* *)


lemma upt_map_conv_Cons:
  assumes \<open>i < j\<close>
    shows "map f [i..<j] = f i # map f [Suc i..<j]"
  using assms(1) by (simp add: upt_conv_Cons)

lemma upds_list:
  assumes \<open>(m) c = d\<close> and \<open>c \<notin> set as\<close>
    shows \<open>(m(as [\<mapsto>] bs)) c = d\<close>
  using assms(1) assms(2) by fastforce

lemma upds_list_eq:
  assumes \<open>c \<notin> set as\<close> and \<open>m\<^sub>1 c = m\<^sub>2 c\<close>
    shows \<open>(m\<^sub>1(as [\<mapsto>] bs)) c = (m\<^sub>2(as [\<mapsto>] bs)) c\<close>
  using assms by simp


lemma the_map_not_keyI: "c \<noteq> a \<Longrightarrow> the (m c) = v \<Longrightarrow> the ((m(a \<mapsto> b)) c) = v"
  by auto

lemma the_map_keyI: "the ((m(a \<mapsto> b)) a) = b"
  by auto

lemma the_map_write_read:
  assumes \<open>length a = length v\<close> 
      and \<open>distinct a\<close>
    shows \<open>map (the \<circ> \<mu>\<^sub>\<pi>(a [\<mapsto>] v)) a = v\<close>
  using assms apply (induct a v rule: list_induct2)
  by (simp_all add: fun_upd_comp)

lemma map_write_read:
  assumes \<open>length a = length v\<close> 
      and \<open>distinct a\<close>
    shows \<open>map (\<mu>\<^sub>\<pi>(a [\<mapsto>] v)) a = map Some v\<close>
  using assms by (induct a v rule: list_induct2, simp_all)
(*
lemma butlast_length_le1[simp]: "llength xs \<le> Suc 0 \<Longrightarrow> lbutlast xs = [[]]"
 by (metis One_nat_def antisym_conv2 enat_ile epred_1 epred_conv_minus 
iless_Suc_eq lbutlast_LNil le_zero_eq lfinite_conv_llength_enat llength_eq_0 
llength_lbutlast_lfinite lnull_def one_eSuc one_enat_def)

(* *)

lemma lappend_llist_of_inj: 
"length xs = length ys \<Longrightarrow> 
 lappend (llist_of xs) as = lappend (llist_of ys) bs \<longleftrightarrow> xs = ys \<and> as = bs"
apply(induct xs ys arbitrary: as bs rule: list_induct2) by auto


(* More convenient corecusor for lazy lists: *)

definition ccorec_llist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b llist) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b llist"
where "ccorec_llist isn h ec e t \<equiv> 
    corec_llist isn (\<lambda>a. if ec a then lhd (e a) else h a) ec (\<lambda>a. case e a of b $ a' \<Rightarrow> a') t"

lemma llist_ccorec_LNil: "isn a \<Longrightarrow> ccorec_llist isn h ec e t a = [[]]"
unfolding ccorec_llist_def llist.corec(1) by auto

lemma llist_ccorec_LCons: 
"\<not> lnull (e a) \<Longrightarrow> \<not> isn a \<Longrightarrow> 
ccorec_llist isn h ec e t a = (if ec a then e a else h a $ ccorec_llist isn h ec e t (t a))"
unfolding ccorec_llist_def llist.corec(2)  
by (cases " e a", auto simp: lnull_def) 

lemmas llist_ccorec = llist_ccorec_LNil llist_ccorec_LCons
*)

(* 
thm list_all_nth[no_vars]

lemma llist_all_lnth: "llist_all P xs = (\<forall>n<llength xs. P (lnth xs n))"
by (metis in_lset_conv_lnth llist.pred_set)


 *)

definition "takeUntil pred xs \<equiv> 
  append (takeWhile (\<lambda>x. \<not> pred x) xs) [hd (dropWhile (\<lambda>x. \<not> pred x) xs)]"

definition "dropUntil pred xs \<equiv> tl (dropWhile (\<lambda>x. \<not> pred x) xs)"

lemma append_takeUntil_dropUntil: 
"\<exists>x\<in>set xs. pred x \<Longrightarrow> append (takeUntil pred xs) (dropUntil pred xs) = xs"
by (simp add: dropUntil_def takeUntil_def) 

lemma takeUntil_not_Nil: 
assumes "\<exists>x\<in>set xs. pred x"  
shows "takeUntil pred xs \<noteq> []"
by (simp add: takeUntil_def) 

lemma takeUntil_ex_butlast: 
assumes "\<exists>x\<in>set xs. pred x" "y \<in> set (butlast (takeUntil pred xs))"
shows "\<not> pred y"
using assms unfolding takeUntil_def 
by (metis butlast_snoc set_takeWhileD) 

lemma takeUntil_never_butlast: 
assumes "\<exists>x\<in>set xs. pred x" 
shows "never pred (butlast (takeUntil pred xs))"
by (metis butlast_snoc lmember_equiv_list_all set_takeWhileD takeUntil_def)

lemma takeUntil_last: 
assumes "\<exists>x\<in>set xs. pred x" 
shows "pred (last (takeUntil pred xs))"
using assms unfolding takeUntil_def 
by (metis dropWhile_eq_Nil_conv hd_dropWhile last_snoc) 

lemma takeUntil_last_butlast: 
assumes "\<exists>x\<in>set xs. pred x" 
shows "takeUntil pred xs = append (butlast (takeUntil pred xs)) [last (takeUntil pred xs)]"
by (simp add: assms takeUntil_not_Nil)

(* INFRASTRUCTURE FOR FINITE-INFINITE SHIFT IN UNWINDING RESULTS *)
(*
declare lconcat_eq_LNil_iff[simp del]

definition "ltakeUntil pred xs \<equiv> 
  list_of (lappend (ltakeWhile (\<lambda>x. \<not> pred x) xs) [[lhd (ldropWhile (\<lambda>x. \<not> pred x) xs)]])"

definition "ldropUntil pred xs \<equiv> ltl (ldropWhile (\<lambda>x. \<not> pred x) xs)"

lemma lappend_ltakeUntil_ldropUntil: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> lappend (llist_of (ltakeUntil pred xs)) (ldropUntil pred xs) = xs"
by (simp add: lappend_snocL1_conv_LCons2 ldropUntil_def lfinite_ltakeWhile ltakeUntil_def)

lemma ltakeUntil_not_Nil: 
assumes "\<exists>x\<in>lset xs. pred x"  
shows "ltakeUntil pred xs \<noteq> []"
by (simp add: assms lfinite_ltakeWhile list_of_lappend ltakeUntil_def)

lemma ltakeUntil_ex_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" "y \<in> set (butlast (ltakeUntil pred xs))"
shows "\<not> pred y"
using assms unfolding ltakeUntil_def 
by (metis (mono_tags, lifting) butlast_snoc lfinite_LConsI lfinite_LNil lfinite_ltakeWhile 
list_of_LCons list_of_LNil list_of_lappend llist_of_list_of lset_llist_of lset_ltakeWhileD) 

lemma ltakeUntil_never_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "never pred (butlast (ltakeUntil pred xs))"
by (meson assms lmember_equiv_list_all ltakeUntil_ex_butlast)

lemma ltakeUntil_last: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "pred (last (ltakeUntil pred xs))"
using assms unfolding ltakeUntil_def 
by (metis lfinite_LConsI lfinite_LNil lfinite_lappend lfinite_ltakeWhile lhd_ldropWhile 
 llast_lappend_LCons llast_llist_of llast_singleton llist_of_list_of)

lemma ltakeUntil_last_butlast: 
assumes "\<exists>x\<in>lset xs. pred x" 
shows "ltakeUntil pred xs = append (butlast (ltakeUntil pred xs)) [last (ltakeUntil pred xs)]"
by (simp add: assms ltakeUntil_not_Nil)


(* *)

lemma llist_all_lappend: "lfinite xs \<Longrightarrow> 
llist_all pred (lappend xs ys) \<longleftrightarrow> llist_all pred xs \<and> llist_all pred ys"
unfolding llist.pred_set by (auto simp add: in_lset_lappend_iff) 

lemma llist_all_lappend_llist_of: 
"llist_all pred (lappend (llist_of xs) ys) \<longleftrightarrow> list_all pred xs \<and> llist_all pred ys"
by (metis lfinite_llist_of list_all_iff llist.pred_set llist_all_lappend lset_llist_of) 

(* *)

primcorec lsplit where 
"lsplit pred xs = 
 (if (\<exists>x\<in>lset xs. pred x)
    then LCons (ltakeUntil pred xs) (lsplit pred (ldropUntil pred xs))
    else [[]])"

declare lsplit.ctr[simp]

term lconcat

lemma infinite_split[simp]: 
"infinite {x \<in> lset xs. pred x} \<Longrightarrow> lsplit pred xs = LCons (ltakeUntil pred xs) (lsplit pred (ldropUntil pred xs))"
using lsplit.ctr(2) not_finite_existsD by force

lemma ltakeUntil_LCons1[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred x \<Longrightarrow> ltakeUntil pred (LCons x xs) = x # ltakeUntil pred xs"
unfolding ltakeUntil_def apply auto 
by (metis lfinite_LConsI lfinite_LNil lfinite_lappend lfinite_ltakeWhile list_of_LCons)

lemma ldropUntil_LCons1[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred x \<Longrightarrow> 
  ldropUntil pred (LCons x xs) = ldropUntil pred xs"
by (simp add: ldropUntil_def)

lemma ltakeUntil_LCons2[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> pred x \<Longrightarrow> ltakeUntil pred (LCons x xs) = [x]"
unfolding ltakeUntil_def by auto

lemma ldropUntil_LCons2[simp]: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> pred x \<Longrightarrow> ldropUntil pred (LCons x xs) = xs"
unfolding ldropUntil_def by auto

lemma ltakeUntil_tl1[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred (lhd xs) \<Longrightarrow> ltakeUntil pred (ltl xs) = tl (ltakeUntil pred xs)"
by (smt (verit, ccfv_SIG) eq_LConsD list.sel(3) lset_cases ltakeUntil_LCons1)

lemma ldropUntil_tl1[simp]: 
"\<exists>x\<in>lset xs. pred x \<Longrightarrow> \<not> pred (lhd xs) \<Longrightarrow> ldropUntil pred (ltl xs) = ldropUntil pred xs"
by (metis bex_empty ldropUntil_def ldropWhile_LCons llist.exhaust_sel llist.set(1))

lemma ltakeUntil_tl2[simp]: 
"xs \<noteq> [[]] \<Longrightarrow> pred (lhd xs) \<Longrightarrow> tl (ltakeUntil pred xs) = []"
by (metis lappend_code(1) lfinite_LNil list.sel(3) list_of_LCons list_of_LNil ltakeUntil_def ltakeWhile_eq_LNil_iff)

lemma ldropUntil_tl2[simp]: 
"xs \<noteq> [[]] \<Longrightarrow> pred (lhd xs) \<Longrightarrow> ldropUntil pred xs = ltl xs"
by (metis lappend_code(1) lappend_ltakeWhile_ldropWhile ldropUntil_def ltakeWhile_eq_LNil_iff)

lemma lconcat_lsplit_not_lfinite: 
"\<not> lfinite (lfilter pred xs) \<Longrightarrow> xs = lconcat (lmap llist_of (lsplit pred xs))"
apply(coinduction arbitrary: xs) apply auto
  subgoal  
    by (metis (full_types) image_subset_iff llist.set_sel(1) lnull_imp_lfinite lnull_lfilter 
  lnull_llist_of lsplit.simps(2) lsplit.simps(3) ltakeUntil_not_Nil mem_Collect_eq) 
  subgoal by (smt (verit) lappend_ltakeUntil_ldropUntil lhd_lappend lhd_lconcat llist.map_disc_iff 
   llist.map_sel(1) llist_of.simps(1) llist_of_inject 
   lnull_def lnull_imp_lfinite lnull_lfilter lsplit.simps(2) lsplit.simps(3) ltakeUntil_not_Nil)
  subgoal for xs apply(subgoal_tac "xs \<noteq> [[]]")
    subgoal apply(subgoal_tac "\<not> lfinite (lfilter pred (ltl xs)) \<and> (\<exists>x\<in>lset xs. pred x)") 
      subgoal apply(cases "pred (lhd xs)") apply simp
      apply (meson ltakeUntil_not_Nil) 
      by (smt (verit) \<open>\<And>xsa. \<lbrakk>\<not> lfinite (lfilter pred xsa); llist_of ` lset (lsplit pred xsa) \<subseteq> {xs. lnull xs}\<rbrakk> \<Longrightarrow> lnull xsa\<close> eq_LConsD lappend_eq_LNil_iff lappend_ltl ldropUntil_tl1 lhd_lappend lhd_lconcat llist.expand llist.map_disc_iff llist.map_sel(1) lnull_def lnull_lconcat lnull_llist_of lset_cases lset_lmap lsplit.ctr(2) ltakeUntil_not_Nil ltakeUntil_tl1 ltl_lconcat ltl_llist_of ltl_lmap)
      subgoal apply (intro conjI) 
        subgoal by (metis lfilter_LCons lfinite_code(2) lhd_LCons_ltl)
        subgoal by (meson lnull_imp_lfinite lnull_lfilter) . .
    subgoal by auto .   
  subgoal by (metis lfilter_LCons lfinite_code(2) lhd_LCons_ltl) .

lemma LCons_lfilter_ldropUntil: "y $ ys = lfilter pred xs \<Longrightarrow> ys = lfilter pred (ldropUntil pred xs)"
unfolding ldropUntil_def apply auto 
by (metis (mono_tags, lifting) comp_apply eq_LConsD ldropWhile_cong lfilter_eq_LCons)

lemma lfinite_lsplit: 
assumes "lfinite (lfilter pred xs)" 
shows "lfinite (lsplit pred xs)"
proof-
  {fix ys assume "lfinite ys"  "ys = lfilter pred xs"
   hence ?thesis proof(induct arbitrary: xs)
     case lfinite_LNil
     then show ?case by (metis lfilter_empty_conv lnull_imp_lfinite lsplit.disc(1))
   next
     case (lfinite_LConsI ys y xs)
     then show ?case apply(cases "\<exists>x\<in>lset xs. pred x")
       subgoal by auto (meson LCons_lfilter_ldropUntil)
       subgoal using lnull_imp_lfinite lsplit.disc(1) by blast .      
   qed 
  }
  thus ?thesis using assms by auto
qed
 
lemma lconcat_lsplit_lfinite: 
assumes "lfinite (lfilter pred xs)"
shows "\<exists>ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"
proof-
  {fix ys assume "lfinite ys"  "ys = lfilter pred xs"
   hence ?thesis proof(induct arbitrary: xs)
     case lfinite_LNil
     then show ?case 
       by (metis lappend_code(1) lconcat_LNil llist.disc(1) llist.simps(12) lnull_lfilter lsplit.ctr(1))
   next
     case (lfinite_LConsI ys y xs)
     then show ?case apply(cases "\<exists>x\<in>lset xs. pred x")
       subgoal by simp (smt (verit) LCons_lfilter_ldropUntil lappend_assoc lappend_ltakeUntil_ldropUntil)
       subgoal by simp .
   qed 
  }
  thus ?thesis using assms by auto
qed

lemma lconcat_lsplit: 
"\<exists>ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"
proof(cases "lfinite (lfilter pred xs)")
  case True
  show ?thesis using lconcat_lsplit_lfinite[OF True] .
next
  case False
  show ?thesis apply(rule exI[of _ LNil]) 
  using lconcat_lsplit_not_lfinite[OF False] by simp
qed

definition "lsplitEnd pred xs \<equiv> SOME ys. xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) ys \<and> (\<forall>y\<in>lset ys. \<not> pred y)"

lemma lsplitEnd: 
"xs = lappend (lconcat (lmap llist_of (lsplit pred xs))) (lsplitEnd pred xs) \<and> 
(\<forall>y\<in>lset (lsplitEnd pred xs). \<not> pred y)"
unfolding lsplitEnd_def apply(rule someI_ex) using lconcat_lsplit .

lemmas lsplit_lsplitEnd = lsplitEnd[THEN conjunct1]
lemmas lset_lsplitEnd = lsplitEnd[THEN conjunct2, rule_format]

lemma lsublist_lsplit: 
assumes "i < llength (lsplit pred xs)"
shows "lsublist (llist_of (lnth (lsplit pred xs) i)) xs"
using lnth_lconcat_lconcat_lsublist[OF lsplit_lsplitEnd assms] . 

lemma lsublist_lsplit2: 
assumes "Suc i < llength (lsplit pred xs)"
shows "lsublist (llist_of (append (lnth (lsplit pred xs) i) (lnth (lsplit pred xs) (Suc i)))) xs"
using lnth_lconcat_lconcat_lsublist2[OF lsplit_lsplitEnd assms] . 

(*  *)

lemma llist_all_conduct: 
"X xs \<Longrightarrow> 
(\<And>xs. X xs \<Longrightarrow> \<not> lnull xs \<Longrightarrow> P (lhd xs) \<and> (X (ltl xs) \<or> llist_all P (ltl xs))) \<Longrightarrow>
llist_all P xs"
unfolding llist.pred_rel apply(coinduct rule: llist_all2_coinduct[of "\<lambda>xs ys. X xs \<and> xs = ys"])
by (auto simp: eq_onp_same_args)

lemma lsplit_main: 
"llist_all (\<lambda>zs. zs \<noteq> [] \<and> list_all (\<lambda>z. \<not> pred z) (butlast zs) \<and> pred (last zs)) 
           (lsplit pred xs)"
proof-
  {fix ys assume "\<exists>xs. ys = (lsplit pred xs)"
   hence "llist_all (\<lambda>zs. zs \<noteq> [] \<and> list_all (\<lambda>z. \<not> pred z) (butlast zs) \<and> pred (last zs))  ys"
   apply(coinduct rule: llist_all_conduct[where X = "\<lambda>ys. \<exists>xs. ys = (lsplit pred xs)"]) apply auto
   apply(meson ltakeUntil_not_Nil)
   apply (meson lmember_equiv_list_all ltakeUntil_ex_butlast)
   by (meson ltakeUntil_last)
  }
  thus ?thesis by auto
qed

(* lemma llist_all_lnth: "llist_all P xs = (\<forall>i<llength xs. P (lnth xs i))"
unfolding llist.pred_set apply simp by (metis in_lset_conv_lnth)
*)

lemma lsplit_main_lset:  
assumes "ys \<in> lset (lsplit pred xs)"
shows "ys \<noteq> [] \<and> 
       list_all (\<lambda>z. \<not> pred z) (butlast ys) \<and> 
       pred (last ys)" 
using assms lsplit_main[of pred] unfolding llist.pred_set by auto

lemma lsplit_main_lnth:  
assumes "i < llength (lsplit pred xs)"
shows "lnth (lsplit pred xs) i \<noteq> [] \<and> 
       list_all (\<lambda>z. \<not> pred z) (butlast (lnth (lsplit pred xs) i)) \<and> 
       pred (last (lnth (lsplit pred xs) i))" 
using assms lsplit_main[of pred] unfolding llist_all_lnth by auto

lemma hd_lhd_lsplit: "\<exists>x\<in>lset xs. pred x \<Longrightarrow> hd (lhd (lsplit pred xs)) = lhd xs"
by (metis lappend_ltakeUntil_ldropUntil lhd_lappend lhd_llist_of lnull_llist_of lsplit.simps(3) ltakeUntil_not_Nil)

lemma lprefix_lsplit: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "lprefix (llist_of (lhd (lsplit pred xs))) xs"
by (metis assms lappend_ltakeUntil_ldropUntil lprefix_lappend lsplit.simps(3)) 

lemma lprefix_lsplit_lbutlast: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "lprefix (llist_of (butlast (lhd (lsplit pred xs)))) (lbutlast xs)"
using lprefix_lsplit[OF assms] unfolding llist_of_butlast 
using lprefix_lbutlast by blast

lemma set_lset_lsplit: 
assumes "ys \<in> lset (lsplit pred xs)"
shows "set ys \<subseteq> lset xs"
proof-
  have "set ys \<subseteq> lset (lconcat (lmap llist_of (lsplit pred xs)))" 
  using su_lset_lconcat_llist_of[OF assms ] .   
  also have "\<dots> \<subseteq> lset xs" 
  by (metis lconcat_lsplit lset_lappend1)
  finally show ?thesis .
qed

lemma set_lnth_lsplit: 
assumes "i < llength (lsplit pred xs)"  
shows "set (lnth (lsplit pred xs) i) \<subseteq> lset xs"
by (meson assms in_lset_conv_lnth set_lset_lsplit)

(* *)

(*  *)

declare lmap_eq_LNil[simp]

lemma llength_lbutlast[simp]: "llength (lbutlast tr) = llength tr - 1"
by (metis idiff_0 idiff_infinity lbutlast_LNil llength_LNil llength_lbutlast_lfinite 
     llength_lbutlast_not_lfinite not_lfinite_llength)

lemma lnth_lbutlast: "i < llength xs - 1 \<Longrightarrow> lnth (lbutlast xs) i = lnth xs i"
unfolding lbutlast_def apply(auto split: if_splits)  
by (metis enat_ord_simps(2) llength_lbutlast llength_llist_of llist_of_butlast 
   llist_of_list_of nth_butlast nth_list_of)

lemma llist_eq_cong: 
assumes "llength xs = llength ys" "\<And>i. i < llength xs \<Longrightarrow> lnth xs i = lnth ys i"
shows "xs = ys"
proof-
  have "llength xs = llength ys \<and> (\<forall>i. i < llength xs \<longrightarrow> lnth xs i = lnth ys i)"
  using assms by auto
  thus ?thesis apply(coinduct rule: llist.coinduct) apply auto  
  apply (metis i0_less lhd_conv_lnth llength_eq_0 zero_enat_def)
  apply (metis epred_llength)
  by (metis eSuc_enat ileI1 iless_Suc_eq lhd_LCons_ltl llength_LCons lnth_ltl)
qed

lemmas llist_eq_lnth = llist_eq_cong


lemma llist_cases: "llength xs = \<infinity> \<or> (\<exists>ys. xs = llist_of ys)"
by (metis llist_of_list_of not_lfinite_llength)

declare llist_of_eq_LNil_conv[simp]

lemma ldrop_Suc: "n < llength xs \<Longrightarrow> ldrop (enat n) xs = LCons (lnth xs n) (ldrop (enat (Suc n)) xs)" 
apply(rule llist_eq_cong)
  subgoal apply(subst llength_ldrop) apply simp apply(subst llength_ldrop) 
  using llist_cases[of xs] by (auto simp: eSuc_enat) 
  subgoal for i apply(subst lnth_ldrop) 
    subgoal by (metis add.commute ldrop_eq_LNil ldrop_ldrop linorder_not_less)
    subgoal apply(subst lnth_LCons)  apply (auto split: nat.splits) apply(subst lnth_ldrop)
      subgoal apply(subst (asm) llength_ldrop) 
      by (metis (full_types) \<open>\<lbrakk>enat n < llength xs; enat i < llength (ldrop (enat n) xs)\<rbrakk> \<Longrightarrow> 
       enat n + enat i < llength xs\<close> add_Suc_shift llength_ldrop plus_enat_simps(1))
      subgoal by auto . . .
    
lemma lappend_ltake_lnth_ldrop: "n < llength xs \<Longrightarrow>
  lappend (ltake (enat n) xs) (LCons (lnth xs n) (ldrop (enat (Suc n)) xs)) = xs"
by (simp add: ldrop_enat ldropn_Suc_conv_ldropn) 

lemma enat_ls_minius_1: "enat i < j - 1 \<Longrightarrow>  enat i < j"
  by (metis One_nat_def betw.ctr(1) betw.ctr(2) idiff_enat_0_right iless_Suc_eq 
linorder_not_less llength_LCons llength_betw one_enat_def order_less_imp_le)

lemma ltake_eq_LNil: "ltake i tr = [[]] \<longleftrightarrow> i = 0 \<or> tr = [[]]" 
by (metis LNil_eq_ltake_iff)


(* *)

lemma lfilter_lappend_llist_of:
  "lfilter P (lappend (llist_of xs) ys) = lappend (llist_of (filter P xs)) (lfilter P ys)"
  by simp


find_theorems lsplit
term lsplit


find_theorems ltakeUntil butlast
term ltakeUntil


(* *)

lemma lenth_ltakeUntil_ge_0: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "length (ltakeUntil pred xs) > 0"
using ltakeUntil_not_Nil[OF assms] by auto

find_theorems ltakeUntil LCons

lemma lenth_ltakeUntil_eq_1: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "length (ltakeUntil pred xs) = Suc 0 \<longleftrightarrow> pred (lhd xs)"
proof-
  obtain x xss where xs: "xs = LCons x xss" 
  using assms by (cases xs, auto)
  hence x: "x = lhd xs" by auto
  show ?thesis unfolding xs 
  using ltakeUntil_LCons2[OF assms, of x] x 
  by (smt (verit, del_insts) assms diff_Suc_1 eq_LConsD lappend_ltakeUntil_ldropUntil 
  length_Suc_conv_rev length_butlast length_tl lenth_ltakeUntil_ge_0 list.size(3) lnth_0 
  lnth_lappend_llist_of ltakeUntil_last ltakeUntil_last_butlast ltakeUntil_tl2 nth_append_length xs)
qed

lemma lenth_ltakeUntil_Suc: 
assumes "\<exists>x\<in>lset xs. pred x" "\<not> pred (lhd xs)"
shows "length (ltakeUntil pred xs) = Suc (length (ltakeUntil pred (ltl xs)))"
proof-
  obtain x xss where xs: "xs = LCons x xss" 
  using assms by (cases xs, auto)
  hence x: "x = lhd xs" and xss: "xss = ltl xs" by auto
  hence 0: "\<exists>x\<in>lset xss. pred x"  
  by (metis assms(1) assms(2) insertE lset_LCons xs)
  show ?thesis unfolding xs 
  unfolding ltakeUntil_LCons1[OF 0 assms(2), unfolded x[symmetric]] by simp
qed

(* *)

definition theN where 
"theN pred xs \<equiv> length (ltakeUntil pred xs) - 1"

lemma theN_eq_0: 
assumes "\<exists>x\<in>lset xs. pred x"
shows "theN pred xs = 0 \<longleftrightarrow> pred (lhd xs)"
using assms unfolding theN_def 
by (metis Suc_pred diff_Suc_1 lenth_ltakeUntil_eq_1 lenth_ltakeUntil_ge_0)

lemma theN_eq_0': 
assumes "\<not> lnever pred xs"
shows "theN pred xs = 0 \<longleftrightarrow> pred (lhd xs)"
apply(rule theN_eq_0)
using assms by (simp add: llist.pred_set)

lemma theN_Suc: 
assumes "\<exists>x\<in>lset xs. pred x" and "\<not> pred (lhd xs)"
shows "theN pred xs = Suc (theN pred (ltl xs))"
using assms unfolding theN_def 
by (smt (verit, best) Suc_pred diff_Suc_1 length_greater_0_conv lenth_ltakeUntil_Suc 
   lenth_ltakeUntil_eq_1 list.size(3))

lemma theN_Suc': 
assumes "\<not> lnever pred xs" and "\<not> pred (lhd xs)"
shows "theN pred xs = Suc (theN pred (ltl xs))"
apply(rule theN_Suc) using assms by (auto simp: llist.pred_set)

lemma theN_append: 
assumes "\<not> lnever pred xs" and "never pred ys"
shows "theN pred (lappend (llist_of ys) xs) = length ys + theN pred xs"
using assms apply(induct ys, auto simp add: llist_all_lappend_llist_of theN_Suc') .

(* *)

definition theNC where 
"theNC xss \<equiv> theN (\<lambda>xs. xs \<noteq> []) xss"

lemma theNC_eq_0: 
assumes "\<exists>xs\<in>lset xss. xs \<noteq> []"
shows "theNC xss = 0 \<longleftrightarrow> lhd xss \<noteq> []"
using assms unfolding theNC_def 
by (simp add: theN_eq_0)

lemma theNC_Suc: 
assumes "\<exists>xs\<in>lset xss. xs \<noteq> []" and "lhd xss = []"
shows "theNC xss = Suc (theNC (ltl xss))"
using assms unfolding theNC_def  
  by (simp add: theN_Suc) 

lemma theNC_LCons_notNil: "xs \<noteq> [] \<Longrightarrow> theNC (xs $ xss) = 0"
by (simp add: theNC_eq_0)

lemma theNC_LCons_Nil: 
"(\<exists>ys\<in>lset xss. ys \<noteq> []) \<Longrightarrow> xs = [] \<Longrightarrow> theNC (xs $ xss) = Suc (theNC xss)"
by (simp add: theNC_Suc)



(******)
(* Turns: *)

datatype turn = L | R

fun switch where "switch L = R" | "switch R = L"

instantiation turn :: wellorder 
begin 
  definition less_eq_turn :: "turn \<Rightarrow> turn \<Rightarrow> bool" where 
  "less_eq_turn trn trn' \<longleftrightarrow> trn = trn' \<or> trn' = R"
  definition less_turn :: "turn \<Rightarrow> turn \<Rightarrow> bool" where 
  "less_turn trn trn' \<longleftrightarrow> trn = L \<and> trn' = R"
  instance apply standard unfolding less_eq_turn_def less_turn_def  
  using switch.cases by auto 
end (* instantiation *)

(* A well-founded relation involving taking turns: *)

definition TWW :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" where 
"TWW \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
  trn < trn' \<or> 
  trn = trn' \<and> (trn = L \<and> trn' = L \<and> wL < wL' \<or> trn = R \<and> trn' = R \<and> wR < wR')}"


lemma wf_TWW: "wf TWW"
proof-     
  define WL :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" 
  where "WL \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
                  trn = L \<and> trn' = L \<and> wL < wL'}"
  have "WL \<subseteq> inv_image {(w,w') . w < w'} (\<lambda>(trn,wL,wR). wL)"
  unfolding WL_def inv_image_def by auto
  hence wfWL: "wf WL" using wf wf_inv_image wf_subset by blast

  define WR :: "((turn \<times> enat \<times> enat) \<times> (turn \<times> enat \<times> enat)) set" 
  where "WR \<equiv> {((trn,wL,wR), (trn',wL',wR')) | trn wL wR trn' wL' wR' . 
                  trn = R \<and> trn' = R \<and> wR < wR'}"
  have "WR \<subseteq> inv_image {(w,w') . w < w'} (\<lambda>(trn,wL,wR). wR)"
  unfolding WR_def inv_image_def by auto
  hence wfWR: "wf WR" using wf wf_inv_image wf_subset by blast

  have wfWW: "wf (WL \<union> WR)" apply(rule wf_Un) 
  using wfWL wfWR unfolding WL_def WR_def by auto
  define f where "f \<equiv> \<lambda>(trn::turn,wL::enat,wR::enat). (trn,(trn,wL,wR))"
  have TWW: "TWW = inv_image (lex_prod {(trn::turn,trn') . trn < trn'} (WL \<union> WR)) f"
  unfolding TWW_def WL_def WR_def inv_image_def f_def by auto

  show ?thesis  unfolding TWW  
  using wf wfWW by blast
qed


lemma \<mu>64_not_in_setI:
  assumes \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close> 
      and k_not_in: \<open>k \<notin> X\<close> \<open>(k + 1) \<notin> X\<close> \<open>(k + 2) \<notin> X\<close> \<open>(k + 3) \<notin> X\<close> \<open>(k + 4) \<notin> X\<close> \<open>(k + 5) \<notin> X\<close> 
                    \<open>(k + 6) \<notin> X\<close> \<open>(k + 7) \<notin> X\<close>
    shows \<open>\<mu>1 k = \<mu>2 k \<and> \<mu>1 (k + 1) = \<mu>2 (k + 1) \<and> \<mu>1 (k + 2) = \<mu>2 (k + 2) \<and> 
           \<mu>1 (k + 3) = \<mu>2 (k + 3) \<and> \<mu>1 (k + 4) = \<mu>2 (k + 4) \<and> \<mu>1 (k + 5) = \<mu>2 (k + 5) \<and> 
           \<mu>1 (k + 6) = \<mu>2 (k + 6) \<and> \<mu>1 (k + 7) = \<mu>2 (k + 7)\<close>
using k_not_in assms(1) proof safe
  assume \<open>k \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 k = \<mu>2 k\<close>
      apply (erule_tac ball_inE[of _ _ k])
      by (rule CollectI)

  assume \<open>k + 1 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 1) = \<mu>2 (k + 1)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 1\<close>])
      by (rule CollectI)

  assume \<open>k + 2 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 2) = \<mu>2 (k + 2)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 2\<close>])
      by (rule CollectI)

  assume \<open>k + 3 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 3) = \<mu>2 (k + 3)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 3\<close>])
      by (rule CollectI)

  assume \<open>k + 4 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 4) = \<mu>2 (k + 4)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 4\<close>])
      by (rule CollectI)

  assume \<open>k + 5 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 5) = \<mu>2 (k + 5)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 5\<close>])
      by (rule CollectI)

  assume \<open>k + 6 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 6) = \<mu>2 (k + 6)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 6\<close>])
      by (rule CollectI)

  assume \<open>k + 7 \<notin> X\<close> and \<open>\<forall>x\<in>{a. a \<notin> X}. \<mu>1 x = \<mu>2 x\<close>
    thus \<open>\<mu>1 (k + 7) = \<mu>2 (k + 7)\<close>
      apply (erule_tac ball_inE[of _ _ \<open>k + 7\<close>])
      by (rule CollectI)
  qed

lemma ib_shrink[intro]:"llength ib = \<infinity> \<Longrightarrow> llength (ltl ib) = \<infinity>"
  by (metis epred_Infty epred_llength)
*)
lemma set_neq_exists: \<open>(\<exists>x. x \<notin> A \<and> x \<in> B) \<Longrightarrow> A \<noteq> B\<close>
  by auto

lemma restrict_eqI[intro]:
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> m\<^sub>1 x = m\<^sub>2 x\<close>
    shows \<open>m\<^sub>1 |` A = m\<^sub>2 |` A\<close>
  using assms unfolding restrict_map_def by auto

lemma restrict_eqE[elim]:
  assumes \<open>m\<^sub>1 |` A = m\<^sub>2 |` A\<close>
      and \<open>(\<And>x. x \<in> A \<Longrightarrow> m\<^sub>1 x = m\<^sub>2 x) \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding restrict_map_def fun_eq_iff
  apply (simp split: if_splits)
  apply (rule assms(2))
  subgoal for x 
    apply (elim allE[of _ x])
    by simp
  .

(*
lemma restrict_forall_eqE'[elim]:
  assumes \<open>m\<^sub>1 |` A\<^sub>1 = m\<^sub>2 |` A\<^sub>2\<close> and \<open>A\<^sub>2 = A\<^sub>1\<close>
    shows \<open>\<forall>x \<in> A\<^sub>1. m\<^sub>1 x = m\<^sub>2 x\<close>
  apply safe
  apply (insert assms, simp)
  by (drule restrict_eqE)

lemma restrict_forall_eqE[elim]:
  assumes \<open>m\<^sub>1 |` A = m\<^sub>2 |` A\<close>
    shows \<open>\<forall>x \<in> A. m\<^sub>1 x = m\<^sub>2 x\<close>
  apply safe
  apply (insert assms)
  by (drule restrict_eqE)
*)
lemmas in_ssubst = ssubst[of _ _ \<open>\<lambda>x. _ \<in> x\<close>]

lemma less_Suc0E: 
  assumes \<open>i < Suc 0\<close> and \<open>i = 0 \<Longrightarrow> P\<close>
    shows P 
  apply (rule assms(2))
  using assms(1) by auto

lemma restrict_eqI'[intro]:
  assumes \<open>\<And>x. x \<in> A\<^sub>1 \<Longrightarrow> m\<^sub>1 x = m\<^sub>2 x\<close> and \<open>A\<^sub>2 = A\<^sub>1\<close>
    shows \<open>m\<^sub>1 |` A\<^sub>1 = m\<^sub>2 |` A\<^sub>2\<close>
  apply (subst assms(2)) 
  using assms(1) by (rule restrict_eqI)


lemma restrict_map_image[simp]: "Y |` X ` X = Y ` X"
  by simp

lemma ball_insert_eqI[intro]:
  assumes "\<forall>x\<in>X. m1 x = m2 x" and \<open>m1 x = m2 x\<close>
    shows "\<forall>x\<in>insert x X. m1 x = m2 x"
proof (intro ballI)
  fix y assume \<open>y \<in> insert x X\<close> thus \<open>m1 y = m2 y\<close>
  proof (elim insertE ssubst)
    show \<open>m1 x = m2 x\<close> using assms(2) .
  next
    assume \<open>y \<in> X\<close> thus \<open>m1 y = m2 y\<close> 
      using assms(1) by (elim ball_inE)
  qed
qed

lemma ball_singleton_eqE[elim]:
  assumes \<open>\<forall>x\<in>{x}. m1 x = m2 x\<close>
      and "\<lbrakk>m1 x = m2 x\<rbrakk> \<Longrightarrow> P"
    shows P
proof (intro assms(2))
  show \<open>m1 x = m2 x\<close>
    using assms apply (elim ball_inE)
    by (rule insertI1)
qed

lemma ball_insert_eqE[elim]:
  assumes \<open>\<forall>x\<in>insert x X. m1 x = m2 x\<close>
      and "\<lbrakk>\<forall>x\<in>X. m1 x = m2 x; m1 x = m2 x\<rbrakk> \<Longrightarrow> P"
    shows P
proof (intro assms(2) ballI)
  fix y assume \<open>y \<in> X\<close> thus \<open>m1 y = m2 y\<close>
    using assms apply (elim ball_inE)
    by (rule insertI2)
next
  show \<open>m1 x = m2 x\<close>
    using assms apply (elim ball_inE)
    by (rule insertI1)
qed

lemma restrict_in_eqE: 
  assumes "\<mu>\<^sub>1 |` X\<^sub>1 = \<mu>\<^sub>2 |` X\<^sub>2" and \<open>x \<in> X\<^sub>1\<close> and  \<open>x \<in> X\<^sub>2\<close> and "\<lbrakk>\<mu>\<^sub>1 x = \<mu>\<^sub>2 x\<rbrakk> \<Longrightarrow> P"
    shows P
  using assms(1-3) unfolding restrict_map_def fun_eq_iff apply (elim allE[of _ x])
  apply simp
  by (rule assms(4))

lemma image_set_eqI: "(\<And>z. z \<in> X \<Longrightarrow> x z = y z) \<Longrightarrow> (x ` X = y ` X)"
  by simp

lemma map_upds_eqI: "length xs = length ys \<Longrightarrow> z \<in> set xs \<Longrightarrow> (m1(xs [\<mapsto>] ys)) z = (m2(xs [\<mapsto>] ys)) z"
  apply (induct xs ys rule: list_induct2, auto)
  by (simp add: map_upd_upds_conv_if)

lemmas insert_congI = arg_cong[of _ _ \<open>\<lambda>x. insert _ x\<close>]
lemmas singleton_congI = arg_cong[of _ _ \<open>\<lambda>x. {x}\<close>]

lemmas insert_cong2I = arg_cong2[of _ _ _ _ \<open>\<lambda>x y. insert x y\<close>]
lemmas union_cong2 = arg_cong2[of _ _ _ _ \<open>\<lambda>x y. x \<union> y\<close>]
lemmas image_congI = arg_cong[of _ _ \<open>\<lambda>x. _ ` x\<close>]
lemmas map_upd_vals_eqI[intro] = arg_cong[of _ _ \<open>\<lambda>s._(_ \<mapsto> s)\<close>]
lemmas collect_not_member_eqI[intro] = arg_cong[of _ _ \<open>\<lambda>x. {a. a \<notin> x}\<close>]

lemmas in_collect_not_in = mem_Collect_eq[of _ \<open>\<lambda>x. x \<notin> _\<close>]

lemma Cons_single: "[x] = (y # ys) \<longleftrightarrow> x = y \<and> ys = []"
  by auto

lemma ball_empty: \<open>\<forall>x\<in>{}. P x\<close>
  by auto

lemma length_eq_ConsI: 
  assumes \<open>length xs = length ys\<close> shows \<open>length (x # xs) = length (y # ys)\<close>
  using assms by simp

lemma length_eq_single[simp]: \<open>length [x] = length [y]\<close>
  by simp



lemma Collect_eq: \<open>{s. P s} = {s. Q s} \<longleftrightarrow> (\<forall>s. P s \<longleftrightarrow> Q s)\<close>
  by blast

lemma classes_eq_iff_equivp: 
  assumes \<open>equivp P\<close>
    shows "{s. P s s\<^sub>1} = {s. P s s\<^sub>2} \<longleftrightarrow> P s\<^sub>1 s\<^sub>2"
  using assms apply (intro iffI)
  using equivp_reflp apply fastforce
  by (simp add: equivp_def)

lemma list_all_True[simp]: "list_all (\<lambda>_. True) tr"
  using list.pred_True by metis


lemma measure_induct4[case_names IH]:
fixes meas :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> nat"
assumes "\<And>x1 x2 x3 x4. (\<And>y1 y2 y3 y4. meas y1 y2 y3 y4 < meas x1 x2 x3 x4 \<Longrightarrow> S y1 y2 y3 y4) \<Longrightarrow> S x1 x2 x3 x4"
shows "S x1 x2 x3 x4"
proof-
  let ?m = "\<lambda> x1x2 x3x4. meas (fst x1x2) (snd x1x2) (fst x3x4) (snd x3x4)" let ?S = "\<lambda> x1x2 x3x4. S (fst x1x2) (snd x1x2) (fst x3x4) (snd x3x4)"
  have "?S (x1,x2) (x3,x4)"
  apply(rule measure_induct2[of ?m ?S])
  using assms by (metis fst_conv snd_conv)
  thus ?thesis by auto
qed

lemma disj_notI1: "(\<not>P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q"
  by auto

lemma Not_Not_comp[simp]: "\<not> (Not \<circ> P) s \<equiv> P s"
  by auto
end

