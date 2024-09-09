(* BD Security for Transition Systems *)


theory BD_Security_STS
  imports (*Abstract_BD_Security*) 
    "Abstract_BD_Security_Extensions" 
    "../General_Preliminaries/Filtermap_Extensions" 
    "../General_Preliminaries/Transition_System"
    "HOL-ex.Sketch_and_Explore" (* TODO *)
begin


declare Let_def[simp]

no_notation relcomp (infixr "O" 75)


locale BD_Security_STS = System_Model istate validTrans final
  for istate :: "'state \<Rightarrow> bool" and validTrans :: "('state \<times> 'state) \<Rightarrow> bool"
  and final :: "'state \<Rightarrow> bool"

+
fixes (* secret filtering and production:  *)
   isSec :: "'state \<Rightarrow> bool" and getSec :: "'state \<Rightarrow> 'secret"
 and (* observation filtering and production: *)
   isObs :: "'state \<Rightarrow> bool" and getObs :: "'state \<Rightarrow> 'obs"
 and (* declassification trigger:  *)
   T :: "'state \<Rightarrow> bool"
 and (* declassification bound: *)
   B :: "'state \<Rightarrow> 'secret list \<Rightarrow> 'state \<Rightarrow> 'secret list \<Rightarrow> bool"

(*assumes final_no_Sec: "final x \<Longrightarrow> \<not>isSec x" (* can get rid of this *)*)
    (*and final_no_Obs: "final x \<Longrightarrow> \<not>isObs x"*)
begin

(* The secrecy function: *)
definition S :: "'state list \<Rightarrow> 'secret list" where "S \<equiv> filtermap isSec getSec"
(* The observation function: *)
definition O :: "'state trace \<Rightarrow> 'obs list" where "O \<equiv> filtermap isObs getObs"

lemma O_map_filter: "O tr = map getObs (filter isObs tr)" unfolding O_def filtermap_map_filter ..
lemma S_map_filter: "S tr = map getSec (filter isSec tr)" unfolding S_def filtermap_map_filter ..

lemma O_never[simp]: \<open>([] = O tr) \<longleftrightarrow> never isObs tr\<close> \<open>(O tr = []) \<longleftrightarrow> never isObs tr\<close>
  unfolding O_def apply auto
  by (metis filtermap_Nil_never)+

lemma O_single[simp]: \<open>([] = O [x]) \<longleftrightarrow> \<not> isObs x\<close> \<open>(O [x] = []) \<longleftrightarrow> \<not> isObs x\<close>
  by auto

lemma S_single[simp]: \<open>([] = S [x]) \<longleftrightarrow> \<not> isSec x\<close> \<open>(S [x] = []) \<longleftrightarrow> \<not> isSec x\<close>
  unfolding S_def by auto

lemma S_simps[simp]:
"S [] = []"  "\<not> isSec trn \<Longrightarrow> S (trn # tr) = S tr"  "isSec trn \<Longrightarrow> S (trn # tr) = getSec trn # S tr"
unfolding S_def by auto

lemma S_Cons_unfold: "S (trn # tr) = (if isSec trn then getSec trn # S tr else S tr)"
by auto

lemma O_simps[simp]:
"O [] = []"  "\<not> isObs trn \<Longrightarrow> O (trn # tr) = O tr"  "isObs trn \<Longrightarrow> O (trn # tr) = getObs trn # O tr"
unfolding O_def by auto

lemma O_Cons_unfold: "O (trn # tr) = (if isObs trn then getObs trn # O tr else O tr)"
by auto

lemma S_append: "S (tr @ tr1) = S tr @ S tr1"
unfolding S_def using filtermap_append by auto

lemma S_snoc:
"\<not> isSec trn \<Longrightarrow> S (tr ## trn) = S tr"  "isSec trn \<Longrightarrow> S (tr ## trn) = S tr ## getSec trn"
unfolding S_def by auto

lemma O_snoc:
"\<not> isObs trn \<Longrightarrow> O (tr ## trn) = O tr"  "isObs trn \<Longrightarrow> O (tr ## trn) = O tr ## getObs trn"
unfolding O_def by auto

lemma S_Nil_list_ex: "S tr = [] \<longleftrightarrow> \<not> list_ex isSec tr"
unfolding S_def using filtermap_Nil_list_ex by auto

lemma S_Nil_never: "S tr = [] \<longleftrightarrow> never isSec tr"
unfolding S_def using filtermap_Nil_never by auto

lemma Nil_S_never: "[] = S tr \<longleftrightarrow> never isSec tr"
unfolding S_def filtermap_map_filter by (induction tr) auto

lemma length_V: "length (S tr) \<le> length tr"
by (auto simp: S_def length_filtermap)

lemma S_list_all: "S tr = map getSec tr \<longleftrightarrow> list_all isSec tr"
by (auto simp: S_def length_filtermap)

lemma S_eq_Cons:
assumes "S tr = v # vl1"
shows "\<exists> trn tr2 tr1. tr = tr2 @ [trn] @ tr1 \<and> never isSec tr2 \<and> isSec trn \<and> getSec trn = v \<and> S tr1 = vl1"
using assms filtermap_eq_Cons unfolding S_def by auto

lemma S_eq_append:
assumes "S tr = vl1 @ vl2"
shows "\<exists> tr1 tr2. tr = tr1 @ tr2 \<and> S tr1 = vl1 \<and> S tr2 = vl2"
using assms filtermap_eq_append[of isSec getSec] unfolding S_def by auto

lemma S_eq_RCons:
assumes "S tr = vl1 ## v"
shows "\<exists> trn tr1 tr2. tr = tr1 @ [trn] @ tr2 \<and> isSec trn \<and> getSec trn = v \<and> S tr1 = vl1 \<and> never isSec tr2"
using assms filtermap_eq_RCons[of isSec getSec] unfolding S_def by blast

lemma S_eq_Cons_RCons:
assumes "S tr = v # vl1 ## w"
shows "\<exists> trv trnv tr1 trnw trw.
   tr = trv @ [trnv] @ tr1 @ [trnw] @ trw \<and>
   never isSec trv \<and> isSec trnv \<and> getSec trnv = v \<and> S tr1 = vl1 \<and> isSec trnw \<and> getSec trnw = w \<and> never isSec trw"
using assms filtermap_eq_Cons_RCons[of isSec getSec] unfolding S_def by blast

lemma O_append: "O (tr @ tr1) = O tr @ O tr1"
unfolding O_def using filtermap_append by auto

lemma O_Nil_list_ex: "O tr = [] \<longleftrightarrow> \<not> list_ex isObs tr"
unfolding O_def using filtermap_Nil_list_ex by auto

lemma O_Nil_never: "O tr = [] \<longleftrightarrow> never isObs tr"
unfolding O_def using filtermap_Nil_never by auto

lemma Nil_O_never: "[] = O tr \<longleftrightarrow> never isObs tr"
unfolding O_def filtermap_map_filter by (induction tr) auto

lemma length_O: "length (O tr) \<le> length tr"
by (auto simp: O_def length_filtermap)

lemma O_list_all: "O tr = map getObs tr \<longleftrightarrow> list_all isObs tr"
by (auto simp: O_def length_filtermap)

lemma O_eq_Cons:
assumes "O tr = obs # obsl1"
shows "\<exists> trn tr2 tr1. tr = tr2 @ [trn] @ tr1 \<and> never isObs tr2 \<and> isObs trn \<and> getObs trn = obs \<and> O tr1 = obsl1"
using assms filtermap_eq_Cons unfolding O_def by auto

lemma O_eq_append:
assumes "O tr = obsl1 @ obsl2"
shows "\<exists> tr1 tr2. tr = tr1 @ tr2 \<and> O tr1 = obsl1 \<and> O tr2 = obsl2"
using assms filtermap_eq_append[of isObs getObs] unfolding O_def by auto

lemma O_eq_RCons:
assumes "O tr = oul1 ## ou"
shows "\<exists> trn tr1 tr2. tr = tr1 @ [trn] @ tr2 \<and> isObs trn \<and> getObs trn = ou \<and> O tr1 = oul1 \<and> never isObs tr2"
using assms filtermap_eq_RCons[of isObs getObs] unfolding O_def by blast

lemma O_eq_Cons_RCons:
assumes "O tr0 = ou # oul1 ## ouu"
shows "\<exists> tr trn tr1 trnn trr.
   tr0 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
   never isObs tr \<and> isObs trn \<and> getObs trn = ou \<and> O tr1 = oul1 \<and> isObs trnn \<and> getObs trnn = ouu \<and> never isObs trr"
using assms filtermap_eq_Cons_RCons[of isObs getObs] unfolding O_def by blast

lemma O_eq_Cons_RCons_append:
assumes "O tr0 = ou # oul1 ## ouu @ oull"
shows "\<exists> tr trn tr1 trnn trr.
   tr0 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
   never isObs tr \<and> isObs trn \<and> getObs trn = ou \<and> O tr1 = oul1 \<and> isObs trnn \<and> getObs trnn = ouu \<and> O trr = oull"
proof-
  from O_eq_append[of tr0 "ou # oul1 ## ouu" oull] assms
  obtain tr00 trrr where 1: "tr0 = tr00 @ trrr"
  and 2: "O tr00 = ou # oul1 ## ouu" and 3: "O trrr = oull" by auto
  from O_eq_Cons_RCons[OF 2] obtain tr trn tr1 trnn trr where
  4:"tr00 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
     never isObs tr \<and>
     isObs trn \<and> getObs trn = ou \<and> O tr1 = oul1 \<and> isObs trnn \<and> getObs trnn = ouu \<and> never isObs trr" by auto
  show ?thesis apply(rule exI[of _ tr], rule exI[of _ trn], rule exI[of _ tr1],
     rule exI[of _ trnn], rule exI[of _ "trr @ trrr"])
  using 1 3 4 by (simp add: O_append O_Nil_never)
qed

lemma O_Nil_tr_Nil: "O tr \<noteq> [] \<Longrightarrow> tr \<noteq> []"
by (induction tr) auto

lemma S_Cons_eq_append: "S (trn # tr) = S [trn] @ S tr"
by (cases "isSec trn") auto

lemma set_V: "set (S tr) \<subseteq> {getSec trn | trn . trn \<in>\<in> tr \<and> isSec trn}"
using set_filtermap unfolding S_def .

lemma set_O: "set (O tr) \<subseteq> {getObs trn | trn . trn \<in>\<in> tr \<and> isObs trn}"
using set_filtermap unfolding O_def .

lemma list_ex_length_O:
assumes "list_ex isObs tr"  shows "length (O tr) > 0"
by (metis assms O_Nil_list_ex length_greater_0_conv)

lemma list_ex_iff_length_O:
"list_ex isObs tr \<longleftrightarrow> length (O tr) > 0"
by (metis O_Nil_list_ex length_greater_0_conv)

lemma length1_O_list_ex_iff:
"length (O tr) > 1 \<Longrightarrow> list_ex isObs tr"
unfolding list_ex_iff_length_O by linarith

lemma list_all_O_map: "list_all isObs tr \<Longrightarrow> O tr = map getObs tr"
using O_list_all by auto

lemma never_O_Nil: "never isObs tr \<Longrightarrow> O tr = []"
using O_Nil_never by auto

lemma list_all_S_map: "list_all isSec tr \<Longrightarrow> S tr = map getSec tr"
using S_list_all by auto

lemma never_S_Nil: "never isSec tr \<Longrightarrow> S tr = []"
using S_Nil_never by auto

(* Reachable states by transitions satisfying T: *)
inductive reachNT:: "'state \<Rightarrow> bool" where
Istate: "istate s \<Longrightarrow> reachNT s"
|
Step:
"\<lbrakk>reachNT s; validTrans (s, s'); \<not> T s\<rbrakk>
 \<Longrightarrow> reachNT s'"

lemma reachNT_reach: assumes "reachNT s"  shows "reach s"
using assms apply induct by (auto intro: reach.intros)

(* This is assumed to be an invariant only modulo non T  *)
definition invarNT where
"invarNT Inv \<equiv> 
  \<forall> s s'. validTrans (s, s') \<and> reachNT s \<and> Inv s \<and> \<not> T s \<longrightarrow> Inv s'"

lemma invarNT_disj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<or> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma invarNT_conj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<and> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma holdsIstate_invarNT:
assumes h: "holdsIstate Inv" and i: "invarNT Inv" and a: "reachNT s"
shows "Inv s"
using a using h i unfolding holdsIstate_def invarNT_def
apply (induct rule: reachNT.induct) by auto 

abbreviation \<open>validTrace tr \<equiv> istate (hd tr) \<and> validFromS (hd tr) tr \<and> completedFrom (hd tr) tr\<close>



definition 
  produces
where
  \<open>produces P cs \<equiv> (\<forall>ctr. validFromS cs ctr \<and> never T ctr \<longrightarrow> list_ex P ctr)\<close>


(* This is syntactic sugar for the command
sublocale BD_Security_TS \<subseteq> Abstract_BD_Security 
when stated outside the context of BD_Security_TS.
*)
sublocale Abstract_BD_Security
  where validSystemTrace = validTrace
    and V = \<open>\<lambda>tr. (hd tr, S tr)\<close> 
    and O = O 
    and B = \<open>\<lambda>(s\<^sub>1, sl\<^sub>1) (s\<^sub>2, sl\<^sub>2). B s\<^sub>1 sl\<^sub>1 s\<^sub>2 sl\<^sub>2\<close> 
    and TT = \<open>never T\<close> .

lemma S_iff_non_\<phi>[simp]: "S (trn # tr) = S tr \<longleftrightarrow> \<not> isSec trn"
by (cases "isSec trn") auto

lemma S_imp_\<phi>: "S (trn # tr) = v # S tr \<Longrightarrow> isSec trn"
by (cases "isSec trn") auto

lemma S_imp_Nil: "S (trn # tr) = [] \<Longrightarrow> S tr = []"
by (metis S_simps list.distinct)

lemma S_iff_Nil[simp]: "S (trn # tr) = [] \<longleftrightarrow> \<not> isSec trn \<and> S tr = []"
by (metis S_iff_non_\<phi> S_imp_Nil)

definition consume :: "'state \<Rightarrow> 'secret list \<Rightarrow> 'secret list \<Rightarrow> bool" where
"consume s vl vl' \<equiv>
 if isSec s then vl \<noteq> [] \<and> getSec s = hd vl \<and> vl' = tl vl
 else vl' = vl"

lemma length_consume[simp]:
"consume trn vl vl' \<Longrightarrow> length vl' < Suc (length vl)"
unfolding consume_def by (auto split: if_splits)

lemma ex_consume_\<phi>:
assumes "\<not> isSec trn"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by auto

lemma ex_consume_NO:
assumes "vl \<noteq> []" and "getSec trn = hd vl"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by (cases "isSec trn") auto

lemma S_Cons_consume: 
assumes  "S (s # tr) = vl" 
shows "\<exists>vl'. consume s vl vl' \<and> S tr = vl'" 
using assms unfolding consume_def by (cases "isSec s") auto

lemma consume_lastE: 
  assumes \<open>consume s vl []\<close> 
      and \<open>\<lbrakk>isSec s; vl = [getSec s]\<rbrakk> \<Longrightarrow> P\<close>
      and \<open>\<lbrakk>\<not>isSec s; vl = []\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def apply auto
  using list.collapse by fastforce

lemma consume_singleE: 
  assumes \<open>consume s [sec] vl\<close> 
      and \<open>\<lbrakk>vl = []; sec = getSec s; isSec s\<rbrakk> \<Longrightarrow> P\<close>
      and \<open>\<lbrakk>vl = [sec]; \<not> isSec s\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms(1) unfolding consume_def apply (cases \<open>isSec s\<close>)
  apply (rule assms(2),auto)
  apply (rule assms(3),auto)
  done

lemma consume_emptyE: 
  assumes \<open>consume s [] vl\<close> 
      and \<open>\<lbrakk>vl = []; \<not> isSec s\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by (cases \<open>isSec s\<close>, auto)

lemma consumeE:
  assumes major: \<open>consume s vl vl'\<close>
      and trueE: \<open>\<lbrakk>isSec s; vl \<noteq> []; getSec s = hd vl; vl' = tl vl\<rbrakk> \<Longrightarrow> P\<close>
      and falseE: \<open>\<lbrakk>\<not> isSec s; vl' = vl\<rbrakk> \<Longrightarrow> P\<close>
    shows P
proof (cases \<open>isSec s\<close>)
  case True
  thus ?thesis
    using major unfolding consume_def apply auto
    by (rule trueE)
next
  case False
  thus ?thesis 
    using major unfolding consume_def apply auto
    by (rule falseE)
qed

lemma consume_secE: 
  assumes \<open>consume s vl vl'\<close> \<open>isSec s\<close> 
      and \<open>\<lbrakk>vl \<noteq> []; getSec s = hd vl; vl' = tl vl\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by (cases \<open>isSec s\<close>, auto)

lemma consume_notSecE: 
  assumes \<open>consume s vl vl'\<close> \<open>\<not> isSec s\<close> 
      and \<open>\<lbrakk>vl' = vl\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by (cases \<open>isSec s\<close>, auto)





(* HOPELESSNESS (inability to produce values) *)

(* No trace starting in state s can produce the values vl: *)
definition hopeless :: "'state \<Rightarrow> 'secret list \<Rightarrow> bool" where 
"hopeless s vl \<equiv> \<forall>tr. validFromS s tr \<and> never T tr \<longrightarrow> S tr \<noteq> vl"

lemma final_allE:
  assumes f: \<open>final s\<close> and valid: \<open>validFromS s tr\<close> and E: \<open>list_all final tr \<Longrightarrow> P\<close> shows P
  apply (rule E)
  using valid[unfolded validFromS_def] apply (elim conjE)
  using f apply - 
  apply (induct tr arbitrary: s rule: list_nonempty_induct)
  apply auto
  subgoal for xs s
    apply (cases xs,simp_all)
    by (metis Simple_Transition_System.validFromS_def hd_Cons list.discI list_all_simps(1) validFromS_alwaysE)
  .
(*
lemma all_final_never_isSecE: \<open>list_all final tr \<Longrightarrow> (never isSec tr \<Longrightarrow> P) \<Longrightarrow> P\<close>
  apply (induct tr,auto)
  using final_no_Sec
  by simp

lemma "final s \<Longrightarrow> \<not> hopeless s vl \<Longrightarrow> vl \<noteq> []"
  unfolding hopeless_def apply auto
  apply (erule final_allE, simp)
  apply (erule all_final_never_isSecE)
  oops
*)


(* Simpler version, amenable to trace-free reasoning: *)
definition hopeless1 :: "'state \<Rightarrow> 'secret \<Rightarrow> bool" where
"hopeless1 s v \<equiv> \<forall> tr s'. validFromS s (tr ## s') \<and> never T (tr ## s') \<and> isSec s' \<longrightarrow> getSec s' \<noteq> v"

lemma hopeless1_trans:
  assumes \<open>hopeless1 s sec\<close> and \<open>validTrans (s,s')\<close> and \<open>\<not>T s\<close>
    shows \<open>hopeless1 s' sec\<close>
  using assms unfolding hopeless1_def apply auto
  subgoal for tr s''
    apply (erule allE[where x=\<open>s # tr\<close>], erule allE[where x=s''], erule impE) 
    apply (intro conjI)
    by auto
  .
  


lemma hopeless1_hopeless:
  assumes vl: "vl \<noteq> []" and i: "hopeless1 s (hd vl)"
    shows "hopeless s vl" 
proof-
  {fix tr assume v: "validFromS s tr" and S: "S tr = vl" and T: "never T tr"
   hence False
   using i proof(induction tr arbitrary: s rule: induct_list012)
     case 1 thus ?case by (metis S_simps(1) vl)
   next
     case (2 s) 
     thus ?case 
       using S_Cons_unfold S_simps(1) append_Nil hd_Cons hopeless1_def vl
       by (metis )
   next
     case (3 s s' tr s'')
     have seq: \<open>s'' = s\<close>
       using 3(3) unfolding validFromS_Cons_iff by (elim conjE)
     show ?case 
     proof(cases "isSec s")
       case True
       hence "getSec s = hd vl" 
         using 3(4) S_simps(3) hd_Cons_tl list.inject vl by metis
       moreover have "validFromS s [s'']" 
         unfolding seq by simp
       ultimately show ?thesis using 3 True unfolding hopeless1_def
         by (elim allE[of _ "[]"]) auto
    next
      case False
      hence "S (s' # tr) = vl" using 3(4) by auto
      
      moreover have "never T (s' # tr)"
        using 3(5) using list_all_simps(1) by auto
      moreover from \<open>validFromS s'' (s # s' # tr)\<close> have "validFromS s' (s' # tr)"
        unfolding seq validFromS_Cons_iff by simp
      moreover have "hopeless1 s' (hd vl)" 
        apply (rule hopeless1_trans[OF 3(6)[unfolded seq]])
        apply (metis "3.prems"(1) Simple_Transition_System.validFromS_Cons_iff list.discI)
        using "3.prems"(3) by auto
      ultimately show ?thesis
        using 3(2) by auto
    qed
  qed
  }
  thus ?thesis unfolding hopeless_def using i vl by auto
qed

(* Trace-free reasoning about hopelessness: *)
(*
lemma hopeless1_coind:
assumes K: "K s" (*\<not> T s' isSec s' getSec s'*)
and I: "\<And> s s'. \<lbrakk>K s; validTrans (s, s'); \<not> T s\<rbrakk>
        \<Longrightarrow> (isSec s \<longrightarrow> getSec s \<noteq> v) \<and> K s'"
shows "hopeless1 s v"
using K unfolding hopeless1_def proof(intro allI conjI impI)
  fix tr s' assume "K s" and "validFromS s (tr ## s') \<and> never T (tr ## s') \<and> isSec s'"
  thus "getSec s' \<noteq> v"
  proof (induction tr arbitrary: s s' rule: induct_list012)
    case 1
    then show ?case 
      apply auto
      using neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE
      sledgehammer
      sorry
  next
    case (2 x)
    then show ?case sorry
  next
    case (3 x y zs)
    then show ?case sorry
  qed
    case Nil
    then show ?case 
      apply auto
      sledgehammer

    next
    case (Cons a tr)
    then show ?case sorry
  qed
(*
  (auto, metis neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE)*)
qed
*)


lemma consume_empty[simp]: "consume s [] vl \<longleftrightarrow> vl = [] \<and> \<not>isSec s"
  unfolding consume_def by auto

lemma consume2_eqE:
  assumes \<open>isSec s \<longleftrightarrow> isSec s1\<close> \<open>consume s vl vl'\<close> \<open>consume s1 vl vl1'\<close> 
      and minor: \<open>vl' = vl1' \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by auto

lemma isSec_consume2_eqE:
  assumes \<open>isSec s \<longleftrightarrow> isSec s\<^sub>1\<close> \<open>isSec s\<close> \<open>consume s vl vl'\<close> \<open>consume s\<^sub>1 vl vl1'\<close> 
      and minor: \<open>\<lbrakk>getSec s = getSec s\<^sub>1; vl' = vl1'\<rbrakk> \<Longrightarrow> P\<close>
    shows P
  using assms unfolding consume_def by auto

definition noVal where
"noVal K v \<equiv>
 \<forall> s s'. validTrans (s, s') \<and> reachNT s \<and> K s \<and> 
         isSec s \<longrightarrow> getSec s' \<noteq> v"

lemma noVal_disj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<or> Inv2 s) v"
using assms unfolding noVal_def by metis

lemma noVal_conj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<and> Inv2 s) v"
using assms unfolding noVal_def by blast

(* Sufficient criterion for noVal: *)
definition no\<phi> where
"no\<phi> K \<equiv> \<forall> s s'. validTrans (s, s') \<and> reachNT s \<and> K s 
                 \<longrightarrow> \<not> isSec s"

lemma no\<phi>_noVal: "no\<phi> K \<Longrightarrow> noVal K v"
unfolding no\<phi>_def noVal_def by auto
(*
(* intro rule for quick inline checks: *)
lemma hopeless1I[consumes 2, induct pred: "hopeless1"]:
assumes rs: "reachNT s" and K: "K s"
and I:
"\<And> trn.
   \<lbrakk>validTrans (s, s'); reach (srcOf trn); reachNT (srcOf trn); K (srcOf trn)\<rbrakk>
   \<Longrightarrow> (isSec trn \<longrightarrow> getSec trn \<noteq> v) \<and> K (tgtOf trn)"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms apply (intro hopeless1_coind[of ?K])
    using reachNT.Step reachNT_reach by blast+
qed

(* intro rule for more elaborate checks: *)
lemma hopeless1I2:
assumes rs: "reachNT s" and K: "K s"
and "invarNT K" and "noVal K v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms unfolding invarNT_def noVal_def apply(intro hopeless1_coind[of ?K])
  using reachNT.Step by blast+ 
qed

(* Binary version of the invariant: *)
definition noVal2 where
"noVal2 K v \<equiv>
 \<forall> trn. validTrans (s, s') \<and> reachNT (srcOf trn) \<and> K (srcOf trn) v \<and> isSec trn 
       \<longrightarrow> getSec trn \<noteq> v"

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
"\<And> trn.
   \<lbrakk>validTrans (s, s'); reach (srcOf trn); reachNT (srcOf trn); K (srcOf trn) v\<rbrakk>
   \<Longrightarrow> (isSec trn \<longrightarrow> getSec trn \<noteq> v) \<and> K (tgtOf trn) v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms apply (intro hopeless1_coind[of ?K])
  using reachNT.Step reachNT_reach by blast+
qed

lemma hopeless1I2_noVal2:
assumes rs: "reachNT s" and K: "K s v"
and "invarNT (\<lambda> s. K s v)" and "noVal2 K v"
shows "hopeless1 s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms unfolding invarNT_def noVal2_def
  apply (intro hopeless1_coind[of ?K]) 
    using reachNT.Step by blast+
qed
*)
(* end binary version *)


lemma not_hopeless_final_secrets:
  assumes major: \<open>\<not>hopeless s vl\<close> \<open>final s\<close> \<open>isSec s\<close> 
      and minor: \<open>vl \<noteq> [] \<Longrightarrow> P\<close>
    shows P
  apply (rule minor)
  using major unfolding hopeless_def apply safe
  apply (erule validFromS_alwaysE[where Q = isSec], assumption+)
  by (metis Nil_is_map_conv list_all_S_map  validFromS_empty)

lemma not_hopeless_final_no_secrets:
  assumes major: \<open>\<not>hopeless s vl\<close> \<open>final s\<close> \<open>\<not>isSec s\<close> 
      and minor: \<open>vl = [] \<Longrightarrow> P\<close>
    shows P
  apply (rule minor)
  using major unfolding hopeless_def apply safe
  apply (erule validFromS_alwaysE[where Q = \<open>\<lambda>s. \<not> isSec s\<close>], assumption+)
  by (metis Nil_S_never)

(* UNWINDING PROOF METHOD *)

(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft \<Delta> s vl s1 vl1 \<equiv>
 \<forall>s' vl'.
   validTrans (s, s') \<and> consume s vl vl' 
   \<longrightarrow> 
   (\<not> isObs s \<longrightarrow> hopeless s' vl' \<or> \<Delta> s' vl' s1 vl1) \<and> 
   (isObs s \<and> final s1 \<and> consume s1 vl1 [] \<longrightarrow> hopeless s' vl')"


definition iactionRight where
"iactionRight \<Delta> s vl s1 vl1 \<equiv>
 \<forall>s1' vl1'.
   validTrans (s1, s1') \<and> consume s1 vl1 vl1' 
   \<longrightarrow> 
   (\<not> isObs s1 \<longrightarrow> hopeless s1' vl1' \<or> \<Delta> s vl s1' vl1') \<and>
   (isObs s1 \<and> final s \<and> consume s vl [] \<longrightarrow> hopeless s1' vl1')"

(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> s' vl' s1' vl1'.
   validTrans (s, s') \<and> consume s vl vl' \<and> validTrans (s1, s1') \<and> consume s1 vl1 vl1' \<and> 
   isObs s \<and> isObs s1
   \<longrightarrow>  
   hopeless s' vl' \<or> hopeless s1' vl1' \<or> 
   (getObs s = getObs s1 \<and> \<Delta> s' vl' s1' vl1')"

(* *)
definition \<open>eqObs s s' \<equiv> (isObs s  \<longleftrightarrow> isObs s') \<and> (isObs s  \<longrightarrow> (getObs s  = getObs s'))\<close>

definition finish where \<open>finish s vl s1 vl1 \<equiv>
  final s \<and> final s1 \<and> consume s vl [] \<and> consume s1 vl1 [] \<longrightarrow> eqObs s s1\<close>

abbreviation \<open>unwindFor \<Delta> s vl s1 vl1 \<equiv> 
   finish s vl s1 vl1 \<and>
   iactionLeft \<Delta> s vl s1 vl1 \<and> 
   iactionRight \<Delta> s vl s1 vl1 \<and> 
   saction \<Delta> s vl s1 vl1\<close>

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reachNT s1 \<and> \<not> T s \<and> \<not> T s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 \<or>
   unwindFor \<Delta> s vl s1 vl1"

lemma unwindI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reachNT s1; \<not> T s; \<not> T s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 
   \<or>
   unwindFor \<Delta> s vl s1 vl1"
shows "unwind \<Delta>"
using assms unfolding unwind_def by auto

lemma filtermap_Nil_never_rhs[simp]: "([] = filtermap pred func tr) \<longleftrightarrow> never pred tr"
  by (metis filtermap_Nil_never)

definition \<open>\<psi> \<Delta> tr tr1 \<equiv> (\<forall>y1 y2 s s1 vl vl1. length y1 + length y2 < length tr + length tr1 \<longrightarrow>
           reachNT s \<longrightarrow>
           reachNT s1 \<longrightarrow>
           \<Delta> s vl s1 vl1 \<longrightarrow>
           validFromS s y1 \<longrightarrow>
           never T y1 \<longrightarrow>
           completedFrom s y1 \<longrightarrow>
           validFromS s1 y2 \<longrightarrow> never T y2 \<longrightarrow> completedFrom s1 y2 \<longrightarrow> S y1 = vl \<longrightarrow> S y2 = vl1 \<longrightarrow> O y1 = O y2)\<close>

(* main *) proposition unwind_via_\<psi>:
  assumes unwind: "unwindFor \<Delta> s vl s1 vl1" and r: "reachNT s" "reachNT s1"
and \<psi>: \<open>\<psi> \<Delta> tr tr1\<close>
and vn: "validFromS s tr" "never T tr" "completedFrom s tr" 
        "validFromS s1 tr1" "never T tr1" "completedFrom s1 tr1"
and S: "S tr = vl" "S tr1 = vl1"
shows "O tr = O tr1"
proof- 
  (* easier to work with *)
  have \<psi>: \<open>\<And>y1 y2 s s1 vl vl1. \<lbrakk>length y1 + length y2 < length tr + length tr1; reachNT s; reachNT s1;
          \<Delta> s vl s1 vl1; validFromS s y1;never T y1;completedFrom s y1;
          validFromS s1 y2;never T y2;completedFrom s1 y2; S y1 = vl; S y2 = vl1\<rbrakk> \<Longrightarrow> O y1 = O y2\<close>
    using \<psi> unfolding \<psi>_def by auto
  have fin: "finish s vl s1 vl1" and 
       ial: "iactionLeft \<Delta> s vl s1 vl1" and 
       iar: "iactionRight \<Delta> s vl s1 vl1" and 
       sa: "saction \<Delta> s vl s1 vl1"  
    using unwind by auto
    show ?thesis
    proof(cases \<open>length tr \<le> 1\<close>)
      case True
      hence tr: \<open>tr = [s]\<close>
        using vn by (cases tr, auto)
      hence final: \<open>final s\<close>
        using vn by auto
      have consume: \<open>consume s vl []\<close>
        using S(1) unfolding tr by (drule_tac S_Cons_consume, simp)
      note RIH = \<psi>[OF _ r(1) _ _ vn(1-3) _ _ _ S(1), simplified] 
      show ?thesis
      proof(cases \<open>length tr1 \<le> 1\<close>)
        case True
        hence trr1: \<open>tr1 = [s1]\<close>
          using vn by (cases tr1, auto)
        hence final1: \<open>final s1\<close>
          using vn by auto
        have consume1: \<open>consume s1 vl1 []\<close>
          using S(2) unfolding trr1 by (drule_tac S_Cons_consume, simp)
        show ?thesis
          using fin final final1 consume consume1 unfolding finish_def tr trr1
          using S unfolding tr trr1 apply simp
          unfolding eqObs_def by auto            
      next
        case False
        then obtain s1' tr1' where trr1: \<open>tr1 = s1 # s1' # tr1'\<close>
          apply (cases tr1, auto)
          subgoal for _ tr1'
            apply (cases tr1', auto)
            using vn(4) validFromS_Cons_iff by auto
          .
        have trn1: \<open>validTrans (s1, s1')\<close>
          using vn trr1 validFromS_Cons_iff by auto
        hence s1': "reachNT s1'"
          apply (rule reachNT.Step[OF r(2)]) 
          using vn trr1 by auto
        have tr1: "validFromS s1' (s1' # tr1')" "never T (s1' # tr1')" "completedFrom s1' (s1' # tr1')"
          using vn trr1 validFromS_Cons_iff apply auto[1]
          using vn trr1 by auto
        obtain vl1' where vl1': "consume s1 vl1 vl1'" and Vtr1: "S (s1' # tr1') = vl1'"
          using S_Cons_consume[OF `S tr1 = vl1`[unfolded trr1]]
          by blast
        hence nh1': "\<not> hopeless s1' vl1'" 
          unfolding hopeless_def by (metis vn(5) list_all_simps(1) tr1(1) trr1)
        have not_g: "\<not> isObs s1"
        proof 
          assume getObs: "isObs s1"
          hence "hopeless s1' vl1'" 
            using iar trn1 getObs consume vl1' final unfolding iactionRight_def by auto
          thus False using nh1' trn1 by auto
        qed  
        have D: "\<Delta> s vl s1' vl1'" 
        using iar nh1' not_g trn1 vl1' trn1(1) unfolding iactionRight_def by force
        have "O tr = O (s1' # tr1')"
          apply (rule RIH[OF _ s1' D tr1 Vtr1])
          using trr1 by auto
        thus ?thesis unfolding trr1 using not_g by auto
      qed       
    next
      case False
      then obtain s' tr' where trr: \<open>tr = s # s' # tr'\<close>
        apply (cases tr, auto)
        subgoal for s' tr'
          apply (cases tr', auto)
          using vn validFromS_Cons_iff by auto
        .
      have trn: \<open>validTrans (s, s')\<close>
        using vn trr validFromS_Cons_iff by auto
      hence s': "reachNT s'"
        apply (rule reachNT.Step[OF r(1)]) 
        using vn trr by auto
      have tr: "validFromS s' (s' # tr')" "never T (s' # tr')" "completedFrom s' (s' # tr')"
        using vn trr validFromS_Cons_iff by auto
      obtain vl' where vl': "consume s vl vl'" and Vtr: "S (s' # tr') = vl'"
        using S_Cons_consume[OF `S tr = vl`[unfolded trr]]
        by blast
      hence nh': "\<not> hopeless s' vl'" 
        unfolding hopeless_def using vn(2) list_all_simps(1) tr(1) trr by metis
      note LIH = \<psi>[OF _ s' _ _ tr _ _ _ Vtr, unfolded trr, simplified] 
      show ?thesis
      proof(cases \<open>length tr1 \<le> 1\<close>)
        case True
        hence trr1: \<open>tr1 = [s1]\<close>
          using vn by (cases tr1, auto)
        hence final1: \<open>final s1\<close>
          using vn by auto
        have consume1: \<open>consume s1 vl1 []\<close>
          using S(2) unfolding trr1 by (drule_tac S_Cons_consume, simp)
        have isntL: \<open>(\<not> isObs s \<longrightarrow> hopeless s' vl' \<or> \<Delta> s' vl' s1 vl1)\<close> and
               isL: \<open>(isObs s \<and> final s1 \<and> consume s1 vl1 [] \<longrightarrow> hopeless s' vl')\<close>
          using nh'
          using ial trn vl' unfolding iactionLeft_def by auto
        have not_g: "\<not> isObs s"
        proof 
          assume getObs: "isObs s"
          hence "hopeless s' vl'" 
            using consume1 final1 getObs isL by blast
          thus False using nh' trn by auto
        qed  
        have D: "\<Delta> s' vl' s1 vl1" 
          using isntL nh' not_g  by force
        have "O (s' # tr') = O tr1"
          by (rule LIH[OF _ r(2) D vn(4-) S(2), simplified])
        thus ?thesis unfolding trr using not_g by auto
      next
        case False
        then obtain s1' tr1' where trr1: \<open>tr1 = s1 # s1' # tr1'\<close>
          apply (cases tr1, auto)
          subgoal for s1' tr1'
            apply (cases tr1', auto)
            using vn validFromS_Cons_iff by auto
          .
        have trn1: \<open>validTrans (s1, s1')\<close>
          using vn trr1 validFromS_Cons_iff by auto
        hence s1': "reachNT s1'"
          apply (rule reachNT.Step[OF r(2)]) 
          using vn trr1 by auto
        have tr1: "validFromS s1' (s1' # tr1')" "never T (s1' # tr1')" "completedFrom s1' (s1' # tr1')"
          using vn trr1 validFromS_Cons_iff apply auto[1]
          using vn trr1 by auto
        obtain vl1' where vl1': "consume s1 vl1 vl1'" and Vtr1: "S (s1' # tr1') = vl1'"
          using S_Cons_consume[OF `S tr1 = vl1`[unfolded trr1]]
          by blast
        hence nh1': "\<not> hopeless s1' vl1'" 
          unfolding hopeless_def by (metis vn(5) list_all_simps(1) tr1(1) trr1)
        thus ?thesis  
        proof(cases "isObs s")
          case False note not_g = False 
          have D: "\<Delta> s' vl' s1 vl1 " 
            using ial nh' not_g trn vl' trn(1) unfolding iactionLeft_def by force
          have "O (s' # tr') = O tr1"
            by (rule LIH[OF _ r(2) D vn(4-) S(2), simplified])
          thus ?thesis unfolding trr using not_g by auto
        next
          case True note getObs = True
          show ?thesis
          proof(cases "isObs s1")
            case False note not_g = False 
            have D: "\<Delta> s vl s1' vl1'" 
              using iar nh1' not_g trn1 vl1' trn1(1) unfolding iactionRight_def by force
            have "O tr = O (s1' # tr1')"
              apply(rule \<psi>[of tr \<open>s1' # tr1'\<close> s s1' vl vl1'])
              using assms trr1 s1' D tr1(1) Vtr1 by auto
            thus ?thesis unfolding trr1 using not_g by auto
          next
            case True note g1 = True 
            have D: "\<Delta> s' vl' s1' vl1'" and geq: "getObs s = getObs s1"
              using sa nh' nh1' getObs g1 trn trn1 vl' vl1' trn1(1) unfolding saction_def by force+
            have "O (s' # tr') = O (s1' # tr1')"
              by (rule LIH[OF _ s1' D tr1 Vtr1, unfolded trr1, simplified])
            thus ?thesis unfolding trr trr1 using getObs g1 geq by auto
        qed
      qed
    qed
  qed
qed

proposition unwind_trace:
assumes unwind: "unwind \<Delta>" and r: "reachNT s" "reachNT s1" "\<Delta> s vl s1 vl1" 
and vn: "validFromS s tr" "never T tr" "completedFrom s tr" 
        "validFromS s1 tr1" "never T tr1" "completedFrom s1 tr1"
and S: "S tr = vl" "S tr1 = vl1"
shows "O tr = O tr1"
proof- 
  let ?f = "\<lambda> tr tr1. length tr + length tr1"
  show ?thesis
  using r vn S proof(induction tr tr1 arbitrary: s s1 vl vl1 rule: measure_induct2[of ?f] )
    case (IH trr trr1 s s1 vl vl1)
    have nh: "\<not> hopeless s vl \<and> \<not> hopeless s1 vl1" 
      using IH.prems unfolding hopeless_def by blast
    have uFor: \<open>unwindFor \<Delta> s vl s1 vl1\<close> 
      using IH.prems(1-8) nh unwind  unfolding unwind_def validFromS_def
      by (metis list_all_hd)+
    have \<psi>: \<open>\<psi> \<Delta> trr trr1\<close>
      unfolding \<psi>_def apply safe
      by (rule IH.IH, simp_all)
    show ?case
      by (rule unwind_via_\<psi>[OF uFor IH.prems(1,2) \<psi> IH.prems(4-)])
  qed
qed

theorem unwind_secure:
  assumes init: "\<And> vl vl1 s s1. \<lbrakk>B s vl s1 vl1; istate s; istate s1\<rbrakk> \<Longrightarrow> \<Delta> s vl s1 vl1"
      and unwind: "unwind \<Delta>"
    shows ForAll_ForAll_Secure
  using assms unwind_trace reachNT.Istate unfolding ForAll_ForAll_Secure_def by blast

lemma iactionLeft_impI:
  assumes major: "iactionLeft \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2" 
      and imp: \<open>\<And>s\<^sub>1' vl\<^sub>1'. \<lbrakk>\<not>isObs s\<^sub>1; validTrans (s\<^sub>1, s\<^sub>1'); consume s\<^sub>1 vl\<^sub>1 vl\<^sub>1'; \<Lambda>1 s\<^sub>1' vl\<^sub>1' s\<^sub>2 vl\<^sub>2;
                   \<not>hopeless s\<^sub>1' vl\<^sub>1'\<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1' vl\<^sub>1' s\<^sub>2 vl\<^sub>2\<close>
    shows "iactionLeft \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
  unfolding iactionLeft_def sketch (intro allI impI; elim conjE)
proof (intro allI impI ; elim conjE)
  fix s' vl'
  assume vt: "validTrans (s\<^sub>1, s')"
    and consume: "consume s\<^sub>1 vl\<^sub>1 vl'"
  hence major:"(\<not> isObs s\<^sub>1 \<longrightarrow> hopeless s' vl' \<or> \<Lambda>1 s' vl' s\<^sub>2 vl\<^sub>2) \<and> (isObs s\<^sub>1 \<and> final s\<^sub>2 \<and> consume s\<^sub>2 vl\<^sub>2 [] \<longrightarrow> hopeless s' vl')"
    using major unfolding iactionLeft_def apply (elim allE[where x = s'] allE[where x = vl'] impE)
    by (intro conjI)
  show "(\<not> isObs s\<^sub>1 \<longrightarrow> hopeless s' vl' \<or> \<Lambda>2 s' vl' s\<^sub>2 vl\<^sub>2) \<and> (isObs s\<^sub>1 \<and> final s\<^sub>2 \<and> consume s\<^sub>2 vl\<^sub>2 [] \<longrightarrow> hopeless s' vl')"
  proof (intro impI conjI ; (elim conjE) ?)
    assume "\<not> isObs s\<^sub>1"
    thus "hopeless s' vl' \<or> \<Lambda>2 s' vl' s\<^sub>2 vl\<^sub>2"
      using major vt consume apply simp
      apply (elim disjE, simp_all)
      by (intro disj_notI1 imp)
  next
    assume "isObs s\<^sub>1"
      and "final s\<^sub>2"
      and "consume s\<^sub>2 vl\<^sub>2 []"
    thus "hopeless s' vl'"
      using major by simp
  qed
qed

lemma iactionRight_impI:
  assumes major: "iactionRight \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2" 
      and imp: \<open>\<And>s\<^sub>2' vl\<^sub>2'. \<lbrakk>\<not>isObs s\<^sub>2; validTrans (s\<^sub>2, s\<^sub>2'); consume s\<^sub>2 vl\<^sub>2 vl\<^sub>2'; \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2' vl\<^sub>2';
                   \<not>hopeless s\<^sub>2' vl\<^sub>2'\<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2' vl\<^sub>2'\<close>
    shows "iactionRight \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
  unfolding iactionRight_def sketch (intro allI impI; elim conjE)
proof (intro allI impI ; elim conjE)
  fix s' vl'
  assume vt: "validTrans (s\<^sub>2, s')"
    and consume: "consume s\<^sub>2 vl\<^sub>2 vl'"
  hence major:"(\<not> isObs s\<^sub>2 \<longrightarrow> hopeless s' vl' \<or> \<Lambda>1 s\<^sub>1 vl\<^sub>1 s' vl') \<and> (isObs s\<^sub>2 \<and> final s\<^sub>1 \<and> consume s\<^sub>1 vl\<^sub>1 [] \<longrightarrow> hopeless s' vl')"
    using major unfolding iactionRight_def apply (elim allE[where x = s'] allE[where x = vl'] impE)
    by (intro conjI)
  show "(\<not> isObs s\<^sub>2 \<longrightarrow> hopeless s' vl' \<or> \<Lambda>2 s\<^sub>1 vl\<^sub>1 s' vl') \<and> (isObs s\<^sub>2 \<and> final s\<^sub>1 \<and> consume s\<^sub>1 vl\<^sub>1 [] \<longrightarrow> hopeless s' vl')"
  proof (intro impI conjI ; (elim conjE) ?)
    assume "\<not> isObs s\<^sub>2"
    thus "hopeless s' vl' \<or> \<Lambda>2 s\<^sub>1 vl\<^sub>1 s' vl'"
      using major vt consume apply simp
      apply (elim disjE, simp_all)
      by (intro disj_notI1 imp)
  next
    assume "isObs s\<^sub>2"
      and "final s\<^sub>1"
      and "consume s\<^sub>1 vl\<^sub>1 []"
    thus "hopeless s' vl'"
      using major by simp
  qed
qed

lemma saction_impI:
  assumes major: "saction \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2" 
      and imp: \<open>\<And>s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2'. \<lbrakk>validTrans (s\<^sub>1, s\<^sub>1'); validTrans (s\<^sub>2, s\<^sub>2'); \<Lambda>1 s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2';
                  consume s\<^sub>1 vl\<^sub>1 vl\<^sub>1'; consume s\<^sub>2 vl\<^sub>2 vl\<^sub>2'; isObs s\<^sub>1; isObs s\<^sub>2; getObs s\<^sub>1 = getObs s\<^sub>2;
                  \<not> hopeless s\<^sub>1' vl\<^sub>1'; \<not> hopeless s\<^sub>2' vl\<^sub>2'
            \<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2'\<close>
    shows "saction \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
unfolding saction_def sketch (intro allI impI; elim conjE)
proof (intro allI impI ; elim conjE)
  fix s' vl' s1' vl1'
  assume validTrans: "validTrans (s\<^sub>1, s')" "validTrans (s\<^sub>2, s1')"
    and consume: "consume s\<^sub>1 vl\<^sub>1 vl'" "consume s\<^sub>2 vl\<^sub>2 vl1'"
    and isObs: "isObs s\<^sub>1" "isObs s\<^sub>2"
  hence \<open>hopeless s' vl' \<or> hopeless s1' vl1' \<or> getObs s\<^sub>1 = getObs s\<^sub>2 \<and> \<Lambda>1 s' vl' s1' vl1'\<close>
    using major unfolding saction_def apply -
    apply (erule allE[where x = s'],  erule allE[where x = vl'], 
           erule allE[where x = s1'], elim impE allE[where x = vl1'])
    by (intro conjI)
  thus "hopeless s' vl' \<or> hopeless s1' vl1' \<or> getObs s\<^sub>1 = getObs s\<^sub>2 \<and> \<Lambda>2 s' vl' s1' vl1'"
    apply auto
    using validTrans apply (rule imp) 
    using consume isObs by auto
qed

lemma unwindFor_impI:
  assumes unwind: \<open>unwindFor \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close> 
      and ialI: \<open>\<And>s\<^sub>1' vl\<^sub>1'. \<lbrakk>\<not>isObs s\<^sub>1; validTrans (s\<^sub>1, s\<^sub>1'); consume s\<^sub>1 vl\<^sub>1 vl\<^sub>1'; \<Lambda>1 s\<^sub>1' vl\<^sub>1' s\<^sub>2 vl\<^sub>2;
                   \<not>hopeless s\<^sub>1' vl\<^sub>1'\<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1' vl\<^sub>1' s\<^sub>2 vl\<^sub>2\<close>
      and iarI: \<open>\<And>s\<^sub>2' vl\<^sub>2'. \<lbrakk>\<not>isObs s\<^sub>2; validTrans (s\<^sub>2, s\<^sub>2'); consume s\<^sub>2 vl\<^sub>2 vl\<^sub>2'; \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2' vl\<^sub>2';
                   \<not>hopeless s\<^sub>2' vl\<^sub>2'\<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2' vl\<^sub>2'\<close>
      and saI: \<open>\<And>s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2'. \<lbrakk>validTrans (s\<^sub>1, s\<^sub>1'); validTrans (s\<^sub>2, s\<^sub>2'); \<Lambda>1 s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2';
                  consume s\<^sub>1 vl\<^sub>1 vl\<^sub>1'; consume s\<^sub>2 vl\<^sub>2 vl\<^sub>2'; isObs s\<^sub>1; isObs s\<^sub>2; getObs s\<^sub>1 = getObs s\<^sub>2;
                  \<not> hopeless s\<^sub>1' vl\<^sub>1'; \<not> hopeless s\<^sub>2' vl\<^sub>2'
            \<rbrakk> \<Longrightarrow> \<Lambda>2 s\<^sub>1' vl\<^sub>1' s\<^sub>2' vl\<^sub>2'\<close>
    shows \<open>unwindFor \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2\<close>
  using unwind proof safe
  assume "iactionLeft \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
  thus "iactionLeft \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    using ialI by (rule iactionLeft_impI)
next
  assume "iactionRight \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
  thus "iactionRight \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    using iarI by (rule iactionRight_impI)
next
  assume "saction \<Lambda>1 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
  thus "saction \<Lambda>2 s\<^sub>1 vl\<^sub>1 s\<^sub>2 vl\<^sub>2"
    using saI by (rule saction_impI)
qed

end (* locale BD_Security_TS *)

end
