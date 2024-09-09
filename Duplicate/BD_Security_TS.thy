(* BD Security for Transition Systems *)


theory BD_Security_TS
  imports Abstract_BD_Security 
    "../General_Preliminaries/Filtermap_Extensions" 
    "../General_Preliminaries/Transition_System"
begin


declare Let_def[simp]

no_notation relcomp (infixr "O" 75)


locale BD_Security_TS = Transition_System istate validTrans srcOf tgtOf
 for istate :: "'state \<Rightarrow> bool" and validTrans :: "'trans \<Rightarrow> bool"
     and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
+
fixes (* secret filtering and production:  *)
   isSec :: "'trans \<Rightarrow> bool" and getSec :: "'trans \<Rightarrow> 'secret"
 and (* observation filtering and production: *)
   isObs :: "'trans \<Rightarrow> bool" and getObs :: "'trans \<Rightarrow> 'obs"
 and (* declassification trigger:  *)
   T :: "'trans \<Rightarrow> bool"
 and (* declassification bound: *)
   B :: "'state \<Rightarrow> 'secret list \<Rightarrow> 'state \<Rightarrow> 'secret list \<Rightarrow> bool"
begin

(* The secrecy function: *)
definition S :: "'trans list \<Rightarrow> 'secret list" where "S \<equiv> filtermap isSec getSec"
(* The observation function: *)
definition O :: "'trans trace \<Rightarrow> 'obs list" where "O \<equiv> filtermap isObs getObs"

lemma O_map_filter: "O tr = map getObs (filter isObs tr)" unfolding O_def filtermap_map_filter ..
lemma S_map_filter: "S tr = map getSec (filter isSec tr)" unfolding S_def filtermap_map_filter ..

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
unfolding list_ex_iff_length_O by auto

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
"\<lbrakk>reachNT (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
 \<Longrightarrow> reachNT (tgtOf trn)"

lemma reachNT_reach: assumes "reachNT s"  shows "reach s"
using assms apply induct by (auto intro: reach.intros)

(* This is assumed to be an invariant only modulo non T  *)
definition invarNT where
"invarNT Inv \<equiv> 
  \<forall> trn. validTrans trn \<and> reachNT (srcOf trn) \<and> Inv (srcOf trn) \<and> \<not> T trn \<longrightarrow> Inv (tgtOf trn)"

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

(* This is syntactic sugar for the command
sublocale BD_Security_TS \<subseteq> Abstract_BD_Security 
when stated outside the context of BD_Security_TS.
*)                   
sublocale Abstract_BD_Security where
(* 'traces = ('state,'act,'out) trace, 'secrets = 'secret list, 'observations = 'obs list   *)
 istate = istate and validFrom = validFrom
 and S = S and O = O and B = B and TT = "never T" .

thm secureFor_alt

thm secure_alt

lemma S_iff_non_\<phi>[simp]: "S (trn # tr) = S tr \<longleftrightarrow> \<not> isSec trn"
by (cases "isSec trn") auto

lemma S_imp_\<phi>: "S (trn # tr) = v # S tr \<Longrightarrow> isSec trn"
by (cases "isSec trn") auto

lemma S_imp_Nil: "S (trn # tr) = [] \<Longrightarrow> S tr = []"
by (metis S_simps list.distinct)

lemma S_iff_Nil[simp]: "S (trn # tr) = [] \<longleftrightarrow> \<not> isSec trn \<and> S tr = []"
by (metis S_iff_non_\<phi> S_imp_Nil)

definition consume :: "'trans \<Rightarrow> 'secret list \<Rightarrow> 'secret list \<Rightarrow> bool" where
"consume trn vl vl' \<equiv>
 if isSec trn then vl \<noteq> [] \<and> getSec trn = hd vl \<and> vl' = tl vl
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
assumes  "S (trn # tr) = vl" 
shows "\<exists>vl'. consume trn vl vl' \<and> S tr = vl'" 
using assms unfolding consume_def by (cases "isSec trn") auto


(* HOPELESSNESS (inability to produce values) *)

(* No trace starting in state s can produce the values vl: *)
definition hopeless :: "'state \<Rightarrow> 'secret list \<Rightarrow> bool" where 
"hopeless s vl \<equiv> \<forall>tr. validFrom s tr \<and> never T tr \<longrightarrow> S tr \<noteq> vl"

(* Simpler version, amenable to trace-free reasoning: *)
definition hopeless1 :: "'state \<Rightarrow> 'secret \<Rightarrow> bool" where
"hopeless1 s v \<equiv> \<forall> tr trn. validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> isSec trn \<longrightarrow> getSec trn \<noteq> v"

lemma hopeless1_hopeless:
assumes vl: "vl \<noteq> []" and i: "hopeless1 s (hd vl)"
shows "hopeless s vl" 
proof-
  {fix tr assume v: "validFrom s tr" and S: "S tr = vl" and T: "never T tr"
   hence False
   using i v S T proof(induction tr arbitrary: s)
     case Nil thus ?case by (metis S_simps(1) vl)
  next
    case (Cons trn tr s)
    show ?case
    proof(cases "isSec trn")
      case True
      hence "getSec trn = hd vl" using Cons by (metis S_simps(3) hd_Cons_tl list.inject vl)
      moreover have "validFrom s [trn]" using \<open>validFrom s (trn # tr)\<close>
      unfolding validFrom_def by auto
      ultimately show ?thesis using Cons True unfolding hopeless1_def
      by (elim allE[of _ "[]"]) auto
    next
      case False
      hence "S tr = vl" using Cons by auto
      moreover have "never T tr" by (metis Cons.prems list_all_simps)
      moreover from \<open>validFrom s (trn # tr)\<close> have "validFrom (tgtOf trn) tr" and s: "s = srcOf trn"
      using validFrom_Cons apply blast 
      using Cons.prems(1) validFrom_Cons by simp   
      moreover have "hopeless1 (tgtOf trn) (hd vl)" using \<open>hopeless1 s (hd vl)\<close>
      unfolding hopeless1_def s 
      by (metis Cons.prems(1,3) append_Cons list_all_simps(1) validFrom_Cons)
      ultimately show ?thesis using Cons(1) by auto
    qed
  qed
  }
  thus ?thesis unfolding hopeless_def using i vl by auto
qed

(* Trace-free reasoning about hopelessness: *)

lemma hopeless1_coind:
assumes K: "K s"
and I: "\<And> trn. \<lbrakk>K (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
        \<Longrightarrow> (isSec trn \<longrightarrow> getSec trn \<noteq> v) \<and> K (tgtOf trn)"
shows "hopeless1 s v"
using K unfolding hopeless1_def proof(intro allI conjI impI)
  fix tr trn assume "K s" and "validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> isSec trn"
  thus "getSec trn \<noteq> v"
  using I unfolding validFrom_def by (induction tr arbitrary: s trn)
  (auto, metis neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE)
qed

definition noVal where
"noVal K v \<equiv>
 \<forall> trn. validTrans trn \<and> reachNT (srcOf trn) \<and> K (srcOf trn) \<and> 
         isSec trn \<longrightarrow> getSec trn \<noteq> v"

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
"no\<phi> K \<equiv> \<forall> trn. validTrans trn \<and> reachNT (srcOf trn) \<and> K (srcOf trn) 
                 \<longrightarrow> \<not> isSec trn"

lemma no\<phi>_noVal: "no\<phi> K \<Longrightarrow> noVal K v"
unfolding no\<phi>_def noVal_def by auto

(* intro rule for quick inline checks: *)
lemma hopeless1I[consumes 2, induct pred: "hopeless1"]:
assumes rs: "reachNT s" and K: "K s"
and I:
"\<And> trn.
   \<lbrakk>validTrans trn; reach (srcOf trn); reachNT (srcOf trn); K (srcOf trn)\<rbrakk>
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
 \<forall> trn. validTrans trn \<and> reachNT (srcOf trn) \<and> K (srcOf trn) v \<and> isSec trn 
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
   \<lbrakk>validTrans trn; reach (srcOf trn); reachNT (srcOf trn); K (srcOf trn) v\<rbrakk>
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

(* end binary version *)


(* UNWINDING PROOF METHOD *)

(* Independent actions (left and right): *)
definition iactionLeft where
"iactionLeft \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn vl'.
   let s' = tgtOf trn in
   validTrans trn \<and> consume trn vl vl' 
   \<longrightarrow> 
   (\<not> isObs trn \<longrightarrow> hopeless s' vl' \<or> \<Delta> s' vl' s1 vl1) \<and> 
   (isObs trn \<and> vl1 = [] \<longrightarrow> hopeless s' vl')"

definition iactionRight where
"iactionRight \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn1 vl1'.
   let s1' = tgtOf trn1 in
   validTrans trn1 \<and> consume trn1 vl1 vl1' 
   \<longrightarrow> 
   (\<not> isObs trn1 \<longrightarrow> hopeless s1' vl1' \<or> \<Delta> s vl s1' vl1') \<and>
   (isObs trn1 \<and> vl = [] \<longrightarrow> hopeless s1' vl1')"

(* Synchronous action: *)
definition saction where
"saction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> trn vl' trn1 vl1'.
   let s' = tgtOf trn; s1' = tgtOf trn1 in
   validTrans trn \<and> consume trn vl vl' \<and> validTrans trn1 \<and> consume trn1 vl1 vl1' \<and> 
   isObs trn \<and> isObs trn1
   \<longrightarrow>  
   hopeless s' vl' \<or> hopeless s1' vl1' \<or> 
   (getObs trn = getObs trn1 \<and> \<Delta> s' vl' s1' vl1')"

(* *)

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reachNT s1 \<and> 
   \<Delta> s vl s1 vl1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 
   \<or>
   iactionLeft \<Delta> s vl s1 vl1 \<and> 
   iactionRight \<Delta> s vl s1 vl1 \<and> 
   saction \<Delta> s vl s1 vl1"

lemma unwindI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reachNT s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 
   \<or>
   iactionLeft \<Delta> s vl s1 vl1 \<and> 
   iactionRight \<Delta> s vl s1 vl1 \<and> 
   saction \<Delta> s vl s1 vl1"
shows "unwind \<Delta>"
using assms unfolding unwind_def by auto

(* main *) proposition unwind_trace:
assumes unwind: "unwind \<Delta>" and r: "reachNT s" "reachNT s1" "\<Delta> s vl s1 vl1"
and vn: "validFrom s tr" "never T tr" "validFrom s1 tr1" "never T tr1" 
and S: "S tr = vl" "S tr1 = vl1"
shows "O tr = O tr1"
proof- 
  let ?f = "\<lambda> tr tr1. length tr + length tr1"
  show ?thesis
  using r vn S proof(induction tr tr1 arbitrary: s s1 vl vl1 rule: measure_induct2[of ?f] )
    case (IH trr trr1 s s1 vl vl1)
    have nh: "\<not> hopeless s vl \<and> \<not> hopeless s1 vl1" 
      using IH.prems(4,5,6,7,8,9) unfolding hopeless_def by blast
    have ial: "iactionLeft \<Delta> s vl s1 vl1" and 
         iar: "iactionRight \<Delta> s vl s1 vl1" and 
         sa: "saction \<Delta> s vl s1 vl1"  
    using IH.prems(1,2,3) nh unwind unfolding unwind_def by auto  

    show ?case
    proof(cases trr)
      case Nil note trr = Nil
      hence vl: "vl = []" using `S trr = vl` by simp
      show ?thesis 
      proof(cases trr1)
        case Nil thus ?thesis using trr by simp
      next
        case (Cons trn1 tr1) note trr1 = Cons
        then obtain s1' where trn1: "validTrans trn1" "srcOf trn1 = s1" "tgtOf trn1 = s1'"
        using `validFrom s1 trr1`  
        using validFrom_Cons by blast+         
        have s1': "reachNT s1'"   
        using IH.prems(2,7) trr1 trn1 reachNT.Step by auto
        have tr1: "validFrom s1' tr1" "never T tr1" 
          using IH.prems(6) trn1(3) trr1 validFrom_Cons apply blast
          using IH.prems(7) trr1 by auto 
        obtain vl1' where vl1': "consume trn1 vl1 vl1'" and Vtr1: "S tr1 = vl1'"
        using S_Cons_consume `S trr1 = vl1` Cons by blast
        hence nh1': "\<not> hopeless s1' vl1'" 
          using hopeless_def tr1 by blast
          
        have not_g: "\<not> isObs trn1"
        proof 
          assume getObs: "isObs trn1"
          hence "hopeless (tgtOf trn1) vl1'" 
          using iar trn1 getObs vl vl1' unfolding iactionRight_def by auto
          thus False using nh1' trn1 by auto
        qed  
        have D: "\<Delta> s vl s1' vl1'" 
        using iar nh1' not_g trn1 vl1' trn1(1) unfolding iactionRight_def by force
        have "O trr = O tr1"
        apply(rule IH.IH[of trr tr1 s s1' vl vl1'])
        using IH.prems trr1 s1' D tr1 Vtr1 by auto
        thus ?thesis unfolding trr1 using not_g by auto
      qed
    next
      case (Cons trn tr) note trr = Cons
       then obtain s' where trn: "validTrans trn" "srcOf trn = s" "tgtOf trn = s'"
        using `validFrom s trr`  
        using validFrom_Cons by blast+        
      have s': "reachNT s'" 
        using IH.prems(1,5) reachNT.Step trn trr  by auto 
      have tr1: "validFrom s' tr" "never T tr" 
      using IH.prems(4) trn(3) trr validFrom_Cons apply blast
      using IH.prems(5) trr by auto
      obtain vl' where vl': "consume trn vl vl'" and Vtr: "S tr = vl'"
      using S_Cons_consume `S trr = vl` trr by blast
      hence nh': "\<not> hopeless s' vl'" 
      using hopeless_def tr1 by blast
      
      show ?thesis 
      proof(cases "isObs trn")
        case False note not_g = False 
        have D: "\<Delta> s' vl' s1 vl1 " 
        using ial nh' not_g trn vl' trn(1) unfolding iactionLeft_def by force
        have "O tr = O trr1"
        apply(rule IH.IH[of tr trr1 s' s1 vl' vl1])
        using IH.prems trr s' D tr1 Vtr by auto
        thus ?thesis unfolding trr using not_g by auto
      next 
        case True note getObs = True
        show ?thesis
        proof(cases trr1)
          case Nil note trr1 = Nil
          hence vl1: "vl1 = []" using `S trr1 = vl1` by simp                          
          have "hopeless (tgtOf trn) vl'" 
          using getObs ial trn vl1 vl' unfolding iactionLeft_def by auto
          hence False using nh' trn by auto
          thus ?thesis by auto
        next 
          case (Cons trn1 tr1) note trr1 = Cons
          case (Cons trn1 tr1) note trr1 = Cons
          then obtain s1' where trn1: "validTrans trn1" "srcOf trn1 = s1" "tgtOf trn1 = s1'"
          using `validFrom s1 trr1`  
          using validFrom_Cons by blast+         
          have s1': "reachNT s1'"   
          using IH.prems(2,7) trr1 trn1 reachNT.Step by auto
          have tr1: "validFrom s1' tr1" "never T tr1" 
          using IH.prems(6) trn1(3) trr1 validFrom_Cons apply blast
          using IH.prems(7) trr1 by auto 
          obtain vl1' where vl1': "consume trn1 vl1 vl1'" and Vtr1: "S tr1 = vl1'"
          using S_Cons_consume `S trr1 = vl1` Cons by blast
          hence nh1': "\<not> hopeless s1' vl1'" 
          using hopeless_def tr1 by blast
       
          show ?thesis 
          proof(cases "isObs trn1")
            case False note not_g = False 
            have D: "\<Delta> s vl s1' vl1'" 
            using iar nh1' not_g trn1 vl1' trn1(1) unfolding iactionRight_def by force
            have "O trr = O tr1"
            apply(rule IH.IH[of trr tr1 s s1' vl vl1'])
            using IH.prems trr1 s1' D tr1(1)  Vtr1 by auto
            thus ?thesis unfolding trr1 using not_g by auto
          next
            case True note g1 = True 
            have D: "\<Delta> s' vl' s1' vl1'" and geq: "getObs trn = getObs trn1"
            using sa nh' nh1' getObs g1 trn trn1 vl' vl1' trn1(1) unfolding saction_def by force+
            have "O tr = O tr1"
            apply(rule IH.IH[of tr tr1 s' s1' vl' vl1'])
            using IH.prems trr trr1 s' s1' D tr1(1) Vtr Vtr1 trn validFrom_Cons by auto
            thus ?thesis unfolding trr trr1 using getObs g1 geq by auto
          qed
        qed
      qed
    qed
  qed
qed
    
theorem unwind_secure:
assumes init: "\<And> vl vl1 s s1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta> s vl s1 vl1"
and unwind: "unwind \<Delta>"
shows secure
using assms unwind_trace reachNT.Istate unfolding secure_alt by blast


end (* locale BD_Security_TS *)


(* CONDITIONAL VARIANT OF BD SECURITY *)

locale Cond_BD_Security = 
(* NB: The secrets, the bound and the states are the same *)
(* Original semantics: *)
 Orig: BD_Security_TS istate1 validTrans1 srcOf1 tgtOf1
          isSec1 getSec1 isObs1 getObs1 T1 B
+   
(* Augmented semantics: *)
 Aug: BD_Security_TS istate2 validTrans2 srcOf2 tgtOf2
          isSec2 getSec2 isObs2 getObs2 T2 B
for
  istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
and
  validTrans1 :: "'trans1 \<Rightarrow> bool" and validTrans2 :: "'trans2 \<Rightarrow> bool"
and
  srcOf1 and srcOf2 and tgtOf1 and tgtOf2
and 
 isSec1 :: "'trans1 \<Rightarrow> bool" and isSec2 :: "'trans2 \<Rightarrow> bool" and
 getSec1 :: "'trans1 \<Rightarrow> 'secret" and getSec2 :: "'trans2 \<Rightarrow> 'secret"
and 
 isObs1 :: "'trans1 \<Rightarrow> bool" and isObs2 :: "'trans2 \<Rightarrow> bool" and 
 getObs1 :: "'trans1 \<Rightarrow> 'obs1" and getObs2 :: "'trans2 \<Rightarrow> 'obs2"
and 
 T1 :: "'trans1 \<Rightarrow> bool"  and T2 :: "'trans2 \<Rightarrow> bool"
and
 B :: "'state \<Rightarrow> 'secret list \<Rightarrow> 'state \<Rightarrow> 'secret list \<Rightarrow> bool"
begin 

abbreviation "validFrom1 \<equiv> Orig.validFrom"
abbreviation "S1 \<equiv> Orig.S"
abbreviation "O1 \<equiv> Orig.O"

abbreviation "validFrom2 \<equiv> Aug.validFrom"
abbreviation "S2 \<equiv> Aug.S"
abbreviation "O2 \<equiv> Aug.O"

sublocale Cond_Abstract_BD_Security 
  where istate1 = istate1 and istate2 = istate2
  and validFrom1 = validFrom1 and validFrom2 = validFrom2
  and S1 = S1 and S2 = S2
  and O1 = O1 and O2 = O2
  and B = B 
  and TT1 = "never T1" and TT2 = "never T2" 
done
(* now we have inherited the predicate condSecure *)
thm condSecure_def

(* thm condSecure_def Orig.secureFor_def Aug.secureFor_def *)
thm Orig.isLeak_def Aug.isLeak_def

thm secure_condSecure


end (* Cond_BD_Security *)


end

