theory BD_TPOD
  imports Observational_Determinism
begin


(* CONDITIONAL VARIANT OF OBSERVATIONAL DETERMINISM *)

locale Cond_OD = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: OD istate1 validTrans1 srcOf1 tgtOf1 lowEquiv lowOp1 
+   
(* Augmented semantics (same lowEquiv) : *)
 Aug:  OD istate2 validTrans2 srcOf2 tgtOf2 lowEquiv lowOp2

  for istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
  and validTrans1 :: "'trans1 \<Rightarrow> bool" and validTrans2 :: "'trans2 \<Rightarrow> bool"
  and srcOf1 and srcOf2 and tgtOf1 and tgtOf2
  and lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
  and lowOp1 :: "'trans1 \<Rightarrow> 'lowOp" and lowOp2 :: "'trans2 \<Rightarrow> 'lowOp"
(*+
assumes equivp_validTrans1_lowEquiv: \<open>equivp Orig.trans_lowEquiv\<close>
*)
begin 

abbreviation "secureFor1 \<equiv> Orig.secureFor"
abbreviation "valid1 \<equiv> Orig.valid"
abbreviation "validFrom1 \<equiv> Orig.validFrom"
(* *)
abbreviation "secureFor2 \<equiv> Aug.secureFor"
abbreviation "valid2 \<equiv> Aug.valid"
abbreviation "validFrom2 \<equiv> Aug.validFrom"

(* Conditional security: *)

definition condSecure :: bool where
"condSecure \<equiv>
 \<forall> s s' lops. 
   istate1 s \<and> istate1 s' \<and> istate2 s \<and> istate2 s' \<and> secureFor1 s s' lops \<longrightarrow> secureFor2 s s' lops"

(* 
definition condSecure'' :: bool where
"condSecure'' \<equiv>
 \<forall> s1 s1' lops. 
   istate1 s1 \<and> istate1 s1' \<and> secureFor1 s1 s1' lops \<longrightarrow> 
   (\<exists>s2 s2'. lowEquiv s1 s2 \<and> lowEquiv s1' s2' \<and> 
             istate2 s2 \<and> istate2 s2' \<and> secureFor2 s2 s2' lops)"
*)


(* Stronger variant: *)
definition condSecure' :: bool where
"condSecure' \<equiv>
 \<forall> s1 s1' s2 s2' lops. 
   istate1 s1 \<and> istate1 s1' \<and> istate2 s2 \<and> istate2 s2' \<and> 
   lowEquiv s1 s2 \<and> lowEquiv s1' s2' \<and>
   secureFor1 s1 s1' lops \<longrightarrow> secureFor2 s2 s2' lops"
(* lowEquiv s1 s2 \<and> lowEquiv s1' s2' not needed *)

(*
 1 leq 2
      
 3 leq 4
*)

lemma condSecure'_implies_condSecure: \<open>condSecure' \<Longrightarrow> condSecure\<close>
  unfolding condSecure_def condSecure'_def apply auto
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=lops in allE)
  apply (erule impE)
  apply simp_all
  
  using Orig.lowEquiv_classes_eq_imp_low_equiv by blast

(* NB: The two locales are already instances of BD_Security_TS,
so they already the BD Security operators: *)

abbreviation "isSec1 \<equiv> Orig.isSec"
abbreviation "getSec1 \<equiv> Orig.getSec"
abbreviation "isObs1 \<equiv> Orig.isObs"
abbreviation "getObs1 \<equiv> Orig.getObs"
abbreviation "T1 \<equiv> Orig.T"

abbreviation "isSec2 \<equiv> Aug.isSec"
abbreviation "getSec2 \<equiv> Aug.getSec"
abbreviation "isObs2 \<equiv> Aug.isObs"
abbreviation "getObs2 \<equiv> Aug.getObs"
abbreviation "T2 \<equiv> Aug.T"
abbreviation "B2 \<equiv> Aug.B"

abbreviation "B \<equiv> Orig.B"

(* The two bounds are the same: *)
lemma "Orig.B = Aug.B" ..

(* Now, the current sublocale is a sublocale 
of conditional BD security: *)
sublocale asCondBD: Cond_BD_Security 
   where istate1 = istate1 and istate2 = istate2
     and validTrans1 = validTrans1 and validTrans2 = validTrans2
     and srcOf1 = srcOf1 and srcOf2 = srcOf2
     and tgtOf1 = tgtOf1 and tgtOf2 = tgtOf2
     and isSec1 = isSec1 and isSec2 = isSec2 
     and getSec1 = getSec1 and getSec2 = getSec2 
     and isObs1 = isObs1 and isObs2 = isObs2
     and getObs1 = getObs1 and getObs2 = getObs2
     and T1 = T1 and T2 = T2
     and B = B
done 

(* ... and conditional OD (as formulated, i.e., fixing not only 
the states s and s' but also the list of low observations lobs), 
is indeed a particular case of conditional BD Security. 
This is expressed as the equality between the condSecure predicate 
defined directly for OD and the condSecure predicate that comes from 
BD security: 
*)
(*
lemma condSecure_imp_asCondBD: "condSecure \<longrightarrow> asCondBD.condSecure" 
  unfolding condSecure_def asCondBD.condSecure_def apply clarify
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (case_tac \<open>vl = [] \<or> vl' = [] \<or> vl \<noteq> vl' \<or> \<not> lowEquiv s s'\<close>)
  using Aug.implies_secureFor apply blast
  apply (erule_tac x=vl' in allE)
  apply (elim impE conjE)  
  using Orig.secureFor_imp_asBD_secureFor apply blast
  oops

lemma asCondBD_imp_condSecure: 
  assumes asCondBD.condSecure 
    shows condSecure 
  using assms unfolding condSecure_def asCondBD.condSecure_def apply clarify
  apply (erule_tac x=s in allE)
  apply (erule_tac x=lops in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=lops in allE)
  apply safe
  using equivp_validTrans1_lowEquiv 
  apply (drule_tac s=s and s'=s' and lops=lops in Orig.asBD_secureFor_imp_secureFor, blast+)
  by (drule Aug.secureFor_imp_asBD_secureFor, blast)
*)
(*
lemma condSecure_iff_asCondBD: "condSecure \<longleftrightarrow> asCondBD.condSecure" 
  using condSecure_imp_asCondBD asCondBD_imp_condSecure by blast
*)

end (* Cond_OD *)

(*
locale Strict_Cond_OD = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: Strict_OD istate1 validTrans1 srcOf1 tgtOf1 lowEquiv1 lowOp1 
+   
(* Augmented semantics (same lowEquiv) : *)
 Aug:  OD istate2 validTrans2 srcOf2 tgtOf2 lowEquiv2 lowOp2

for istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
  and validTrans1 :: "'trans1 \<Rightarrow> bool" and validTrans2 :: "'trans2 \<Rightarrow> bool"
  and srcOf1 and srcOf2 and tgtOf1 and tgtOf2
  and lowEquiv1 :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
  and lowEquiv2 :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
  and lowOp1 :: "'trans1 \<Rightarrow> 'lowOp" and lowOp2 :: "'trans2 \<Rightarrow> 'lowOp"
+
assumes lowEquiv1_imp_lowEquiv2: \<open>\<And>s s'. lowEquiv1 s s' \<Longrightarrow> lowEquiv2 s s'\<close>

begin 

(*
sublocale asCond_OD: Cond_OD
   where istate1 = istate1 and istate2 = istate2
     and validTrans1 = validTrans1 and validTrans2 = validTrans2
     and srcOf1 = srcOf1 and srcOf2 = srcOf2 
     and tgtOf1 = tgtOf1 and tgtOf2 = tgtOf2
     and lowEquiv = lowEquiv2
     and lowOp1 = lowOp1 and lowOp2 = lowOp2
  by standard
*)
abbreviation "secureFor1 \<equiv> Orig.secureFor"
abbreviation "valid1 \<equiv> Orig.valid"
abbreviation "validFrom1 \<equiv> Orig.validFrom"
abbreviation "secureFor2 \<equiv> Aug.secureFor"
abbreviation "valid2 \<equiv> Aug.valid"
abbreviation "validFrom2 \<equiv> Aug.validFrom"


(* Conditional security: *)

definition condSecure :: bool where
"condSecure \<equiv>
 \<forall> s s' lops. 
   istate1 s \<and> istate1 s' \<and> istate2 s \<and> istate2 s' \<and> secureFor1 s s' lops \<longrightarrow> secureFor2 s s' lops"

(* 
definition condSecure'' :: bool where
"condSecure'' \<equiv>
 \<forall> s1 s1' lops. 
   istate1 s1 \<and> istate1 s1' \<and> secureFor1 s1 s1' lops \<longrightarrow> 
   (\<exists>s2 s2'. lowEquiv s1 s2 \<and> lowEquiv s1' s2' \<and> 
             istate2 s2 \<and> istate2 s2' \<and> secureFor2 s2 s2' lops)"
*)


(* Stronger variant: *)
(*
definition condSecure' :: bool where
"condSecure' \<equiv>
 \<forall> s1 s1' s2 s2' lops. 
   istate1 s1 \<and> istate1 s1' \<and> istate2 s2 \<and> istate2 s2' \<and> 
   lowEquiv1 s1 s2 \<and> lowEquiv s1' s2' \<and>
   secureFor1 s1 s1' lops \<longrightarrow> secureFor2 s2 s2' lops"
*)
(* lowEquiv s1 s2 \<and> lowEquiv s1' s2' not needed *)

(*
 1 leq 2
      
 3 leq 4
*)
(*
lemma condSecure'_implies_condSecure: 
"condSecure' \<Longrightarrow> condSecure"
  unfolding condSecure_def condSecure'_def apply auto
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=lops in allE)
  apply (erule impE)
  by simp_all
*)
(* NB: The two locales are already instances of BD_Security_TS,
so they already the BD Security operators: *)

abbreviation "isSec1 \<equiv> Orig.isSec"
abbreviation "getSec1 \<equiv> Orig.getSec"
abbreviation "isObs1 \<equiv> Orig.isObs"
abbreviation "getObs1 \<equiv> Orig.getObs"
abbreviation "T1 \<equiv> Orig.T"

abbreviation "isSec2 \<equiv> Aug.isSec"
abbreviation "getSec2 \<equiv> Aug.getSec"
abbreviation "isObs2 \<equiv> Aug.isObs"
abbreviation "getObs2 \<equiv> Aug.getObs"
abbreviation "T2 \<equiv> Aug.T"
abbreviation "B2 \<equiv> Aug.B"

abbreviation "B \<equiv> Orig.B"

(* Now, the current sublocale is a sublocale 
of conditional BD security: *)
sublocale asCondBD: Cond_BD_Security 
   where istate1 = istate1 and istate2 = istate2
     and validTrans1 = validTrans1 and validTrans2 = validTrans2
     and srcOf1 = srcOf1 and srcOf2 = srcOf2
     and tgtOf1 = tgtOf1 and tgtOf2 = tgtOf2
     and isSec1 = isSec1 and isSec2 = isSec2 
     and getSec1 = getSec1 and getSec2 = getSec2 
     and isObs1 = isObs1 and isObs2 = isObs2
     and getObs1 = getObs1 and getObs2 = getObs2
     and T1 = T1 and T2 = T2
     and B = B2
done 

(* ... and conditional OD (as formulated, i.e., fixing not only 
the states s and s' but also the list of low observations lobs), 
is indeed a particular case of conditional BD Security. 
This is expressed as the equality between the condSecure predicate 
defined directly for OD and the condSecure predicate that comes from 
BD security: 
*)


lemma condSecure_imp_asCondBD: "condSecure \<longrightarrow> asCondBD.condSecure" 
  unfolding condSecure_def asCondBD.condSecure_def apply clarify
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s' in allE)
  apply (case_tac \<open>vl = [] \<or> vl' = [] \<or> vl \<noteq> vl' \<or> \<not> lowEquiv2 s s'\<close>)
  apply (frule_tac Aug.implies_secureFor)
  apply clarify
  apply (erule_tac x=vl' in allE)
  apply (elim impE conjE)
  apply clarify
  using Aug.B_def Orig.asBD.secureFor_def Orig.secureFor_imp_asBD_secureFor asCondBD.Orig.secureFor_def apply auto[1]
  using Aug.secureFor_imp_asBD_secureFor
  sledgehammer
 
  apply safe
  using Aug.asBD.secureFor_def Orig.asBD.secureFor_def Orig.secureFor_imp_asBD_secureFor asCondBD.Orig.secureFor_def apply blast
  apply (elim notE)

  using Orig.secureFor_imp_asBD_secureFor


  
  sorry

lemma asCondBD_imp_condSecure: "asCondBD.condSecure --> condSecure" 
  unfolding condSecure_def asCondBD.condSecure_def apply clarify
  apply (erule_tac x=s in allE)
  apply (erule_tac x=lops in allE)
  apply (erule_tac x=s' in allE)
  apply (erule_tac x=lops in allE)
  apply safe
  using Orig.secureFor_iff_asBD_secureFor apply auto[1]
  defer
  using Aug.secureFor_imp_asBD_secureFor apply simp
  sorry
(*  by (simp add: Aug.secureFor_imp_asBD_secureFor)*)

lemma condSecure_iff_asCondBD: "condSecure \<longleftrightarrow> asCondBD.condSecure" 
  using condSecure_imp_asCondBD asCondBD_imp_condSecure by blast


end (* Cond_OD *)
*)

(******************)
(* TPOD *)
(*****************)

(* So far, high operations were not needed. Now we introduce them, in order to define 
TPOD: *)


locale OD_plus_highOps = OD istate validTrans srcOf tgtOf lowEquiv lowOp
(* we want sets *)
  for istate :: "'state \<Rightarrow> bool" and validTrans :: "'trans \<Rightarrow> bool"
     and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
     and lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
     and lowOp :: "'trans \<Rightarrow> 'lowOp"
+
(* M&B: relationship between lowOp and highOp in your semantics: 
define highOp and then take lowOp to be the complement? - YES
*)

  fixes highOp :: "'trans \<Rightarrow> 'highOp"
begin

definition highOpT :: "'trans list \<Rightarrow> 'highOp list" where 
"highOpT tr \<equiv> map highOp tr"

end 



locale TPOD = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: OD_plus_highOps istate1 validTrans1 srcOf1 tgtOf1
          lowEquiv lowOp1 highOp1 
+   
(* Augmented semantics (same lowEquiv) : *)
 Aug: OD_plus_highOps istate2 validTrans2 srcOf2 tgtOf2
          lowEquiv lowOp2 highOp2
for
  istate1 :: "'state \<Rightarrow> bool" and istate2 :: "'state \<Rightarrow> bool"
and
  validTrans1 :: "'trans1 \<Rightarrow> bool" and validTrans2 :: "'trans2 \<Rightarrow> bool"
and
  srcOf1 and srcOf2 and tgtOf1 and tgtOf2
and 
 lowEquiv :: "'state \<Rightarrow> 'state \<Rightarrow> bool" 
and lowOp1 :: "'trans1 \<Rightarrow> 'lowOp" and lowOp2 :: "'trans2 \<Rightarrow> 'lowOp"
and highOp1 :: "'trans1 \<Rightarrow> 'highOp" and highOp2 :: "'trans2 \<Rightarrow> 'highOp"
(* TPOD adds the trace property T such that violation of T introduced a
new counterexample to observational determinism. *)
(*and T :: \<open>'state list \<Rightarrow> bool\<close>*) (* I'm not su*)
+
fixes speculating :: \<open>'trans2 \<Rightarrow> bool\<close>
(*
assumes equivp_validTrans1_lowEquiv: \<open>equivp Orig.trans_lowEquiv\<close>
*)
begin 

sublocale Cond_OD where 
 istate1 = istate1 and istate2 = istate2
and
 validTrans1 = validTrans1 and validTrans2 = validTrans2
and
 srcOf1 = srcOf1 and srcOf2 = srcOf2 and tgtOf1 = tgtOf1 and tgtOf2 = tgtOf2
and 
 lowEquiv = lowEquiv
and lowOp1 = lowOp1 and lowOp2 = lowOp2 
  by standard 

abbreviation "lowEquivT1 \<equiv> Orig.lowEquivT"
abbreviation "lowOpT1 \<equiv> Orig.lowOpT"  
abbreviation "highOpT1 \<equiv> Orig.highOpT" 
abbreviation "tracesLeakVia1 \<equiv> Orig.tracesLeakVia" 
abbreviation "tracesLeak1 \<equiv> Orig.tracesLeak" 

interpretation lowEquivT1: list_all2_lemmas lowEquivT1 Orig.lowEquivTrans
  by (rule Orig.list_all2_lemmas_lowEquivT)

abbreviation "lowEquivT2 \<equiv> Aug.lowEquivT"
abbreviation "lowOpT2 \<equiv> Aug.lowOpT"
abbreviation "highOpT2 \<equiv> Aug.highOpT" 
abbreviation "tracesLeakVia2 \<equiv> Aug.tracesLeakVia" 
abbreviation "tracesLeak2 \<equiv> Aug.tracesLeak" 

interpretation lowEquivT2: list_all2_lemmas lowEquivT2 Aug.lowEquivTrans
  by (rule Aug.list_all2_lemmas_lowEquivT)

(* TPOD and friends *)

definition 
  stutterT :: "'trans2 \<Rightarrow> 'trans1 \<Rightarrow> bool" 
where
  \<open>stutterT trn2 trn1 = (
    if speculating trn2 
      then srcOf1 trn1 = tgtOf1 trn1
      else srcOf1 trn1 \<noteq> tgtOf1 trn1
  )\<close>

definition
  counterpart_stutterT :: "'trans2 list \<Rightarrow> 'trans1 list \<Rightarrow> bool" 
where
  \<open>counterpart_stutterT = list_all2 stutterT\<close>

lemma list_all2_lemmas_counterpart_stutterT: \<open>list_all2_lemmas counterpart_stutterT stutterT\<close>
  unfolding counterpart_stutterT_def apply standard
  by blast

interpretation counterpart_stutterT: list_all2_lemmas counterpart_stutterT stutterT
  using list_all2_lemmas_counterpart_stutterT .

definition 
  counterpart :: "'state \<Rightarrow> 'trans2 list \<Rightarrow> 'state \<Rightarrow> 'trans1 list \<Rightarrow> bool" 
where 
"counterpart s2 tr2 s1 tr1 \<equiv> 
 lowOpT2 tr2 = lowOpT1 tr1 \<and> highOpT2 tr2 = highOpT1 tr1 
  \<and> counterpart_stutterT tr2 tr1"

definition tracesOK1 :: "'trans1 list \<Rightarrow> 'trans1 list \<Rightarrow> bool" where 
"tracesOK1 tr tr' \<equiv> lowOpT1 tr = lowOpT1 tr' \<and> lowEquivT1 tr tr'"

lemma tracesOK1_empty[simp]: \<open>tracesOK1 [] []\<close>
  unfolding tracesOK1_def by auto

lemma tracesOK1_length: 
  assumes \<open>tracesOK1 tr tr'\<close>
    shows \<open>length tr = length tr'\<close>
  using assms unfolding tracesOK1_def by (simp add: lowEquivT1.lengthD)


lemma tracesOK1_validFrom_lowEquiv:
  assumes \<open>tracesOK1 tr tr'\<close>
      and \<open>validFrom1 s tr\<close> and \<open>validFrom1 s' tr'\<close>
      and \<open>tr \<noteq> []\<close>
    shows \<open>lowEquiv s s'\<close>
  using assms apply (frule_tac tracesOK1_length)
  unfolding tracesOK1_def Orig.validFrom_def apply safe
  using Orig.lowEquivT_def2 by blast

  

definition tpod :: bool where 
"tpod \<equiv> \<forall>s2 tr2 s2' tr2' s1 tr1 s1' tr1'.
   counterpart s2 tr2 s1 tr1 \<and> counterpart s2' tr2' s1' tr1' 
   \<and> 
   istate1 s1 \<and> istate1 s1' \<and> validFrom1 s1 tr1 \<and> validFrom1 s1' tr1' 
   \<and> tracesOK1 tr1 tr1' 
   \<and> 
   istate2 s2 \<and> istate2 s2' \<and> validFrom2 s2 tr2 \<and> validFrom2 s2' tr2' 
   \<longrightarrow> 
   \<not> tracesLeak2 s2 tr2 s2' tr2'"


(* Unwinding theorem for TPOD: *)

definition initCond :: "('state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where 
"initCond \<Delta> \<equiv> \<forall>s2 s2' s1 s1'. 
   istate2 s2 \<and> istate2 s2' \<and> istate1 s1 \<and> istate1 s1' \<and> 
   lowEquiv s1 s1'
   \<longrightarrow> \<Delta> s2 s2' s1 s1'"

definition unwindCond :: "('state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where 
"unwindCond \<Delta> \<equiv> \<forall>s2 s2' s1 s1'. 
 \<Delta> s2 s2' s1 s1' \<and> lowEquiv s2 s2' \<and> lowEquiv s1 s1' \<longrightarrow> 
 (\<forall>trn2 ss2 trn2' ss2' trn1 ss1 trn1' ss1'. 
   validTrans2 trn2 \<and> validTrans2 trn2' \<and> 
   srcOf2 trn2 = s2 \<and> tgtOf2 trn2 = ss2 \<and> srcOf2 trn2' = s2' \<and> 
   tgtOf2 trn2' = ss2' \<and> lowOp2 trn2 = lowOp2 trn2' 
   \<and>
   validTrans1 trn1 \<and> validTrans1 trn1' \<and> 
   srcOf1 trn1 = s1 \<and> tgtOf1 trn1 = ss1 \<and> srcOf1 trn1' = s1' \<and> 
   tgtOf1 trn1' = ss1' \<and> lowOp1 trn1 = lowOp1 trn1' \<and> 

   lowOp1 trn1 = lowOp2 trn2 \<and> 
   highOp1 trn1 = highOp2 trn2 \<and> highOp1 trn1' = highOp2 trn2' \<and>
   stutterT trn2 trn1 \<and> stutterT trn2' trn1'
   \<and> 
   lowEquiv ss1 ss1'
   \<longrightarrow> 
   \<Delta> ss2 ss2' ss1 ss1' \<and> lowEquiv ss2 ss2')"

lemma unwindCond_secureFor: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> s2 s2' s1 s1'" 
and v: "validFrom2 s2 tr2" "validFrom2 s2' tr2'" "validFrom1 s1 tr1" "validFrom1 s1' tr1'"
and c: "lowOpT2 tr2 = lowOpT1 tr1"   "highOpT2 tr2 = highOpT1 tr1" 
       "lowOpT2 tr2' = lowOpT1 tr1'" "highOpT2 tr2' = highOpT1 tr1'"
and s: "counterpart_stutterT tr2 tr1" "counterpart_stutterT tr2' tr1'"
and ok: "tracesOK1 tr1 tr1'"
shows "\<not> tracesLeak2 s2 tr2 s2' tr2'"
proof -
  {
    assume "length tr2 = length tr2'" "length tr2' = length tr1" "length tr1 = length tr1'"
    hence ?thesis 
      using \<Delta> v c ok s proof(induction tr2 tr2' tr1 tr1' arbitrary: s2 s2' s1 s1' rule: list_induct4)
        case (Nil s2 s2' s1 s1')
        thus ?case by auto
      next 
        case (Cons trn2 tr2 trn2' tr2' trn1 tr1 trn1' tr1' s2 s2' s1 s1')
        obtain ss2 ss2'
          where ss2: "srcOf2 trn2 = s2" "tgtOf2 trn2 = ss2" "validFrom2 ss2 tr2"
            and ss2': "srcOf2 trn2' = s2'" "tgtOf2 trn2' = ss2'" "validFrom2 ss2' tr2'"
          using Aug.validFrom_Cons Cons.prems(2) Cons.prems(3) by blast
        obtain ss1 ss1' 
          where ss1: "srcOf1 trn1 = s1" "tgtOf1 trn1 = ss1" "validFrom1 ss1 tr1"
            and ss1': "srcOf1 trn1' = s1'" "tgtOf1 trn1' = ss1'" "validFrom1 ss1' tr1'"
          using Cons.prems(4) Cons.prems(5) Orig.validFrom_Cons by blast
        {
          assume ls: "lowEquiv s2 s2'" 
             and "lowOpT2 (trn2 # tr2) = lowOpT2 (trn2' # tr2')" 
             and "lowOpT2 (trn2 # tr2) = lowOpT2 (trn2' # tr2')" 
          hence lt: "lowOp2 trn2 = lowOp2 trn2'" "lowOpT2 tr2 = lowOpT2 tr2'"
            by (auto simp: Aug.lowOpT_def)
          have dlss: "\<Delta> ss2 ss2' ss1 ss1' \<and> lowEquiv ss2 ss2'" 
            apply(rule unwind[unfolded unwindCond_def, rule_format, 
                              of s2 s2' s1 s1' trn2 trn2' _ _ trn1 trn1' _])
            using Cons.prems ls lt ss1 ss1' ss2 ss2' apply safe
            using tracesOK1_validFrom_lowEquiv apply blast
            using Aug.validFrom_Cons apply blast+
            using Orig.validFrom_Cons apply blast+
            unfolding tracesOK1_def Orig.lowOpT_def apply (metis list.inject list.simps(9))
            apply (simp add: Aug.lowOpT_def)
            apply (metis OD_plus_highOps.highOpT_def Orig.OD_plus_highOps_axioms list.inject list.simps(9))
            apply (metis OD_plus_highOps.highOpT_def Orig.OD_plus_highOps_axioms list.inject list.simps(9))
            using counterpart_stutterT.Cons apply blast
            using counterpart_stutterT.Cons apply blast
            using Orig.lowEquivT_Cons by blast
      note dss = dlss[THEN conjunct1] and lss = dlss[THEN conjunct2] 
      hence cp: "lowOpT2 tr2 = lowOpT1 tr1 \<and> highOpT2 tr2 = highOpT1 tr1"  
        using Cons.prems(6,7)
        unfolding Aug.lowOpT_def Orig.lowOpT_def Aug.highOpT_def Orig.highOpT_def 
        by auto
      have cp': "lowOpT2 tr2' = lowOpT1 tr1' \<and> highOpT2 tr2' = highOpT1 tr1'" 
        using Cons.prems(8,9)
      unfolding Aug.lowOpT_def Orig.lowOpT_def Aug.highOpT_def Orig.highOpT_def 
        by auto
      have ntrl: "\<not> tracesLeak2 ss2 tr2 ss2' tr2'" apply(rule Cons.IH[OF dss])
        using cp cp' ss2 ss2' ss1 ss1' Cons.prems(10) counterpart_def lt(2) tracesOK1_def 
        apply auto
        using Cons.prems(11, 12) counterpart_stutterT.Cons by blast+
      have let2: "lowEquivT2 tr2 tr2'"
        using ntrl lss lt(2) unfolding Aug.tracesLeak_def by auto
      have "lowEquivT2 (trn2 # tr2) (trn2' # tr2')"  
        by (simp add: let2 ls lss ss2'(1) ss2'(2) ss2(1) ss2(2))
     } 
     thus ?case unfolding Aug.tracesLeak_def by auto
   qed
  }
  thus ?thesis 
    using c unfolding Aug.tracesLeak_def counterpart_def 
    by (metis Aug.lowOpT_def Orig.lowOpT_def map_eq_imp_length_eq)
qed

theorem unwind_secure: 
  assumes \<open>initCond \<Delta>\<close>
      and \<open>unwindCond \<Delta>\<close>
    shows tpod
  using assms unfolding tpod_def counterpart_def initCond_def 
  apply (intro allI impI notI)
  apply (elim conjE)
  apply (erule_tac x=s2 in allE)
  apply (erule_tac x=s2' in allE)
  apply (erule_tac x=s1 in allE)
  apply (erule_tac x=s1' in allE)
  apply (elim impE conjE)
  apply clarify
  using tracesOK1_validFrom_lowEquiv 
  apply (metis Aug.not_tracesLeak_NilL counterpart_stutterT_def list_all2_Nil2)

  apply (case_tac \<open>tr2 = []\<close>)
  using Aug.not_tracesLeak_NilL apply blast
  apply (case_tac \<open>tr1 = []\<close>)
  apply (metis Aug.lowOpT_def Nil_is_map_conv Orig.lowOpT_def)
  apply (case_tac \<open>tr2' = []\<close>)
  using Aug.not_tracesLeak_NilR apply blast
  apply (case_tac \<open>tr1' = []\<close>)
   apply (simp add: Orig.lowEquivT_def tracesOK1_def)

  by (frule unwindCond_secureFor, blast+)


(* Compositional version: *)
definition 
  unwindIntoCond :: "'pcounter set \<Rightarrow> 'pcounter \<Rightarrow> ('pcounter \<Rightarrow> 'pcounter) \<Rightarrow> ('pcounter \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" 
where 
  "unwindIntoCond PC first next \<Delta>s \<equiv> \<forall>pc\<in>PC. \<forall>s2 s2' s1 s1'. 
    \<Delta>s pc s2 s2' s1 s1' \<and> lowEquiv s2 s2' \<and> lowEquiv s1 s1' \<longrightarrow> 
 (\<forall>trn2 ss2 trn2' ss2' trn1 ss1 trn1' ss1'. 
   validTrans2 trn2 \<and> validTrans2 trn2' \<and> 
   srcOf2 trn2 = s2 \<and> tgtOf2 trn2 = ss2 \<and> srcOf2 trn2' = s2' \<and> 
   tgtOf2 trn2' = ss2' \<and> lowOp2 trn2 = lowOp2 trn2' 
   \<and>
   validTrans1 trn1 \<and> validTrans1 trn1' \<and> 
   srcOf1 trn1 = s1 \<and> tgtOf1 trn1 = ss1 \<and> srcOf1 trn1' = s1' \<and> 
   tgtOf1 trn1' = ss1' \<and> lowOp1 trn1 = lowOp1 trn1' \<and> 
   lowOp1 trn1 = lowOp2 trn2 \<and> highOp1 trn1 = highOp2 trn2 \<and> highOp1 trn1' = highOp2 trn2'
   \<and> 
   stutterT trn2 trn1 \<and> stutterT trn2' trn1' \<and>
   lowEquiv ss1 ss1'
   \<longrightarrow> 
   \<Delta>s (next pc) ss2 ss2' ss1 ss1' \<and> lowEquiv ss2 ss2')"


theorem compositional_unwind_secure:
  assumes i: "initCond (\<Delta>s first)" 
      and u: "unwindIntoCond PC first next \<Delta>s"
      and PC_closed: "first \<in> PC" "\<And>pc. pc \<in> PC \<longrightarrow> next pc \<in> PC"
    shows tpod
proof-
  define \<Delta> 
    where "\<Delta> \<equiv> \<lambda>s2 s2' s1 s1'. \<exists>pc \<in> PC. \<Delta>s pc s2 s2' s1 s1'"
  have "initCond \<Delta>" 
    using i PC_closed(1) unfolding \<Delta>_def initCond_def by blast
  moreover have "unwindCond \<Delta>" 
    using u PC_closed(2) unfolding \<Delta>_def unwindCond_def unwindIntoCond_def by blast
  ultimately show ?thesis 
    using unwind_secure by blast
qed


(*    *)
(* The more natural (but less effective) version of tpod. 
It is closer in spirit to conditional security:
*)

definition tpod' :: bool where 
"tpod' \<equiv> \<forall>s2 tr2 s2' tr2'.
   (\<forall>s1 tr1 s1' tr1'. 
      counterpart s2 tr2 s1 tr1 \<and> counterpart s2' tr2' s1' tr1' \<and>     
      istate1 s1 \<and> istate1 s1' \<and> validFrom1 s1 tr1 \<and> validFrom1 s1' tr1'
      \<longrightarrow>  
      \<not> tracesLeak1 s1 tr1 s1' tr1')
   \<and> 
   istate2 s2 \<and> istate2 s2' \<and> validFrom2 s2 tr2 \<and> validFrom2 s2' tr2' 
   \<longrightarrow> 
   \<not> tracesLeak2 s2 tr2 s2' tr2'"

lemma counterpart_length: "counterpart s2 tr2 s1 tr1 \<Longrightarrow> length tr2 = length tr1"
unfolding counterpart_def Aug.lowOpT_def Orig.lowOpT_def 
using map_eq_imp_length_eq by fastforce

lemma aux_impI:
"(\<And>sl2 sl2' sl1 sl1'. \<phi> sl2 sl2' sl1 sl1' \<longrightarrow> \<psi> sl2 sl2' sl1 sl1')
 \<Longrightarrow>
 (\<forall>sl2 sl2' sl1 sl1'. \<phi> sl2 sl2' sl1 sl1') \<Longrightarrow>
 (\<forall>sl2 sl2' sl1 sl1'. \<psi> sl2 sl2' sl1 sl1')"
  by auto

(*
lemma tpod_implies_tpod':
  assumes counter: "\<forall>s2 tr2. istate2 s2 \<and> validFrom2 s2 tr2 \<longrightarrow> 
            (\<exists>s1 tr1. istate1 s1 \<and> validFrom1 s1 tr1 \<and> counterpart s2 tr2 s1 tr1)" 
      and tpod: tpod
    shows tpod' 
  unfolding tpod'_def apply (intro allI)
  using counter 
  apply (erule_tac x=s2 in allE)
  apply (erule_tac x=tr2 in allE)
  using counter 
  apply (erule_tac x=s2' in allE)
  apply (erule_tac x=tr2' in allE)
  apply safe
  apply (erule_tac x=s1 in allE)
  apply (erule_tac x=tr1 in allE)
  apply (erule_tac x=s1a in allE)
  apply (erule_tac x=tr1a in allE)
  
  using tpod unfolding tpod_def
  apply (erule_tac x=s2 in allE)
  apply (erule_tac x=tr2 in allE)
  apply (erule_tac x=s2' in allE)
  apply (erule_tac x=tr2' in allE)
  apply (erule_tac x=s1 in allE)
  apply (erule_tac x=tr1 in allE)
  apply (erule_tac x=s1a in allE)
  apply (erule_tac x=tr1a in allE)
  apply safe

  unfolding Orig.tracesLeak_def tracesOK1_def apply simp
  apply (erule impE)
  apply (metis Aug.tracesLeak_def counterpart_def)
  apply (case_tac \<open>lowEquivT1 tr1 tr1a\<close>, simp_all)
  apply (simp add: Aug.tracesLeak_def counterpart_def tracesOK1_def)
  unfolding Aug.tracesLeak_def  apply safe
  apply (simp add: counterpart_def tracesOK1_def)
  apply auto
  sledgehammer


  apply (intro allI impI, elim conjE)
*)

(*
proof(intro allI impI, elim conjE)
  fix s2 tr2 s2' tr2' 
  assume 0: "\<forall>s1 tr1 s1' tr1'.
          counterpart s2 tr2 s1 tr1 \<and> counterpart s2' tr2' s1' tr1' \<and> 
          istate1 s1 \<and> istate1 s1' \<and> 
          validFrom1 s1 tr1 \<and> validFrom1 s1' tr1'
          \<longrightarrow>
          \<not> tracesLeak1 s1 tr1 s1' tr1'"
     and 1: "istate2 s2" "istate2 s2'" "validFrom2 s2 tr2" "validFrom2 s2' tr2'"
  from 1 
  obtain s1 tr1 s1' tr1' 
    where 2: 
    "istate1 s1 \<and> validFrom1 s1 tr1 \<and> counterpart s2 tr2 s1 tr1"
    "istate1 s1' \<and> validFrom1 s1' tr1' \<and> counterpart s2' tr2' s1' tr1'"
      using counter by presburger
  {
    assume "lowEquiv s2 s2'" "lowOpT2 tr2 = lowOpT2 tr2'" 
    with 0 have 3: " tracesOK1 tr1 tr1'" 
      apply (subgoal_tac "\<not> tracesLeak1 s1 tr1 s1' tr1'") defer
      using "2"(1) "2"(2) apply blast
      unfolding tracesOK1_def apply (intro conjI)
      apply (metis "2"(1) "2"(2) counterpart_def)
      unfolding Orig.tracesLeak_def apply auto
      apply (metis "2"(1) "2"(2) counterpart_def)
      apply (erule_tac x=s1 in allE)
      apply (erule_tac x=tr1 in allE)
      apply (erule_tac x=s1' in allE)
      apply (erule_tac x=tr1' in allE)
      using 2 apply safe
      using counterpart_def apply fastforce
      sledgehammer

      apply (simp add: "2"(1))

      by (metis "2"(1) "2"(2) counterpart_def)

    have "\<not> tracesLeak2 s2 tr2 s2' tr2'"
      apply(rule tpod[unfolded tpod_def, rule_format])
      using 1 2 3 by auto 
  }
  thus "\<not> tracesLeak2 s2 tr2 s2' tr2'"  
    unfolding Aug.tracesLeak_def by auto
qed
*)

(* TPOD implies conditional security (even the strong version): *)
(*
(* TPOD implies conditional security: *)
>>>>>>> Stashed changes
lemma tpod_implies_condSecure':
  assumes counter: \<open>\<forall>s2 tr2 s1. istate2 s2 \<and> validFrom2 s2 tr2 \<and> istate1 s1 \<longrightarrow> 
               (\<exists>tr1. validFrom1 s1 tr1 \<and> counterpart s2 tr2 s1 tr1  \<and> nomispredT tr1)\<close>
      and t: tpod
    shows condSecure'
unfolding condSecure'_def proof safe
  fix s1 s1' s2 s2' lops
  assume s: "istate1 s1" "istate1 s1'" "istate2 s2" "istate2 s2'" 
  and sec: "secureFor1 s1 s1' lops"
  show "secureFor2 s2 s2' lops"  
  unfolding Aug.secureFor_def proof (intro allI impI, elim conjE)
    fix tr2 tr2' assume v: "validFrom2 s2 tr2" "validFrom2 s2' tr2'"
    with counter obtain tr1 tr1' where 
    vtr1: "validFrom1 s1 tr1" "counterpart s2 tr2 s1 tr1" "nomispredT tr1"
          "validFrom1 s1' tr1'" "counterpart s2' tr2' s1' tr1'"  "nomispredT tr1'"
      using s by meson
    {assume l: "lowEquiv s2 s2'" "lowOpT2 tr2 = lops" "lowOpT2 tr2' = lops"
     then have ntl: "\<not> tracesLeak2 s2 tr2 s2' tr2'" 
     apply(intro t[unfolded tpod_def, rule_format, of _ _ s1 tr1 _ _ s1' tr1'])
       using s l v vtr1 apply (auto simp add: tracesOK1_def counterpart_def) 
      (* Andrei to Matt: I don't remember what was the status of this: 
  was the proof already broken or did it break in response to recent changes? *) sorry
     (* by (metis (full_types) Orig.lowEquiv_classes_equal Orig.secureFor_def Orig.tracesLeakVia_def sec) *)
(*       using sec unfolding Orig.secureFor_def Orig.tracesLeakVia_def apply safe 
       apply (erule_tac x=tr1 in allE)
       apply (erule_tac x=tr1' in allE)
       apply safe
       by (metis (full_types) )*)

     have "lowEquivT2 tr2 tr2'" using l ntl unfolding Aug.tracesLeak_def by auto
    }
    thus "\<not> tracesLeakVia2 s2 tr2 s2' tr2' lops" unfolding Aug.tracesLeakVia_def by auto
  qed
qed

(* NB: TPOD' does not imply conditional security because the latter quantfies 
universally over s2 and s2'. *)


(* So we have : 

TODO \<rightarrow> TPOD \<Rightarrow> condSecure'

TPOD \<Rightarrow> TPOD'
TPOD \<Rightarrow> condSecure' \<Rightarrow> condSecure
               
In summary:
-- I defined conditional security in general, for (the \<forall>\<forall> variant of) BD security
-- I showed that conditional BD security yields a natural notion of conditional OD 
(the counterpart of conditional noninterference)
-- I showed that TPOD implies conditional OD 
-- And I have an unwinding proof rule for TPOD, including a compositional version

TODO: 
 -- match the compositional compositional version of TPOD unwinding with what M&B prove concretely
 -- unwinding proof rules for TPOD' and conditional OD
*)
*)
end (* locale TPOD *)


end
