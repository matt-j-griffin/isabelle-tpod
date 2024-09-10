(* 
Capturing the standard, forall-exist version of BD security 
from the Archive of Formal Proofs: 
https://www.isa-afp.org/entries/Bounded_Deducibility_Security.html
Can be imported as follows: 
imports Bounded_Deducibility_Security.Bounded_Deducibility_Security 
*)

theory FE_Abstract_BD_Security
imports Abstract_Abstract_BD_Security 
begin

locale FE_Abstract_BD_Security =
 fixes
  validSystemTrace :: "'traces \<Rightarrow> bool"
and
  S :: "'traces \<Rightarrow> 'secrets"
and
  O :: "'traces \<Rightarrow> 'observations"
and (* declassification bound: *)
  B :: "'secrets \<Rightarrow> 'secrets \<Rightarrow> bool"
and (* declassification trigger: *)
  TT :: "'traces \<Rightarrow> bool"
begin

(* BD security: *)
definition isLeak :: "'secrets \<Rightarrow> 'secrets \<Rightarrow> bool" where 
"isLeak sl sl' \<equiv> 
 \<exists>tr. validSystemTrace tr \<and> TT tr \<and> S tr = sl \<and> 
 (\<forall> tr'. validSystemTrace tr' \<and> S tr' = sl' \<longrightarrow> O tr \<noteq> O tr')"

sublocale Abstract_Abstract_BD_Security where B = B and isLeak = isLeak .
(* now we have inherited the predicate secure *)
term secure

(* The standard formulation of \<forall>\<exists> version of BD security: *)
definition secure_altDef :: bool where
"secure_altDef \<equiv>
 \<forall> tr vl vl'.
   validSystemTrace tr \<and> TT tr \<and> B vl vl' \<and> S tr = vl \<longrightarrow>
   (\<exists> tr'. validSystemTrace tr' \<and> O tr' = O tr \<and> S tr' = vl')"

lemma secure_altDef_secure: "secure_altDef \<longleftrightarrow> secure" 
  unfolding secure_altDef_def secure_def isLeak_def secureFor_def by fastforce

end (* context FE_Abstract_BD_Security *)


locale FE_Cond_Abstract_BD_Security = 
(* NB: The secrets and the bound are the same *)
(* Original semantics: *)
 Orig: FE_Abstract_BD_Security validSystemTrace1 S1 O1 B TT1
+   
(* Augmented semantics: *)
 Aug: FE_Abstract_BD_Security validSystemTrace2 S2 O2 B TT2
for
  validSystemTrace1 :: "'traces1 \<Rightarrow> bool" and validSystemTrace2 :: "'traces2 \<Rightarrow> bool"
and
  S1 :: "'traces1 \<Rightarrow> 'secrets" and S2 :: "'traces2 \<Rightarrow> 'secrets"
and
  O1 :: "'traces1 \<Rightarrow> 'observations1" and O2 :: "'traces2 \<Rightarrow> 'observations2"
and 
  B :: "'secrets \<Rightarrow> 'secrets \<Rightarrow> bool"
and 
  TT1 :: "'traces1 \<Rightarrow> bool" and TT2 :: "'traces2 \<Rightarrow> bool"
begin 

abbreviation "isLeak1 \<equiv> Orig.isLeak"
abbreviation "isLeak2 \<equiv> Aug.isLeak"

sublocale Cond_Abstract_Abstract_BD_Security 
  where B = B and isLeak1 = isLeak1 and isLeak2 = isLeak2 .
(* now we have inherited the predicate condSecure *)
term condSecure

lemma condSecure_altDef: 
"condSecure \<longleftrightarrow> 
 (\<forall> sl sl'. B sl sl' \<and> isLeak2 sl sl' \<longrightarrow> isLeak1 sl sl')"
unfolding condSecure_def Orig.secureFor_def Aug.secureFor_def by auto

lemma secure_condSecure: 
"Orig.secure \<Longrightarrow> condSecure \<Longrightarrow> Aug.secure"
  unfolding Orig.secure_def condSecure_def Aug.secure_def by auto

end (* FE_Cond_Abstract_BD_Security *)


(* A version of the locale where we have the same observation domain. 
(For higher flexibility, we can have a version with different domains 
and a surjective function between them.)
*)

locale FE_Cond_Abstract_BD_Security_same_obsDomain = 
FE_Cond_Abstract_BD_Security 
   validSystemTrace1 validSystemTrace2
   S1 S2 O1 O2 B TT1 TT2
for validSystemTrace1 validSystemTrace2 S1 S2 
and O1 :: "'traces1 \<Rightarrow> 'observations"
and O2 :: "'traces2 \<Rightarrow> 'observations"
and B TT1 TT2
begin

(* Criterion for proving conditional \<exists>\<forall> BD Security. 
Unlike with the \<forall>\<forall>-variant, here we need a back and forth condition: 
*)
lemma crit_condSecure: 
assumes 
"\<And>tr2. validSystemTrace2 tr2 \<and> TT2 tr2 \<Longrightarrow> 
   \<exists>tr1. validSystemTrace1 tr1 \<and> TT1 tr1 \<and> O1 tr1 = O2 tr2 \<and> S1 tr1 = S2 tr2"
and 
"\<And>tr1. validSystemTrace1 tr1  \<Longrightarrow> 
   \<exists>tr2. validSystemTrace2 tr2 \<and> TT2 tr2 \<and> O1 tr1 = O2 tr2 \<and> S1 tr1 = S2 tr2"
shows condSecure
using assms 
unfolding condSecure_def Orig.secureFor_def Aug.secureFor_def
    Orig.isLeak_def Aug.isLeak_def by metis


end (* FE_Cond_Abstract_BD_Security_same_obsDomain *)


end
