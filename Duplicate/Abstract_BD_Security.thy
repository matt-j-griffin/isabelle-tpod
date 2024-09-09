theory Abstract_BD_Security
  imports Abstract_Abstract_BD_Security 
(* Bounded_Deducibility_Security.Bounded_Deducibility_Security *)
begin

locale Abstract_BD_Security =
 fixes
  istate :: "'states \<Rightarrow> bool" and 
  validFrom :: "'states \<Rightarrow> 'traces \<Rightarrow> bool"
and
  S :: "'traces \<Rightarrow> 'secrets"
and
  O :: "'traces \<Rightarrow> 'observations"
and (* declassification bound: *)
  B :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
and (* declassification trigger: *)
  TT :: "'traces \<Rightarrow> bool"
begin

(* BD security: *)
definition isLeak :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets  \<Rightarrow> bool" where 
"isLeak s vl s' vl' \<equiv> 
 \<exists>tr tr'. validFrom s tr \<and> TT tr \<and> validFrom s' tr' \<and> TT tr' \<and> 
          S tr = vl \<and> S tr' = vl' \<and> O tr \<noteq> O tr'"

sublocale Abstract_Abstract_BD_Security where B = B and isLeak = isLeak .
(* now we have inherited the predicate secure *)
term secure

lemma secureFor_alt: 
"secureFor s vl s' vl' \<longleftrightarrow> 
 (\<forall> tr tr'.
   validFrom s tr \<and> TT tr \<and> validFrom s' tr' \<and> TT tr' \<and> 
   S tr = vl \<and> S tr' = vl' \<and> 
   B s vl s' vl' \<longrightarrow>
   O tr = O tr')" 
unfolding secureFor_def isLeak_def by auto

thm secure_def

lemma secure_alt: 
"secure \<longleftrightarrow> 
 (\<forall> s tr s' tr'.
   istate s \<and> validFrom s tr \<and> TT tr \<and> istate s' \<and> validFrom s' tr' \<and> 
   TT tr' \<and> B s (S tr) s' (S tr') 
   \<longrightarrow>
   O tr = O tr')" 
unfolding secure_def secureFor_alt by auto

end (* context BD_Security *)



(* CONDITIONAL VERSION *)


locale Cond_Abstract_BD_Security = 
(* NB: The secrets, the states and the bound are the same. 
*)
(* Original semantics: *)
 Orig: Abstract_BD_Security istate1 validFrom1 S1 O1 B TT1
+   
(* Augmented semantics: *)
 Aug: Abstract_BD_Security istate2 validFrom2 S2 O2 B TT2
for
  istate1 :: "'states \<Rightarrow> bool" and istate2 :: "'states \<Rightarrow> bool"
and
  validFrom1 :: "'states \<Rightarrow> 'traces1 \<Rightarrow> bool" and 
  validFrom2 :: "'states \<Rightarrow> 'traces2 \<Rightarrow> bool"
and
  S1 :: "'traces1 \<Rightarrow> 'secrets" and S2 :: "'traces2 \<Rightarrow> 'secrets"
and
  O1 :: "'traces1 \<Rightarrow> 'observations1" and O2 :: "'traces2 \<Rightarrow> 'observations2"
and 
  B :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
and 
  TT1 :: "'traces1 \<Rightarrow> bool" and TT2 :: "'traces2 \<Rightarrow> bool"
begin 

abbreviation "isLeak1 \<equiv> Orig.isLeak"
abbreviation "isLeak2 \<equiv> Aug.isLeak"

sublocale Cond_Abstract_Abstract_BD_Security 
  where B = B and isLeak1 = isLeak1 and isLeak2 = isLeak2 .
(* now we have inherited the predicate condSecure *)
term condSecure

thm condSecure_alt

thm secure_condSecure

end (* Cond_Abstract_BD_Security *)


(* A version of the locale where we have the same observation domain. 
(For higher flexibility, we can have a version with different domains 
and a surjective function between them.)
*)

locale Cond_Abstract_BD_Security_same_obsDomain = 
Cond_Abstract_BD_Security 
   istate istate
   validFrom1 validFrom2
   S1 S2 O1 O2 B TT1 TT2
for istate validFrom1 validFrom2 S1 S2 
and O1 :: "'traces1 \<Rightarrow> 'observations"
and O2 :: "'traces2 \<Rightarrow> 'observations"
and B TT1 TT2
begin

(* Criterion for proving conditional \<forall>\<forall> BD Security: *)
lemma crit_condSecure: 
assumes 
"\<And> s tr2. validFrom2 s tr2 \<and> TT2 tr2 \<Longrightarrow> 
   \<exists>tr1. validFrom1 s tr1 \<and> TT1 tr1 \<and> O1 tr1 = O2 tr2 \<and> S1 tr1 = S2 tr2"
shows condSecure 
unfolding condSecure_alt Orig.isLeak_def Aug.isLeak_def by (metis assms)


(* Question: Is this sufficient to handle 
more precise versions of the cases from the Cheung paper? 
Do the observations fulfil the conditions from that paper? 
*)

end (* Cond_Abstract_BD_Security_same_obsDomain *)




end
