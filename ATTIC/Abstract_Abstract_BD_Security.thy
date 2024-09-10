theory Abstract_Abstract_BD_Security
  imports Main
begin

print_classes

class_deps

no_notation relcomp (infixr "O" 75)

(* This locale is the mother of both 
the standard (\<forall>\<exists> version of) and \<forall>\<forall> version of BD security . *)

locale Abstract_Abstract_BD_Security = 
  fixes istate :: "'states \<Rightarrow> bool"
  and B :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
  and isLeak :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
begin 

definition secureFor :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool" where
"secureFor s vl s' vl' \<equiv> B s vl s' vl' \<longrightarrow> \<not> isLeak s vl s' vl'"

definition secure :: bool where
"secure \<equiv> \<forall> s vl s' vl'. istate s \<and> istate s' \<longrightarrow> secureFor s vl s' vl'"

end  (* context Abstract_Abstract_BD_Security *)


(* CONDITIONAL VERSION *)

(* Conditional formulation: *)
locale Cond_Abstract_Abstract_BD_Security = 
(* NB: The secrets and the bound are the same, but the 
 notion of leakage is different. 
(For the states, we can later refine to a forgetful function 
from the augmented semantics state to the original semantics state.)
*)
(* Original semantics: *)
Orig: Abstract_Abstract_BD_Security istate1 B isLeak1 + 
(* Augmented semantics: *)
Aug: Abstract_Abstract_BD_Security istate2 B isLeak2
for istate1 :: "'states \<Rightarrow> bool" and istate2 :: "'states \<Rightarrow> bool" 
and B :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
and isLeak1 :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
and isLeak2 :: "'states \<Rightarrow> 'secrets \<Rightarrow> 'states \<Rightarrow> 'secrets \<Rightarrow> bool"
begin

abbreviation "secureFor1 \<equiv> Orig.secureFor"
abbreviation "secure1 \<equiv> Orig.secure"

abbreviation "secureFor2 \<equiv> Aug.secureFor"
abbreviation "secure2 \<equiv> Aug.secure"

(* Conditional security: *)
definition condSecure :: bool where
"condSecure \<equiv>
 \<forall> s vl s' vl'. istate1 s \<and> istate1 s' \<and> istate2 s \<and> istate2 s' \<and> secureFor1 s vl s' vl' 
                \<longrightarrow> secureFor2 s vl s' vl'"

lemma condSecure_alt: 
"condSecure \<longleftrightarrow>
 (\<forall> s vl s' vl'. istate1 s \<and> istate1 s' \<and> istate2 s \<and> istate2 s' \<and> 
    B s vl s' vl' \<and> isLeak2 s vl s' vl' \<longrightarrow> isLeak1 s vl s' vl')"
unfolding condSecure_def Orig.secureFor_def Aug.secureFor_def by auto

lemma secure_condSecure: 
"Orig.secure \<Longrightarrow> condSecure \<Longrightarrow> (\<forall>s. istate2 s \<longrightarrow> istate1 s) \<longrightarrow> Aug.secure"
  unfolding Orig.secure_def condSecure_def Aug.secure_def by auto


end (* Cond_Abstract_Abstract_BD_Security *)


end