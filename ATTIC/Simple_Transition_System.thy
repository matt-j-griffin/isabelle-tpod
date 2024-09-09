theory Simple_Transition_System 
imports Main 
begin

(* Transition system where transitions are just pairs of states *)

locale Simple_Transition_System = 
fixes istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<Rightarrow> 'state  \<Rightarrow> bool"

locale System_Model = 
Simple_Transition_System istate validTrans   
for istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<Rightarrow> 'state  \<Rightarrow> bool"
+
fixes final :: "'state \<Rightarrow> bool"
assumes final_def: "final s1 \<longleftrightarrow> (\<forall>s2. \<not> validTrans s1 s2)" 

(* Assuming the transitions are deterministic: *)
locale System_Model_Deterministic = 
System_Model istate validTrans final
for istate :: "'state \<Rightarrow> bool"
and validTrans :: "'state \<Rightarrow> 'state  \<Rightarrow> bool"
and final :: "'state \<Rightarrow> bool"
+  
fixes "next" :: "'state \<Rightarrow> 'state"
assumes validTrans_iff_next: "validTrans s1 s2 \<longleftrightarrow> \<not> final s1 \<and> next s1 = s2"


type_synonym 'state trace = "nat \<Rightarrow> 'state"

context System_Model
begin 

(* validity as a finite trace: *)
definition validF :: "'state trace \<Rightarrow> bool" where
"validF tr \<equiv> \<exists>n. (\<forall>i<n. validTrans (tr i) (tr (Suc i))) \<and> (\<forall>i\<ge>n. final (tr i))" 

(* validity as an infinite trace: *)
definition validI :: "'state trace \<Rightarrow> bool" where
"validI tr \<equiv> \<forall>i. validTrans (tr i) (tr (Suc i))" 

definition valid :: "'state trace \<Rightarrow> bool" where
"valid tr \<equiv> validF tr \<or> validI tr" 

lemma validF_imp_not_validI: 
"validF tr \<Longrightarrow> \<not> validI tr"
unfolding validF_def validI_def final_def by auto

lemma validI_imp_not_validF: 
"validI tr \<Longrightarrow> \<not> validF tr"
unfolding validF_def validI_def final_def by auto

(* The length of a finite trace: *)
definition len :: "'state trace \<Rightarrow> nat" where 
"len tr \<equiv> LEAST n. \<forall>i\<ge>n. final (tr i)"

lemma gt_len_final: 
assumes "validF tr" and "i \<ge> len tr" 
shows "final (tr i)"
using assms unfolding validF_def len_def by (smt (verit, ccfv_threshold) LeastI)

lemma final_len: 
"validF tr \<Longrightarrow> final (tr (len tr))"
by (simp add: gt_len_final)

lemma ls_len_not_final_valid: 
assumes "valid tr" and "i < len tr" 
shows "\<not> final (tr i)"
using assms unfolding validF_def len_def 
apply(cases "validF tr")
  subgoal by (smt (verit, del_insts) Least_le dual_order.strict_trans1 final_def validF_def)
  subgoal unfolding final_def valid_def validI_def by auto .

lemma ls_len_not_final_validF: 
assumes "validF tr" and "i < len tr" 
shows "\<not> final (tr i)"
by (simp add: assms ls_len_not_final_valid valid_def)

lemma not_final_validI: 
assumes "validI tr" 
shows "\<not> final (tr i)"
using assms final_def validI_def by auto

end (* context Simple_Transition_System *)


end