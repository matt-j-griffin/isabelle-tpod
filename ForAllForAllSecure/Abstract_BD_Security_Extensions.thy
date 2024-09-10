(*<*)
theory Abstract_BD_Security_Extensions
  imports Bounded_Deducibility_Security.Abstract_BD_Security
begin
(*>*)

section \<open>BD Security Extensions\<close>

subsection \<open>ForAll-ForAll and ForAll-Exists secure\<close>

context Abstract_BD_Security
begin

text \<open>Abbreviations for consistency with the thesis\<close>

abbreviation \<open>ForAll_Exists_Secure \<equiv> secure\<close>

text \<open>Alternate definition of security ForAll-ForAll-Secure, quantified universally for both
      traces.\<close>

abbreviation
  ForAll_ForAll_Secure_For :: \<open>'traces \<Rightarrow> 'traces \<Rightarrow> bool\<close>
where
  \<open>ForAll_ForAll_Secure_For tr\<^sub>1 tr\<^sub>2 \<equiv> validSystemTrace tr\<^sub>1 \<and> validSystemTrace tr\<^sub>2 \<and> TT tr\<^sub>1 \<and> TT tr\<^sub>2
    \<and> B (V tr\<^sub>1) (V tr\<^sub>2) \<longrightarrow> O tr\<^sub>1 = O tr\<^sub>2\<close>

definition 
  ForAll_ForAll_Secure :: bool 
where
  \<open>ForAll_ForAll_Secure \<equiv> \<forall>tr\<^sub>1 tr\<^sub>2. ForAll_ForAll_Secure_For tr\<^sub>1 tr\<^sub>2\<close>

lemma ForAll_ForAll_SecureE:
  assumes \<open>ForAll_ForAll_Secure\<close> and \<open>validSystemTrace tr\<^sub>1\<close> and \<open>validSystemTrace tr\<^sub>2\<close> 
      and \<open>TT tr\<^sub>1\<close> and \<open>TT tr\<^sub>2\<close>
      and \<open>B (V tr\<^sub>1) (V tr\<^sub>2)\<close>
    shows \<open>O tr\<^sub>1 = O tr\<^sub>2\<close>
using assms unfolding ForAll_ForAll_Secure_def by auto

end (* context Abstract_BD_Security *)

(*<*)
end
(*>*)
