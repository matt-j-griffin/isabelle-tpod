theory Cond_Abstract_BD_Security
  imports Abstract_BD_Security_Extensions
begin

locale Cond_Abstract_BD_Security = 
(* NB: The secrets, the states and the bound are the same. 
*)
(* Original semantics: *)
 Van: Abstract_BD_Security validTrace\<^sub>v\<^sub>a\<^sub>n S\<^sub>v\<^sub>a\<^sub>n O\<^sub>v\<^sub>a\<^sub>n B\<^sub>v\<^sub>a\<^sub>n TT\<^sub>v\<^sub>a\<^sub>n
+   
(* Augmented semantics: *)
 Opt: Abstract_BD_Security validTrace\<^sub>o\<^sub>p\<^sub>t S\<^sub>o\<^sub>p\<^sub>t O\<^sub>o\<^sub>p\<^sub>t B\<^sub>o\<^sub>p\<^sub>t TT\<^sub>o\<^sub>p\<^sub>t
for
  validTrace\<^sub>v\<^sub>a\<^sub>n :: "'traces\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> bool" and 
  validTrace\<^sub>o\<^sub>p\<^sub>t :: "'traces\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> bool"
and
  S\<^sub>v\<^sub>a\<^sub>n :: "'traces\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'secrets\<^sub>v\<^sub>a\<^sub>n" and S\<^sub>o\<^sub>p\<^sub>t :: "'traces\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> 'secrets\<^sub>o\<^sub>p\<^sub>t"
and
  O\<^sub>v\<^sub>a\<^sub>n :: "'traces\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'observations\<^sub>v\<^sub>a\<^sub>n" and O\<^sub>o\<^sub>p\<^sub>t :: "'traces\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> 'observations\<^sub>o\<^sub>p\<^sub>t"
and 
  B\<^sub>v\<^sub>a\<^sub>n :: "'secrets\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'secrets\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> bool" and B\<^sub>o\<^sub>p\<^sub>t :: "'secrets\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> 'secrets\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> bool"
and
  TT\<^sub>v\<^sub>a\<^sub>n :: "'traces\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> bool" and TT\<^sub>o\<^sub>p\<^sub>t :: "'traces\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> bool"
+
fixes B\<^sub>c\<^sub>t\<^sub>r :: \<open>'secrets\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'secrets\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> bool\<close>

begin 

definition
  B :: \<open>'secrets\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'secrets\<^sub>v\<^sub>a\<^sub>n \<Rightarrow> 'secrets\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> 'secrets\<^sub>o\<^sub>p\<^sub>t \<Rightarrow> bool\<close>
where
  \<open>B csl\<^sub>1 csl\<^sub>2 sl\<^sub>1 sl\<^sub>2 \<equiv> B\<^sub>v\<^sub>a\<^sub>n csl\<^sub>1 csl\<^sub>2 \<and> B\<^sub>o\<^sub>p\<^sub>t sl\<^sub>1 sl\<^sub>2 \<and> B\<^sub>c\<^sub>t\<^sub>r csl\<^sub>1 sl\<^sub>1 \<and> B\<^sub>c\<^sub>t\<^sub>r csl\<^sub>2 sl\<^sub>2\<close>

definition
  ForAll_ForAll_CSecure :: bool
where
  \<open>ForAll_ForAll_CSecure \<equiv> \<forall>ctr\<^sub>1 ctr\<^sub>2 tr\<^sub>1 tr\<^sub>2. TT\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and> TT\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> TT\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> TT\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 
     \<and> validTrace\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 \<and> validTrace\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 \<and> validTrace\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 \<and> validTrace\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2 
     \<and> B (S\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1) (S\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2) (S\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1) (S\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2) 
     \<and> O\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>1 = O\<^sub>v\<^sub>a\<^sub>n ctr\<^sub>2 
    \<longrightarrow> O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>1 = O\<^sub>o\<^sub>p\<^sub>t tr\<^sub>2\<close>


end (* Cond_Abstract_BD_Security *)

end
