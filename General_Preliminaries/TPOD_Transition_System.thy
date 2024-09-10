theory TPOD_Transition_System
  imports TPOD_Trivia 
          Relative_Security.Transition_System
begin

context Simple_Transition_System
begin

lemma validFromSE: 
  assumes major: \<open>validFromS s sl\<close> \<open>sl \<noteq> []\<close>
      and emptyE: \<open>sl = [] \<Longrightarrow> P\<close> 
      and ConsE: \<open>\<And>x xs. \<lbrakk>sl = (x # xs); x = s; validS (x # xs)\<rbrakk> \<Longrightarrow> P\<close> 
  shows P
  using major apply (cases sl)
  apply simp
  apply simp
  unfolding validFromS_def apply auto
  apply (erule ConsE)
  by simp_all


lemma validFromS_length_le_1: 
  assumes \<open>validFromS s sl\<close>
    shows \<open>length sl \<le> Suc 0 \<longleftrightarrow> sl = [] \<or> sl = [s]\<close>
using assms unfolding le_Suc_eq le_zero_eq length_0_conv apply (intro iffI)
  subgoal
    using validFromS_singl_iff
    by (metis Suc_length_conv length_0_conv)
  subgoal
    apply (elim disjE)
    unfolding Suc_length_conv le_Suc_eq
    by simp_all
  .

end (* context Simple_Transition_System *)

context System_Mod
begin 

lemma validFromS_alwaysE: (* might not be needed *)
  assumes \<open>final s\<close> and \<open>validFromS s tr\<close> and \<open>Q s\<close> and \<open>list_all Q tr \<Longrightarrow> P\<close>
      and \<open>tr \<noteq> []\<close>
    shows P
  using assms unfolding validFromS_def apply auto
using assms unfolding validFromS_def 
proof auto
  assume "tr \<noteq> []"  "final (hd tr)" "Q (hd tr)" "list_all Q tr \<Longrightarrow> P" "validS tr" "s = hd tr"
    thus ?thesis
      apply (induct tr rule: list_nonempty_induct, auto)
      by (metis Simple_Transition_System.validFromS_Cons_iff Simple_Transition_System.validFromS_def final_def)
  qed

end

end


