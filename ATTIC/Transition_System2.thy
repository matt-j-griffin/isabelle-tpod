
chapter \<open>Transition System with two traces\<close>

text \<open>To enable verification of Hyperproperties we extend a transition system 
      to incorporate a left (\<pi>1) and right (\<pi>2) trace. In this example we use the
      same valid_Trans in each trace.\<close>

theory Transition_System2
  imports "Transition_System"
begin

locale Transition_System2 =
  Left: Transition_System istatel validTrans srcOf tgtOf
+
  Right: Transition_System istater validTrans srcOf tgtOf

  for validTrans :: "'trans \<Rightarrow> bool"
  and istatel :: "'state \<Rightarrow> bool"
  and istater :: "'state \<Rightarrow> bool"
  and srcOf :: "'trans \<Rightarrow> 'state"
  and tgtOf :: "'trans \<Rightarrow> 'state"

begin


end

end
