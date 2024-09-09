theory OD
  imports HOL.List
begin


type_synonym 'state trace = \<open>'state list\<close>

text \<open>Definition of OD\<close>

locale OD = 
  fixes Tr :: \<open>'state trace set\<close>
    and ops\<^sub>\<L> :: \<open>'state trace \<Rightarrow> 'lop\<close>
    and low_equiv :: \<open>'state \<Rightarrow> 'state \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<close> 100)
begin

abbreviation 
  low_equivs :: \<open>'state trace \<Rightarrow> 'state trace \<Rightarrow> bool\<close>  (infixl \<open>\<approx>\<^sub>\<L>\<^sub>s\<close> 100)
where
  \<open>low_equivs \<equiv> list_all2 low_equiv\<close> 

abbreviation
  secureFor :: \<open>'state trace \<Rightarrow> 'state trace \<Rightarrow> bool\<close>
where
  \<open>secureFor \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 \<approx>\<^sub>\<L>\<^sub>s \<pi>\<^sub>2\<close>

lemma secureFor_empty[simp]: \<open>secureFor [] []\<close>
  by auto

definition
  secure :: bool
where
  \<open>secure = (\<forall>\<pi>\<^sub>1 \<in> Tr. \<forall>\<pi>\<^sub>2 \<in> Tr. (hd \<pi>\<^sub>1) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>2) \<longrightarrow> secureFor \<pi>\<^sub>1 \<pi>\<^sub>2)\<close>

end

end
