theory OD
  imports Main
begin

type_synonym 'state trace = \<open>'state list\<close>

class low_equiv =
  fixes low_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<approx>\<^sub>\<L>\<close> 100)


instantiation list :: (low_equiv) low_equiv 
begin

definition
  low_equiv_list :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>
where
  \<open>low_equiv_list \<equiv> list_all2 low_equiv\<close>

instance ..

end


text \<open>Definition of OD\<close>

locale OD =
  fixes Tr :: \<open>('state::low_equiv) trace set\<close>
    and ops\<^sub>\<L> :: \<open>'state trace \<Rightarrow> 'lop\<close>
begin

abbreviation
  secureFor :: \<open>'state trace \<Rightarrow> 'state trace \<Rightarrow> bool\<close>
where
  \<open>secureFor \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> ops\<^sub>\<L> \<pi>\<^sub>1 = ops\<^sub>\<L> \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 \<approx>\<^sub>\<L> \<pi>\<^sub>2\<close>

lemma secureFor_empty[simp]: \<open>secureFor [] []\<close>
  unfolding low_equiv_list_def by auto

definition
  secure :: bool
where
  \<open>secure = (\<forall>\<pi>\<^sub>1 \<in> Tr. \<forall>\<pi>\<^sub>2 \<in> Tr. (hd \<pi>\<^sub>1) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>2) \<longrightarrow> secureFor \<pi>\<^sub>1 \<pi>\<^sub>2)\<close>

end

end
