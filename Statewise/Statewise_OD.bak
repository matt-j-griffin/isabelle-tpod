theory Statewise_OD
  imports
    "../Duplicate/BD_Security_STS"
    "../OD"
    "HOL-ex.Sketch_and_Explore" (* TODO *)
begin

locale Statewise_OD = System_Model istate validTrans final
  for istate :: \<open>('state::low_equiv) \<Rightarrow> bool\<close> and validTrans :: \<open>'state \<times> 'state \<Rightarrow> bool\<close>
  and final :: \<open>'state \<Rightarrow> bool\<close>
+ 
fixes isInter :: \<open>'state \<Rightarrow> bool\<close> and op\<^sub>\<L> :: \<open>'state \<Rightarrow> 'lowOp\<close>

  assumes isInter_not_final: \<open>\<And>x. final x \<Longrightarrow> \<not> isInter x\<close>
      assumes equivp_lowEquiv: \<open>\<And>x y. \<lbrakk>isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y\<rbrakk> \<Longrightarrow> x \<approx>\<^sub>\<L> y = ((\<approx>\<^sub>\<L>) x = (\<approx>\<^sub>\<L>) y)\<close> (* Equivalence under assumptions *)

      and reflp_lowEquiv: \<open>reflp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>
      and symp_lowEquiv: \<open>symp ((\<approx>\<^sub>\<L>)::'state \<Rightarrow> 'state \<Rightarrow> bool)\<close>

      and low_equiv_interE: \<open>\<And>x y. \<lbrakk>x \<approx>\<^sub>\<L> y; isInter x \<longleftrightarrow> isInter y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>
(*
fixes TEST :: "'lowOp set"
*)
begin
(*
(*equivp TEST *) 
abbreviation "EXAMPLE x y \<equiv> ((isInter x \<longleftrightarrow> isInter y) \<and> ((isInter x \<longrightarrow> (op\<^sub>\<L> x \<in> TEST \<and> op\<^sub>\<L> y \<in> TEST)) \<longrightarrow> x = y)) "

lemma "EXAMPLE x y \<Longrightarrow> isInter x \<longleftrightarrow> isInter y"
  by auto

lemma reflp_E: \<open>reflp EXAMPLE\<close>
  unfolding reflp_def by auto

lemma symp_E: \<open>symp EXAMPLE\<close>
  unfolding symp_def by auto

lemma transp_asms: \<open>\<And>x y z. \<lbrakk>isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y\<rbrakk> \<Longrightarrow> 
       EXAMPLE x y \<longrightarrow>
       EXAMPLE y z \<longrightarrow> 
       EXAMPLE x z\<close>
  by auto
(* Equivalence under assumptions *)

lemma equivp_lowEquivQ:
  \<open>\<And>x y. \<lbrakk>(isInter x \<Longrightarrow> op\<^sub>\<L> x = op\<^sub>\<L> y)\<rbrakk> \<Longrightarrow> EXAMPLE x y = (EXAMPLE x = EXAMPLE y)\<close> 
  apply auto
  by metis+
*)

definition T :: "'state \<Rightarrow> bool" where 
"T trn \<equiv> False"

lemma not_T[simp]: "\<not> T trn" unfolding T_def by auto
                            
lemma neverT[simp,intro!]: "never T tr" unfolding T_def list_all_def by simp


abbreviation \<open>completed \<equiv> list_all final\<close>
abbreviation \<open>neverInter \<equiv> never isInter\<close>

lemma completed_neverInterE[elim]: \<open>completed tr \<Longrightarrow> (neverInter tr \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using isInter_not_final by (induct tr, auto)

definition \<open>ops\<^sub>\<L> = filtermap isInter op\<^sub>\<L>\<close> 

(* TODO filtermap lemma for interpretation? *)
lemma ops\<^sub>\<L>_Cons_unfold: "ops\<^sub>\<L> (trn # tr) = (if isInter trn then op\<^sub>\<L> trn # ops\<^sub>\<L> tr else ops\<^sub>\<L> tr)"
unfolding ops\<^sub>\<L>_def by auto

sublocale OD
  where Tr = \<open>{\<pi>. istate (hd \<pi>) \<and> validFromS (hd \<pi>) \<pi> \<and> completedFrom (hd \<pi>) \<pi>}\<close>
    and ops\<^sub>\<L> = ops\<^sub>\<L>
    (*and lowEquiv = lowEquiv*)
  .

lemma secure_alt_def: \<open>secure = 
    (\<forall>\<pi>\<^sub>1 \<pi>\<^sub>2. istate (hd \<pi>\<^sub>1) \<and> validFromS (hd \<pi>\<^sub>1) \<pi>\<^sub>1 \<and> completedFrom (hd \<pi>\<^sub>1) \<pi>\<^sub>1 \<and>
             istate (hd \<pi>\<^sub>2) \<and> validFromS (hd \<pi>\<^sub>2) \<pi>\<^sub>2 \<and> completedFrom (hd \<pi>\<^sub>2) \<pi>\<^sub>2 \<and>
            (hd \<pi>\<^sub>1) \<approx>\<^sub>\<L> (hd \<pi>\<^sub>2) \<longrightarrow>
      secureFor \<pi>\<^sub>1 \<pi>\<^sub>2
)\<close>
  using secure_def by auto


(* TODO - introduce later*)
lemma list_all2_lemmas_lowEquivs: \<open>list_all2_lemmas (\<approx>\<^sub>\<L>) (\<approx>\<^sub>\<L>)\<close>
  apply (standard)
  using low_equiv_list_def by blast

text \<open>OD as instance of \<forall>\<forall> BD Security:\<close>

definition isObs :: "'state \<Rightarrow> bool" where 
"isObs s \<equiv> True"

lemma isObs: "isObs s" unfolding isObs_def by auto

definition getObs :: "'state \<Rightarrow> 'state set" where 
"getObs s' \<equiv> {s . s \<approx>\<^sub>\<L> s'}"

lemma getObs_imp_lowEquiv: "getObs s = getObs s' \<Longrightarrow> s \<approx>\<^sub>\<L> s'"
  unfolding getObs_def Collect_eq 
  apply (erule allE[where x = s])
  by (meson reflpE reflp_lowEquiv)

lemma lowEquiv_eq:
  fixes s :: 'state assumes "(\<approx>\<^sub>\<L>) s = (\<approx>\<^sub>\<L>) s'" shows "{sa. sa \<approx>\<^sub>\<L> s} = {s. s \<approx>\<^sub>\<L> s'}"
  using assms unfolding Collect_eq apply auto
  by (metis sympE symp_lowEquiv)+

lemma lowEquiv_imp_getObs: "\<lbrakk>isInter s \<Longrightarrow>  op\<^sub>\<L> s = op\<^sub>\<L> s'; s \<approx>\<^sub>\<L> s'\<rbrakk> \<Longrightarrow> getObs s = getObs s'"
  apply (drule equivp_lowEquiv)
  unfolding getObs_def
  using lowEquiv_eq by blast
  
end 

end
