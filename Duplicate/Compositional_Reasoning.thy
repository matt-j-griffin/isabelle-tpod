theory Compositional_Reasoning
imports BD_Security_TS
begin


context BD_Security_TS begin


(* Preliminaries *)

definition "disjAll \<Delta>s s vl s1 vl1 \<equiv> (\<exists>\<Delta> \<in> \<Delta>s. \<Delta> s vl s1 vl1)"

lemma disjAll_simps[simp]:
  "disjAll {} \<equiv> \<lambda>_ _ _ _. False"
  "disjAll (insert \<Delta> \<Delta>s) \<equiv> \<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<or> disjAll \<Delta>s s vl s1 vl1"
  unfolding disjAll_def[abs_def] by auto

lemma disjAll_mono:
assumes "disjAll \<Delta>s s vl s1 vl1"
and "\<Delta>s \<subseteq> \<Delta>s'"
shows "disjAll \<Delta>s' s vl s1 vl1"
using assms unfolding disjAll_def by auto

lemma iactionLeft_mono:
assumes 1: "iactionLeft \<Delta> s vl s1 vl1" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "iactionLeft \<Delta>' s vl s1 vl1"
using assms unfolding iactionLeft_def by fastforce

lemma iactionRight_mono:
assumes 1: "iactionRight \<Delta> s vl s1 vl1" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "iactionRight \<Delta>' s vl s1 vl1"
using assms unfolding iactionRight_def by fastforce

lemma saction_mono:
assumes 1: "saction \<Delta> s vl s1 vl1" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "saction \<Delta>' s vl s1 vl1"
using assms unfolding saction_def by fastforce


(* Decomposition into an arbitrary network of components *)

(* Unwind not to itself, but to a disjunction of other relations: *)
definition unwind_to where
"unwind_to \<Delta> \<Delta>s \<equiv>
\<forall> s vl s1 vl1.
   reachNT s \<and> reachNT s1 \<and> 
   \<Delta> s vl s1 vl1
   \<longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 
   \<or>
   iactionLeft (disjAll \<Delta>s) s vl s1 vl1 \<and> 
   iactionRight (disjAll \<Delta>s) s vl s1 vl1 \<and> 
   saction (disjAll \<Delta>s) s vl s1 vl1"

lemma unwind_toI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reachNT s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   hopeless s vl \<or> hopeless s1 vl1 
   \<or>
   iactionLeft (disjAll \<Delta>s) s vl s1 vl1 \<and> 
   iactionRight (disjAll \<Delta>s) s vl s1 vl1 \<and> 
   saction (disjAll \<Delta>s) s vl s1 vl1"
shows "unwind_to \<Delta> \<Delta>s"
using assms unfolding unwind_to_def by auto

(* Decomposition: *)
lemma unwind_dec:
assumes ne: "\<And> \<Delta>. \<Delta> \<in> \<Delta>s \<Longrightarrow> next \<Delta> \<subseteq> \<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
shows "unwind (disjAll \<Delta>s)" (is "unwind ?\<Delta>")
proof
  fix s s1 :: 'state and vl vl1 :: "'secret list"
  assume r: "reachNT s" "reachNT s1" and \<Delta>: "?\<Delta> s vl s1 vl1"
  then obtain \<Delta> where \<Delta>: "\<Delta> \<in> \<Delta>s" and 2: "\<Delta> s vl s1 vl1" unfolding disjAll_def by auto
  let ?\<Delta>s' = "next \<Delta>"  let ?\<Delta>' = "disjAll ?\<Delta>s'"
  have "hopeless s vl \<or> hopeless s1 vl1 
        \<or>
        iactionLeft ?\<Delta>' s vl s1 vl1 \<and> 
        iactionRight ?\<Delta>' s vl s1 vl1 \<and> 
        saction ?\<Delta>' s vl s1 vl1"
  using 2 \<Delta> ne r unfolding unwind_to_def by auto
  moreover have "\<And> s vl s1 vl1. ?\<Delta>' s vl s1 vl1 \<Longrightarrow> ?\<Delta> s vl s1 vl1"
  using ne[OF \<Delta>] unfolding disjAll_def by auto
  ultimately show
       "hopeless s vl \<or> hopeless s1 vl1 
        \<or>
        iactionLeft ?\<Delta> s vl s1 vl1 \<and> 
        iactionRight ?\<Delta> s vl s1 vl1 \<and> 
        saction ?\<Delta> s vl s1 vl1"
  using iactionLeft_mono[of ?\<Delta>' _ _ _ _ ?\<Delta>] iactionRight_mono[of ?\<Delta>' _ _ _ _ ?\<Delta>] 
       saction_mono[of ?\<Delta>' _ _ _ _ ?\<Delta>] 
       by auto
qed


lemma init_dec:
assumes \<Delta>0: "\<Delta>0 \<in> \<Delta>s"
and i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>0 s vl s1 vl1"
shows "\<forall> s vl s1 vl1. B s vl s1 vl1 \<longrightarrow> istate s \<longrightarrow> istate s1 \<longrightarrow> disjAll \<Delta>s s vl s1 vl1"
using assms unfolding disjAll_def by meson

theorem unwind_dec_secure:
assumes \<Delta>0: "\<Delta>0 \<in> \<Delta>s"
and i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>0 s vl s1 vl1"
and ne: "\<And> \<Delta>. \<Delta> \<in> \<Delta>s \<Longrightarrow> next \<Delta> \<subseteq> \<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
shows secure
using init_dec[OF \<Delta>0 i] unwind_dec[OF ne] unwind_secure by metis


(* A customization for linear modular reasoning *)

(* The customization assumes that each component unwinds only into itself,
its successor or an exit component.  *)


fun allConsec :: "'a list \<Rightarrow> ('a * 'a) set" where
  "allConsec [] = {}"
| "allConsec [a] = {}"
| "allConsec (a # b # as) = insert (a,b) (allConsec (b#as))"


lemma set_allConsec:
assumes "\<Delta> \<in> set \<Delta>s'" and "\<Delta>s = \<Delta>s' ## \<Delta>1"
shows "\<exists> \<Delta>2. (\<Delta>,\<Delta>2) \<in> allConsec \<Delta>s"
using assms proof (induction \<Delta>s' arbitrary: \<Delta>s)
  case Nil thus ?case by auto
next
  case (Cons \<Delta>3 \<Delta>s' \<Delta>s)
  show ?case proof(cases "\<Delta> = \<Delta>3")
    case True
    show ?thesis proof(cases \<Delta>s')
      case Nil
      show ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> Nil True by (rule exI[of _ \<Delta>1]) simp
    next
      case (Cons \<Delta>4 \<Delta>s'')
      show ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> Cons True by (rule exI[of _ \<Delta>4]) simp
    qed
  next
    case False hence "\<Delta> \<in> set \<Delta>s'" using Cons by auto
    then obtain \<Delta>2 where "(\<Delta>, \<Delta>2) \<in> allConsec (\<Delta>s' ## \<Delta>1)" using Cons by auto
    thus ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> by (intro exI[of _ \<Delta>2]) (cases \<Delta>s', auto)
  qed
qed

lemma allConsec_set:
assumes "(\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s"
shows "\<Delta>1 \<in> set \<Delta>s \<and> \<Delta>2 \<in> set \<Delta>s"
using assms by (induct \<Delta>s rule: allConsec.induct) auto

(* Liniar decomposition: *)
theorem unwind_decomp_secure:
assumes n: "\<Delta>s \<noteq> []"
and i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> hd \<Delta>s s vl s1 vl1"
and c: "\<And> \<Delta>1 \<Delta>2. (\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s \<Longrightarrow> unwind_to \<Delta>1 {\<Delta>1, \<Delta>2}"
and l: "unwind_to (last \<Delta>s) {last \<Delta>s}"
shows secure
proof-
  let ?\<Delta>0 = "hd \<Delta>s"  let ?\<Delta>s = "set \<Delta>s"
  define "next" where "next \<Delta>1 =
    (if \<Delta>1 = last \<Delta>s then {\<Delta>1}
     else {\<Delta>1,SOME \<Delta>2. (\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s})" for \<Delta>1
  show ?thesis
  proof(rule unwind_dec_secure)
    show "?\<Delta>0 \<in> ?\<Delta>s" using n by auto
  next
    fix s vl s1 vl1 assume "B s vl s1 vl1" and "istate s" "istate s1"
    thus "?\<Delta>0 s vl s1 vl1" by fact
  next
    fix \<Delta>
    assume 1: "\<Delta> \<in> ?\<Delta>s" show "next \<Delta> \<subseteq> ?\<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)" 
    proof-
      {assume "\<Delta> = last \<Delta>s"  
       hence ?thesis using n l unfolding next_def unwind_to_def by simp
      }
      moreover
      {assume 1: "\<Delta> \<in> set \<Delta>s" and 2: "\<Delta> \<noteq> last \<Delta>s" 
       then obtain \<Delta>' \<Delta>s' where \<Delta>s: "\<Delta>s = \<Delta>s' ## \<Delta>'" and \<Delta>: "\<Delta> \<in> set \<Delta>s'"
       by (metis (no_types) append_Cons append_assoc in_set_conv_decomp last_snoc rev_exhaust)
       have "\<exists> \<Delta>2. (\<Delta>, \<Delta>2) \<in> allConsec \<Delta>s" using set_allConsec[OF \<Delta> \<Delta>s] .
       hence "(\<Delta>, SOME \<Delta>2. (\<Delta>, \<Delta>2) \<in> allConsec \<Delta>s) \<in> allConsec \<Delta>s" by (metis (lifting) someI_ex)
       hence ?thesis using 1 2 c unfolding next_def unwind_to_def
       by simp (metis (no_types) allConsec_set)
      }
      ultimately show ?thesis using 1 by blast
    qed
  qed
qed

(* Instances of the above: *)

corollary unwind_decomp3_secure:
assumes
i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>1 s vl s1 vl1"
and c1: "unwind_to \<Delta>1 {\<Delta>1, \<Delta>2}"
and c2: "unwind_to \<Delta>2 {\<Delta>2, \<Delta>3}"
and l: "unwind_to \<Delta>3 {\<Delta>3}"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3]"])
using assms by auto

corollary unwind_decomp4_secure:
assumes
i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>1 s vl s1 vl1"
and c1: "unwind_to \<Delta>1 {\<Delta>1, \<Delta>2}"
and c2: "unwind_to \<Delta>2 {\<Delta>2, \<Delta>3}"
and c3: "unwind_to \<Delta>3 {\<Delta>3, \<Delta>4}"
and l: "unwind_to \<Delta>4 {\<Delta>4}"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3, \<Delta>4]"])
using assms by auto

corollary unwind_decomp5_secure:
assumes
i: "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>1 s vl s1 vl1"
and c1: "unwind_to \<Delta>1 {\<Delta>1, \<Delta>2}"
and c2: "unwind_to \<Delta>2 {\<Delta>2, \<Delta>3}"
and c3: "unwind_to \<Delta>3 {\<Delta>3, \<Delta>4}"
and c4: "unwind_to \<Delta>4 {\<Delta>4, \<Delta>5}"
and l: "unwind_to \<Delta>5 {\<Delta>5}"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3, \<Delta>4, \<Delta>5]"])
using assms by auto


(* A Graph Alternative Presentation *)

(* This is more flexible for instantiation. *)

theorem unwind_decomp_secure_graph:
  assumes n: "\<forall> \<Delta> \<in> Domain Gr. \<exists> \<Delta>s. \<Delta>s \<subseteq> Domain Gr \<and> (\<Delta>,\<Delta>s) \<in> Gr"
  and i: "\<Delta>0 \<in> Domain Gr" "\<And> s vl s1 vl1. B s vl s1 vl1 \<Longrightarrow> istate s \<Longrightarrow> istate s1 \<Longrightarrow> \<Delta>0 s vl s1 vl1"
  and c: "\<And> \<Delta>. \<forall> \<Delta>s. (\<Delta>,\<Delta>s) \<in> Gr \<longrightarrow> unwind_to \<Delta> \<Delta>s"
  shows secure
proof -
  let ?pr = "\<lambda> \<Delta> \<Delta>s. \<Delta>s \<subseteq> Domain Gr \<and> (\<Delta>,\<Delta>s) \<in> Gr"
  define "next" where "next \<Delta> = (SOME \<Delta>s. ?pr \<Delta> \<Delta>s)" for \<Delta>
  let ?\<Delta>s = "Domain Gr"
  show ?thesis
  proof(rule unwind_dec_secure)
    show "\<Delta>0 \<in> ?\<Delta>s" using i by auto
    fix s vl s1 vl1 assume "B s vl s1 vl1" "istate s" "istate s1"
    thus "\<Delta>0 s vl s1 vl1" by fact
  next
    fix \<Delta>
    assume "\<Delta> \<in> ?\<Delta>s"
    hence "?pr \<Delta> (next \<Delta>)" using n someI_ex[of "?pr \<Delta>"] unfolding next_def by auto
    hence "next \<Delta> \<subseteq> ?\<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)" using c by auto
    thus "next \<Delta> \<subseteq> ?\<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
      unfolding unwind_to_def unwind_to_def
      by blast
  qed
qed

end (* context BD_Security_TS *)

end

