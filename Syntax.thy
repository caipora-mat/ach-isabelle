theory Syntax

imports Main "First_Order_Terms.Term"

begin

datatype ach = Unin | AC | Hom

locale signature =
  fixes arity :: "'f \<Rightarrow> nat"
    and label :: "'f \<Rightarrow> ach"

begin

lemma non_ac :
  assumes \<open>label f \<noteq> AC\<close>
  shows \<open>label f = Unin \<or> label f = Hom\<close>
  using ach.exhaust assms by blast

section \<open>Flattened Terms\<close>

inductive is_flattened :: "('f, 'v) term \<Rightarrow> bool" where
  var_is_flattened [simp]:
    "is_flattened (Var x)" |

  fun_is_flattened:
    "\<lbrakk> label f \<noteq> AC; \<And>t. t \<in> set ts \<Longrightarrow> is_flattened t \<rbrakk> \<Longrightarrow> is_flattened (Fun f ts)" |

  ac_is_flattened:
    "\<lbrakk> label f = AC;
       \<And>t. t \<in> set ts \<Longrightarrow> is_flattened t;
       \<And>t g gs. t \<in> set ts \<Longrightarrow> t = Fun g gs \<Longrightarrow> g \<noteq> f \<rbrakk>  \<Longrightarrow> is_flattened (Fun f ts)"

lemma constants_flattened:
  shows "is_flattened (Fun f [])"
  using ac_is_flattened empty_iff empty_set fun_is_flattened by metis

fun is_headed_by_ac :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>is_headed_by_ac (Var _)   = False\<close> |
  \<open>is_headed_by_ac (Fun g _) = (
    case label g of
      AC \<Rightarrow> True |
      _  \<Rightarrow> False
  )\<close>

fun get_fun_symb :: \<open>('f, 'v) term \<Rightarrow> 'f option \<close> where
  \<open>get_fun_symb (Var _ )  = None\<close> |
  \<open>get_fun_symb (Fun f _) = Some f\<close>

lemma isVar_None: "is_Var s \<longleftrightarrow> get_fun_symb s = None"
  by (cases s) simp_all

fun dec_is_flattened :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_is_flattened (Var _) = True\<close> |
  \<open>dec_is_flattened (Fun f ts) =
    (case label f of
      AC \<Rightarrow> (
        let ac_arg =
          find (
            \<lambda> s. (is_headed_by_ac s) \<and>
            (case (get_fun_symb s) of None \<Rightarrow> False | Some g \<Rightarrow> f = g)
          ) ts
        in
        (case ac_arg of
          None   \<Rightarrow> foldl (\<and>) True (map dec_is_flattened ts) |
          Some _ \<Rightarrow> False
        )
      )|
      _  \<Rightarrow> foldl (\<and>) True (map dec_is_flattened ts)
    )\<close>

lemma dec_pred_is_flatten: \<open>\<forall> s :: ('f, 'v) term. is_flatenned s \<longleftrightarrow> dec_is_flatened s\<close>
  sorry

subsection "Flattening"

fun flatten_aux :: \<open>'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list\<close> where
  \<open>flatten_aux f s =
    (case s of
      Var _    \<Rightarrow> [s] |
      Fun g ss \<Rightarrow>
        if label g = AC \<and> g = f then
          args s
        else
          [s]
    )\<close>


fun flatten :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term\<close> where
  \<open>flatten s =
    (case s of
      Var _    \<Rightarrow> s |
      Fun f ss \<Rightarrow>
        (case label f of
          AC \<Rightarrow>
          (
            let flatten_all_args = map flatten ss in
            let new_args = concat (map (flatten_aux f) flatten_all_args) in
            Fun f new_args
          )|
          _  \<Rightarrow> Fun f (map flatten ss)
        )
    )\<close>

section \<open>Lemmata for Flatten\<close>

lemma flatten_aux_AC:
  assumes "label f = AC"
  shows "flatten_aux f (Fun f ts) = ts"
  using assms by simp

lemma flatten_aux_flattened:
  assumes "is_flattened t"
  shows "\<And>s. s \<in> set (flatten_aux f t) \<Longrightarrow> is_flattened s"
proof-
  fix s
  assume "s \<in> set (flatten_aux f t)"
  from assms this
  show "is_flattened s"
   proof (induct rule: is_flattened.induct)
     case (var_is_flattened x)
     then show ?case
       by (simp add: signature.var_is_flattened)
   next
     case (fun_is_flattened f ts)
     then show ?case
       by (simp add: is_flattened.fun_is_flattened)
   next
     case (ac_is_flattened g ts)
     show ?case
     proof (cases "f = g")
      case True
      then have "flatten_aux f (Fun g ts) = ts"
        using ac_is_flattened.hyps by simp
      with ac_is_flattened True show ?thesis
        by simp
    next
      case False
      then have "s = Fun g ts"
        using ac_is_flattened by simp
      then show ?thesis
        using ac_is_flattened is_flattened.simps by blast
   qed
 qed
qed


lemma flatten_AC_args_flattened:
  assumes "label f = AC"
  assumes "\<And>t. t \<in> set ss \<Longrightarrow> is_flattened (flatten t)"
  assumes "t \<in> set (concat (map (flatten_aux f) (map flatten ss)))"
  shows   "is_flattened t"
proof-
  from assms(3)
  obtain s u where
    "s \<in> set ss"
    "u = flatten s"
    "t \<in> set (flatten_aux f u)"
    by auto

  moreover have "is_flattened u"
    using assms(2) \<open>s \<in> set ss\<close> calculation(2) by blast

  ultimately show "is_flattened t"
    using flatten_aux_flattened by blast
qed


lemma flatten_aux_no_head:
  assumes "is_flattened u"
      and "label f = AC"
      and "t \<in> set (flatten_aux f u)"
      and "t = Fun g gs"
  shows "g \<noteq> f"
using assms
proof (induct rule: is_flattened.induct)
  case (var_is_flattened x)
  then show ?case by simp
next
  case (fun_is_flattened h ts)
  then show ?case by auto
next
  case (ac_is_flattened h ts)
  then show ?case
  proof (cases "f = h")
    case True
    then have "flatten_aux f (Fun h ts) = ts"
      using ac_is_flattened.hyps by simp
    with ac_is_flattened True show ?thesis
      by auto
  next
    case False
    then have "flatten_aux f (Fun h ts) = [Fun h ts]"
      by simp
    with ac_is_flattened False show ?thesis
      by simp
  qed
qed


lemma flatten_AC_no_nested:
  assumes "label f = AC"
  assumes "\<And>t. t \<in> set ss \<Longrightarrow> is_flattened (flatten t)"
  assumes "t \<in> set (concat (map (flatten_aux f) (map flatten ss)))"
  assumes "t = Fun g gs"
  shows   "g \<noteq> f"
proof-
  from assms(3)
  obtain s u where
    "s \<in> set ss"
    "u = flatten s"
    "t \<in> set (flatten_aux f u)"
    by auto
  moreover have "is_flattened u"
    using assms(2) \<open>s \<in> set ss\<close> calculation(2) by blast
  ultimately show "g \<noteq> f"
    using assms(1,4) flatten_aux_no_head
    by blast
qed


lemma flatten_soundness: \<open>\<forall> t::('f, 'v) term. is_flattened (flatten t)\<close>
proof
  fix t :: "('f, 'v) term"
  show "is_flattened (flatten t)"
  proof (induct t)
    case (Var x)
    then show ?case using var_is_flattened by simp
  next
    case (Fun f ss)
    then show ?case
    proof(cases "label f = AC")
      case True
      have a: "flatten (Fun f ss) = Fun f (concat (map (flatten_aux f) (map flatten ss)))"
        using True by simp
      show ?thesis
        apply (subst a)
        apply(rule is_flattened.ac_is_flattened)
      proof-
        show "label f = AC"
          by fact
        show "\<And>t. t \<in> set (concat (map (flatten_aux f) (map flatten ss))) \<Longrightarrow> is_flattened t"
          using flatten_AC_args_flattened Fun.hyps True by blast
        show "\<And>t g gs. t \<in> set (concat (map (flatten_aux f) (map flatten ss))) \<Longrightarrow> t = Fun g gs \<Longrightarrow> g \<noteq> f"
          using flatten_AC_no_nested Fun.hyps True
            by blast
        qed
    next
      case False
      have b: "flatten (Fun f ss) = Fun f (map flatten ss)"
        using False non_ac flatten.simps by force
      show ?thesis
        apply(subst b)
        apply (rule fun_is_flattened)
        using False Fun.hyps by auto
    qed
  qed
qed

lemma flatten_soundness_dec: \<open>\<forall> t::('f, 'v) term. dec_is_flattened (flatten t)\<close>
  using dec_pred_is_flatten flatten_soundness oops

lemma flatten_idempotent: \<open>flatten (flatten t) = flatten t\<close>
proof (induct t)
  case (Var x)
  then show ?case using var_is_flattened by simp
next
  case (Fun f ss)
  then show ?case
  proof (cases \<open>label f = AC\<close>)
    case True
    have H1:\<open>label f = AC\<close> by fact
    then show ?thesis
      sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

end
end
