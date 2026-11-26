(*
Author: Guilherme Borges Brandão
*)

theory Bounded_ACh_Completeness
  imports Bounded_ACh_Unification ACh_Normal_Form
begin

section \<open>Completeness\<close>

text \<open>
  For completeness we need the AC-unification algorithm to be complete. We state this in the
  form used by the (AC) rule: every ACh-solution \<open>\<theta>\<close> of a problem of flat sum equations
  extends to a solution of \<open>GetEqs(\<rho>)\<close> for one of the computed unifiers \<open>\<rho>\<close>. The extension
  agrees with \<open>\<theta>\<close> on the variables of the problem, and the new variables are bound to parts of
  the old solution, so their h-height is not larger. This is the content of [AFSS22] that
  Lemma 3.6, case 7, refers to.
\<close>

locale bounded_ach_complete = bounded_ach plus hom \<kappa> ac_unify
  for plus :: 'f and hom :: 'f and \<kappa> :: nat
    and ac_unify :: "'v set \<Rightarrow> ('f, 'v) problem \<Rightarrow> ('v \<times> ('f, 'v) term) list list" +
  assumes ac_unify_complete:
    "\<lbrakk>\<forall>e \<in># \<Psi>. flat_sum_eq e; sat_problem \<theta> \<Psi>\<rbrakk> \<Longrightarrow>
      \<exists>\<rho> \<in> set (ac_unify V \<Psi>). \<exists>\<theta>'.
        (\<forall>x \<in> vars_problem \<Psi>. \<theta>' x = \<theta> x) \<and> sat_problem \<theta>' (get_eqs \<rho>) \<and>
        (\<forall>v \<in> vars_problem (get_eqs \<rho>). \<exists>x \<in> vars_problem \<Psi>. hh (\<theta>' v) \<le> hh (\<theta> x))"
begin

subsection \<open>Bounded solutions of triples\<close>

text \<open>
  \<open>\<theta>\<close> is a \<open>\<kappa>\<close>-bounded solution of \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<sigma>\<close> if it satisfies the triple, the instances of
  both sides of every equation have h-height at most \<open>\<kappa>\<close> (Definition 1.24), and the depths in
  \<open>\<Delta>\<close> are consistent with \<open>\<theta>\<close>: a variable at h-depth \<open>d\<close> is instantiated with a term of
  h-height at most \<open>\<kappa> - d\<close>. The dissertation leaves this last condition implicit, but it is what
  guarantees that (BC) never discards a bounded solution.
\<close>

fun bsol :: "('f, 'v) subst \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" where
  "bsol \<theta> (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow>
    sat_problem \<theta> \<Gamma> \<and> sat_bindings \<theta> \<sigma> \<and>
    (\<forall>(s, t) \<in># \<Gamma>. hh (s \<cdot> \<theta>) \<le> \<kappa> \<and> hh (t \<cdot> \<theta>) \<le> \<kappa>) \<and>
    (\<forall>x d. \<Delta> x = Some d \<longrightarrow> d + hh (\<theta> x) \<le> \<kappa>)"

lemma bsol_sat: "bsol \<theta> S \<Longrightarrow> \<theta> \<Turnstile> S"
  by (cases S) (fastforce simp: bounded_depths_def)

definition hbounded :: "('f, 'v) subst \<Rightarrow> ('f, 'v) problem \<Rightarrow> bool" where
  "hbounded \<theta> \<Gamma> \<longleftrightarrow> (\<forall>(s, t) \<in># \<Gamma>. hh (s \<cdot> \<theta>) \<le> \<kappa> \<and> hh (t \<cdot> \<theta>) \<le> \<kappa>)"

definition depths_ok :: "('f, 'v) subst \<Rightarrow> 'v depth_set \<Rightarrow> bool" where
  "depths_ok \<theta> \<Delta> \<longleftrightarrow> (\<forall>x d. \<Delta> x = Some d \<longrightarrow> d + hh (\<theta> x) \<le> \<kappa>)"

lemma bsol_iff:
  "bsol \<theta> (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow>
    sat_problem \<theta> \<Gamma> \<and> sat_bindings \<theta> \<sigma> \<and> hbounded \<theta> \<Gamma> \<and> depths_ok \<theta> \<Delta>"
  by (simp add: hbounded_def depths_ok_def)

declare bsol.simps [simp del]

lemma hbounded_simps [simp]:
  "hbounded \<theta> {#}"
  "hbounded \<theta> (add_mset (s, t) \<Gamma>) \<longleftrightarrow> hh (s \<cdot> \<theta>) \<le> \<kappa> \<and> hh (t \<cdot> \<theta>) \<le> \<kappa> \<and> hbounded \<theta> \<Gamma>"
  "hbounded \<theta> (\<Gamma> + \<Gamma>') \<longleftrightarrow> hbounded \<theta> \<Gamma> \<and> hbounded \<theta> \<Gamma>'"
  by (auto simp: hbounded_def)

lemma depths_ok_upd [simp]:
  "depths_ok \<theta> (\<Delta>(x \<mapsto> d)) \<longleftrightarrow> d + hh (\<theta> x) \<le> \<kappa> \<and> depths_ok \<theta> (\<Delta>(x := None))"
  by (auto simp: depths_ok_def)

lemma depths_ok_del: "depths_ok \<theta> \<Delta> \<Longrightarrow> depths_ok \<theta> (\<Delta>(x := None))"
  by (simp add: depths_ok_def)

lemma depths_okD: "depths_ok \<theta> \<Delta> \<Longrightarrow> \<Delta> x = Some d \<Longrightarrow> d + hh (\<theta> x) \<le> \<kappa>"
  by (simp add: depths_ok_def)

lemma depths_ok_fresh_upd:
  "\<Delta> x = None \<Longrightarrow> depths_ok \<theta> (\<Delta>(x := None)) \<longleftrightarrow> depths_ok \<theta> \<Delta>"
  by (simp add: fun_upd_idem)

text \<open>Solutions only matter on the variables of the triple.\<close>

lemma subst_agree:
  "(\<And>x. x \<in> vars_term t \<Longrightarrow> \<theta>' x = \<theta> x) \<Longrightarrow> t \<cdot> \<theta>' = t \<cdot> \<theta>"
  by (rule term_subst_eq)

lemma bsol_agree:
  assumes "\<And>x. x \<in> vars_triple S \<Longrightarrow> \<theta>' x = \<theta> x"
  shows "bsol \<theta>' S \<longleftrightarrow> bsol \<theta> S"
proof -
  obtain \<Gamma> \<Delta> \<sigma> where S: "S = (\<Gamma>, \<Delta>, \<sigma>)"
    by (cases S)
  have sub: "vars_term s \<subseteq> vars_triple S" "vars_term t \<subseteq> vars_triple S" if "(s, t) \<in># \<Gamma>" for s t
    using that unfolding S by (force simp: vars_problem_def)+
  have eqs: "s \<cdot> \<theta>' = s \<cdot> \<theta>" "t \<cdot> \<theta>' = t \<cdot> \<theta>" if "(s, t) \<in># \<Gamma>" for s t
    using sub[OF that] assms by (meson subsetD subst_agree)+
  have sub': "insert x (vars_term t) \<subseteq> vars_triple S" if "(x, t) \<in> \<sigma>" for x t
    using that unfolding S by (force simp: vars_bindings_def)
  have binds: "\<theta>' x = \<theta> x" "t \<cdot> \<theta>' = t \<cdot> \<theta>" if "(x, t) \<in> \<sigma>" for x t
    using sub'[OF that] assms by (meson insert_subset subsetD subst_agree)+
  have dom: "\<theta>' x = \<theta> x" if "\<Delta> x = Some d" for x d
    using assms that by (auto simp: S)
  show ?thesis
    unfolding S bsol_iff sat_problem_def sat_bindings_def hbounded_def depths_ok_def
    using eqs binds dom by (auto 0 3 split: prod.splits)
qed

lemma hbounded_eliminate:
  assumes "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
  shows "hbounded \<theta> (subst_problem (Var(x := t)) \<Gamma>) \<longleftrightarrow> hbounded \<theta> \<Gamma>"
  using hh_eq_ACh[OF eq_ACh_eliminate[OF assms]]
  by (auto simp: hbounded_def subst_problem_def)

lemma problem_zip_props:
  assumes "length ss = length ts"
    and "\<And>i. i < length ss \<Longrightarrow> ss ! i \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h ts ! i \<cdot> \<theta>"
    and "\<And>i. i < length ss \<Longrightarrow> hh (ss ! i \<cdot> \<theta>) \<le> \<kappa> \<and> hh (ts ! i \<cdot> \<theta>) \<le> \<kappa>"
  shows "sat_problem \<theta> (mset (zip ss ts))" and "hbounded \<theta> (mset (zip ss ts))"
  using assms by (auto simp: sat_problem_def hbounded_def in_set_zip)

lemma depths_ok_upds:
  assumes "depths_ok \<theta> \<Delta>" and "length ds = length vs"
    and "\<And>i. i < length vs \<Longrightarrow> ds ! i + hh (\<theta> (vs ! i)) \<le> \<kappa>"
  shows "depths_ok \<theta> (\<Delta>(vs [\<mapsto>] ds))"
  using assms
  by (auto simp: depths_ok_def map_upds_def map_add_Some_iff in_set_zip dest!: map_of_SomeD)

lemma depths_ok_add_zero:
  assumes "depths_ok \<theta> \<Delta>" and "\<And>z. z \<in> N \<Longrightarrow> hh (\<theta> z) \<le> \<kappa>"
  shows "depths_ok \<theta> (add_zero_depths N \<Delta>)"
  using assms by (auto simp: depths_ok_def add_zero_depths_def)

lemma hbounded_var:
  assumes "hbounded \<theta> \<Gamma>" and "z \<in> vars_problem \<Gamma>"
  shows "hh (\<theta> z) \<le> \<kappa>"
proof -
  obtain s t where "(s, t) \<in># \<Gamma>" "z \<in> vars_term s \<or> z \<in> vars_term t"
    using assms(2) by (auto simp: vars_problem_def vars_eq_def)
  then show ?thesis
    using assms(1) hh_subst_le[of z s \<theta>] hh_subst_le[of z t \<theta>]
    by (auto simp: hbounded_def)
qed

lemma problem_map2_props:
  assumes "length vs = length xs"
    and eqs: "\<And>i. i < length xs \<Longrightarrow> \<theta> (xs ! i) \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> (vs ! i))"
    and bnd: "\<And>i. i < length xs \<Longrightarrow> hh (\<theta> (xs ! i)) \<le> \<kappa>"
  shows "sat_problem \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    and "hbounded \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
proof -
  have "hh (H (\<theta> (vs ! i))) \<le> \<kappa>" if "i < length xs" for i
    using hh_eq_ACh[OF eqs[OF that]] bnd[OF that] by simp
  then show "sat_problem \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    and "hbounded \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    using assms(1) eqs bnd by (auto simp: sat_problem_def hbounded_def in_set_zip)
qed

text \<open>Extending a substitution on a list of (fresh) variables.\<close>

definition ext_subst :: "('f, 'v) subst \<Rightarrow> 'v list \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) subst" where
  "ext_subst \<theta> vs us y = (case map_of (zip vs us) y of Some u \<Rightarrow> u | None \<Rightarrow> \<theta> y)"

lemma ext_subst_out: "y \<notin> set vs \<Longrightarrow> ext_subst \<theta> vs us y = \<theta> y"
  by (auto simp: ext_subst_def dest: map_of_SomeD set_zip_leftD split: option.split)

lemma ext_subst_nth:
  assumes "distinct vs" and "length vs = length us" and "i < length vs"
  shows "ext_subst \<theta> vs us (vs ! i) = us ! i"
  using assms by (simp add: ext_subst_def map_of_zip_nth)

lemma map_ext_subst:
  assumes "distinct vs" and "length vs = length us"
  shows "map (ext_subst \<theta> vs us) vs = us"
  using assms by (auto intro: nth_equalityI simp: ext_subst_nth)

lemma sat_problem_agree:
  assumes "\<And>z. z \<in> vars_problem \<Gamma> \<Longrightarrow> \<theta>' z = \<theta> z"
  shows "sat_problem \<theta>' \<Gamma> \<longleftrightarrow> sat_problem \<theta> \<Gamma>"
proof -
  have "s \<cdot> \<theta>' = s \<cdot> \<theta> \<and> t \<cdot> \<theta>' = t \<cdot> \<theta>" if "(s, t) \<in># \<Gamma>" for s t
    using that assms by (intro conjI subst_agree) (force simp: vars_problem_def)+
  then show ?thesis
    by (auto simp: sat_problem_def)
qed

subsection \<open>Every rule preserves bounded solutions\<close>

text \<open>
  Lemma 3.6 of the dissertation, in a stronger, strategy-independent form: \<^emph>\<open>whichever\<close> rule
  is applied to a triple with a bounded solution \<open>\<theta>\<close>, one of the resulting triples has a bounded
  solution extending \<open>\<theta>\<close>. In particular, the failure rules (OC), (Clash), and (BC) never apply
  to such a triple.
\<close>

lemma step_complete:
  assumes "S \<leadsto> Ss" and "bsol \<theta> S"
  shows "\<exists>S' \<in> Ss. \<exists>\<theta>'. bsol \<theta>' S' \<and> (\<forall>x \<in> vars_triple S. \<theta>' x = \<theta> x)"
  using assms
proof (induction rule: step.induct)
  case (FBS t\<^sub>1 t\<^sub>2 v \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (t\<^sub>1, t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)"
  let ?\<theta> = "\<theta>(v := t\<^sub>1 \<cdot> \<theta>)"
  have agree: "\<forall>x \<in> vars_triple ?S. ?\<theta> x = \<theta> x"
    using FBS.hyps(3) by auto
  then have "bsol ?\<theta> ?S"
    using bsol_agree FBS.prems by blast
  moreover have "?\<theta> v = t\<^sub>1 \<cdot> ?\<theta>" "\<Delta> v = None"
    using agree FBS.hyps(3) by (auto intro!: subst_agree)
  ultimately have "bsol ?\<theta> (add_mset (Var v, t\<^sub>1) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
    by (simp add: bsol_iff depths_ok_fresh_upd)
  with agree show ?case
    by blast
next
  case (FL t\<^sub>1 v t t\<^sub>2 \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)"
  let ?\<theta> = "\<theta>(v := t\<^sub>1 \<cdot> \<theta>)"
  have agree: "\<forall>x \<in> vars_triple ?S. ?\<theta> x = \<theta> x"
    using FL.hyps(2) by auto
  then have "bsol ?\<theta> ?S"
    using bsol_agree FL.prems by blast
  moreover have "?\<theta> v = t\<^sub>1 \<cdot> ?\<theta>" "\<Delta> v = None"
    using agree FL.hyps(2) by (auto intro!: subst_agree)
  ultimately have "bsol ?\<theta> (add_mset (t, Var v \<oplus> t\<^sub>2) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
    by (simp add: bsol_iff depths_ok_fresh_upd)
  with agree show ?case
    by blast
next
  case (FR t\<^sub>2 v t t\<^sub>1 \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)"
  let ?\<theta> = "\<theta>(v := t\<^sub>2 \<cdot> \<theta>)"
  have agree: "\<forall>x \<in> vars_triple ?S. ?\<theta> x = \<theta> x"
    using FR.hyps(2) by auto
  then have "bsol ?\<theta> ?S"
    using bsol_agree FR.prems by blast
  moreover have "?\<theta> v = t\<^sub>2 \<cdot> ?\<theta>" "\<Delta> v = None"
    using agree FR.hyps(2) by (auto intro!: subst_agree)
  ultimately have "bsol ?\<theta> (add_mset (t, t\<^sub>1 \<oplus> Var v) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
    by (simp add: bsol_iff depths_ok_fresh_upd)
  with agree show ?case
    by blast
next
  case (FU t\<^sub>1 v t \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (t, H t\<^sub>1) \<Gamma>, \<Delta>, \<sigma>)"
  let ?\<theta> = "\<theta>(v := t\<^sub>1 \<cdot> \<theta>)"
  have agree: "\<forall>x \<in> vars_triple ?S. ?\<theta> x = \<theta> x"
    using FU.hyps(2) by auto
  then have "bsol ?\<theta> ?S"
    using bsol_agree FU.prems by blast
  moreover have "?\<theta> v = t\<^sub>1 \<cdot> ?\<theta>" "\<Delta> v = None"
    using agree FU.hyps(2) by (auto intro!: subst_agree)
  ultimately have "bsol ?\<theta> (add_mset (t, H (Var v)) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 1), \<sigma>)"
    by (simp add: bsol_iff depths_ok_fresh_upd)
  with agree show ?case
    by blast
next
  case (FlFun f ts vs t \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (t, Fun f ts) \<Gamma>, \<Delta>, \<sigma>)"
  let ?\<theta> = "ext_subst \<theta> vs (map (\<lambda>u. u \<cdot> \<theta>) ts)"
  have agree: "\<forall>x \<in> vars_triple ?S. ?\<theta> x = \<theta> x"
    by (intro ballI ext_subst_out) (use FlFun.hyps(6) in blast)
  then have b: "bsol ?\<theta> ?S"
    using bsol_agree FlFun.prems by blast
  have ts_agree: "u \<cdot> ?\<theta> = u \<cdot> \<theta>" if "u \<in> set ts" for u
    using agree that by (intro subst_agree) auto
  have vs_i: "?\<theta> (vs ! i) = ts ! i \<cdot> ?\<theta>" if "i < length ts" for i
    using that FlFun.hyps(4,5) ts_agree[of "ts ! i"] by (simp add: ext_subst_nth)
  have fun_eq: "Fun f (map Var vs) \<cdot> ?\<theta> = Fun f ts \<cdot> ?\<theta>"
    using FlFun.hyps(4,5) ts_agree by (simp add: map_ext_subst comp_def)
  have hb: "hh (Fun f ts \<cdot> ?\<theta>) \<le> \<kappa>"
    using b by (simp add: bsol_iff)
  have harg: "hh (ts ! i \<cdot> ?\<theta>) \<le> \<kappa>" if "i < length ts" for i
    using hb hh_arg_le[of "ts ! i \<cdot> ?\<theta>" "map (\<lambda>u. u \<cdot> ?\<theta>) ts" f] that by simp
  have zip: "sat_problem ?\<theta> (mset (zip (map Var vs) ts))" "hbounded ?\<theta> (mset (zip (map Var vs) ts))"
    using problem_zip_props[of "map Var vs" ts ?\<theta>] FlFun.hyps(4) vs_i harg by simp_all
  have "depths_ok ?\<theta> (\<Delta>(vs [\<mapsto>] replicate (length vs) 0))"
  proof (rule depths_ok_upds)
    show "depths_ok ?\<theta> \<Delta>"
      using b by (simp add: bsol_iff)
  qed (simp_all add: FlFun.hyps(4) vs_i harg)
  then have "bsol ?\<theta> (add_mset (t, Fun f (map Var vs)) (mset (zip (map Var vs) ts) + \<Gamma>),
      \<Delta>(vs [\<mapsto>] replicate (length vs) 0), \<sigma>)"
    using b zip fun_eq by (simp add: bsol_iff)
  with agree show ?case
    by blast
next
  case (USum x ys \<Gamma> y \<Delta> k l \<sigma>)
  have "ys \<noteq> []"
    using USum.hyps(2) by auto
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map \<theta> ys)" "k + hh (\<theta> x) \<le> \<kappa>"
    using USum by (auto simp: bsol_iff sat_problem_def sum_terms_subst comp_def dest: depths_okD)
  moreover have "hh (\<theta> y) \<le> hh (sum_terms (map \<theta> ys))"
    using USum.hyps(2) by (simp add: hh_sum_terms_le)
  ultimately have "k + hh (\<theta> y) \<le> \<kappa>"
    using hh_eq_ACh by fastforce
  then show ?case
    using USum.prems by (auto simp: bsol_iff intro!: exI[of _ \<theta>] depths_ok_del)
next
  case (UV x y \<Gamma> \<Delta> k l \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h \<theta> y" "k + hh (\<theta> x) \<le> \<kappa>"
    by (auto simp: bsol_iff sat_problem_def dest: depths_okD)
  then have "k + hh (\<theta> y) \<le> \<kappa>"
    using hh_eq_ACh by fastforce
  then show ?case
    using UV.prems by (auto simp: bsol_iff intro!: exI[of _ \<theta>] depths_ok_del)
next
  case (Uh x y \<Gamma> \<Delta> k l \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> y)" "k + hh (\<theta> x) \<le> \<kappa>"
    by (auto simp: bsol_iff sat_problem_def dest: depths_okD)
  then have "Suc k + hh (\<theta> y) \<le> \<kappa>"
    using hh_eq_ACh by fastforce
  then show ?case
    using Uh.prems by (auto simp: bsol_iff intro!: exI[of _ \<theta>] depths_ok_del)
next
  case (UL x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h \<theta> y\<^sub>1 \<oplus> \<theta> y\<^sub>2" "k + hh (\<theta> x) \<le> \<kappa>"
    by (auto simp: bsol_iff sat_problem_def dest: depths_okD)
  then have "k + hh (\<theta> y\<^sub>1) \<le> \<kappa>"
    using hh_eq_ACh by fastforce
  then show ?case
    using UL.prems by (auto simp: bsol_iff intro!: exI[of _ \<theta>] depths_ok_del)
next
  case (UR x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h \<theta> y\<^sub>1 \<oplus> \<theta> y\<^sub>2" "k + hh (\<theta> x) \<le> \<kappa>"
    by (auto simp: bsol_iff sat_problem_def dest: depths_okD)
  then have "k + hh (\<theta> y\<^sub>2) \<le> \<kappa>"
    using hh_eq_ACh by fastforce
  then show ?case
    using UR.prems by (auto simp: bsol_iff intro!: exI[of _ \<theta>] depths_ok_del)
next
  case (VE1 x y \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Var y \<cdot> \<theta>"
    by (simp add: bsol_iff)
  with VE1.prems show ?case
    by (auto simp: bsol_iff sat_problem_eliminate sat_bindings_eliminate hbounded_eliminate
        intro!: exI[of _ \<theta>])
next
  case (VE2 x t \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
    by (simp add: bsol_iff)
  with VE2.prems show ?case
    by (auto simp: bsol_iff sat_problem_eliminate sat_bindings_eliminate hbounded_eliminate
        intro!: exI[of _ \<theta>])
next
  case (Triv t \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by (auto simp: bsol_iff intro!: exI[of _ \<theta>])
next
  case (Orient t x \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by (auto simp: bsol_iff intro!: exI[of _ \<theta>] intro: eq_theory.sym)
next
  case (Dec f ss ts x \<Gamma> \<Delta> \<sigma>)
  then have x_ss: "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ss \<cdot> \<theta>" and x_ts: "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
    and bnd: "hh (Fun f ss \<cdot> \<theta>) \<le> \<kappa>" "hh (Fun f ts \<cdot> \<theta>) \<le> \<kappa>"
    by (simp_all add: bsol_iff)
  have "Fun f (map (\<lambda>s. s \<cdot> \<theta>) ss) \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f (map (\<lambda>t. t \<cdot> \<theta>) ts)"
    using x_ss x_ts by (auto intro: eq_theory.trans eq_theory.sym)
  then have args: "ss ! i \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h ts ! i \<cdot> \<theta>" if "i < length ss" for i
    using eq_ACh_decompose[of f "map (\<lambda>s. s \<cdot> \<theta>) ss" "map (\<lambda>t. t \<cdot> \<theta>) ts" i] Dec.hyps that
    by simp
  have hargs: "hh (ss ! i \<cdot> \<theta>) \<le> \<kappa> \<and> hh (ts ! i \<cdot> \<theta>) \<le> \<kappa>" if "i < length ss" for i
    using hh_arg_le[of "ss ! i \<cdot> \<theta>" "map (\<lambda>s. s \<cdot> \<theta>) ss" f]
      hh_arg_le[of "ts ! i \<cdot> \<theta>" "map (\<lambda>t. t \<cdot> \<theta>) ts" f] bnd that Dec.hyps(2)
    by auto
  show ?case
    using Dec.prems problem_zip_props[OF Dec.hyps(2) args hargs]
    by (auto simp: bsol_iff intro!: exI[of _ \<theta>])
next
  case (OC x f ts \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
    by (simp add: bsol_iff)
  with eq_ACh_occurs[OF OC.hyps] show ?case
    by contradiction
next
  case (Clash f g x ss ts \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ss \<cdot> \<theta>" "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun g ts \<cdot> \<theta>"
    by (simp_all add: bsol_iff)
  then have eq: "Fun f (map (\<lambda>s. s \<cdot> \<theta>) ss) \<approx>\<^sub>A\<^sub>C\<^sub>h Fun g (map (\<lambda>t. t \<cdot> \<theta>) ts)"
    by (auto intro: eq_theory.trans eq_theory.sym)
  from Clash.hyps(2) show ?case
  proof
    assume "f \<notin> {plus, hom}"
    then show ?case
      using eq eq_ACh_clash[OF Clash.hyps(1)] by blast
  next
    assume "g \<notin> {plus, hom}"
    then show ?case
      using eq_theory.sym[OF eq] eq_ACh_clash[of g f] Clash.hyps(1) by blast
  qed
next
  case (BC \<Delta> \<Gamma> \<sigma>)
  then show ?case
    using bsol_sat by fastforce
next
  case (Split xs x y vs \<Gamma> \<Delta> \<sigma>)
  let ?S = "(add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>), \<Delta>, \<sigma>)"
  have "xs \<noteq> []" "vs \<noteq> []"
    using Split.hyps(1,4) by auto
  have sum_xs: "sum_terms (map Var xs) \<cdot> \<rho> = sum_terms (map \<rho> xs)" for \<rho> :: "('f, 'v) subst"
    using \<open>xs \<noteq> []\<close> by (simp add: sum_terms_subst comp_def)
  have x_H: "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> y)" and x_sum: "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map \<theta> xs)"
    and hx: "hh (\<theta> x) \<le> \<kappa>" and hsum: "hh (sum_terms (map \<theta> xs)) \<le> \<kappa>"
    using Split.prems by (simp_all add: bsol_iff sum_xs)
  have "H (\<theta> y) \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map \<theta> xs)"
    using x_H x_sum by (meson eq_theory.sym eq_theory.trans)
  then obtain ws where len_ws: "length ws = length xs"
    and ws: "\<And>i. i < length xs \<Longrightarrow> \<theta> (xs ! i) \<approx>\<^sub>A\<^sub>C\<^sub>h H (ws ! i)"
    and y_ws: "\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms ws"
    using \<open>xs \<noteq> []\<close> by (auto elim!: eq_ACh_H_sum)
  let ?\<theta> = "ext_subst \<theta> vs ws"
  have agree: "\<forall>z \<in> vars_triple ?S. ?\<theta> z = \<theta> z"
    by (intro ballI ext_subst_out) (use Split.hyps(6) in blast)
  then have b: "bsol ?\<theta> ?S"
    using bsol_agree Split.prems by blast
  have old: "?\<theta> x = \<theta> x" "?\<theta> y = \<theta> y" "\<And>i. i < length xs \<Longrightarrow> ?\<theta> (xs ! i) = \<theta> (xs ! i)"
    using agree \<open>xs \<noteq> []\<close> by (auto simp: vars_sum_terms)
  have new: "\<And>i. i < length xs \<Longrightarrow> ?\<theta> (vs ! i) = ws ! i" "map ?\<theta> vs = ws"
    using Split.hyps(4,5) len_ws by (simp_all add: ext_subst_nth map_ext_subst)
  have hy: "hh (\<theta> y) < \<kappa>"
    using hx hh_eq_ACh[OF x_H] by simp
  have hxs: "hh (\<theta> (xs ! i)) \<le> \<kappa>" if "i < length xs" for i
    using hsum hh_sum_terms_le[of "\<theta> (xs ! i)" "map \<theta> xs"] that by simp
  have y_eq: "?\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map Var vs) \<cdot> ?\<theta>" "hh (sum_terms (map Var vs) \<cdot> ?\<theta>) \<le> \<kappa>"
    using y_ws old new hy hh_eq_ACh[OF y_ws] \<open>vs \<noteq> []\<close> by (simp_all add: sum_terms_subst comp_def)
  have m2: "sat_problem ?\<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    "hbounded ?\<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    using problem_map2_props[of vs xs ?\<theta>] Split.hyps(4) old new ws hxs by simp_all
  have "depths_ok ?\<theta> (\<Delta>(vs [\<mapsto>] replicate (length vs) 1))"
  proof (rule depths_ok_upds)
    show "depths_ok ?\<theta> \<Delta>"
      using b by (simp add: bsol_iff)
    fix i
    assume "i < length vs"
    then show "replicate (length vs) 1 ! i + hh (?\<theta> (vs ! i)) \<le> \<kappa>"
      using new hxs hh_eq_ACh[OF ws] Split.hyps(4) by simp
  qed simp
  then have "bsol ?\<theta> (add_mset (Var x, H (Var y))
      (add_mset (Var y, sum_terms (map Var vs))
        (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs) + \<Gamma>)),
      \<Delta>(vs [\<mapsto>] replicate (length vs) 1), \<sigma>)"
    using b y_eq m2 old hy by (simp add: bsol_iff)
  with agree show ?case
    by blast
next
  case (AC \<Psi> \<Gamma>\<^sub>0 \<Gamma> \<Delta> \<sigma>)
  have \<Gamma>\<^sub>0: "\<Gamma>\<^sub>0 = \<Psi> + \<Gamma>"
    using AC.hyps(1,2) by simp
  have sat_\<Psi>: "sat_problem \<theta> \<Psi>" and hb_\<Psi>: "hbounded \<theta> \<Psi>"
    using AC.prems by (simp_all add: \<Gamma>\<^sub>0 bsol_iff)
  obtain \<rho> \<theta>\<^sub>1 where \<rho>: "\<rho> \<in> set (ac_unify (vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)) \<Psi>)"
    and agree\<^sub>1: "\<forall>z \<in> vars_problem \<Psi>. \<theta>\<^sub>1 z = \<theta> z"
    and sat\<^sub>1: "sat_problem \<theta>\<^sub>1 (get_eqs \<rho>)"
    and new\<^sub>1: "\<forall>v \<in> vars_problem (get_eqs \<rho>). \<exists>z \<in> vars_problem \<Psi>. hh (\<theta>\<^sub>1 v) \<le> hh (\<theta> z)"
    using ac_unify_complete[OF AC.hyps(4) sat_\<Psi>] by blast
  let ?N = "vars_problem (get_eqs \<rho>) - vars_problem \<Psi>"
  let ?\<theta> = "\<lambda>z. if z \<in> ?N then \<theta>\<^sub>1 z else \<theta> z"
  have fresh: "?N \<inter> vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>) = {}"
    using AC.hyps(3) \<rho> by blast
  have agree: "\<forall>z \<in> vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>). ?\<theta> z = \<theta> z"
    using fresh by auto
  have b: "bsol ?\<theta> (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)"
    by (rule bsol_agree[THEN iffD2]) (use agree AC.prems in auto)
  have agree': "\<forall>z \<in> vars_problem (get_eqs \<rho>). ?\<theta> z = \<theta>\<^sub>1 z"
    using agree\<^sub>1 by auto
  have sat': "sat_problem ?\<theta> (get_eqs \<rho>)"
    by (rule sat_problem_agree[THEN iffD2]) (use agree' sat\<^sub>1 in auto)
  have hz: "hh (?\<theta> z) \<le> \<kappa>" if "z \<in> vars_problem (get_eqs \<rho>)" for z
  proof (cases "z \<in> vars_problem \<Psi>")
    case True
    then show ?thesis
      using hbounded_var[OF hb_\<Psi>] by simp
  next
    case False
    then obtain z' where "z' \<in> vars_problem \<Psi>" "hh (\<theta>\<^sub>1 z) \<le> hh (\<theta> z')"
      using bspec[OF new\<^sub>1 \<open>z \<in> vars_problem (get_eqs \<rho>)\<close>] by blast
    then show ?thesis
      using False that hbounded_var[OF hb_\<Psi>, of z'] by simp
  qed
  have hb': "hbounded ?\<theta> (get_eqs \<rho>)"
    unfolding hbounded_def
  proof safe
    fix s t
    assume st: "(s, t) \<in># get_eqs \<rho>"
    then obtain z where s: "s = Var z"
      by (auto simp: get_eqs_def)
    have "z \<in> vars_problem (get_eqs \<rho>)"
      using st s by (force simp: vars_problem_def)
    moreover have "?\<theta> z \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> ?\<theta>"
      using sat' st s by (auto simp: sat_problem_def)
    ultimately show "hh (s \<cdot> ?\<theta>) \<le> \<kappa>" "hh (t \<cdot> ?\<theta>) \<le> \<kappa>"
      using hz hh_eq_ACh s by fastforce+
  qed
  have "depths_ok ?\<theta> (add_zero_depths ?N \<Delta>)"
  proof (rule depths_ok_add_zero)
    show "depths_ok ?\<theta> \<Delta>"
      using b by (simp add: bsol_iff)
    show "hh (?\<theta> z) \<le> \<kappa>" if "z \<in> ?N" for z
      using hz that by blast
  qed
  then have "bsol ?\<theta> (get_eqs \<rho> + \<Gamma>, add_zero_depths ?N \<Delta>, \<sigma>)"
    using b sat' hb' by (simp add: bsol_iff \<Gamma>\<^sub>0)
  with agree \<rho> show ?case
    by blast
qed

corollary step_no_failure:
  assumes "S \<leadsto> Ss" and "bsol \<theta> S"
  shows "Ss \<noteq> {}"
  using step_complete[OF assms] by blast

subsection \<open>The variables recorded in \<open>\<Delta>\<close> never disappear\<close>

abbreviation depth_vars :: "('f, 'v) triple \<Rightarrow> 'v set" where
  "depth_vars S \<equiv> dom (fst (snd S))"

lemma step_depth_vars_mono:
  assumes "S \<leadsto> Ss" and "S' \<in> Ss"
  shows "depth_vars S \<subseteq> depth_vars S'"
  using assms by (induction rule: step.induct) (auto simp: add_zero_depths_def)

lemma depth_vars_sub_vars_triple: "depth_vars S \<subseteq> vars_triple S"
  by (cases S) auto

subsection \<open>Derivation trees\<close>

text \<open>
  Theorem 3.3: a bounded solution of the root extends to a bounded solution of some leaf,
  without changing it on the variables recorded in \<open>\<Delta>\<close>.
\<close>

theorem tree_complete:
  assumes "tree S L" and "bsol \<theta> S"
  shows "\<exists>S' \<in> L. \<exists>\<theta>'. bsol \<theta>' S' \<and> (\<forall>x \<in> depth_vars S. \<theta>' x = \<theta> x)"
  using assms
proof (induction arbitrary: \<theta> rule: tree.induct)
  case (leaf S)
  then show ?case
    by blast
next
  case (node S Ss L)
  obtain S' \<theta>\<^sub>1 where S': "S' \<in> Ss" and b1: "bsol \<theta>\<^sub>1 S'"
    and agree1: "\<forall>x \<in> vars_triple S. \<theta>\<^sub>1 x = \<theta> x"
    using step_complete[OF node.hyps(1) node.prems] by blast
  obtain S'' \<theta>\<^sub>2 where "S'' \<in> L S'" "bsol \<theta>\<^sub>2 S''"
    and agree2: "\<forall>x \<in> depth_vars S'. \<theta>\<^sub>2 x = \<theta>\<^sub>1 x"
    using node.IH[OF S' b1] by blast
  moreover have "\<forall>x \<in> depth_vars S. \<theta>\<^sub>2 x = \<theta> x"
  proof
    fix x
    assume x: "x \<in> depth_vars S"
    then have "\<theta>\<^sub>2 x = \<theta>\<^sub>1 x"
      using agree2 step_depth_vars_mono[OF node.hyps(1) S'] by (meson subsetD)
    also have "\<dots> = \<theta> x"
      using agree1 x depth_vars_sub_vars_triple[of S] by (meson subsetD)
    finally show "\<theta>\<^sub>2 x = \<theta> x" .
  qed
  ultimately show ?case
    using S' by blast
qed

subsection \<open>Finiteness and progress\<close>

fun finite_triple :: "('f, 'v) triple \<Rightarrow> bool" where
  "finite_triple (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> finite (dom \<Delta>) \<and> finite \<sigma>"

lemma finite_vars_problem: "finite (vars_problem \<Gamma>)"
  by (auto simp: vars_problem_def vars_eq_def)

lemma finite_vars_triple: "finite_triple S \<Longrightarrow> finite (vars_triple S)"
  by (cases S) (auto simp: finite_vars_problem vars_bindings_def)

lemma dom_add_zero_depths: "dom (add_zero_depths N \<Delta>) = N \<union> dom \<Delta>"
  by (auto simp: add_zero_depths_def)

lemma step_finite_triple:
  assumes "S \<leadsto> Ss" and "S' \<in> Ss" and "finite_triple S"
  shows "finite_triple S'"
  using assms
  by (induction rule: step.induct)
    (auto simp: subst_bindings_def dom_add_zero_depths finite_vars_problem)

text \<open>Every triple with a non-empty problem can be transformed, provided fresh variables exist.\<close>

lemma progress:
  assumes "infinite (UNIV :: 'v set)" and "finite_triple (\<Gamma>, \<Delta>, \<sigma>)" and "\<Gamma> \<noteq> {#}"
  shows "\<exists>Ss. (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> Ss"
proof -
  obtain s t \<Gamma>' where \<Gamma>: "\<Gamma> = add_mset (s, t) \<Gamma>'"
    using assms(3) by (metis multiset_cases surj_pair)
  obtain v where v: "v \<notin> vars_triple (\<Gamma>, \<Delta>, \<sigma>)"
    using ex_new_if_finite[OF assms(1) finite_vars_triple[OF assms(2)]] by blast
  show ?thesis
  proof (cases "s = t")
    case True
    then show ?thesis
      unfolding \<Gamma> using step.Triv by blast
  next
    case False
    show ?thesis
    proof (cases s)
      case (Var x)
      show ?thesis
      proof (cases "x \<in> vars_term t")
        case True
        with False Var obtain f ts where "t = Fun f ts"
          by (cases t) auto
        with True show ?thesis
          unfolding \<Gamma> Var using step.OC by blast
      next
        case False
        then show ?thesis
          unfolding \<Gamma> Var using step.VE2 by blast
      qed
    next
      case (Fun f ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        then show ?thesis
          unfolding \<Gamma> \<open>s = Fun f ss\<close> using step.Orient[of "Fun f ss" x] by blast
      next
        case (Fun g ts)
        then show ?thesis
          using step.FBS[of s t v \<Gamma>' \<Delta> \<sigma>] v \<open>s = Fun f ss\<close> unfolding \<Gamma> by auto
      qed
    qed
  qed
qed

subsection \<open>Completeness of the computed unifiers\<close>

lemma subst_of_bindings_solved:
  assumes "solved_inv (\<Gamma>, \<Delta>, \<sigma>)" and "(x, t) \<in> \<sigma>"
  shows "subst_of_bindings \<sigma> x = t"
proof -
  have "\<forall>x t t'. (x, t) \<in> \<sigma> \<longrightarrow> (x, t') \<in> \<sigma> \<longrightarrow> t = t'"
    using assms(1) by (simp add: solved_inv.simps)
  then have "(THE s. (x, s) \<in> \<sigma>) = t"
    using assms(2) by blast
  then show ?thesis
    using assms(2) by (auto simp: subst_of_bindings_def)
qed

text \<open>
  Corollary 3.3 (Completeness). Let \<open>L\<close> be the leaves of a derivation tree from
  \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<emptyset>\<close> to which no rule applies, where \<open>\<Delta>\<close> records all variables of \<open>\<Gamma>\<close>. Then for every
  bounded solution \<open>\<theta>\<close> there is a leaf \<open>\<emptyset> \<parallel> \<Delta>' \<parallel> \<sigma>'\<close> whose computed substitution \<open>\<sigma>'\<close> is more
  general than \<open>\<theta>\<close> modulo ACh on the variables of \<open>\<Gamma>\<close>.
\<close>

theorem completeness:
  assumes inf: "infinite (UNIV :: 'v set)"
    and tree: "tree (\<Gamma>, \<Delta>, {}) L"
    and final: "\<forall>S \<in> L. \<nexists>Ss. S \<leadsto> Ss"
    and dom: "vars_problem \<Gamma> \<subseteq> dom \<Delta>" "finite (dom \<Delta>)"
    and sol: "bsol \<theta> (\<Gamma>, \<Delta>, {})"
  shows "\<exists>\<Delta>' \<sigma>'. ({#}, \<Delta>', \<sigma>') \<in> L \<and>
    (\<exists>\<tau>. \<forall>x \<in> vars_problem \<Gamma>. \<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h subst_of_bindings \<sigma>' x \<cdot> \<tau>)"
proof -
  obtain S' \<theta>' where "S' \<in> L" and b: "bsol \<theta>' S'" and agree: "\<forall>x \<in> dom \<Delta>. \<theta>' x = \<theta> x"
    using tree_complete[OF tree sol] by auto
  obtain \<Gamma>' \<Delta>' \<sigma>' where S': "S' = (\<Gamma>', \<Delta>', \<sigma>')"
    by (cases S')
  have "finite_triple (\<Gamma>, \<Delta>, {})"
    using dom(2) by simp
  then have fin: "finite_triple S'"
    using tree_invariant[OF tree, where P = finite_triple] step_finite_triple \<open>S' \<in> L\<close> by blast
  have inv: "solved_inv S'"
    using tree_invariant[OF tree, where P = solved_inv] solved_inv_initial step_solved_inv
      \<open>S' \<in> L\<close> by blast
  have "\<Gamma>' = {#}"
    using progress[OF inf] fin final \<open>S' \<in> L\<close> unfolding S' by blast
  moreover have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h subst_of_bindings \<sigma>' x \<cdot> \<theta>'" if "x \<in> vars_problem \<Gamma>" for x
  proof -
    have \<theta>x: "\<theta> x = \<theta>' x"
      using agree that dom(1) by (metis subsetD)
    show ?thesis
    proof (cases "\<exists>t. (x, t) \<in> \<sigma>'")
      case True
      then obtain t where t: "(x, t) \<in> \<sigma>'"
        by blast
      then have "\<theta>' x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>'"
        using b by (auto simp: S' bsol_iff sat_bindings_def)
      then show ?thesis
        using \<theta>x subst_of_bindings_solved[OF inv[unfolded S'] t] by simp
    next
      case False
      then show ?thesis
        using \<theta>x by (simp add: subst_of_bindings_def)
    qed
  qed
  ultimately show ?thesis
    using \<open>S' \<in> L\<close> S' by blast
qed

text \<open>
  The same statement for the initial h-depth set of Algorithm 1 (every variable of \<open>\<Gamma>\<close> at depth
  0) and a \<open>\<kappa>\<close>-bounded ACh-unifier in the sense of Definition 1.24.
\<close>

definition initial_depths :: "('f, 'v) problem \<Rightarrow> 'v depth_set" where
  "initial_depths \<Gamma> = (\<lambda>x. if x \<in> vars_problem \<Gamma> then Some 0 else None)"

corollary completeness_bounded_unifier:
  assumes "infinite (UNIV :: 'v set)"
    and "tree (\<Gamma>, initial_depths \<Gamma>, {}) L"
    and "\<forall>S \<in> L. \<nexists>Ss. S \<leadsto> Ss"
    and unif: "sat_problem \<theta> \<Gamma>" and bounded: "hbounded \<theta> \<Gamma>"
  shows "\<exists>\<Delta>' \<sigma>'. ({#}, \<Delta>', \<sigma>') \<in> L \<and>
    (\<exists>\<tau>. \<forall>x \<in> vars_problem \<Gamma>. \<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h subst_of_bindings \<sigma>' x \<cdot> \<tau>)"
proof (rule completeness[OF assms(1-3)])
  have dom: "dom (initial_depths \<Gamma>) = vars_problem \<Gamma>"
    by (auto simp: initial_depths_def split: if_splits)
  then show "vars_problem \<Gamma> \<subseteq> dom (initial_depths \<Gamma>)" "finite (dom (initial_depths \<Gamma>))"
    by (simp_all add: finite_vars_problem)
  show "bsol \<theta> (\<Gamma>, initial_depths \<Gamma>, {})"
    using unif bounded hbounded_var[OF bounded]
    by (auto simp: bsol_iff depths_ok_def initial_depths_def split: if_splits)
qed

end

end
