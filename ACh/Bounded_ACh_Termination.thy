(*
Author: Guilherme Borges Brandão
*)

theory Bounded_ACh_Termination
  imports Bounded_ACh_Unification ACh_Normal_Form
begin

section \<open>Termination\<close>

subsection \<open>Termination of flattening (Lemma 3.1)\<close>

context bounded_ach
begin

text \<open>One application of a flattening rule (FBS), (FL), (FR), (FU), or (FlFun).\<close>

inductive flat_step :: "('f, 'v) triple \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" (infix \<open>\<leadsto>\<^sub>F\<close> 50) where
  FBS: "\<lbrakk>is_Fun t\<^sub>1; is_Fun t\<^sub>2; fresh_for {v} (add_mset (t\<^sub>1, t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t\<^sub>1, t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F
      (add_mset (Var v, t\<^sub>1) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
| FL: "\<lbrakk>is_Fun t\<^sub>1; fresh_for {v} (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F
      (add_mset (t, Var v \<oplus> t\<^sub>2) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
| FR: "\<lbrakk>is_Fun t\<^sub>2; fresh_for {v} (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F
      (add_mset (t, t\<^sub>1 \<oplus> Var v) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)"
| FU: "\<lbrakk>is_Fun t\<^sub>1; fresh_for {v} (add_mset (t, H t\<^sub>1) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, H t\<^sub>1) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F
      (add_mset (t, H (Var v)) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 1), \<sigma>)"
| FlFun: "\<lbrakk>f \<noteq> plus; f \<noteq> hom; \<exists>u \<in> set ts. is_Fun u; length vs = length ts; distinct vs;
      fresh_for (set vs) (add_mset (t, Fun f ts) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, Fun f ts) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F
      (add_mset (t, Fun f (map Var vs)) (mset (zip (map Var vs) ts) + \<Gamma>),
        \<Delta>(vs [\<mapsto>] replicate (length vs) 0), \<sigma>)"

lemma flat_step_step: "S \<leadsto>\<^sub>F S' \<Longrightarrow> S \<leadsto> {S'}"
  by (induction rule: flat_step.induct) (blast intro: step.FBS step.FL step.FR step.FU step.FlFun)+

text \<open>
  The measure \<open>M(\<Gamma>)\<close> of Lemma 3.1: the multiset of the numbers of function symbols of the
  equations of \<open>\<Gamma>\<close>, compared in the multiset extension of \<open><\<close> on \<open>\<nat>\<close>.
\<close>

definition flat_measure :: "('f, 'v) problem \<Rightarrow> nat multiset" where
  "flat_measure \<Gamma> = image_mset (\<lambda>(s, t). num_funs s + num_funs t) \<Gamma>"

lemma num_funs_pos: "is_Fun t \<Longrightarrow> num_funs t > 0"
  by (cases t) auto

lemma flat_measure_add [simp]:
  "flat_measure {#} = {#}"
  "flat_measure (add_mset (s, t) \<Gamma>) = add_mset (num_funs s + num_funs t) (flat_measure \<Gamma>)"
  "flat_measure (\<Gamma> + \<Gamma>') = flat_measure \<Gamma> + flat_measure \<Gamma>'"
  by (simp_all add: flat_measure_def)

lemma mult_less_than_step:
  assumes "\<forall>k \<in># K. k < n"
  shows "(K + I, add_mset n I) \<in> mult less_than"
  using one_step_implies_mult[of "{#n#}" K less_than I] assms by (simp add: add.commute)

text \<open>Lemma 3.1: every flattening step decreases \<open>M(\<Gamma>)\<close>.\<close>

lemma flat_step_decreases:
  assumes "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (\<Gamma>', \<Delta>', \<sigma>')"
  shows "(flat_measure \<Gamma>', flat_measure \<Gamma>) \<in> mult less_than"
  using assms
proof (induction "(\<Gamma>, \<Delta>, \<sigma>)" "(\<Gamma>', \<Delta>', \<sigma>')" arbitrary: \<Gamma> \<Delta> \<sigma> \<Gamma>' \<Delta>' \<sigma> rule: flat_step.induct)
  case (FBS t\<^sub>1 t\<^sub>2 v \<Gamma>)
  then show ?case
    using mult_less_than_step[of "{#num_funs t\<^sub>1, num_funs t\<^sub>2#}"] num_funs_pos[of t\<^sub>1] num_funs_pos[of t\<^sub>2]
    by (simp add: add_mset_commute)
next
  case (FL t\<^sub>1 v t t\<^sub>2 \<Gamma>)
  then show ?case
    using mult_less_than_step[of "{#num_funs t + Suc (num_funs t\<^sub>2), num_funs t\<^sub>1#}"]
      num_funs_pos[of t\<^sub>1]
    by (simp add: add_mset_commute)
next
  case (FR t\<^sub>2 v t t\<^sub>1 \<Gamma>)
  then show ?case
    using mult_less_than_step[of "{#num_funs t + Suc (num_funs t\<^sub>1), num_funs t\<^sub>2#}"]
      num_funs_pos[of t\<^sub>2]
    by (simp add: add_mset_commute)
next
  case (FU t\<^sub>1 v t \<Gamma>)
  then show ?case
    using mult_less_than_step[of "{#num_funs t + 1, num_funs t\<^sub>1#}"] num_funs_pos[of t\<^sub>1]
    by (simp add: add_mset_commute)
next
  case (FlFun f ts vs t \<Gamma>)
  let ?N = "sum_list (map num_funs ts)"
  have zip: "flat_measure (mset (zip (map Var vs) ts)) = mset (map num_funs ts)"
    using FlFun.hyps(4) by (induction vs ts rule: list_induct2) auto
  have le: "num_funs u \<le> ?N" if "u \<in> set ts" for u
    using that by (simp add: member_le_sum_list)
  obtain u where "u \<in> set ts" "is_Fun u"
    using FlFun.hyps(3) by blast
  then have "?N > 0"
    using le[of u] num_funs_pos[of u] by linarith
  moreover have "num_funs u < num_funs t + Suc ?N" if "u \<in> set ts" for u
    using le[OF that] by linarith
  ultimately have "\<forall>k \<in># add_mset (num_funs t + Suc 0) (mset (map num_funs ts)).
      k < num_funs t + Suc ?N"
    by auto
  then show ?case
    using mult_less_than_step[of "add_mset (num_funs t + Suc 0) (mset (map num_funs ts))"
        "num_funs t + Suc ?N" "flat_measure \<Gamma>"]
    by (simp add: zip add.commute comp_def)
qed

text \<open>Hence Algorithm 2 (Flattening) terminates: there is no infinite sequence of flattening steps.\<close>

theorem flattening_terminates: "wf {(S', S). S \<leadsto>\<^sub>F S'}"
proof (rule wf_subset)
  show "wf (inv_image (mult less_than) (\<lambda>S. flat_measure (fst S)))"
    by (intro wf_inv_image wf_mult wf_less_than)
  show "{(S', S). S \<leadsto>\<^sub>F S'} \<subseteq> inv_image (mult less_than) (\<lambda>S. flat_measure (fst S))"
    using flat_step_decreases by (auto simp: inv_image_def)
qed

subsection \<open>The measure of Theorem 3.1 does not decrease under (VE2)\<close>

text \<open>
  Definition 3.3 measures a triple by \<open>(\<kappa> - a, n\<^sub>X, |Sym(\<Gamma>)|, m, p, |\<Gamma>|, hd(\<Delta>))\<close>, ordered
  lexicographically. The proof of Theorem 3.1 claims that (VE2) decreases it. It does not:
  eliminating \<open>X\<close> from \<open>{X =\<^sup>? c, Y =\<^sup>? g(X, X)}\<close> yields \<open>{Y =\<^sup>? g(c, c)}\<close>, where \<open>|Sym|\<close> grows
  from 2 to 3. The first two components are unchanged: no (AC) step happens and there are no
  \<open>+\<close>-equations. So the measure increases. Algorithm 1 applies (VE2) only in its final phase, so
  termination of the algorithm must be argued phase by phase, not rule by rule.
\<close>

definition sym_count :: "('f, 'v) problem \<Rightarrow> nat" where
  "sym_count \<Gamma> = sum_mset (flat_measure \<Gamma>)"

lemma VE2_increases_sym_count:
  fixes x y :: 'v and c g :: 'f
  assumes "x \<noteq> y"
  defines "\<Gamma> \<equiv> {#(Var x, Fun c []), (Var y, Fun g [Var x, Var x])#}"
    and "\<Gamma>' \<equiv> {#(Var y, Fun g [Fun c [], Fun c []])#}"
  shows "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>', \<Delta>, subst_bindings (Var(x := Fun c [])) \<sigma> \<union> {(x, Fun c [])})}"
    and "sym_count \<Gamma>' > sym_count \<Gamma>"
proof -
  have "subst_problem (Var(x := Fun c [])) {#(Var y, Fun g [Var x, Var x])#} = \<Gamma>'"
    using assms(1) by (simp add: subst_problem_def \<Gamma>'_def)
  then show "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>', \<Delta>, subst_bindings (Var(x := Fun c [])) \<sigma> \<union> {(x, Fun c [])})}"
    using step.VE2[of x "Fun c []" "{#(Var y, Fun g [Var x, Var x])#}" \<Delta> \<sigma>]
    by (simp add: \<Gamma>_def)
  show "sym_count \<Gamma>' > sym_count \<Gamma>"
    by (simp add: sym_count_def \<Gamma>_def \<Gamma>'_def)
qed

end

subsection \<open>Assumptions for the termination of the main loop\<close>

text \<open>
  Besides a supply of fresh variables, termination needs:
  \<^item> a fixed arity for every function symbol (Definition 1.1), with \<open>+\<close> binary and \<open>h\<close> unary;
    otherwise \<open>X =\<^sup>? f(a, b), X =\<^sup>? f(c)\<close> could be neither decomposed nor rejected;
  \<^item> that the AC-unification algorithm, given a finite set \<open>V\<close> of variables to avoid, introduces
    only variables outside \<open>V\<close>;
  \<^item> that its unifiers of flat problems have the shape of Stickel's algorithm: every variable
    of the problem is bound at most once, either to a single new variable or to a sum of at
    least two new variables.
\<close>

locale bounded_ach_term = bounded_ach plus hom \<kappa> ac_unify
  for plus :: 'f and hom :: 'f and \<kappa> :: nat
    and ac_unify :: "'v set \<Rightarrow> ('f, 'v) problem \<Rightarrow> ('v \<times> ('f, 'v) term) list list" +
  fixes arity :: "'f \<Rightarrow> nat"
  assumes infinite_vars: "infinite (UNIV :: 'v set)"
    and arity_plus: "arity plus = 2"
    and arity_hom: "arity hom = 1"
    and ac_fresh: "finite V \<Longrightarrow> \<rho> \<in> set (ac_unify V \<Psi>) \<Longrightarrow>
      (vars_problem (get_eqs \<rho>) - vars_problem \<Psi>) \<inter> V = {}"
    and ac_shape: "\<forall>e \<in># \<Psi>. flat_sum_eq e \<Longrightarrow> \<rho> \<in> set (ac_unify V \<Psi>) \<Longrightarrow>
      distinct (map fst \<rho>) \<and>
      (\<forall>(x, t) \<in> set \<rho>. x \<in> vars_problem \<Psi> \<and>
        ((\<exists>v. t = Var v \<and> v \<notin> vars_problem \<Psi>) \<or>
         (\<exists>vs. 2 \<le> length vs \<and> t = sum_terms (map Var vs) \<and> set vs \<inter> vars_problem \<Psi> = {})))"
begin

subsection \<open>Closing the h-depth set under the update rules\<close>

definition dep :: "'v depth_set \<Rightarrow> 'v \<Rightarrow> nat" where
  "dep \<Delta> x = (case \<Delta> x of Some d \<Rightarrow> d | None \<Rightarrow> 0)"

text \<open>
  The edges of the graph of \<open>\<Gamma>\<close> (Definition 1.19) along which the update rules propagate
  depths: \<open>X \<rightarrow> Y\<close> with increment 1 for \<open>X =\<^sup>? h(Y)\<close>, and with increment 0 for
  \<open>X =\<^sup>? \<dots> + Y + \<dots>\<close> and \<open>X =\<^sup>? Y\<close> (a sum with one summand).
\<close>

definition edge :: "('f, 'v) problem \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> bool" where
  "edge \<Gamma> x y i \<longleftrightarrow>
    ((Var x, H (Var y)) \<in># \<Gamma> \<and> i = 1) \<or>
    (\<exists>ys. (Var x, sum_terms (map Var ys)) \<in># \<Gamma> \<and> y \<in> set ys \<and> i = 0)"

definition closed :: "('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> bool" where
  "closed \<Gamma> \<Delta> \<longleftrightarrow> (\<forall>x y i. edge \<Gamma> x y i \<longrightarrow> dep \<Delta> x + i \<le> dep \<Delta> y)"

definition lhs_vars :: "('f, 'v) problem \<Rightarrow> 'v set" where
  "lhs_vars \<Gamma> = {x. \<exists>t. (Var x, t) \<in># \<Gamma>}"

text \<open>
  Protection of the levels below \<open>L\<close>: every edge that still needs an update starts at depth
  at least \<open>L\<close>, and if it ends below \<open>L\<close>, its target heads no equation. Then closing \<open>\<Delta>\<close>
  never changes the depth of a variable below \<open>L\<close> that heads an equation.
\<close>

definition prot :: "nat \<Rightarrow> ('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> bool" where
  "prot L \<Gamma> \<Delta> \<longleftrightarrow> (\<forall>x y i. edge \<Gamma> x y i \<longrightarrow> dep \<Delta> y < dep \<Delta> x + i \<longrightarrow>
    L \<le> dep \<Delta> x \<and> (dep \<Delta> y < L \<longrightarrow> y \<notin> lhs_vars \<Gamma>))"

definition potential :: "'v depth_set \<Rightarrow> nat" where
  "potential \<Delta> = (\<Sum>x \<in> dom \<Delta>. Suc \<kappa> - dep \<Delta> x)"

lemma edge_vars:
  assumes "edge \<Gamma> x y i"
  shows "x \<in> vars_problem \<Gamma>" "y \<in> vars_problem \<Gamma>" "x \<in> lhs_vars \<Gamma>"
proof -
  have "x \<in> vars_problem \<Gamma> \<and> y \<in> vars_problem \<Gamma> \<and> x \<in> lhs_vars \<Gamma>"
  proof (cases "(Var x, H (Var y)) \<in># \<Gamma>")
    case True
    then show ?thesis
      by (force simp: vars_problem_def lhs_vars_def)
  next
    case False
    then obtain ys where ys: "(Var x, sum_terms (map Var ys)) \<in># \<Gamma>" "y \<in> set ys"
      using assms by (auto simp: edge_def)
    then have "vars_term (sum_terms (map Var ys)) = set ys"
      by (subst vars_sum_terms) auto
    then have "{x, y} \<subseteq> vars_eq (Var x, sum_terms (map Var ys))"
      using ys(2) by simp
    then show ?thesis
      using ys(1) unfolding vars_problem_def lhs_vars_def by blast
  qed
  then show "x \<in> vars_problem \<Gamma>" "y \<in> vars_problem \<Gamma>" "x \<in> lhs_vars \<Gamma>"
    by simp_all
qed

lemma edge_step:
  assumes "edge \<Gamma> x y i" and "\<Delta> x = Some k" and "\<Delta> y = Some l" and "l < k + i"
  shows "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y \<mapsto> k + i), \<sigma>)}"
proof -
  consider "(Var x, H (Var y)) \<in># \<Gamma>" "i = 1"
    | ys where "(Var x, sum_terms (map Var ys)) \<in># \<Gamma>" "y \<in> set ys" "i = 0"
    using assms(1) by (auto simp: edge_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using step.Uh[of x y \<Gamma> \<Delta> k l \<sigma>] assms(2-4) by simp
  next
    case 2
    then show ?thesis
      using step.USum[of x ys \<Gamma> y \<Delta> k l \<sigma>] assms(2-4) by simp
  qed
qed

lemma dep_Some [simp]: "\<Delta> x = Some d \<Longrightarrow> dep \<Delta> x = d"
  by (simp add: dep_def)

lemma dom_dep: "x \<in> dom \<Delta> \<Longrightarrow> \<Delta> x = Some (dep \<Delta> x)"
  by (auto simp: dep_def)

lemma dep_upd: "dep (\<Delta>(y \<mapsto> n)) z = (if z = y then n else dep \<Delta> z)"
  by (simp add: dep_def)

lemma prot_upd:
  assumes "prot L \<Gamma> \<Delta>" and "edge \<Gamma> x y i" and "dep \<Delta> y < dep \<Delta> x + i"
  shows "prot L \<Gamma> (\<Delta>(y \<mapsto> dep \<Delta> x + i))"
  unfolding prot_def
proof (intro allI impI)
  let ?\<Delta> = "\<Delta>(y \<mapsto> dep \<Delta> x + i)"
  fix a b j
  assume ab: "edge \<Gamma> a b j" and unsat: "dep ?\<Delta> b < dep ?\<Delta> a + j"
  have xy: "L \<le> dep \<Delta> x" "dep \<Delta> y < L \<longrightarrow> y \<notin> lhs_vars \<Gamma>"
    using assms unfolding prot_def by blast+
  show "L \<le> dep ?\<Delta> a \<and> (dep ?\<Delta> b < L \<longrightarrow> b \<notin> lhs_vars \<Gamma>)"
  proof (cases "a = y")
    case True
    then have "y \<in> lhs_vars \<Gamma>"
      using edge_vars(3)[OF ab] by simp
    then have "L \<le> dep \<Delta> y"
      using xy(2) by linarith
    have "dep ?\<Delta> b < L \<longrightarrow> b \<notin> lhs_vars \<Gamma>"
    proof (cases "b = y")
      case False
      show ?thesis
      proof (cases "dep \<Delta> b < dep \<Delta> a + j")
        case True
        then show ?thesis
          using assms(1) ab False unfolding prot_def by (auto simp: dep_upd)
      next
        case False
        then show ?thesis
          using \<open>a = y\<close> \<open>L \<le> dep \<Delta> y\<close> \<open>b \<noteq> y\<close> by (auto simp: dep_upd)
      qed
    qed (use xy in \<open>simp add: dep_upd\<close>)
    then show ?thesis
      using True xy(1) by (simp add: dep_upd)
  next
    case False
    show ?thesis
    proof (cases "b = y")
      case True
      then have "dep \<Delta> b < dep \<Delta> a + j"
        using unsat False assms(3) by (simp add: dep_upd)
      then have "L \<le> dep \<Delta> a"
        using assms(1) ab unfolding prot_def by blast
      then show ?thesis
        using False True xy(1) by (simp add: dep_upd)
    next
      case b: False
      then show ?thesis
        using assms(1) ab unsat False unfolding prot_def by (simp add: dep_upd)
    qed
  qed
qed

lemma potential_upd:
  assumes "finite (dom \<Delta>)" and "y \<in> dom \<Delta>" and "dep \<Delta> y < n" and "n \<le> Suc \<kappa>"
  shows "potential (\<Delta>(y \<mapsto> n)) < potential \<Delta>"
proof -
  have dom: "dom (\<Delta>(y \<mapsto> n)) = dom \<Delta>"
    using assms(2) by auto
  have "potential \<Delta> = (Suc \<kappa> - dep \<Delta> y) + (\<Sum>z \<in> dom \<Delta> - {y}. Suc \<kappa> - dep \<Delta> z)"
    unfolding potential_def using assms(1,2) by (simp add: sum.remove)
  moreover have "potential (\<Delta>(y \<mapsto> n)) = (Suc \<kappa> - n) + (\<Sum>z \<in> dom \<Delta> - {y}. Suc \<kappa> - dep \<Delta> z)"
    unfolding potential_def dom using assms(1,2) by (simp add: sum.remove dep_upd)
  ultimately show ?thesis
    using assms(3,4) by linarith
qed

text \<open>
  Closing \<open>\<Delta>\<close> under the update rules terminates, by the potential \<open>\<Sum>\<^sub>x (\<kappa> + 1 - \<Delta>(x))\<close>.
  Either (BC) applies, or we reach a closed and bounded \<open>\<Delta>'\<close> above \<open>\<Delta>\<close>, which agrees with \<open>\<Delta>\<close>
  on the protected variables.
\<close>

lemma update_closure:
  assumes "finite (dom \<Delta>)" and "vars_problem \<Gamma> \<subseteq> dom \<Delta>" and "prot L \<Gamma> \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. \<exists>\<Delta>'. S' = (\<Gamma>, \<Delta>', \<sigma>) \<and> closed \<Gamma> \<Delta>' \<and> bounded_depths \<Delta>' \<and>
    dom \<Delta>' = dom \<Delta> \<and> (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and>
    (\<forall>z \<in> lhs_vars \<Gamma>. dep \<Delta> z < L \<longrightarrow> \<Delta>' z = \<Delta> z))"
  using assms
proof (induction "potential \<Delta>" arbitrary: \<Delta> rule: less_induct)
  case less
  show ?case
  proof (cases "bounded_depths \<Delta>")
    case False
    then show ?thesis
      by (intro reach_fail step.BC)
  next
    case bounded: True
    show ?thesis
    proof (cases "closed \<Gamma> \<Delta>")
      case True
      with bounded show ?thesis
        by (intro reach_refl) auto
    next
      case False
      then obtain x y i where e: "edge \<Gamma> x y i" and lt: "dep \<Delta> y < dep \<Delta> x + i"
        unfolding closed_def by auto
      have xy: "x \<in> dom \<Delta>" "y \<in> dom \<Delta>"
        using edge_vars[OF e] less.prems(2) by auto
      have "i \<le> 1"
        using e by (auto simp: edge_def)
      moreover have "dep \<Delta> x \<le> \<kappa>"
        using bounded dom_dep[OF xy(1)] unfolding bounded_depths_def by blast
      ultimately have le: "dep \<Delta> x + i \<le> Suc \<kappa>"
        by linarith
      let ?\<Delta> = "\<Delta>(y \<mapsto> dep \<Delta> x + i)"
      have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, ?\<Delta>, \<sigma>)}"
        using edge_step[OF e dom_dep[OF xy(1)] dom_dep[OF xy(2)] lt] .
      have IH: "reach (\<Gamma>, ?\<Delta>, \<sigma>) (\<lambda>S'. \<exists>\<Delta>'. S' = (\<Gamma>, \<Delta>', \<sigma>) \<and> closed \<Gamma> \<Delta>' \<and>
          bounded_depths \<Delta>' \<and> dom \<Delta>' = dom ?\<Delta> \<and> (\<forall>z. dep ?\<Delta> z \<le> dep \<Delta>' z) \<and>
          (\<forall>z \<in> lhs_vars \<Gamma>. dep ?\<Delta> z < L \<longrightarrow> \<Delta>' z = ?\<Delta> z))"
      proof (rule less.hyps)
        show "potential ?\<Delta> < potential \<Delta>"
          using potential_upd[OF less.prems(1) xy(2) lt le] .
        show "finite (dom ?\<Delta>)" "vars_problem \<Gamma> \<subseteq> dom ?\<Delta>"
          using less.prems(1,2) by auto
        show "prot L \<Gamma> ?\<Delta>"
          using prot_upd[OF less.prems(3) e lt] .
      qed
      have y_prot: "y \<in> lhs_vars \<Gamma> \<Longrightarrow> L \<le> dep \<Delta> y"
        using less.prems(3) e lt unfolding prot_def by force
      show ?thesis
      proof (rule reach_single[OF step], rule reach_mono[OF IH], elim exE conjE)
        fix S' \<Delta>'
        assume S': "S' = (\<Gamma>, \<Delta>', \<sigma>)" and props: "closed \<Gamma> \<Delta>'" "bounded_depths \<Delta>'"
          "dom \<Delta>' = dom ?\<Delta>" "\<forall>z. dep ?\<Delta> z \<le> dep \<Delta>' z"
          "\<forall>z \<in> lhs_vars \<Gamma>. dep ?\<Delta> z < L \<longrightarrow> \<Delta>' z = ?\<Delta> z"
        have "dom \<Delta>' = dom \<Delta>"
          using props(3) xy(2) by auto
        moreover have "dep \<Delta> z \<le> dep \<Delta>' z" for z
          using props(4)[rule_format, of z] lt by (auto simp: dep_upd split: if_splits)
        moreover have "\<Delta>' z = \<Delta> z" if "z \<in> lhs_vars \<Gamma>" "dep \<Delta> z < L" for z
        proof -
          have "z \<noteq> y"
            using y_prot that by fastforce
          then show ?thesis
            using props(5) that by (simp add: dep_upd)
        qed
        ultimately show "\<exists>\<Delta>'. S' = (\<Gamma>, \<Delta>', \<sigma>) \<and> closed \<Gamma> \<Delta>' \<and> bounded_depths \<Delta>' \<and>
          dom \<Delta>' = dom \<Delta> \<and> (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and>
          (\<forall>z \<in> lhs_vars \<Gamma>. dep \<Delta> z < L \<longrightarrow> \<Delta>' z = \<Delta> z)"
          using S' props(1,2) by blast
      qed
    qed
  qed
qed

text \<open>The guarantees of closing \<open>\<Delta>\<close> while protecting the levels below \<open>L\<close>.\<close>

definition close_post :: "nat \<Rightarrow> ('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> 'v depth_set \<Rightarrow> bool" where
  "close_post L \<Gamma> \<Delta> \<Delta>' \<longleftrightarrow> closed \<Gamma> \<Delta>' \<and> bounded_depths \<Delta>' \<and> dom \<Delta>' = dom \<Delta> \<and>
    (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and> (\<forall>z \<in> lhs_vars \<Gamma>. dep \<Delta> z < L \<longrightarrow> \<Delta>' z = \<Delta> z)"

lemma update_closure':
  assumes "finite (dom \<Delta>)" and "vars_problem \<Gamma> \<subseteq> dom \<Delta>" and "prot L \<Gamma> \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. \<exists>\<Delta>'. S' = (\<Gamma>, \<Delta>', \<sigma>) \<and> close_post L \<Gamma> \<Delta> \<Delta>')"
  using update_closure[OF assms] unfolding close_post_def .

subsection \<open>The final phase: variable elimination\<close>

abbreviation irreducible :: "('f, 'v) triple \<Rightarrow> bool" where
  "irreducible S \<equiv> \<nexists>Ss. S \<leadsto> Ss"

definition lhs_count :: "('f, 'v) problem \<Rightarrow> 'v \<Rightarrow> nat" where
  "lhs_count \<Gamma> x = size (filter_mset (\<lambda>e. fst e = Var x) \<Gamma>)"

lemma lhs_count_add [simp]:
  "lhs_count (add_mset e \<Gamma>) x = (if fst e = Var x then Suc (lhs_count \<Gamma> x) else lhs_count \<Gamma> x)"
  by (simp add: lhs_count_def)

text \<open>
  Step (j) of Algorithm 1: if every equation has a variable on the left and no variable heads
  two equations, then (VE2), (Triv) and (OC) empty the problem.
\<close>

lemma final_phase:
  assumes "\<forall>e \<in># \<Gamma>. is_Var (fst e)" and "\<forall>x. lhs_count \<Gamma> x \<le> 1" and "bounded_depths \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) irreducible"
  using assms(1,2)
proof (induction "size \<Gamma>" arbitrary: \<Gamma> \<sigma> rule: less_induct)
  case less
  show ?case
  proof (cases "\<Gamma> = {#}")
    case True
    then show ?thesis
      using irreducible_solved assms(3) by (intro reach_refl) simp
  next
    case False
    then obtain e \<Gamma>' where \<Gamma>: "\<Gamma> = add_mset e \<Gamma>'"
      by (meson multiset_cases)
    then obtain z s where e: "e = (Var z, s)"
      using less.prems(1) by (cases e) (auto simp: is_Var_def)
    have sub: "lhs_count \<Gamma>' x \<le> 1" for x
      using less.prems(2)[rule_format, of x] unfolding \<Gamma> lhs_count_add by (simp split: if_splits)
    have z_once: "lhs_count \<Gamma>' z = 0"
      using less.prems(2)[rule_format, of z] by (simp add: \<Gamma> e)
    have IH: "reach (\<Gamma>'', \<Delta>, \<sigma>') irreducible"
      if "size \<Gamma>'' < size \<Gamma>" "\<forall>e \<in># \<Gamma>''. is_Var (fst e)" "\<forall>x. lhs_count \<Gamma>'' x \<le> 1" for \<Gamma>'' \<sigma>'
      using less.hyps that by blast
    show ?thesis
    proof (cases "s = Var z")
      case True
      show ?thesis
        unfolding \<Gamma> e True
      proof (rule reach_single[OF step.Triv], rule IH)
        show "\<forall>x. lhs_count \<Gamma>' x \<le> 1"
          using sub by blast
      qed (use less.prems(1) \<Gamma> in auto)
    next
      case False
      show ?thesis
      proof (cases "z \<in> vars_term s")
        case True
        with False obtain f ts where "s = Fun f ts"
          by (cases s) auto
        with True show ?thesis
          unfolding \<Gamma> e \<open>s = Fun f ts\<close> by (intro reach_fail step.OC) simp
      next
        case z: False
        let ?\<tau> = "Var(z := s)"
        have lhs: "fst e' \<cdot> ?\<tau> = fst e'" if "e' \<in># \<Gamma>'" for e'
        proof -
          have "is_Var (fst e')"
            using less.prems(1) that \<Gamma> by simp
          then obtain w where w: "fst e' = Var w"
            by (cases "fst e'") auto
          moreover have "w \<noteq> z"
          proof
            assume "w = z"
            then have "e' \<in># filter_mset (\<lambda>e. fst e = Var z) \<Gamma>'"
              using that w by simp
            then have "filter_mset (\<lambda>e. fst e = Var z) \<Gamma>' \<noteq> {#}"
              by force
            then show False
              using z_once by (simp add: lhs_count_def, blast)
          qed
          ultimately show ?thesis
            by simp
        qed
        have count: "lhs_count (subst_problem ?\<tau> \<Gamma>') x = lhs_count \<Gamma>' x" for x
        proof -
          have gen: "\<forall>e' \<in># M. fst e' \<cdot> ?\<tau> = fst e' \<Longrightarrow>
            size (filter_mset (\<lambda>e. fst e = Var x) (subst_problem ?\<tau> M)) =
            size (filter_mset (\<lambda>e. fst e = Var x) M)" for M
            by (induction M) (auto simp: subst_problem_def split: prod.splits)
          then show ?thesis
            using lhs by (simp add: lhs_count_def)
        qed
        show ?thesis
          unfolding \<Gamma> e
        proof (rule reach_single[OF step.VE2[OF z]], rule IH)
          show "size (subst_problem ?\<tau> \<Gamma>') < size \<Gamma>"
            by (simp add: \<Gamma> subst_problem_def)
          show "\<forall>e \<in># subst_problem ?\<tau> \<Gamma>'. is_Var (fst e)"
            using lhs less.prems(1) \<Gamma> by (fastforce simp: subst_problem_def)
          show "\<forall>x. lhs_count (subst_problem ?\<tau> \<Gamma>') x \<le> 1"
            using count sub by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>Flat problems and the termination measure\<close>

definition vv_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "vv_eq e \<longleftrightarrow> (\<exists>x y. e = (Var x, Var y))"

definition h_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "h_eq e \<longleftrightarrow> (\<exists>x y. e = (Var x, H (Var y)))"

definition free_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "free_eq e \<longleftrightarrow> (\<exists>x f ys. e = (Var x, Fun f (map Var ys)) \<and> f \<noteq> plus \<and> f \<noteq> hom \<and> length ys = arity f)"

text \<open>Definition 1.18 (flattened form), including the equations \<open>X =\<^sup>? Y\<close>.\<close>

definition flat_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "flat_eq e \<longleftrightarrow> vv_eq e \<or> h_eq e \<or> flat_sum_eq e \<or> free_eq e"

definition lhsv :: "('f, 'v) equation \<Rightarrow> 'v" where
  "lhsv e = the_Var (fst e)"

text \<open>The left-hand variables of the \<open>+\<close>-equations and of the \<open>h\<close>-equations, with multiplicity.\<close>

definition SUMS :: "('f, 'v) problem \<Rightarrow> 'v multiset" where
  "SUMS \<Gamma> = image_mset lhsv (filter_mset flat_sum_eq \<Gamma>)"

definition HS :: "('f, 'v) problem \<Rightarrow> 'v multiset" where
  "HS \<Gamma> = image_mset lhsv (filter_mset h_eq \<Gamma>)"

definition at_level :: "'v depth_set \<Rightarrow> nat \<Rightarrow> 'v multiset \<Rightarrow> 'v multiset" where
  "at_level \<Delta> l M = filter_mset (\<lambda>z. dep \<Delta> z = l) M"

text \<open>
  The work left at level \<open>l\<close>: the number of excess \<open>+\<close>-equations (a variable with \<open>k\<close>
  \<open>+\<close>-equations contributes \<open>k - 1\<close>), the number of \<open>+\<close>-equations, and the number of
  \<open>h\<close>-equations whose left-hand side has depth \<open>l\<close>.
\<close>

definition excess :: "'v multiset \<Rightarrow> nat" where
  "excess M = size M - card (set_mset M)"

definition counts :: "('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "counts \<Gamma> \<Delta> l = (excess (at_level \<Delta> l (SUMS \<Gamma>)), size (at_level \<Delta> l (SUMS \<Gamma>)),
    size (at_level \<Delta> l (HS \<Gamma>)))"

definition levels :: "('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "levels \<Gamma> \<Delta> = map (counts \<Gamma> \<Delta>) [0..<Suc \<kappa>]"

definition nfree :: "('f, 'v) problem \<Rightarrow> nat" where
  "nfree \<Gamma> = size (filter_mset free_eq \<Gamma>)"

fun tmeasure :: "('f, 'v) triple \<Rightarrow> nat \<times> (nat \<times> nat \<times> nat) list" where
  "tmeasure (\<Gamma>, \<Delta>, \<sigma>) = (nfree \<Gamma>, levels \<Gamma> \<Delta>)"

abbreviation R3 :: "((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)) set" where
  "R3 \<equiv> less_than <*lex*> less_than <*lex*> less_than"

definition term_rel :: "((nat \<times> (nat \<times> nat \<times> nat) list) \<times> (nat \<times> (nat \<times> nat \<times> nat) list)) set" where
  "term_rel = less_than <*lex*> lex R3"

lemma wf_term_rel: "wf term_rel"
  unfolding term_rel_def by (intro wf_lex_prod wf_lex wf_less_than)

text \<open>
  The vector of levels decreases if the levels below \<open>l\<close> are unchanged and level \<open>l\<close> decreases
  lexicographically.
\<close>

lemma levels_decrease:
  assumes "l \<le> \<kappa>" and "\<And>i. i < l \<Longrightarrow> counts \<Gamma>' \<Delta>' i = counts \<Gamma> \<Delta> i"
    and "(counts \<Gamma>' \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
  shows "(levels \<Gamma>' \<Delta>', levels \<Gamma> \<Delta>) \<in> lex R3"
proof -
  let ?xs = "levels \<Gamma>' \<Delta>'" and ?ys = "levels \<Gamma> \<Delta>"
  have len: "length ?xs = Suc \<kappa>" "length ?ys = Suc \<kappa>" "l < Suc \<kappa>"
    using assms(1) by (simp_all add: levels_def)
  have take: "take l ?xs = take l ?ys"
    using assms(1,2) by (intro nth_equalityI) (auto simp: levels_def)
  have nth: "?xs ! l = counts \<Gamma>' \<Delta>' l" "?ys ! l = counts \<Gamma> \<Delta> l"
    using len(3) by (simp_all add: levels_def del: upt_Suc)
  have eqs: "?xs = take l ?ys @ counts \<Gamma>' \<Delta>' l # drop (Suc l) ?xs"
    "?ys = take l ?ys @ counts \<Gamma> \<Delta> l # drop (Suc l) ?ys"
    using id_take_nth_drop[of l ?xs] id_take_nth_drop[of l ?ys] len take nth by simp_all
  have "\<exists>xys x y xs' ys'. ?xs = xys @ x # xs' \<and> ?ys = xys @ y # ys' \<and> (x, y) \<in> R3"
    by (rule exI[of _ "take l ?ys"], rule exI[of _ "counts \<Gamma>' \<Delta>' l"],
        rule exI[of _ "counts \<Gamma> \<Delta> l"], rule exI[of _ "drop (Suc l) ?xs"],
        rule exI[of _ "drop (Suc l) ?ys"]) (use eqs assms(3) in simp)
  then show ?thesis
    unfolding lex_conv using len(1,2) by simp
qed

lemma R3_le_less:
  assumes "a' \<le> a" "b' \<le> b" "c' \<le> c" and "a' < a \<or> b' < b \<or> c' < c"
  shows "((a', b', c'), (a, b, c)) \<in> R3"
  using assms by auto

definition le3 :: "nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat \<Rightarrow> bool" where
  "le3 p q \<longleftrightarrow> fst p \<le> fst q \<and> fst (snd p) \<le> fst (snd q) \<and> snd (snd p) \<le> snd (snd q)"

lemma le3_trans: "le3 p q \<Longrightarrow> le3 q r \<Longrightarrow> le3 p r"
  by (auto simp: le3_def)

lemma le3_refl [simp]: "le3 p p"
  by (simp add: le3_def)

lemma card_set_mset_le_size: "card (set_mset N) \<le> size N"
  by (induction N) (auto simp: card_insert_if)

lemma excess_mono:
  assumes "N \<subseteq># M"
  shows "excess N \<le> excess M"
proof -
  obtain K where M: "M = N + K"
    using assms by (metis subset_mset.le_iff_add)
  have "card (set_mset M) \<le> card (set_mset N) + card (set_mset K)"
    unfolding M by (simp add: card_Un_le)
  moreover have "card (set_mset N) \<le> size N" "card (set_mset K) \<le> size K"
    by (simp_all add: card_set_mset_le_size)
  ultimately show ?thesis
    unfolding excess_def M by simp
qed

subsection \<open>Renaming variables\<close>

definition rename_eq :: "('v \<Rightarrow> 'v) \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" where
  "rename_eq r e = (fst e \<cdot> (Var \<circ> r), snd e \<cdot> (Var \<circ> r))"

lemma subst_problem_rename: "subst_problem (Var \<circ> r) \<Gamma> = image_mset (rename_eq r) \<Gamma>"
  unfolding subst_problem_def rename_eq_def by (rule image_mset_cong) auto

lemma sum_terms_rename:
  "ys \<noteq> [] \<Longrightarrow> sum_terms (map Var ys) \<cdot> (Var \<circ> r) = sum_terms (map Var (map r ys))"
  by (simp add: sum_terms_subst comp_def)

lemma flat_kinds_disjoint:
  "flat_sum_eq e \<Longrightarrow> \<not> h_eq e" "flat_sum_eq e \<Longrightarrow> \<not> vv_eq e" "flat_sum_eq e \<Longrightarrow> \<not> free_eq e"
  "h_eq e \<Longrightarrow> \<not> vv_eq e" "h_eq e \<Longrightarrow> \<not> free_eq e" "vv_eq e \<Longrightarrow> \<not> free_eq e"
proof -
  have sum_Fun: "\<exists>us. sum_terms (map Var ys) = Fun plus us" if "2 \<le> length ys" for ys :: "'v list"
    using that by (cases ys rule: remdups_adj.cases) auto
  show "flat_sum_eq e \<Longrightarrow> \<not> h_eq e" "flat_sum_eq e \<Longrightarrow> \<not> vv_eq e"
    "flat_sum_eq e \<Longrightarrow> \<not> free_eq e"
    using sum_Fun plus_neq_hom by (fastforce simp: flat_sum_eq_def h_eq_def vv_eq_def free_eq_def)+
  show "h_eq e \<Longrightarrow> \<not> vv_eq e" "h_eq e \<Longrightarrow> \<not> free_eq e" "vv_eq e \<Longrightarrow> \<not> free_eq e"
    by (auto simp: h_eq_def vv_eq_def free_eq_def)
qed

text \<open>Renaming preserves the kind of every flat equation and renames its left-hand side.\<close>

lemma rename_flat:
  assumes "flat_eq e"
  shows "flat_eq (rename_eq r e)" "lhsv (rename_eq r e) = r (lhsv e)"
    "flat_sum_eq (rename_eq r e) \<longleftrightarrow> flat_sum_eq e" "h_eq (rename_eq r e) \<longleftrightarrow> h_eq e"
    "vv_eq (rename_eq r e) \<longleftrightarrow> vv_eq e" "free_eq (rename_eq r e) \<longleftrightarrow> free_eq e"
proof -
  have both: "((vv_eq (rename_eq r e) \<and> vv_eq e) \<or> (h_eq (rename_eq r e) \<and> h_eq e) \<or>
      (flat_sum_eq (rename_eq r e) \<and> flat_sum_eq e) \<or> (free_eq (rename_eq r e) \<and> free_eq e)) \<and>
    lhsv (rename_eq r e) = r (lhsv e)"
  proof -
    consider (vv) "vv_eq e" | (h) "h_eq e" | (s) "flat_sum_eq e" | (f) "free_eq e"
      using assms by (auto simp: flat_eq_def)
    then show ?thesis
    proof cases
      case vv
      then show ?thesis
        by (auto simp: vv_eq_def rename_eq_def lhsv_def)
    next
      case h
      then show ?thesis
        by (auto simp: h_eq_def rename_eq_def lhsv_def)
    next
      case s
      then obtain x ys where e: "e = (Var x, sum_terms (map Var ys))" "2 \<le> length ys"
        by (auto simp: flat_sum_eq_def)
      then have "ys \<noteq> []"
        by auto
      then have re: "rename_eq r e = (Var (r x), sum_terms (map Var (map r ys)))"
        using e by (simp add: rename_eq_def sum_terms_rename)
      then have "flat_sum_eq (rename_eq r e)"
        using e(2) unfolding flat_sum_eq_def by (metis length_map)
      then show ?thesis
        using s re e(1) by (simp add: lhsv_def)
    next
      case f
      then show ?thesis
        by (auto simp: free_eq_def rename_eq_def lhsv_def comp_def intro!: exI[of _ "map r _"])
    qed
  qed
  note kinds = both[THEN conjunct1]
  show "flat_eq (rename_eq r e)" "lhsv (rename_eq r e) = r (lhsv e)"
    using both by (auto simp: flat_eq_def)
  show "flat_sum_eq (rename_eq r e) \<longleftrightarrow> flat_sum_eq e" "h_eq (rename_eq r e) \<longleftrightarrow> h_eq e"
    "vv_eq (rename_eq r e) \<longleftrightarrow> vv_eq e" "free_eq (rename_eq r e) \<longleftrightarrow> free_eq e"
    using kinds flat_kinds_disjoint by blast+
qed

abbreviation flat_problem :: "('f, 'v) problem \<Rightarrow> bool" where
  "flat_problem \<Gamma> \<equiv> \<forall>e \<in># \<Gamma>. flat_eq e"

lemma filter_image_rename:
  assumes "flat_problem \<Gamma>" and "\<And>e. flat_eq e \<Longrightarrow> P (rename_eq r e) \<longleftrightarrow> P e"
  shows "filter_mset P (image_mset (rename_eq r) \<Gamma>) = image_mset (rename_eq r) (filter_mset P \<Gamma>)"
  using assms(1)
proof (induction \<Gamma>)
  case (add e \<Gamma>)
  then show ?case
    using assms(2)[of e] by auto
qed simp

lemma SUMS_rename: "flat_problem \<Gamma> \<Longrightarrow> SUMS (image_mset (rename_eq r) \<Gamma>) = image_mset r (SUMS \<Gamma>)"
  unfolding SUMS_def
  by (subst filter_image_rename[of _ flat_sum_eq r]) (auto simp: rename_flat multiset.map_comp comp_def
      intro!: image_mset_cong)

lemma HS_rename: "flat_problem \<Gamma> \<Longrightarrow> HS (image_mset (rename_eq r) \<Gamma>) = image_mset r (HS \<Gamma>)"
  unfolding HS_def
  by (subst filter_image_rename[of _ h_eq r]) (auto simp: rename_flat multiset.map_comp comp_def
      intro!: image_mset_cong)

lemma nfree_rename: "flat_problem \<Gamma> \<Longrightarrow> nfree (image_mset (rename_eq r) \<Gamma>) = nfree \<Gamma>"
  unfolding nfree_def by (subst filter_image_rename[of _ free_eq r]) (auto simp: rename_flat)

definition nvv :: "('f, 'v) problem \<Rightarrow> nat" where
  "nvv \<Gamma> = size (filter_mset vv_eq \<Gamma>)"

lemma nvv_rename: "flat_problem \<Gamma> \<Longrightarrow> nvv (image_mset (rename_eq r) \<Gamma>) = nvv \<Gamma>"
  unfolding nvv_def by (subst filter_image_rename[of _ vv_eq r]) (auto simp: rename_flat)

lemma flat_rename: "flat_problem \<Gamma> \<Longrightarrow> flat_problem (image_mset (rename_eq r) \<Gamma>)"
  by (auto simp: rename_flat)

text \<open>Edges of a renamed flat problem come from edges of the original problem.\<close>

lemma edge_rename:
  assumes "flat_problem \<Gamma>" and "edge (image_mset (rename_eq r) \<Gamma>) a' b' i"
  obtains a b where "edge \<Gamma> a b i" "a' = r a" "b' = r b"
proof -
  have "\<exists>a b. edge \<Gamma> a b i \<and> a' = r a \<and> b' = r b"
  proof (cases "(Var a', H (Var b')) \<in># image_mset (rename_eq r) \<Gamma> \<and> i = 1")
    case True
    then obtain e where e: "e \<in># \<Gamma>" "rename_eq r e = (Var a', H (Var b'))"
      by auto
    then have "h_eq e"
      using rename_flat(4)[of e r] assms(1) by (auto simp: h_eq_def)
    then obtain a b where "e = (Var a, H (Var b))"
      by (auto simp: h_eq_def)
    then show ?thesis
      using e True by (auto simp: edge_def rename_eq_def)
  next
    case False
    then obtain ys' where ys': "(Var a', sum_terms (map Var ys')) \<in># image_mset (rename_eq r) \<Gamma>"
      "b' \<in> set ys'" "i = 0"
      using assms(2) by (auto simp: edge_def)
    then obtain e where e: "e \<in># \<Gamma>" "rename_eq r e = (Var a', sum_terms (map Var ys'))"
      by auto
    have "\<exists>a ys. e = (Var a, sum_terms (map Var ys)) \<and> ys \<noteq> []"
    proof -
      consider (vv) "vv_eq e" | (h) "h_eq e" | (s) "flat_sum_eq e" | (f) "free_eq e"
        using assms(1) e(1) by (auto simp: flat_eq_def)
      then show ?thesis
      proof cases
        case vv
        then obtain a b where "e = (Var a, Var b)"
          by (auto simp: vv_eq_def)
        then show ?thesis
          by (intro exI[of _ a] exI[of _ "[b]"]) simp
      next
        case h
        then have "h_eq (rename_eq r e)"
          using rename_flat(4) assms(1) e(1) by blast
        then obtain u where "sum_terms (map Var ys') = H (Var u)"
          using e(2) by (auto simp: h_eq_def)
        then show ?thesis
          using plus_neq_hom ys'(2) by (cases ys' rule: remdups_adj.cases) auto
      next
        case s
        then show ?thesis
          by (fastforce simp: flat_sum_eq_def)
      next
        case f
        then have "free_eq (rename_eq r e)"
          using rename_flat(6) assms(1) e(1) by blast
        then obtain g us where "sum_terms (map Var ys') = Fun g (map Var us)" "g \<noteq> plus"
          using e(2) by (auto simp: free_eq_def)
        then show ?thesis
          using ys'(2) by (cases ys' rule: remdups_adj.cases) auto
      qed
    qed
    then obtain a ys where a: "e = (Var a, sum_terms (map Var ys))" "ys \<noteq> []"
      by blast
    then have "rename_eq r e = (Var (r a), sum_terms (map Var (map r ys)))"
      by (simp add: rename_eq_def sum_terms_rename)
    then have "a' = r a" "vars_term (sum_terms (map Var ys')) = r ` set ys"
      using e(2) a(2) by (auto simp: vars_sum_terms)
    moreover have "vars_term (sum_terms (map Var ys')) = set ys'"
      using ys'(2) by (subst vars_sum_terms) auto
    ultimately obtain b where "b \<in> set ys" "b' = r b"
      using ys'(2) by auto
    then show ?thesis
      using e(1) a ys'(3) \<open>a' = r a\<close> unfolding edge_def by blast
  qed
  then show ?thesis
    using that by blast
qed

lemma edge_mono: "edge \<Gamma>' a b i \<Longrightarrow> \<Gamma>' \<subseteq># \<Gamma> \<Longrightarrow> edge \<Gamma> a b i"
  unfolding edge_def by (meson mset_subset_eqD)

lemma edge_vv: "(Var x, Var y) \<in># \<Gamma> \<Longrightarrow> edge \<Gamma> x y 0"
  unfolding edge_def by (intro disjI2 exI[of _ "[y]"]) simp

subsection \<open>Merging variables\<close>

text \<open>
  States between the macro steps of the strategy: the problem is flat, \<open>\<Delta>\<close> covers its variables
  and is closed under the update rules and bounded. Normal states have no \<open>X =\<^sup>? Y\<close> equations.
\<close>

fun pnormal :: "('f, 'v) triple \<Rightarrow> bool" where
  "pnormal (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> flat_problem \<Gamma> \<and> finite (dom \<Delta>) \<and> finite \<sigma> \<and>
    vars_problem \<Gamma> \<subseteq> dom \<Delta> \<and> closed \<Gamma> \<Delta> \<and> bounded_depths \<Delta>"

fun normal :: "('f, 'v) triple \<Rightarrow> bool" where
  "normal (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> pnormal (\<Gamma>, \<Delta>, \<sigma>) \<and> nvv \<Gamma> = 0"

definition ren :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
  "ren x y v = (if v = x then y else v)"

lemma Var_upd_ren: "Var(x := Var y) = Var \<circ> ren x y"
  by (auto simp: ren_def)

lemma closed_mono: "closed \<Gamma> \<Delta> \<Longrightarrow> \<Gamma>' \<subseteq># \<Gamma> \<Longrightarrow> closed \<Gamma>' \<Delta>"
  unfolding closed_def using edge_mono by blast

lemma finite_subst_bindings: "finite \<sigma> \<Longrightarrow> finite (subst_bindings \<tau> \<sigma>)"
  by (simp add: subst_bindings_def)

text \<open>
  One merge: eliminate \<open>X\<close> by (VE1) using \<open>X =\<^sup>? Y\<close>, then close \<open>\<Delta>\<close>. Since \<open>\<Delta>\<close> was closed,
  \<open>\<Delta>(Y) \<ge> \<Delta>(X)\<close>, so the equations of \<open>X\<close> move to a depth at least \<open>\<Delta>(X)\<close>, and the closure
  does not change the depth of any variable below \<open>\<Delta>(X)\<close> that heads an equation.
\<close>

lemma merge_step:
  assumes "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and "(Var x, Var y) \<in># \<Gamma>" and "x \<noteq> y"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. \<exists>\<Delta>' \<sigma>'.
    S' = (image_mset (rename_eq (ren x y)) (\<Gamma> - {#(Var x, Var y)#}), \<Delta>', \<sigma>') \<and> pnormal S' \<and>
    (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and>
    (\<forall>z \<in> lhs_vars (image_mset (rename_eq (ren x y)) (\<Gamma> - {#(Var x, Var y)#})).
      dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z))"
proof -
  let ?\<Gamma>0 = "\<Gamma> - {#(Var x, Var y)#}"
  let ?\<Gamma>' = "image_mset (rename_eq (ren x y)) ?\<Gamma>0"
  have \<Gamma>: "\<Gamma> = add_mset (Var x, Var y) ?\<Gamma>0"
    using assms(2) by simp
  have flat0: "flat_problem ?\<Gamma>0" and closed: "closed \<Gamma> \<Delta>"
    using assms(1) by (auto dest: in_diffD)
  let ?\<sigma>1 = "subst_bindings (Var(x := Var y)) \<sigma> \<union> {(x, Var y)}"
  have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(?\<Gamma>', \<Delta>, ?\<sigma>1)}"
    using step.VE1[OF assms(3), of ?\<Gamma>0 \<Delta> \<sigma>] \<Gamma> by (simp add: Var_upd_ren subst_problem_rename)
  have xy: "dep \<Delta> x \<le> dep \<Delta> y"
    using closed edge_vv[OF assms(2)] unfolding closed_def by fastforce
  have cover: "vars_problem ?\<Gamma>' \<subseteq> dom \<Delta>"
  proof -
    have "vars_problem ?\<Gamma>' \<subseteq> (vars_problem ?\<Gamma>0 - {x}) \<union> {y}"
      using vars_subst_problem_upd[of x "Var y" ?\<Gamma>0] by (simp add: Var_upd_ren subst_problem_rename)
    moreover have "vars_problem ?\<Gamma>0 \<subseteq> vars_problem \<Gamma>"
      by (rule vars_problem_mono) simp
    moreover have "y \<in> vars_problem \<Gamma>"
      using assms(2) by (force simp: vars_problem_def)
    moreover have "vars_problem \<Gamma> \<subseteq> dom \<Delta>"
      using assms(1) by simp
    ultimately show ?thesis
      by blast
  qed
  have prot: "prot (dep \<Delta> x) ?\<Gamma>' \<Delta>"
    unfolding prot_def
  proof (intro allI impI)
    fix a' b' i
    assume e': "edge ?\<Gamma>' a' b' i" and unsat: "dep \<Delta> b' < dep \<Delta> a' + i"
    obtain a b where e: "edge ?\<Gamma>0 a b i" and ab: "a' = ren x y a" "b' = ren x y b"
      using edge_rename[OF flat0 e'] by blast
    have sat: "dep \<Delta> a + i \<le> dep \<Delta> b"
      using closed edge_mono[OF e] unfolding closed_def by (meson diff_subset_eq_self)
    show "dep \<Delta> x \<le> dep \<Delta> a' \<and> (dep \<Delta> b' < dep \<Delta> x \<longrightarrow> b' \<notin> lhs_vars ?\<Gamma>')"
      using sat unsat xy ab by (auto simp: ren_def split: if_splits)
  qed
  have closure: "reach (?\<Gamma>', \<Delta>, ?\<sigma>1) (\<lambda>S'. \<exists>\<Delta>'. S' = (?\<Gamma>', \<Delta>', ?\<sigma>1) \<and> closed ?\<Gamma>' \<Delta>' \<and>
      bounded_depths \<Delta>' \<and> dom \<Delta>' = dom \<Delta> \<and> (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and>
      (\<forall>z \<in> lhs_vars ?\<Gamma>'. dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z))"
    using update_closure[OF _ cover prot] assms(1) by simp
  show ?thesis
  proof (rule reach_single[OF step], rule reach_mono[OF closure], elim exE conjE)
    fix S' \<Delta>'
    assume S': "S' = (?\<Gamma>', \<Delta>', ?\<sigma>1)" and props: "closed ?\<Gamma>' \<Delta>'" "bounded_depths \<Delta>'"
      "dom \<Delta>' = dom \<Delta>" "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
      "\<forall>z \<in> lhs_vars ?\<Gamma>'. dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z"
    have "pnormal S'"
      using S' props assms(1) cover flat_rename[OF flat0] by (auto simp: finite_subst_bindings)
    then show "\<exists>\<Delta>' \<sigma>'. S' = (?\<Gamma>', \<Delta>', \<sigma>') \<and> pnormal S' \<and> (\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z) \<and>
      (\<forall>z \<in> lhs_vars ?\<Gamma>'. dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z)"
      using S' props by blast
  qed
qed

lemma kinds_vv:
  assumes "vv_eq e"
  shows "\<not> flat_sum_eq e" "\<not> h_eq e" "\<not> free_eq e" "flat_eq e"
  using assms flat_kinds_disjoint[of e] by (auto simp: flat_eq_def)

lemma remove_vv:
  assumes "vv_eq e"
  shows "SUMS (add_mset e \<Gamma>) = SUMS \<Gamma>" "HS (add_mset e \<Gamma>) = HS \<Gamma>"
    "nfree (add_mset e \<Gamma>) = nfree \<Gamma>" "nvv (add_mset e \<Gamma>) = Suc (nvv \<Gamma>)"
  using kinds_vv[OF assms] assms by (simp_all add: SUMS_def HS_def nfree_def nvv_def)

lemma pnormal_sub:
  assumes "pnormal (add_mset e \<Gamma>, \<Delta>, \<sigma>)"
  shows "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
  using assms closed_mono[of "add_mset e \<Gamma>" \<Delta> \<Gamma>] by auto

lemma obtain_vv:
  assumes "nvv \<Gamma> \<noteq> 0"
  obtains x y \<Gamma>0 where "\<Gamma> = add_mset (Var x, Var y) \<Gamma>0"
proof -
  obtain e where "e \<in># filter_mset vv_eq \<Gamma>"
    using assms by (metis multiset_nonemptyE nvv_def size_empty)
  then obtain x y where "(Var x, Var y) \<in># \<Gamma>"
    by (auto simp: vv_eq_def)
  then show ?thesis
    using that by (metis insert_DiffM)
qed

text \<open>Repeated merging removes all \<open>X =\<^sup>? Y\<close> equations.\<close>

lemma vv_closure_basic:
  assumes "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>)"
  using assms
proof (induction "nvv \<Gamma>" arbitrary: \<Gamma> \<Delta> \<sigma> rule: less_induct)
  case less
  show ?case
  proof (cases "nvv \<Gamma> = 0")
    case True
    then show ?thesis
      using less.prems by (intro reach_refl) simp
  next
    case False
    then obtain x y \<Gamma>0 where \<Gamma>: "\<Gamma> = add_mset (Var x, Var y) \<Gamma>0"
      by (rule obtain_vv)
    have vv: "vv_eq (Var x, Var y)"
      by (simp add: vv_eq_def)
    show ?thesis
    proof (cases "x = y")
      case True
      have lt: "nvv \<Gamma>0 < nvv \<Gamma>"
        using remove_vv(4)[OF vv, of \<Gamma>0] \<Gamma> by simp
      have pn: "pnormal (\<Gamma>0, \<Delta>, \<sigma>)"
        using pnormal_sub less.prems \<Gamma> by blast
      have eq: "nfree \<Gamma>0 = nfree \<Gamma>"
        using remove_vv(3)[OF vv, of \<Gamma>0] \<Gamma> by simp
      have "reach (\<Gamma>0, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>0)"
        using less.hyps[OF lt pn] .
      then have "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>0)"
        unfolding \<Gamma> True by (rule reach_single[OF step.Triv])
      then show ?thesis
        unfolding eq .
    next
      case False
      have flat0: "flat_problem \<Gamma>0"
        using less.prems \<Gamma> by simp
      have mem: "(Var x, Var y) \<in># \<Gamma>"
        using \<Gamma> by simp
      show ?thesis
      proof (rule reach_trans[OF merge_step[OF less.prems mem False]], elim exE conjE)
        fix S' \<Delta>' \<sigma>'
        assume S': "S' = (image_mset (rename_eq (ren x y)) (\<Gamma> - {#(Var x, Var y)#}), \<Delta>', \<sigma>')"
          and pn: "pnormal S'"
        let ?\<Gamma>' = "image_mset (rename_eq (ren x y)) \<Gamma>0"
        have S'': "S' = (?\<Gamma>', \<Delta>', \<sigma>')"
          using S' \<Gamma> by simp
        have lt: "nvv ?\<Gamma>' < nvv \<Gamma>"
          using nvv_rename[OF flat0] remove_vv[OF vv] \<Gamma> by simp
        have eq: "nfree ?\<Gamma>' = nfree \<Gamma>"
          using nfree_rename[OF flat0] remove_vv[OF vv] \<Gamma> by simp
        have "reach (?\<Gamma>', \<Delta>', \<sigma>') (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree ?\<Gamma>')"
          using less.hyps[OF lt] pn S'' by blast
        then show "reach S' (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>)"
          unfolding S'' eq .
      qed
    qed
  qed
qed

subsection \<open>Merges and the per-level counts\<close>

text \<open>
  How renaming \<open>x\<close> to \<open>y\<close>, together with raising the depths, affects a multiset of left-hand
  variables at the levels up to \<open>L \<le> \<Delta>(x)\<close>: the levels below \<open>L\<close> are unchanged, and level
  \<open>L\<close> does not grow.
\<close>

lemma at_level_ren:
  fixes M :: "'v multiset"
  assumes xy: "dep \<Delta> x \<le> dep \<Delta>' y" and mono: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
    and keep: "\<forall>z \<in># M. z \<noteq> x \<longrightarrow> dep \<Delta> z < dep \<Delta> x \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
    and L: "L \<le> dep \<Delta> x"
  shows "i < L \<Longrightarrow> at_level \<Delta>' i (image_mset (ren x y) M) = at_level \<Delta> i M"
    and "size (at_level \<Delta>' L (image_mset (ren x y) M)) \<le> size (at_level \<Delta> L M)"
    and "(dep \<Delta> x = L \<longrightarrow> x \<notin># M) \<Longrightarrow> at_level \<Delta>' L (image_mset (ren x y) M) \<subseteq># at_level \<Delta> L M"
proof -
  have bk: "dep \<Delta> z = i \<and> (z = x \<longrightarrow> dep \<Delta> x = L)"
    if "z \<in># M" "dep \<Delta>' (ren x y z) = i" "i \<le> L" for z i
  proof (cases "z = x")
    case True
    then show ?thesis
      using that xy L by (simp add: ren_def)
  next
    case False
    then have "dep \<Delta>' z = i"
      using that(2) by (simp add: ren_def)
    then show ?thesis
      using False keep that(1,3) mono L by (metis le_trans linorder_not_le order_antisym)
  qed
  have fw: "dep \<Delta>' (ren x y z) = i \<and> ren x y z = z"
    if "z \<in># M" "dep \<Delta> z = i" "i < L" for z i
  proof -
    have "z \<noteq> x"
      using that L by auto
    then show ?thesis
      using keep that L by (simp add: ren_def)
  qed
  have img: "at_level \<Delta>' i (image_mset (ren x y) M) =
      image_mset (ren x y) (filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = i) M)" for i
    unfolding at_level_def by (rule image_mset_filter_mset_swap[symmetric])
  show "at_level \<Delta>' i (image_mset (ren x y) M) = at_level \<Delta> i M" if "i < L"
  proof -
    have "filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = i) M = at_level \<Delta> i M"
      unfolding at_level_def
    proof (rule filter_mset_cong[OF HOL.refl])
      fix z
      assume "z \<in># M"
      then show "(dep \<Delta>' (ren x y z) = i) = (dep \<Delta> z = i)"
        using bk[of z i] fw[of z i] that by (meson less_imp_le)
    qed
    moreover have "image_mset (ren x y) (at_level \<Delta> i M) = at_level \<Delta> i M"
      using fw[of _ i] that by (subst image_mset_cong[of _ _ id]) (auto simp: at_level_def)
    ultimately show ?thesis
      using img by simp
  qed
  have sub: "filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = L) M \<subseteq># at_level \<Delta> L M"
  proof -
    have "filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = L) M =
        filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = L) (at_level \<Delta> L M)"
      unfolding at_level_def filter_filter_mset using bk[of _ L]
      by (intro filter_mset_cong) auto
    then show ?thesis
      by simp
  qed
  show "size (at_level \<Delta>' L (image_mset (ren x y) M)) \<le> size (at_level \<Delta> L M)"
    unfolding img using size_mset_mono[OF sub] by simp
  show "at_level \<Delta>' L (image_mset (ren x y) M) \<subseteq># at_level \<Delta> L M" if "dep \<Delta> x = L \<longrightarrow> x \<notin># M"
  proof -
    have "image_mset (ren x y) (filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = L) M) =
        filter_mset (\<lambda>z. dep \<Delta>' (ren x y z) = L) M"
      using bk[of _ L] that by (subst image_mset_cong[of _ _ id]) (auto simp: ren_def)
    then show ?thesis
      unfolding img using sub by simp
  qed
qed

definition VV :: "('f, 'v) problem \<Rightarrow> 'v multiset" where
  "VV \<Gamma> = image_mset lhsv (filter_mset vv_eq \<Gamma>)"

lemma VV_rename: "flat_problem \<Gamma> \<Longrightarrow> VV (image_mset (rename_eq r) \<Gamma>) = image_mset r (VV \<Gamma>)"
  unfolding VV_def
  by (subst filter_image_rename[of _ vv_eq r]) (auto simp: rename_flat multiset.map_comp comp_def
      intro!: image_mset_cong)

lemma SUMS_lhs: "z \<in># SUMS \<Gamma> \<Longrightarrow> z \<in> lhs_vars \<Gamma>"
  by (force simp: SUMS_def lhs_vars_def flat_sum_eq_def lhsv_def)

lemma HS_lhs: "z \<in># HS \<Gamma> \<Longrightarrow> z \<in> lhs_vars \<Gamma>"
  by (force simp: HS_def lhs_vars_def h_eq_def lhsv_def)

lemma count_image_ren:
  "x \<noteq> y \<Longrightarrow> count (image_mset (ren x y) M) a =
    (if a = x then 0 else count M a + (if a = y then count M x else 0))"
  by (induction M) (auto simp: ren_def)

lemma VV_add_vv [simp]: "VV (add_mset (Var x, Var y) \<Gamma>) = add_mset x (VV \<Gamma>)"
  by (simp add: VV_def vv_eq_def lhsv_def)

text \<open>
  The invariant of the merges at level \<open>L\<close>: every \<open>X =\<^sup>? Y\<close> equation has \<open>\<Delta>(X) \<ge> L\<close>, and if
  \<open>\<Delta>(X) = L\<close>, then \<open>X\<close> heads no \<open>+\<close>-equation and no other \<open>X =\<^sup>? Y\<close> equation.
\<close>

definition merge_inv :: "nat \<Rightarrow> ('f, 'v) problem \<Rightarrow> 'v depth_set \<Rightarrow> bool" where
  "merge_inv L \<Gamma> \<Delta> \<longleftrightarrow> (\<forall>a \<in># VV \<Gamma>. L \<le> dep \<Delta> a \<and>
    (dep \<Delta> a = L \<longrightarrow> a \<notin># SUMS \<Gamma> \<and> count (VV \<Gamma>) a = 1))"

lemma merge_counts:
  assumes \<Gamma>: "\<Gamma> = add_mset (Var x, Var y) \<Gamma>0" and "x \<noteq> y" and flat: "flat_problem \<Gamma>0"
    and xy: "dep \<Delta> x \<le> dep \<Delta> y" and inv: "merge_inv L \<Gamma> \<Delta>"
    and mono: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
    and keep: "\<forall>z \<in> lhs_vars (image_mset (rename_eq (ren x y)) \<Gamma>0). dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z"
  defines "\<Gamma>' \<equiv> image_mset (rename_eq (ren x y)) \<Gamma>0"
  shows "\<And>i. i < L \<Longrightarrow> counts \<Gamma>' \<Delta>' i = counts \<Gamma> \<Delta> i"
    and "le3 (counts \<Gamma>' \<Delta>' L) (counts \<Gamma> \<Delta> L)"
    and "merge_inv L \<Gamma>' \<Delta>'"
proof -
  have vv: "vv_eq (Var x, Var y)"
    by (simp add: vv_eq_def)
  have S: "SUMS \<Gamma>' = image_mset (ren x y) (SUMS \<Gamma>)" "HS \<Gamma>' = image_mset (ren x y) (HS \<Gamma>)"
    "VV \<Gamma>' = image_mset (ren x y) (VV \<Gamma>0)"
    using SUMS_rename[OF flat] HS_rename[OF flat] VV_rename[OF flat] remove_vv[OF vv] \<Gamma>
    unfolding \<Gamma>'_def by simp_all
  have x: "x \<in># VV \<Gamma>"
    using \<Gamma> by simp
  have Lx: "L \<le> dep \<Delta> x" and xL: "dep \<Delta> x = L \<Longrightarrow> x \<notin># SUMS \<Gamma> \<and> count (VV \<Gamma>) x = 1"
    using inv x unfolding merge_inv_def by blast+
  have xy': "dep \<Delta> x \<le> dep \<Delta>' y"
    using xy mono le_trans by blast
  have keepM: "\<forall>z \<in># M. z \<noteq> x \<longrightarrow> dep \<Delta> z < dep \<Delta> x \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
    if "\<forall>z \<in># M. ren x y z \<in> lhs_vars \<Gamma>'" for M
  proof (intro ballI impI)
    fix z
    assume "z \<in># M" "z \<noteq> x" "dep \<Delta> z < dep \<Delta> x"
    then have "z \<in> lhs_vars \<Gamma>'"
      using that by (auto simp: ren_def)
    then show "dep \<Delta>' z = dep \<Delta> z"
      using keep \<open>dep \<Delta> z < dep \<Delta> x\<close> unfolding \<Gamma>'_def by (simp add: dep_def)
  qed
  have kS: "\<forall>z \<in># SUMS \<Gamma>. z \<noteq> x \<longrightarrow> dep \<Delta> z < dep \<Delta> x \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
    by (rule keepM) (use S SUMS_lhs in auto)
  have kH: "\<forall>z \<in># HS \<Gamma>. z \<noteq> x \<longrightarrow> dep \<Delta> z < dep \<Delta> x \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
    by (rule keepM) (use S HS_lhs in auto)
  note AS = at_level_ren[OF xy' mono kS Lx] and AH = at_level_ren[OF xy' mono kH Lx]
  show "counts \<Gamma>' \<Delta>' i = counts \<Gamma> \<Delta> i" if "i < L" for i
    unfolding counts_def S using AS(1)[OF that] AH(1)[OF that] by simp
  have "at_level \<Delta>' L (SUMS \<Gamma>') \<subseteq># at_level \<Delta> L (SUMS \<Gamma>)"
    unfolding S using AS(3) xL by blast
  then show "le3 (counts \<Gamma>' \<Delta>' L) (counts \<Gamma> \<Delta> L)"
    unfolding counts_def le3_def using excess_mono size_mset_mono AH(2) S(2) by auto
  show "merge_inv L \<Gamma>' \<Delta>'"
    unfolding merge_inv_def
  proof
    fix a'
    assume "a' \<in># VV \<Gamma>'"
    then obtain a where a: "a \<in># VV \<Gamma>0" "a' = ren x y a"
      using S(3) by auto
    have VV\<Gamma>: "VV \<Gamma> = add_mset x (VV \<Gamma>0)"
      using \<Gamma> by simp
    have aV: "a \<in># VV \<Gamma>"
      using a(1) VV\<Gamma> by simp
    have x2: "dep \<Delta> x = L \<Longrightarrow> x \<notin># VV \<Gamma>0"
      using xL VV\<Gamma> by (auto simp: count_eq_zero_iff[symmetric])
    have "L \<le> dep \<Delta>' a'"
    proof (cases "a = x")
      case True
      then show ?thesis
        using a(2) Lx xy' by (simp add: ren_def)
    next
      case False
      then show ?thesis
        using a(2) aV inv mono unfolding merge_inv_def by (metis le_trans ren_def)
    qed
    moreover have "a' \<notin># SUMS \<Gamma>' \<and> count (VV \<Gamma>') a' = 1" if a'L: "dep \<Delta>' a' = L"
    proof -
      have "a \<noteq> x"
      proof
        assume "a = x"
        then have "dep \<Delta> x \<noteq> L"
          using x2 a(1) by blast
        then have "L < dep \<Delta> x"
          using Lx by simp
        then show False
          using a'L a(2) \<open>a = x\<close> xy' by (simp add: ren_def)
      qed
      then have a'a: "a' = a"
        using a(2) by (simp add: ren_def)
      have "dep \<Delta> a = L"
        using a'L a'a mono aV inv unfolding merge_inv_def by (metis le_antisym)
      then have aS: "a \<notin># SUMS \<Gamma>" and ac: "count (VV \<Gamma>) a = 1"
        using inv aV unfolding merge_inv_def by blast+
      have no_y: "a = y \<Longrightarrow> L < dep \<Delta> x \<Longrightarrow> False"
        using a'L a'a xy' by simp
      have "a' \<notin># SUMS \<Gamma>'"
      proof
        assume "a' \<in># SUMS \<Gamma>'"
        then obtain z where z: "z \<in># SUMS \<Gamma>" "a = ren x y z"
          using S(1) a'a by auto
        show False
        proof (cases "z = x")
          case True
          then have "a = y" "dep \<Delta> x \<noteq> L"
            using z xL by (auto simp: ren_def)
          then show False
            using no_y Lx by simp
        next
          case False
          then show False
            using z aS by (simp add: ren_def)
        qed
      qed
      moreover have "count (VV \<Gamma>') a' = 1"
      proof -
        have "count (VV \<Gamma>0) a = 1"
          using ac VV\<Gamma> \<open>a \<noteq> x\<close> by simp
        moreover have "a = y \<Longrightarrow> count (VV \<Gamma>0) x = 0"
          using no_y x2 Lx by (metis count_eq_zero_iff le_neq_implies_less)
        ultimately show ?thesis
          using S(3) a'a \<open>a \<noteq> x\<close> count_image_ren[OF assms(2)] by simp
      qed
      ultimately show ?thesis ..
    qed
    ultimately show "L \<le> dep \<Delta>' a' \<and> (dep \<Delta>' a' = L \<longrightarrow> a' \<notin># SUMS \<Gamma>' \<and> count (VV \<Gamma>') a' = 1)"
      by blast
  qed
qed

lemma merge_inv_Triv:
  assumes "merge_inv L (add_mset (Var x, Var x) \<Gamma>) \<Delta>"
  shows "merge_inv L \<Gamma> \<Delta>"
proof -
  have vv: "vv_eq (Var x, Var x)"
    by (simp add: vv_eq_def)
  show ?thesis
    unfolding merge_inv_def
  proof
    fix a
    assume a: "a \<in># VV \<Gamma>"
    then have P: "L \<le> dep \<Delta> a \<and> (dep \<Delta> a = L \<longrightarrow> a \<notin># SUMS \<Gamma> \<and> count (add_mset x (VV \<Gamma>)) a = 1)"
      using assms remove_vv(1)[OF vv] unfolding merge_inv_def by auto
    have "0 < count (VV \<Gamma>) a"
      using a by simp
    then have "count (add_mset x (VV \<Gamma>)) a = 1 \<Longrightarrow> a \<noteq> x \<and> count (VV \<Gamma>) a = 1"
      by (cases "a = x") auto
    then show "L \<le> dep \<Delta> a \<and> (dep \<Delta> a = L \<longrightarrow> a \<notin># SUMS \<Gamma> \<and> count (VV \<Gamma>) a = 1)"
      using P by blast
  qed
qed

fun tcounts :: "('f, 'v) triple \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "tcounts (\<Gamma>, \<Delta>, \<sigma>) i = counts \<Gamma> \<Delta> i"

text \<open>
  Repeated merging under the invariant: the levels below \<open>L\<close> are unchanged and level \<open>L\<close> does
  not grow.
\<close>

lemma vv_closure:
  assumes "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and "merge_inv L \<Gamma> \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma> \<and>
    (\<forall>i < L. tcounts S' i = counts \<Gamma> \<Delta> i) \<and> le3 (tcounts S' L) (counts \<Gamma> \<Delta> L))"
  using assms
proof (induction "nvv \<Gamma>" arbitrary: \<Gamma> \<Delta> \<sigma> rule: less_induct)
  case less
  show ?case
  proof (cases "nvv \<Gamma> = 0")
    case True
    then show ?thesis
      using less.prems by (intro reach_refl) simp
  next
    case False
    then obtain x y \<Gamma>0 where \<Gamma>: "\<Gamma> = add_mset (Var x, Var y) \<Gamma>0"
      by (rule obtain_vv)
    have vv: "vv_eq (Var x, Var y)"
      by (simp add: vv_eq_def)
    have lt: "nvv \<Gamma>0 < nvv \<Gamma>" and eq: "nfree \<Gamma>0 = nfree \<Gamma>"
      using remove_vv(3,4)[OF vv, of \<Gamma>0] \<Gamma> by simp_all
    have flat0: "flat_problem \<Gamma>0"
      using less.prems \<Gamma> by simp
    show ?thesis
    proof (cases "x = y")
      case True
      have cnt: "counts \<Gamma>0 \<Delta> = counts \<Gamma> \<Delta>"
        using remove_vv(1,2)[OF vv, of \<Gamma>0] \<Gamma> by (simp add: counts_def fun_eq_iff)
      have pn: "pnormal (\<Gamma>0, \<Delta>, \<sigma>)"
        using pnormal_sub less.prems \<Gamma> by blast
      have inv: "merge_inv L \<Gamma>0 \<Delta>"
        using merge_inv_Triv less.prems(2) \<Gamma> True by blast
      have "reach (\<Gamma>0, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>0 \<and>
          (\<forall>i < L. tcounts S' i = counts \<Gamma>0 \<Delta> i) \<and> le3 (tcounts S' L) (counts \<Gamma>0 \<Delta> L))"
        using less.hyps[OF lt pn inv] .
      then have "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>0 \<and>
          (\<forall>i < L. tcounts S' i = counts \<Gamma>0 \<Delta> i) \<and> le3 (tcounts S' L) (counts \<Gamma>0 \<Delta> L))"
        unfolding \<Gamma> True by (rule reach_single[OF step.Triv])
      then show ?thesis
        unfolding eq cnt \<Gamma> .
    next
      case False
      have mem: "(Var x, Var y) \<in># \<Gamma>"
        using \<Gamma> by simp
      have xy: "dep \<Delta> x \<le> dep \<Delta> y"
      proof -
        have "closed \<Gamma> \<Delta>"
          using less.prems(1) by simp
        then show ?thesis
          using edge_vv[OF mem] unfolding closed_def by fastforce
      qed
      show ?thesis
      proof (rule reach_trans[OF merge_step[OF less.prems(1) mem False]], elim exE conjE)
        fix S' \<Delta>' \<sigma>'
        let ?\<Gamma>' = "image_mset (rename_eq (ren x y)) \<Gamma>0"
        assume S': "S' = (image_mset (rename_eq (ren x y)) (\<Gamma> - {#(Var x, Var y)#}), \<Delta>', \<sigma>')"
          and pn: "pnormal S'" and mono: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
          and keep: "\<forall>z \<in> lhs_vars (image_mset (rename_eq (ren x y)) (\<Gamma> - {#(Var x, Var y)#})).
            dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z"
        have S'': "S' = (?\<Gamma>', \<Delta>', \<sigma>')"
          using S' \<Gamma> by simp
        have keep': "\<forall>z \<in> lhs_vars ?\<Gamma>'. dep \<Delta> z < dep \<Delta> x \<longrightarrow> \<Delta>' z = \<Delta> z"
          using keep \<Gamma> by simp
        note mc = merge_counts[OF \<Gamma> False flat0 xy less.prems(2) mono keep']
        have lt': "nvv ?\<Gamma>' < nvv \<Gamma>"
          using nvv_rename[OF flat0] lt by simp
        have eq': "nfree ?\<Gamma>' = nfree \<Gamma>"
          using nfree_rename[OF flat0] eq by simp
        have "reach (?\<Gamma>', \<Delta>', \<sigma>') (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree ?\<Gamma>' \<and>
            (\<forall>i < L. tcounts S' i = counts ?\<Gamma>' \<Delta>' i) \<and> le3 (tcounts S' L) (counts ?\<Gamma>' \<Delta>' L))"
          using less.hyps[OF lt'] pn mc(3) S'' by blast
        then show "reach S' (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma> \<and>
            (\<forall>i < L. tcounts S' i = counts \<Gamma> \<Delta> i) \<and> le3 (tcounts S' L) (counts \<Gamma> \<Delta> L))"
          unfolding S''
        proof (rule reach_mono)
          fix T
          assume "normal T \<and> nfree (fst T) = nfree ?\<Gamma>' \<and>
            (\<forall>i < L. tcounts T i = counts ?\<Gamma>' \<Delta>' i) \<and> le3 (tcounts T L) (counts ?\<Gamma>' \<Delta>' L)"
          then show "normal T \<and> nfree (fst T) = nfree \<Gamma> \<and>
            (\<forall>i < L. tcounts T i = counts \<Gamma> \<Delta> i) \<and> le3 (tcounts T L) (counts \<Gamma> \<Delta> L)"
            using mc(1) eq' le3_trans[OF _ mc(2)] by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>Infrastructure for the macro steps\<close>

lemma lhsv_simp [simp]: "lhsv (Var x, t) = x"
  by (simp add: lhsv_def)

lemma kinds_add [simp]:
  "SUMS (add_mset e \<Gamma>) = (if flat_sum_eq e then add_mset (lhsv e) (SUMS \<Gamma>) else SUMS \<Gamma>)"
  "HS (add_mset e \<Gamma>) = (if h_eq e then add_mset (lhsv e) (HS \<Gamma>) else HS \<Gamma>)"
  "VV (add_mset e \<Gamma>) = (if vv_eq e then add_mset (lhsv e) (VV \<Gamma>) else VV \<Gamma>)"
  "nfree (add_mset e \<Gamma>) = (if free_eq e then Suc (nfree \<Gamma>) else nfree \<Gamma>)"
  "nvv (add_mset e \<Gamma>) = (if vv_eq e then Suc (nvv \<Gamma>) else nvv \<Gamma>)"
  by (simp_all add: SUMS_def HS_def VV_def nfree_def nvv_def)

lemma kinds_union [simp]:
  "SUMS (\<Gamma> + \<Gamma>') = SUMS \<Gamma> + SUMS \<Gamma>'" "HS (\<Gamma> + \<Gamma>') = HS \<Gamma> + HS \<Gamma>'"
  "VV (\<Gamma> + \<Gamma>') = VV \<Gamma> + VV \<Gamma>'" "nfree (\<Gamma> + \<Gamma>') = nfree \<Gamma> + nfree \<Gamma>'"
  "nvv (\<Gamma> + \<Gamma>') = nvv \<Gamma> + nvv \<Gamma>'"
  by (simp_all add: SUMS_def HS_def VV_def nfree_def nvv_def)

lemma kinds_empty [simp]:
  "SUMS {#} = {#}" "HS {#} = {#}" "VV {#} = {#}" "nfree {#} = 0" "nvv {#} = 0"
  by (simp_all add: SUMS_def HS_def VV_def nfree_def nvv_def)

lemma vv_kinds [simp]:
  "vv_eq (Var x, Var y)" "\<not> h_eq (Var x, Var y)" "\<not> flat_sum_eq (Var x, Var y)"
  "\<not> free_eq (Var x, Var y)"
  using flat_kinds_disjoint[of "(Var x, Var y)"] by (auto simp: vv_eq_def)

lemma h_kinds [simp]:
  "h_eq (Var x, H (Var y))" "\<not> vv_eq (Var x, H (Var y))" "\<not> flat_sum_eq (Var x, H (Var y))"
  "\<not> free_eq (Var x, H (Var y))"
  using flat_kinds_disjoint[of "(Var x, H (Var y))"] by (auto simp: h_eq_def)

lemma sum_kinds:
  assumes "2 \<le> length ys"
  shows "flat_sum_eq (Var x, sum_terms (map Var ys))" "\<not> vv_eq (Var x, sum_terms (map Var ys))"
    "\<not> h_eq (Var x, sum_terms (map Var ys))" "\<not> free_eq (Var x, sum_terms (map Var ys))"
proof -
  show s: "flat_sum_eq (Var x, sum_terms (map Var ys))"
    using assms by (auto simp: flat_sum_eq_def)
  show "\<not> vv_eq (Var x, sum_terms (map Var ys))" "\<not> h_eq (Var x, sum_terms (map Var ys))"
    "\<not> free_eq (Var x, sum_terms (map Var ys))"
    using flat_kinds_disjoint s by blast+
qed

lemma VV_normal: "nvv \<Gamma> = 0 \<Longrightarrow> VV \<Gamma> = {#}"
  by (simp add: VV_def nvv_def)

text \<open>Edges, equation by equation.\<close>

lemma edge_add: "edge (add_mset e \<Gamma>) a b i \<longleftrightarrow> edge {#e#} a b i \<or> edge \<Gamma> a b i"
  by (auto simp: edge_def)

lemma edge_union: "edge (\<Gamma> + \<Gamma>') a b i \<longleftrightarrow> edge \<Gamma> a b i \<or> edge \<Gamma>' a b i"
  by (auto simp: edge_def)

lemma edge_eq:
  assumes "edge \<Gamma> a b i"
  obtains t where "(Var a, t) \<in># \<Gamma>" "b \<in> vars_term t"
proof -
  have "\<exists>t. (Var a, t) \<in># \<Gamma> \<and> b \<in> vars_term t"
  proof (cases "(Var a, H (Var b)) \<in># \<Gamma>")
    case False
    then obtain ys where "(Var a, sum_terms (map Var ys)) \<in># \<Gamma>" "b \<in> set ys"
      using assms by (auto simp: edge_def)
    moreover have "vars_term (sum_terms (map Var ys)) = set ys"
      using \<open>b \<in> set ys\<close> by (subst vars_sum_terms) auto
    ultimately show ?thesis
      by auto
  qed auto
  then show ?thesis
    using that by blast
qed

lemma sum_terms_not_H: "ys \<noteq> [] \<Longrightarrow> sum_terms (map Var ys) \<noteq> H t"
  using plus_neq_hom by (cases ys rule: remdups_adj.cases) auto

lemma sum_terms_mem: "b \<in> set ys \<Longrightarrow> sum_terms (map Var ys) = t \<Longrightarrow> b \<in> vars_term t"
  using vars_sum_terms[of "map Var ys"] by (cases "ys = []") auto

lemma edge_single_vv: "edge {#(Var y, Var z)#} a b i \<longleftrightarrow> a = y \<and> b = z \<and> i = 0"
proof
  assume "edge {#(Var y, Var z)#} a b i"
  then show "a = y \<and> b = z \<and> i = 0"
    using sum_terms_mem[of b _ "Var z"] by (auto simp: edge_def)
next
  assume "a = y \<and> b = z \<and> i = 0"
  then show "edge {#(Var y, Var z)#} a b i"
    unfolding edge_def by (intro disjI2 exI[of _ "[z]"]) simp
qed

lemma edge_single_h: "edge {#(Var x, H (Var y))#} a b i \<longleftrightarrow> a = x \<and> b = y \<and> i = 1"
proof
  assume e: "edge {#(Var x, H (Var y))#} a b i"
  have "\<not> (sum_terms (map Var ys) = H (Var y) \<and> b \<in> set ys)" for ys
    using sum_terms_not_H[of ys "Var y"] by (cases "ys = []") auto
  then show "a = x \<and> b = y \<and> i = 1"
    using e by (auto simp: edge_def)
next
  assume "a = x \<and> b = y \<and> i = 1"
  then show "edge {#(Var x, H (Var y))#} a b i"
    by (simp add: edge_def)
qed

lemma edge_single_sum:
  assumes "2 \<le> length ys"
  shows "edge {#(Var x, sum_terms (map Var ys))#} a b i \<longleftrightarrow> a = x \<and> b \<in> set ys \<and> i = 0"
proof
  assume e: "edge {#(Var x, sum_terms (map Var ys))#} a b i"
  have ne: "ys \<noteq> []"
    using assms by auto
  have "vars_term (sum_terms (map Var ys)) = set ys"
    using assms by (subst vars_sum_terms) auto
  then show "a = x \<and> b \<in> set ys \<and> i = 0"
    using e sum_terms_not_H[OF ne, of "Var b"] sum_terms_mem[of b _ "sum_terms (map Var ys)"]
    by (auto simp: edge_def)
next
  assume "a = x \<and> b \<in> set ys \<and> i = 0"
  then show "edge {#(Var x, sum_terms (map Var ys))#} a b i"
    unfolding edge_def by (intro disjI2 exI[of _ ys]) auto
qed

text \<open>Fresh variables and updates of \<open>\<Delta>\<close>.\<close>

lemma fresh_list:
  assumes "finite V"
  obtains vs :: "'v list" where "length vs = n" "distinct vs" "set vs \<inter> V = {}"
proof -
  have "infinite (UNIV - V)"
    using infinite_vars assms by (simp add: Diff_infinite_finite)
  then obtain B where B: "finite B" "card B = n" "B \<subseteq> UNIV - V"
    using infinite_arbitrarily_large by blast
  obtain vs where "set vs = B" "distinct vs"
    using finite_distinct_list[OF B(1)] by blast
  then show ?thesis
    using that B distinct_card by fastforce
qed

lemma finite_vars_problem: "finite (vars_problem \<Gamma>)"
  by (auto simp: vars_problem_def vars_eq_def)

lemma pnormal_finite_vars: "pnormal S \<Longrightarrow> finite (vars_triple S)"
  by (cases S) (auto simp: finite_vars_problem vars_bindings_def)

lemma map_upds_replicate:
  "(\<Delta>(vs [\<mapsto>] replicate (length vs) c)) z = (if z \<in> set vs then Some c else \<Delta> z)"
  by (induction vs arbitrary: \<Delta>) auto

text \<open>Composing the measure.\<close>

lemma R3_le3: "le3 p q \<Longrightarrow> (q, r) \<in> R3 \<Longrightarrow> (p, r) \<in> R3"
  by (cases p; cases q; cases r) (auto simp: le3_def)

lemma term_rel_level:
  assumes "nfree \<Gamma>' = nfree \<Gamma>" and "l \<le> \<kappa>" and "\<forall>i < l. counts \<Gamma>' \<Delta>' i = counts \<Gamma> \<Delta> i"
    and "(counts \<Gamma>' \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
  shows "(tmeasure (\<Gamma>', \<Delta>', \<sigma>'), tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
  using levels_decrease[of l \<Gamma>' \<Delta>' \<Gamma> \<Delta>] assms by (simp add: term_rel_def)

lemma term_rel_free:
  "nfree \<Gamma>' < nfree \<Gamma> \<Longrightarrow> (tmeasure (\<Gamma>', \<Delta>', \<sigma>'), tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
  by (simp add: term_rel_def)

text \<open>Raising depths without touching the protected levels.\<close>

lemma at_level_raise:
  assumes mono: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
    and keep: "\<forall>z \<in># M. dep \<Delta> z < L \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
  shows "i < L \<Longrightarrow> at_level \<Delta>' i M = at_level \<Delta> i M"
    and "at_level \<Delta>' L M \<subseteq># at_level \<Delta> L M"
proof -
  have iff: "dep \<Delta>' z = i \<longleftrightarrow> dep \<Delta> z = i" if "z \<in># M" "i < L" for z i
    using mono[rule_format, of z] keep that by (cases "dep \<Delta> z < L") auto
  show "at_level \<Delta>' i M = at_level \<Delta> i M" if "i < L"
    unfolding at_level_def using iff[OF _ that] by (intro filter_mset_cong[OF HOL.refl]) simp
  have "at_level \<Delta>' L M = filter_mset (\<lambda>z. dep \<Delta>' z = L) (at_level \<Delta> L M)"
    unfolding at_level_def filter_filter_mset
  proof (rule filter_mset_cong[OF HOL.refl])
    fix z
    assume "z \<in># M"
    then show "(dep \<Delta>' z = L) = (dep \<Delta> z = L \<and> dep \<Delta>' z = L)"
      using mono[rule_format, of z] keep by (metis le_neq_implies_less)
  qed
  then show "at_level \<Delta>' L M \<subseteq># at_level \<Delta> L M"
    by simp
qed

lemma at_level_cong: "(\<forall>z \<in># M. dep \<Delta>' z = dep \<Delta> z) \<Longrightarrow> at_level \<Delta>' i M = at_level \<Delta> i M"
  unfolding at_level_def by (intro filter_mset_cong[OF HOL.refl]) auto

lemma at_level_simps [simp]:
  "at_level \<Delta> l {#} = {#}"
  "at_level \<Delta> l (add_mset z M) = (if dep \<Delta> z = l then add_mset z (at_level \<Delta> l M) else at_level \<Delta> l M)"
  "at_level \<Delta> l (M + N) = at_level \<Delta> l M + at_level \<Delta> l N"
  by (simp_all add: at_level_def)

lemma excess_pos:
  assumes "2 \<le> count M x"
  shows "0 < excess M"
proof -
  have "x \<in># M"
    using assms by (simp flip: count_greater_zero_iff)
  then obtain M1 where M1: "M = add_mset x M1"
    by (blast dest: multi_member_split)
  then have "x \<in># M1"
    using assms by (simp flip: count_greater_zero_iff)
  then obtain M' where "M1 = add_mset x M'"
    by (blast dest: multi_member_split)
  then have M: "M = add_mset x (add_mset x M')"
    using M1 by simp
  have "card (set_mset M) \<le> Suc (size M')"
    unfolding M using card_set_mset_le_size[of M'] by (simp add: card_insert_if)
  then show ?thesis
    unfolding excess_def M by simp
qed

lemma excess_zero: "(\<forall>x. count M x \<le> 1) \<Longrightarrow> excess M = 0"
proof (induction M)
  case (add x M)
  have "count (add_mset x M) x \<le> 1" "\<forall>y. count M y \<le> count (add_mset x M) y"
    using add.prems by blast simp
  then have "x \<notin># M" "\<forall>y. count M y \<le> 1"
    using add.prems by (auto simp: count_eq_zero_iff[symmetric] intro: le_trans)
  then show ?case
    using add.IH card_set_mset_le_size[of M] by (simp add: excess_def)
qed (simp add: excess_def)

lemma dep_le_kappa: "bounded_depths \<Delta> \<Longrightarrow> dep \<Delta> x \<le> \<kappa>"
  by (cases "\<Delta> x") (auto simp: dep_def bounded_depths_def)

text \<open>
  The common end of the macro steps at level \<open>l\<close>: if an intermediate problem \<open>\<Gamma>\<^sub>1\<close> is
  smaller than \<open>\<Gamma>\<close> at level \<open>l\<close> and equal below, so is every normal state reached from it by
  steps that keep the levels below \<open>l\<close> and do not increase level \<open>l\<close>.
\<close>

lemma finish_level:
  assumes "reach S1 (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>1 \<and>
      (\<forall>i < l. tcounts S' i = counts \<Gamma>1 \<Delta>1 i) \<and> le3 (tcounts S' l) (counts \<Gamma>1 \<Delta>1 l))"
    and "nfree \<Gamma>1 = nfree \<Gamma>" and "l \<le> \<kappa>" and "\<forall>i < l. counts \<Gamma>1 \<Delta>1 i = counts \<Gamma> \<Delta> i"
    and "(counts \<Gamma>1 \<Delta>1 l, counts \<Gamma> \<Delta> l) \<in> R3"
  shows "reach S1 (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
  using assms(1)
proof (rule reach_mono)
  fix S'
  assume S': "normal S' \<and> nfree (fst S') = nfree \<Gamma>1 \<and>
    (\<forall>i < l. tcounts S' i = counts \<Gamma>1 \<Delta>1 i) \<and> le3 (tcounts S' l) (counts \<Gamma>1 \<Delta>1 l)"
  obtain \<Gamma>' \<Delta>' \<sigma>' where S'_eq: "S' = (\<Gamma>', \<Delta>', \<sigma>')"
    by (cases S')
  have le: "le3 (counts \<Gamma>' \<Delta>' l) (counts \<Gamma>1 \<Delta>1 l)"
    using S' unfolding S'_eq by simp
  have "(tmeasure (\<Gamma>', \<Delta>', \<sigma>'), tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
    using S' assms(2-4) R3_le3[OF le assms(5)] unfolding S'_eq
    by (intro term_rel_level) auto
  then show "normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
    using S' S'_eq by simp
qed

lemma closed_edge: "closed \<Gamma> \<Delta> \<Longrightarrow> edge \<Gamma> x y i \<Longrightarrow> dep \<Delta> x + i \<le> dep \<Delta> y"
  unfolding closed_def by blast

lemma edge_h_mem: "(Var x, H (Var y)) \<in># \<Gamma> \<Longrightarrow> edge \<Gamma> x y 1"
  by (simp add: edge_def)

lemma edge_sum_mem: "(Var x, sum_terms (map Var ys)) \<in># \<Gamma> \<Longrightarrow> y \<in> set ys \<Longrightarrow> edge \<Gamma> x y 0"
  unfolding edge_def by blast

subsection \<open>The macro steps at a level\<close>

text \<open>(Dec) on \<open>X =\<^sup>? h(Y)\<close> and \<open>X =\<^sup>? h(Z)\<close>, followed by merging \<open>Y\<close> and \<open>Z\<close>.\<close>

lemma dec_h_facts:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)"
    and \<Gamma>: "\<Gamma> = add_mset (Var x, H (Var y)) (add_mset (Var x, H (Var z)) \<Gamma>0)"
    and yz: "dep \<Delta> y \<le> dep \<Delta> z"
  shows "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0), \<Delta>, \<sigma>)}"
    and "pnormal (add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0), \<Delta>, \<sigma>)"
    and "merge_inv (dep \<Delta> x) (add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0)) \<Delta>"
    and "dep \<Delta> x \<le> \<kappa>"
    and "nfree (add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0)) = nfree \<Gamma>"
    and "\<forall>i < dep \<Delta> x. counts (add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0)) \<Delta> i =
      counts \<Gamma> \<Delta> i"
    and "(counts (add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0)) \<Delta> (dep \<Delta> x),
      counts \<Gamma> \<Delta> (dep \<Delta> x)) \<in> R3"
proof -
  let ?\<Gamma>1 = "add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) \<Gamma>0)"
  let ?l = "dep \<Delta> x"
  have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(?\<Gamma>1, \<Delta>, \<sigma>)}"
    using step.Dec[of hom "[Var y]" "[Var z]" x \<Gamma>0 \<Delta> \<sigma>] plus_neq_hom \<Gamma> by (simp add: add_mset_commute)
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and nvv: "nvv \<Gamma> = 0"
    using N by simp_all
  have closed: "closed \<Gamma> \<Delta>"
    using pn by simp
  have xy: "?l + 1 \<le> dep \<Delta> y"
    using closed_edge[OF closed edge_h_mem[of x y]] \<Gamma> by simp
  have sub: "add_mset (Var x, H (Var y)) \<Gamma>0 \<subseteq># \<Gamma>"
    using \<Gamma> by simp
  have closed1: "closed ?\<Gamma>1 \<Delta>"
    unfolding closed_def
  proof (intro allI impI)
    fix a b i
    assume "edge ?\<Gamma>1 a b i"
    then consider "a = y" "b = z" "i = 0" | "edge (add_mset (Var x, H (Var y)) \<Gamma>0) a b i"
      unfolding edge_add[of "(Var y, Var z)"] edge_single_vv by blast
    then show "dep \<Delta> a + i \<le> dep \<Delta> b"
      by cases (use yz closed_edge[OF closed] edge_mono[OF _ sub] in auto)
  qed
  have pn1: "pnormal (?\<Gamma>1, \<Delta>, \<sigma>)"
    using pn closed1 \<Gamma> by (auto simp: flat_eq_def)
  have VV0: "VV \<Gamma>0 = {#}"
    using nvv \<Gamma> VV_normal[of \<Gamma>0] by simp
  have inv: "merge_inv ?l ?\<Gamma>1 \<Delta>"
    using xy VV0 by (simp add: merge_inv_def)
  have l: "?l \<le> \<kappa>"
    using pn dep_le_kappa by simp
  have cnt: "\<forall>i < ?l. counts ?\<Gamma>1 \<Delta> i = counts \<Gamma> \<Delta> i"
    "(counts ?\<Gamma>1 \<Delta> ?l, counts \<Gamma> \<Delta> ?l) \<in> R3"
    using \<Gamma> by (simp_all add: counts_def)
  show "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(?\<Gamma>1, \<Delta>, \<sigma>)}" "pnormal (?\<Gamma>1, \<Delta>, \<sigma>)" "merge_inv ?l ?\<Gamma>1 \<Delta>" "?l \<le> \<kappa>"
    "\<forall>i < ?l. counts ?\<Gamma>1 \<Delta> i = counts \<Gamma> \<Delta> i" "(counts ?\<Gamma>1 \<Delta> ?l, counts \<Gamma> \<Delta> ?l) \<in> R3"
    using step pn1 inv l cnt by blast+
  show "nfree ?\<Gamma>1 = nfree \<Gamma>"
    using \<Gamma> by simp
qed

lemma dec_h_step:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)"
    and \<Gamma>: "\<Gamma> = add_mset (Var x, H (Var y)) (add_mset (Var x, H (Var z)) \<Gamma>0)"
    and yz: "dep \<Delta> y \<le> dep \<Delta> z"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  note F = dec_h_facts[OF assms]
  show ?thesis
    by (rule reach_single[OF F(1)], rule finish_level[OF vv_closure[OF F(2,3)]])
      (use F(4-7) in simp_all)
qed

text \<open>
  When the free equations decrease, the levels do not matter: close \<open>\<Delta>\<close> without protecting any
  level, then merge.
\<close>

lemma prot_zero [simp]: "prot 0 \<Gamma> \<Delta>"
  by (simp add: prot_def)

lemma close_merge:
  assumes "flat_problem \<Gamma>" and "finite (dom \<Delta>)" and "finite \<sigma>" and "vars_problem \<Gamma> \<subseteq> dom \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>)"
proof (rule reach_trans[OF update_closure[OF assms(2,4) prot_zero]], elim exE conjE)
  fix S' \<Delta>'
  assume S': "S' = (\<Gamma>, \<Delta>', \<sigma>)" and "closed \<Gamma> \<Delta>'" "bounded_depths \<Delta>'" "dom \<Delta>' = dom \<Delta>"
  then have "pnormal S'"
    using assms by simp
  then show "reach S' (\<lambda>S'. normal S' \<and> nfree (fst S') = nfree \<Gamma>)"
    using vv_closure_basic[of \<Gamma> \<Delta>' \<sigma>] S' by simp
qed

text \<open>(Dec) on two free equations \<open>X =\<^sup>? f(Y\<^sub>1, \<dots>, Y\<^sub>n)\<close> and \<open>X =\<^sup>? f(Z\<^sub>1, \<dots>, Z\<^sub>n)\<close>, then merging.\<close>

lemma dec_free_step:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)"
    and \<Gamma>: "\<Gamma> = add_mset (Var x, Fun f (map Var ys)) (add_mset (Var x, Fun f (map Var zs)) \<Gamma>0)"
    and f: "f \<noteq> plus" and len: "length ys = length zs"
    and fr: "free_eq (Var x, Fun f (map Var ys))" "free_eq (Var x, Fun f (map Var zs))"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  let ?Z = "mset (zip (map Var ys) (map Var zs)) :: ('f, 'v) problem"
  let ?\<Gamma>1 = "add_mset (Var x, Fun f (map Var ys)) (?Z + \<Gamma>0)"
  have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(?\<Gamma>1, \<Delta>, \<sigma>)}"
    using step.Dec[of f "map Var ys" "map Var zs" x \<Gamma>0 \<Delta> \<sigma>] f len \<Gamma> by simp
  have Z_vv: "\<forall>e \<in># ?Z. vv_eq e"
    by (auto simp: vv_eq_def set_zip)
  have nfree_Z: "nfree ?Z = 0"
    using Z_vv kinds_vv(3) unfolding nfree_def by simp
  have vars_Z: "vars_problem ?Z \<subseteq> set ys \<union> set zs"
    by (auto simp: vars_problem_def set_zip in_set_conv_nth)
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
    using N by simp
  have flat1: "flat_problem ?\<Gamma>1"
    using pn Z_vv kinds_vv(4) \<Gamma> by auto
  have vars1: "vars_problem ?\<Gamma>1 \<subseteq> dom \<Delta>"
    using pn vars_Z \<Gamma> by auto
  have nfree1: "nfree ?\<Gamma>1 < nfree \<Gamma>"
    using fr nfree_Z \<Gamma> by simp
  show ?thesis
  proof (rule reach_single[OF step], rule reach_mono[OF close_merge[OF flat1 _ _ vars1]])
    show "finite (dom \<Delta>)" "finite \<sigma>"
      using pn by simp_all
  next
    fix S'
    assume A: "normal S' \<and> nfree (fst S') = nfree ?\<Gamma>1"
    obtain \<Gamma>' \<Delta>' \<sigma>' where S'_eq: "S' = (\<Gamma>', \<Delta>', \<sigma>')"
      by (cases S')
    have "nfree \<Gamma>' < nfree \<Gamma>"
      using A nfree1 unfolding S'_eq by simp
    then show "normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
      using A term_rel_free unfolding S'_eq by blast
  qed
qed

text \<open>The equations \<open>X\<^sub>i =\<^sup>? h(V\<^sub>i)\<close> introduced by (Split).\<close>

abbreviation hlist :: "'v list \<Rightarrow> 'v list \<Rightarrow> ('f, 'v) problem" where
  "hlist xs vs \<equiv> mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs)"

lemma edge_empty [simp]: "\<not> edge {#} a b i"
  by (simp add: edge_def)

lemma lhs_vars_simps [simp]:
  "lhs_vars {#} = {}"
  "lhs_vars (add_mset (Var x, t) \<Gamma>) = insert x (lhs_vars \<Gamma>)"
  "lhs_vars (\<Gamma> + \<Gamma>') = lhs_vars \<Gamma> \<union> lhs_vars \<Gamma>'"
  by (auto simp: lhs_vars_def)

lemma hlist_props:
  assumes "length xs = length vs"
  shows "edge (hlist xs vs) a b i \<longleftrightarrow> (a, b) \<in> set (zip xs vs) \<and> i = 1"
    and "SUMS (hlist xs vs) = {#}" "HS (hlist xs vs) = mset xs"
    and "nvv (hlist xs vs) = 0" "nfree (hlist xs vs) = 0" "flat_problem (hlist xs vs)"
    and "vars_problem (hlist xs vs) = set xs \<union> set vs" "lhs_vars (hlist xs vs) = set xs"
proof -
  show "edge (hlist xs vs) a b i \<longleftrightarrow> (a, b) \<in> set (zip xs vs) \<and> i = 1"
    using assms
  proof (induction xs vs rule: list_induct2)
    case (Cons x xs v vs)
    then show ?case
      using edge_add[of "(Var x, H (Var v))" "hlist xs vs" a b i] edge_single_h[of x v a b i]
      by auto
  qed simp
  show "SUMS (hlist xs vs) = {#}" "HS (hlist xs vs) = mset xs"
    "nvv (hlist xs vs) = 0" "nfree (hlist xs vs) = 0" "flat_problem (hlist xs vs)"
    "vars_problem (hlist xs vs) = set xs \<union> set vs" "lhs_vars (hlist xs vs) = set xs"
    using assms by (induction xs vs rule: list_induct2) (auto simp: flat_eq_def)
qed

lemma lhs_vars_sub: "lhs_vars \<Gamma> \<subseteq> vars_problem \<Gamma>"
  by (force simp: lhs_vars_def vars_problem_def)

lemma at_level_above: "\<forall>z \<in># M. l < dep \<Delta> z \<Longrightarrow> at_level \<Delta> l M = {#}"
  by (auto simp: at_level_def)

text \<open>
  (Split) on \<open>X =\<^sup>? h(Y)\<close> and \<open>X =\<^sup>? X\<^sub>1 + \<cdots> + X\<^sub>n\<close>, then closing \<open>\<Delta>\<close>. At the level \<open>\<Delta>(X)\<close>,
  the \<open>+\<close>-equations decrease and their excess does not grow.
\<close>

definition split_problem :: "'v \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> ('f, 'v) problem \<Rightarrow> ('f, 'v) problem" where
  "split_problem x y vs xs \<Gamma>0 = add_mset (Var x, H (Var y))
    (add_mset (Var y, sum_terms (map Var vs)) (hlist xs vs + \<Gamma>0))"

lemma split_facts:
  fixes vs :: "'v list"
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)"
    and \<Gamma>: "\<Gamma> = add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>0)"
    and len: "2 \<le> length xs" and xy: "x \<noteq> y" and x_xs: "x \<notin> set xs"
    and vs: "length vs = length xs" "distinct vs" "set vs \<inter> vars_triple (\<Gamma>, \<Delta>, \<sigma>) = {}"
  shows "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(split_problem x y vs xs \<Gamma>0, \<Delta>(vs [\<mapsto>] replicate (length vs) 1), \<sigma>)}"
    and "finite (dom (\<Delta>(vs [\<mapsto>] replicate (length vs) 1)))"
    and "vars_problem (split_problem x y vs xs \<Gamma>0) \<subseteq> dom (\<Delta>(vs [\<mapsto>] replicate (length vs) 1))"
    and "prot (dep \<Delta> x) (split_problem x y vs xs \<Gamma>0) (\<Delta>(vs [\<mapsto>] replicate (length vs) 1))"
    and "\<And>\<Delta>'. close_post (dep \<Delta> x) (split_problem x y vs xs \<Gamma>0)
        (\<Delta>(vs [\<mapsto>] replicate (length vs) 1)) \<Delta>' \<Longrightarrow>
      normal (split_problem x y vs xs \<Gamma>0, \<Delta>', \<sigma>) \<and>
      (tmeasure (split_problem x y vs xs \<Gamma>0, \<Delta>', \<sigma>), tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
proof -
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and nvv: "nvv \<Gamma> = 0"
    using N by simp_all
  let ?l = "dep \<Delta> x"
  let ?\<Gamma>1 = "add_mset (Var x, H (Var y))
    (add_mset (Var y, sum_terms (map Var vs)) (hlist xs vs + \<Gamma>0))"
  let ?\<Delta>1 = "\<Delta>(vs [\<mapsto>] replicate (length vs) 1)"
  define \<Delta>1 where "\<Delta>1 = \<Delta>(vs [\<mapsto>] replicate (length vs) 1)"
  have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(?\<Gamma>1, \<Delta>1, \<sigma>)}"
    using step.Split[of xs x y vs \<Gamma>0 \<Delta> \<sigma>] len xy x_xs vs \<Gamma> by (simp add: \<Delta>1_def)
  have lenv: "2 \<le> length vs"
    using len vs(1) by simp
  have hl: "edge (hlist xs vs) a b i \<longleftrightarrow> (a, b) \<in> set (zip xs vs) \<and> i = 1"
    "SUMS (hlist xs vs) = {#}" "HS (hlist xs vs) = mset xs"
    "nvv (hlist xs vs) = 0" "nfree (hlist xs vs) = 0" "flat_problem (hlist xs vs)"
    "vars_problem (hlist xs vs) = set xs \<union> set vs" "lhs_vars (hlist xs vs) = set xs" for a b i
    using hlist_props[OF vs(1)[symmetric]] by simp_all
  have "xs \<noteq> []"
    using len by auto
  then have vars\<Gamma>: "vars_problem \<Gamma> = {x, y} \<union> set xs \<union> vars_problem \<Gamma>0"
    using \<Gamma> vars_sum_terms[of "map Var xs"] by auto
  have fresh: "z \<in> set vs \<Longrightarrow> z \<notin> dom \<Delta> \<and> z \<notin> vars_problem \<Gamma>" for z
    using vs(3) by auto
  have \<Delta>1: "\<Delta>1 z = (if z \<in> set vs then Some 1 else \<Delta> z)" for z
    unfolding \<Delta>1_def using map_upds_replicate[of \<Delta> vs 1 z] by simp
  have dep1: "dep \<Delta>1 z = (if z \<in> set vs then 1 else dep \<Delta> z)" for z
    using \<Delta>1[of z] by (simp add: dep_def)
  have closed: "closed \<Gamma> \<Delta>"
    using pn by simp
  have dep_y: "?l + 1 \<le> dep \<Delta> y"
    using closed_edge[OF closed edge_h_mem[of x y]] \<Gamma> by simp
  have dep_xs: "z \<in> set xs \<Longrightarrow> ?l \<le> dep \<Delta> z" for z
    using closed_edge[OF closed edge_sum_mem[of x xs _ z]] \<Gamma> by simp
  have closed0: "closed \<Gamma>0 \<Delta>"
    using closed_mono[OF closed] \<Gamma> by simp
  have edge1: "edge ?\<Gamma>1 a b i \<longleftrightarrow> (a = x \<and> b = y \<and> i = 1) \<or> (a = y \<and> b \<in> set vs \<and> i = 0) \<or>
      ((a, b) \<in> set (zip xs vs) \<and> i = 1) \<or> edge \<Gamma>0 a b i" for a b i
    using edge_add[of "(Var x, H (Var y))"
        "add_mset (Var y, sum_terms (map Var vs)) (hlist xs vs + \<Gamma>0)" a b i]
      edge_single_h[of x y a b i]
      edge_add[of "(Var y, sum_terms (map Var vs))" "hlist xs vs + \<Gamma>0" a b i]
      edge_single_sum[OF lenv, of y a b i]
      edge_union[of "hlist xs vs" \<Gamma>0 a b i] hl(1)[of a b i]
    by argo
  have lhs1: "lhs_vars ?\<Gamma>1 = {x, y} \<union> set xs \<union> lhs_vars \<Gamma>0"
    using hl(8) by auto
  have lhs1_vs: "z \<in> lhs_vars ?\<Gamma>1 \<Longrightarrow> z \<notin> set vs" for z
    using lhs1 lhs_vars_sub[of \<Gamma>0] fresh vars\<Gamma> by blast
  have prot: "prot ?l ?\<Gamma>1 \<Delta>1"
    unfolding prot_def
  proof (intro allI impI)
    fix a b i
    assume e: "edge ?\<Gamma>1 a b i" and lt: "dep \<Delta>1 b < dep \<Delta>1 a + i"
    have ab: "a \<notin> set vs" "a \<in> lhs_vars ?\<Gamma>1"
      using edge_vars(3)[OF e] lhs1_vs by auto
    from e consider "a = x" "b = y" "i = 1" | "a = y" "b \<in> set vs" "i = 0"
      | "(a, b) \<in> set (zip xs vs)" "i = 1" | "edge \<Gamma>0 a b i"
      unfolding edge1 by blast
    then show "?l \<le> dep \<Delta>1 a \<and> (dep \<Delta>1 b < ?l \<longrightarrow> b \<notin> lhs_vars ?\<Gamma>1)"
    proof cases
      case 1
      have "y \<notin> set vs"
        using fresh vars\<Gamma> by blast
      then have False
        using lt dep_y ab(1) 1 by (simp add: dep1)
      then show ?thesis ..
    next
      case 2
      have "?l \<le> dep \<Delta>1 a"
        using dep_y ab(1) 2(1) by (simp add: dep1)
      moreover have "b \<notin> lhs_vars ?\<Gamma>1"
        using lhs1_vs[of b] 2(2) by blast
      ultimately show ?thesis
        by blast
    next
      case 3
      then have "a \<in> set xs" "b \<in> set vs"
        by (auto dest: set_zip_leftD set_zip_rightD)
      have "?l \<le> dep \<Delta>1 a"
        using dep_xs[of a] ab(1) \<open>a \<in> set xs\<close> by (simp add: dep1)
      moreover have "b \<notin> lhs_vars ?\<Gamma>1"
        using \<open>b \<in> set vs\<close> lhs1_vs[of b] by blast
      ultimately show ?thesis
        by blast
    next
      case 4
      have "b \<in> vars_problem \<Gamma>"
        using edge_vars(2)[OF 4] vars\<Gamma> by blast
      then have "b \<notin> set vs"
        using fresh by blast
      then have False
        using lt closed_edge[OF closed0 4] ab(1) by (simp add: dep1)
      then show ?thesis ..
    qed
  qed
  have pn0: "flat_problem \<Gamma>0" "nvv \<Gamma>0 = 0" "nfree \<Gamma>0 = nfree \<Gamma>"
    using pn nvv \<Gamma> sum_kinds[OF len] by auto
  have fin1: "finite (dom \<Delta>1)"
    using pn by (simp add: \<Delta>1_def)
  have dom1: "dom \<Delta>1 = dom \<Delta> \<union> set vs"
    using \<Delta>1 by auto
  have vsv: "vars_term (sum_terms (map Var vs)) = set vs"
    using lenv vars_sum_terms[of "map Var vs"] by (cases vs) auto
  have vars1: "vars_problem ?\<Gamma>1 \<subseteq> dom \<Delta>1"
    using pn vars\<Gamma> dom1 hl(7) vsv by auto
  have S1: "SUMS ?\<Gamma>1 = add_mset y (SUMS \<Gamma>0)" "HS ?\<Gamma>1 = add_mset x (mset xs + HS \<Gamma>0)"
    "nfree ?\<Gamma>1 = nfree \<Gamma>0" "nvv ?\<Gamma>1 = 0" "flat_problem ?\<Gamma>1"
    using hl(2-6) sum_kinds[OF lenv] pn0 by (auto simp: flat_eq_def)
  have S0: "SUMS \<Gamma> = add_mset x (SUMS \<Gamma>0)" "HS \<Gamma> = add_mset x (HS \<Gamma>0)"
    using \<Gamma> sum_kinds[OF len] by simp_all
  have l_kappa: "?l \<le> \<kappa>"
    using pn dep_le_kappa by simp
  show "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(split_problem x y vs xs \<Gamma>0, ?\<Delta>1, \<sigma>)}"
    using step unfolding \<Delta>1_def split_problem_def .
  show "finite (dom ?\<Delta>1)"
    using fin1 unfolding \<Delta>1_def .
  show "vars_problem (split_problem x y vs xs \<Gamma>0) \<subseteq> dom ?\<Delta>1"
    using vars1 unfolding \<Delta>1_def split_problem_def .
  show "prot (dep \<Delta> x) (split_problem x y vs xs \<Gamma>0) ?\<Delta>1"
    using prot unfolding \<Delta>1_def split_problem_def .
  fix \<Delta>'
  assume "close_post (dep \<Delta> x) (split_problem x y vs xs \<Gamma>0) ?\<Delta>1 \<Delta>'"
  then have cl: "closed ?\<Gamma>1 \<Delta>'" and bd: "bounded_depths \<Delta>'"
    and dom': "dom \<Delta>' = dom \<Delta>1" and mono: "\<forall>z. dep \<Delta>1 z \<le> dep \<Delta>' z"
    and keep: "\<forall>z \<in> lhs_vars ?\<Gamma>1. dep \<Delta>1 z < ?l \<longrightarrow> \<Delta>' z = \<Delta>1 z"
    unfolding close_post_def \<Delta>1_def[symmetric] split_problem_def by blast+
  define S' where "S' = (?\<Gamma>1, \<Delta>', \<sigma>)"
  have S': "S' = (?\<Gamma>1, \<Delta>', \<sigma>)"
    unfolding S'_def ..
  show "normal (split_problem x y vs xs \<Gamma>0, \<Delta>', \<sigma>) \<and>
      (tmeasure (split_problem x y vs xs \<Gamma>0, \<Delta>', \<sigma>), tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
    unfolding split_problem_def S'[symmetric]
  proof -
    have norm: "normal S'"
      using S' S1(4,5) cl bd dom' fin1 vars1 pn by simp
    have mono0: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
    proof
      fix z
      show "dep \<Delta> z \<le> dep \<Delta>' z"
      proof (cases "z \<in> set vs")
        case True
        then have "dep \<Delta> z = 0"
          using fresh by (simp add: dep_def domIff)
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using mono[rule_format, of z] by (simp add: dep1)
      qed
    qed
    have keep0: "\<forall>z \<in># M. dep \<Delta> z < ?l \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
      if "\<forall>z \<in># M. z \<in> lhs_vars ?\<Gamma>1" for M
    proof (intro ballI impI)
      fix z
      assume "z \<in># M" "dep \<Delta> z < ?l"
      have zl: "z \<in> lhs_vars ?\<Gamma>1"
        using that \<open>z \<in># M\<close> by blast
      then have zv: "z \<notin> set vs"
        using lhs1_vs by blast
      then have "dep \<Delta>1 z < ?l"
        using \<open>dep \<Delta> z < ?l\<close> by (simp add: dep1)
      then have "\<Delta>' z = \<Delta>1 z"
        using keep zl by blast
      then show "dep \<Delta>' z = dep \<Delta> z"
        using zv \<Delta>1[of z] by (simp add: dep_def)
    qed
    have rS: "\<And>i. i < ?l \<Longrightarrow> at_level \<Delta>' i (SUMS ?\<Gamma>1) = at_level \<Delta> i (SUMS ?\<Gamma>1)"
      "at_level \<Delta>' ?l (SUMS ?\<Gamma>1) \<subseteq># at_level \<Delta> ?l (SUMS ?\<Gamma>1)"
      using at_level_raise[OF mono0 keep0[of "SUMS ?\<Gamma>1"]] SUMS_lhs by blast+
    have rH: "\<And>i. i < ?l \<Longrightarrow> at_level \<Delta>' i (HS ?\<Gamma>1) = at_level \<Delta> i (HS ?\<Gamma>1)"
      "at_level \<Delta>' ?l (HS ?\<Gamma>1) \<subseteq># at_level \<Delta> ?l (HS ?\<Gamma>1)"
      using at_level_raise[OF mono0 keep0[of "HS ?\<Gamma>1"]] HS_lhs by blast+
    have xs_above: "i < ?l \<Longrightarrow> at_level \<Delta> i (mset xs) = {#}" for i
      using dep_xs by (intro at_level_above) fastforce
    have below: "counts ?\<Gamma>1 \<Delta>' i = counts \<Gamma> \<Delta> i" if "i < ?l" for i
      using rS(1)[OF that] rH(1)[OF that] xs_above[OF that] that dep_y
      unfolding counts_def S1(1,2) S0 by simp
    have lvl: "(counts ?\<Gamma>1 \<Delta>' ?l, counts \<Gamma> \<Delta> ?l) \<in> R3"
    proof -
      define B where "B = at_level \<Delta> ?l (SUMS \<Gamma>0)"
      define A where "A = at_level \<Delta>' ?l (SUMS ?\<Gamma>1)"
      have AB: "A \<subseteq># B"
        using rS(2) dep_y unfolding S1(1) A_def B_def by simp
      have B: "at_level \<Delta> ?l (SUMS \<Gamma>) = add_mset x B"
        unfolding S0 B_def by simp
      have e: "excess A \<le> excess (add_mset x B)"
        using excess_mono[OF AB] excess_mono[of B "add_mset x B"] by simp
      have s: "size A < size (add_mset x B)"
        using size_mset_mono[OF AB] by simp
      have c1: "counts ?\<Gamma>1 \<Delta>' ?l = (excess A, size A, size (at_level \<Delta>' ?l (HS ?\<Gamma>1)))"
        unfolding counts_def A_def ..
      have c2: "counts \<Gamma> \<Delta> ?l =
          (excess (add_mset x B), size (add_mset x B), size (at_level \<Delta> ?l (HS \<Gamma>)))"
        unfolding counts_def B ..
      show ?thesis
        unfolding c1 c2 using e s by (simp only: in_lex_prod less_than_iff simp_thms) (metis le_neq_implies_less)
    qed
    show "normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
      using norm term_rel_level[OF _ l_kappa _ lvl] below S1(3) pn0(3) S' by simp
  qed
qed

lemma split_step:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)"
    and \<Gamma>: "\<Gamma> = add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>0)"
    and len: "2 \<le> length xs" and xy: "x \<noteq> y" and x_xs: "x \<notin> set xs"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
    using N by simp
  obtain vs :: "'v list" where vs: "length vs = length xs" "distinct vs"
    "set vs \<inter> vars_triple (\<Gamma>, \<Delta>, \<sigma>) = {}"
    using fresh_list[OF pnormal_finite_vars[OF pn]] by metis
  note F = split_facts[OF N \<Gamma> len xy x_xs vs]
  show ?thesis
    by (rule reach_single[OF F(1)], rule reach_mono[OF update_closure'[OF F(2-4)]])
      (use F(5) in blast)
qed

text \<open>The equations \<open>GetEqs(\<theta>)\<close> of a unifier \<open>\<theta>\<close> returned by the AC-unification algorithm.\<close>

lemma get_eqs_simps [simp]:
  "get_eqs [] = {#}" "get_eqs ((x, t) # \<theta>) = add_mset (Var x, t) (get_eqs \<theta>)"
  by (simp_all add: get_eqs_def)

lemma get_eqs_kinds:
  assumes "\<forall>(x, t) \<in> set \<theta>. vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)"
  shows "count (SUMS (get_eqs \<theta>)) a + count (VV (get_eqs \<theta>)) a = count (mset (map fst \<theta>)) a"
    and "HS (get_eqs \<theta>) = {#}" "nfree (get_eqs \<theta>) = 0" "flat_problem (get_eqs \<theta>)"
  using assms
  by (induction \<theta>) (auto dest: flat_kinds_disjoint simp: flat_eq_def)

lemma lhs_vars_get_eqs: "lhs_vars (get_eqs \<theta>) = fst ` set \<theta>"
  by (induction \<theta>) force+

text \<open>The shape of the unifiers (assumption \<open>ac_shape\<close>) and its consequences.\<close>

lemma ac_unifier_shape:
  assumes "\<forall>e \<in># \<Psi>. flat_sum_eq e" and "\<theta> \<in> set (ac_unify V \<Psi>)" and "(x, t) \<in> set \<theta>"
  shows "x \<in> vars_problem \<Psi>" "vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)"
    "vars_term t \<inter> vars_problem \<Psi> = {}" "\<not> h_eq (Var x, t)"
proof -
  have sh: "x \<in> vars_problem \<Psi> \<and> ((\<exists>v. t = Var v \<and> v \<notin> vars_problem \<Psi>) \<or>
      (\<exists>vs. 2 \<le> length vs \<and> t = sum_terms (map Var vs) \<and> set vs \<inter> vars_problem \<Psi> = {}))"
    using ac_shape[OF assms(1,2)] assms(3) by fast
  then show "x \<in> vars_problem \<Psi>"
    by blast
  from sh have "(\<exists>v. t = Var v \<and> v \<notin> vars_problem \<Psi>) \<or>
      (\<exists>vs. 2 \<le> length vs \<and> t = sum_terms (map Var vs) \<and> set vs \<inter> vars_problem \<Psi> = {})"
    by blast
  then have all: "(vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)) \<and>
      vars_term t \<inter> vars_problem \<Psi> = {} \<and> \<not> h_eq (Var x, t)"
  proof (elim disjE exE conjE)
    fix v
    assume "t = Var v" "v \<notin> vars_problem \<Psi>"
    then show ?thesis
      by (auto simp: vv_eq_def h_eq_def)
  next
    fix vs :: "'v list"
    assume 2: "2 \<le> length vs" "t = sum_terms (map Var vs)" "set vs \<inter> vars_problem \<Psi> = {}"
    have "map Var vs \<noteq> []"
      using 2(1) by auto
    then show ?thesis
      using 2 sum_kinds[OF 2(1), of x] vars_sum_terms[of "map Var vs"] by auto
  qed
  then show "vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)" "vars_term t \<inter> vars_problem \<Psi> = {}"
    "\<not> h_eq (Var x, t)"
    by blast+
qed

lemma get_eqs_mem: "(Var x, t) \<in># get_eqs \<theta> \<longleftrightarrow> (x, t) \<in> set \<theta>"
  by (induction \<theta>) auto

lemma get_eqs_lhs: "e \<in># get_eqs \<theta> \<Longrightarrow> \<exists>x t. e = (Var x, t) \<and> (x, t) \<in> set \<theta>"
  by (induction \<theta>) auto

lemma VV_lhs: "z \<in># VV \<Gamma> \<Longrightarrow> z \<in> lhs_vars \<Gamma>"
  by (force simp: VV_def lhs_vars_def vv_eq_def lhsv_def)

lemma SUMS_lhsv: "z \<in># SUMS \<Gamma> \<Longrightarrow> \<exists>e \<in># \<Gamma>. flat_sum_eq e \<and> z = lhsv e"
  by (auto simp: SUMS_def)

text \<open>
  One branch of (AC) applied to all \<open>+\<close>-equations \<open>\<Psi>\<close> at level \<open>l\<close>, followed by closing \<open>\<Delta>\<close> and
  merging. Afterwards no variable at level \<open>l\<close> heads two \<open>+\<close>-equations, so the excess at level \<open>l\<close>
  drops to 0.
\<close>

lemma ac_facts:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)" and l: "l \<le> \<kappa>"
    and exc: "0 < excess (at_level \<Delta> l (SUMS \<Gamma>))"
    and \<Psi>: "\<Psi> = filter_mset (\<lambda>e. flat_sum_eq e \<and> dep \<Delta> (lhsv e) = l) \<Gamma>"
    and \<theta>: "\<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>)"
  defines "N \<equiv> vars_problem (get_eqs \<theta>) - vars_problem \<Psi>"
  shows "finite (dom (add_zero_depths N \<Delta>))"
    and "vars_problem (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<subseteq> dom (add_zero_depths N \<Delta>)"
    and "prot l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) (add_zero_depths N \<Delta>)"
    and "\<And>\<Delta>'. close_post l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) (add_zero_depths N \<Delta>) \<Delta>' \<Longrightarrow>
      pnormal (get_eqs \<theta> + (\<Gamma> - \<Psi>), \<Delta>', \<sigma>) \<and> merge_inv l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' \<and>
      nfree (get_eqs \<theta> + (\<Gamma> - \<Psi>)) = nfree \<Gamma> \<and>
      (\<forall>i < l. counts (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' i = counts \<Gamma> \<Delta> i) \<and>
      (counts (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
proof -
  define G where "G = get_eqs \<theta>"
  define \<Gamma>r where "\<Gamma>r = filter_mset (\<lambda>e. \<not> (flat_sum_eq e \<and> dep \<Delta> (lhsv e) = l)) \<Gamma>"
  define \<Delta>1 where "\<Delta>1 = add_zero_depths N \<Delta>"
  have \<Gamma>_split: "\<Gamma> = \<Psi> + \<Gamma>r"
    unfolding \<Psi> \<Gamma>r_def by (rule multiset_partition)
  then have \<Gamma>r_eq: "\<Gamma> - \<Psi> = \<Gamma>r"
    by simp
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and nvv: "nvv \<Gamma> = 0"
    using N by simp_all
  have closed: "closed \<Gamma> \<Delta>"
    using pn by simp
  have \<Psi>sum: "\<forall>e \<in># \<Psi>. flat_sum_eq e" and \<Psi>lvl: "\<forall>e \<in># \<Psi>. dep \<Delta> (lhsv e) = l"
    unfolding \<Psi> by simp_all
  have \<Gamma>r_lvl: "\<forall>e \<in># \<Gamma>r. flat_sum_eq e \<longrightarrow> dep \<Delta> (lhsv e) \<noteq> l"
    unfolding \<Gamma>r_def by simp
  have finV: "finite (vars_triple (\<Gamma>, \<Delta>, \<sigma>))"
    using pnormal_finite_vars[OF pn] .
  have fresh: "N \<inter> vars_triple (\<Gamma>, \<Delta>, \<sigma>) = {}"
    using ac_fresh[OF finV \<theta>] unfolding N_def .
  have N_out: "z \<in> N \<Longrightarrow> z \<notin> dom \<Delta> \<and> z \<notin> vars_problem \<Gamma>" for z
    using fresh by auto
  have finN: "finite N"
    unfolding N_def using finite_vars_problem by blast
  have shape: "x \<in> vars_problem \<Psi>" "vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)"
    "vars_term t \<inter> vars_problem \<Psi> = {}" "\<not> h_eq (Var x, t)" if "(x, t) \<in> set \<theta>" for x t
    using ac_unifier_shape[OF \<Psi>sum \<theta> that] by simp_all
  have dist: "distinct (map fst \<theta>)"
    using ac_shape[OF \<Psi>sum \<theta>] by blast
  have kindsG: "\<forall>(x, t) \<in> set \<theta>. vv_eq (Var x, t) \<or> flat_sum_eq (Var x, t)"
    using shape(2) by blast
  have G: "\<And>a. count (SUMS G) a + count (VV G) a = count (mset (map fst \<theta>)) a"
    "HS G = {#}" "nfree G = 0" "flat_problem G" "lhs_vars G = fst ` set \<theta>"
    using get_eqs_kinds[OF kindsG] lhs_vars_get_eqs unfolding G_def by simp_all
  have cnt1: "count (mset (map fst \<theta>)) a \<le> 1" for a
    using dist by (simp add: distinct_count_atmost_1)
  have vars\<Psi>: "vars_problem \<Psi> \<subseteq> vars_problem \<Gamma>"
    using \<Gamma>_split by simp
  have vars\<Psi>_dep: "l \<le> dep \<Delta> z" if z\<Psi>: "z \<in> vars_problem \<Psi>" for z
  proof -
    obtain e where e: "e \<in># \<Psi>" "z \<in> vars_eq e"
      using z\<Psi> unfolding vars_problem_def by blast
    obtain x ys where xys: "e = (Var x, sum_terms (map Var ys))" "2 \<le> length ys"
      using \<Psi>sum e(1) by (auto simp: flat_sum_eq_def)
    have dx: "dep \<Delta> x = l"
      using \<Psi>lvl e(1) xys(1) by fastforce
    have "map Var ys \<noteq> []"
      using xys(2) by auto
    then have "z = x \<or> z \<in> set ys"
      using e(2) xys(1) vars_sum_terms[of "map Var ys"] by auto
    moreover have "z \<in> set ys \<Longrightarrow> dep \<Delta> x \<le> dep \<Delta> z"
      using closed_edge[OF closed edge_sum_mem[of x ys \<Gamma> z]] e(1) xys(1) \<Gamma>_split by simp
    ultimately show ?thesis
      using dx by auto
  qed
  have lhsG: "z \<in> lhs_vars G \<Longrightarrow> z \<in> vars_problem \<Psi>" for z
    using G(5) shape(1) by auto
  have varsG: "vars_problem G \<subseteq> vars_problem \<Psi> \<union> N"
    unfolding N_def G_def by blast
  have \<Delta>1: "\<Delta>1 z = (if z \<in> N then Some 0 else \<Delta> z)" for z
    by (simp add: \<Delta>1_def add_zero_depths_def)
  have dep1: "dep \<Delta>1 z = (if z \<in> N then 0 else dep \<Delta> z)" for z
    using \<Delta>1[of z] by (simp add: dep_def)
  have edgeG: "i = 0 \<and> a \<in> vars_problem \<Psi> \<and> b \<in> N" if e: "edge G a b i" for a b i
  proof -
    obtain t where t: "(Var a, t) \<in># G" "b \<in> vars_term t"
      using edge_eq[OF e] by blast
    have at: "(a, t) \<in> set \<theta>"
      using t(1) unfolding G_def get_eqs_mem .
    have "i = 0"
    proof (rule ccontr)
      assume "i \<noteq> 0"
      then have "(Var a, H (Var b)) \<in># G"
        using e by (auto simp: edge_def)
      then have "(a, H (Var b)) \<in> set \<theta>"
        unfolding G_def get_eqs_mem .
      from shape(4)[OF this] show False
        by simp
    qed
    moreover have "b \<in> vars_problem G"
      using t by (force simp: vars_problem_def)
    ultimately show ?thesis
      using shape(1,3)[OF at] t(2) unfolding N_def G_def by blast
  qed
  have lhs\<Gamma>r: "lhs_vars \<Gamma>r \<subseteq> vars_problem \<Gamma>"
    using lhs_vars_sub[of \<Gamma>r] \<Gamma>_split by auto
  have lhs1: "lhs_vars (G + \<Gamma>r) \<subseteq> vars_problem \<Gamma>"
    using lhsG vars\<Psi> lhs\<Gamma>r by auto
  have closedr: "closed \<Gamma>r \<Delta>"
    using closed_mono[OF closed] \<Gamma>_split by simp
  have prot: "prot l (G + \<Gamma>r) \<Delta>1"
    unfolding prot_def
  proof (intro allI impI)
    fix a b i
    assume e: "edge (G + \<Gamma>r) a b i" and lt: "dep \<Delta>1 b < dep \<Delta>1 a + i"
    show "l \<le> dep \<Delta>1 a \<and> (dep \<Delta>1 b < l \<longrightarrow> b \<notin> lhs_vars (G + \<Gamma>r))"
    proof (cases "edge G a b i")
      case True
      then have "a \<in> vars_problem \<Psi>" "b \<in> N"
        using edgeG by blast+
      moreover have "a \<notin> N"
        using \<open>a \<in> vars_problem \<Psi>\<close> vars\<Psi> N_out by blast
      moreover have "b \<notin> lhs_vars (G + \<Gamma>r)"
        using \<open>b \<in> N\<close> lhs1 N_out by blast
      ultimately show ?thesis
        using vars\<Psi>_dep[of a] by (simp add: dep1)
    next
      case False
      then have er: "edge \<Gamma>r a b i"
        using e edge_union by blast
      have "a \<in> vars_problem \<Gamma>" "b \<in> vars_problem \<Gamma>"
        using edge_vars(1,2)[OF er] \<Gamma>_split by auto
      then have "a \<notin> N" "b \<notin> N"
        using N_out by blast+
      then have False
        using lt closed_edge[OF closedr er] by (simp add: dep1)
      then show ?thesis ..
    qed
  qed
  have dom1: "dom \<Delta>1 = dom \<Delta> \<union> N"
    using \<Delta>1 by (auto simp: dom_def)
  have fin1: "finite (dom \<Delta>1)"
    using pn finN dom1 by simp
  have vars1: "vars_problem (G + \<Gamma>r) \<subseteq> dom \<Delta>1"
    using varsG vars\<Psi> pn \<Gamma>_split dom1 by auto
  have flat1: "flat_problem (G + \<Gamma>r)"
    using G(4) pn \<Gamma>_split by auto
  have VVr: "VV \<Gamma>r = {#}"
    using VV_normal[of \<Gamma>r] nvv \<Gamma>_split by simp
  have HS\<Psi>: "HS \<Psi> = {#}" and nfree\<Psi>: "nfree \<Psi> = 0"
    using \<Psi>sum flat_kinds_disjoint(1,3) by (auto simp: HS_def nfree_def)
  have K1: "SUMS (G + \<Gamma>r) = SUMS G + SUMS \<Gamma>r" "HS (G + \<Gamma>r) = HS \<Gamma>r" "VV (G + \<Gamma>r) = VV G"
    "nfree (G + \<Gamma>r) = nfree \<Gamma>r"
    using G(2,3) VVr by simp_all
  have K0: "SUMS \<Gamma> = SUMS \<Psi> + SUMS \<Gamma>r" "HS \<Gamma> = HS \<Gamma>r" "nfree \<Gamma> = nfree \<Gamma>r"
    using HS\<Psi> nfree\<Psi> by (subst \<Gamma>_split, simp)+
  have SUMS\<Psi>_lvl: "dep \<Delta> z = l" if "z \<in># SUMS \<Psi>" for z
    using SUMS_lhsv[OF that] \<Psi>lvl by auto
  have SUMSr_lvl: "dep \<Delta> z \<noteq> l" if "z \<in># SUMS \<Gamma>r" for z
    using SUMS_lhsv[OF that] \<Gamma>r_lvl by auto
  have SUMSG_dep: "l \<le> dep \<Delta> z" if "z \<in># SUMS G" for z
    using vars\<Psi>_dep lhsG SUMS_lhs[OF that] by blast
  have cntG: "count (SUMS G) a + count (VV G) a \<le> 1" for a
    using G(1)[of a] cnt1[of a] by simp
  show "finite (dom (add_zero_depths N \<Delta>))"
    using fin1 unfolding \<Delta>1_def .
  show "vars_problem (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<subseteq> dom (add_zero_depths N \<Delta>)"
    using vars1 unfolding \<Gamma>r_eq G_def \<Delta>1_def .
  show "prot l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) (add_zero_depths N \<Delta>)"
    using prot unfolding \<Gamma>r_eq G_def \<Delta>1_def .
  fix \<Delta>'
  assume "close_post l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) (add_zero_depths N \<Delta>) \<Delta>'"
  then have cl: "closed (G + \<Gamma>r) \<Delta>'" and bd: "bounded_depths \<Delta>'"
    and dom': "dom \<Delta>' = dom \<Delta>1" and mono: "\<forall>z. dep \<Delta>1 z \<le> dep \<Delta>' z"
    and keep: "\<forall>z \<in> lhs_vars (G + \<Gamma>r). dep \<Delta>1 z < l \<longrightarrow> \<Delta>' z = \<Delta>1 z"
    unfolding close_post_def \<Gamma>r_eq G_def[symmetric] \<Delta>1_def[symmetric] by blast+
  show "pnormal (get_eqs \<theta> + (\<Gamma> - \<Psi>), \<Delta>', \<sigma>) \<and> merge_inv l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' \<and>
      nfree (get_eqs \<theta> + (\<Gamma> - \<Psi>)) = nfree \<Gamma> \<and>
      (\<forall>i < l. counts (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' i = counts \<Gamma> \<Delta> i) \<and>
      (counts (get_eqs \<theta> + (\<Gamma> - \<Psi>)) \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
    unfolding \<Gamma>r_eq G_def[symmetric]
  proof -
    have pn1: "pnormal (G + \<Gamma>r, \<Delta>', \<sigma>)"
      using flat1 fin1 dom' pn vars1 cl bd by simp
    have mono0: "\<forall>z. dep \<Delta> z \<le> dep \<Delta>' z"
    proof
      fix z
      show "dep \<Delta> z \<le> dep \<Delta>' z"
      proof (cases "z \<in> N")
        case True
        then have "dep \<Delta> z = 0"
          using N_out by (simp add: dep_def domIff)
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          using mono[rule_format, of z] by (simp add: dep1)
      qed
    qed
    have keep0: "\<forall>z \<in># M. dep \<Delta> z < l \<longrightarrow> dep \<Delta>' z = dep \<Delta> z"
      if "\<forall>z \<in># M. z \<in> lhs_vars (G + \<Gamma>r)" for M
    proof (intro ballI impI)
      fix z
      assume "z \<in># M" "dep \<Delta> z < l"
      have zl: "z \<in> lhs_vars (G + \<Gamma>r)"
        using that \<open>z \<in># M\<close> by blast
      then have zN: "z \<notin> N"
        using lhs1 N_out by blast
      then have "dep \<Delta>1 z < l"
        using \<open>dep \<Delta> z < l\<close> by (simp add: dep1)
      then have "\<Delta>' z = \<Delta>1 z"
        using keep zl by blast
      then show "dep \<Delta>' z = dep \<Delta> z"
        using zN \<Delta>1[of z] by (simp add: dep_def)
    qed
    have inv: "merge_inv l (G + \<Gamma>r) \<Delta>'"
      unfolding merge_inv_def K1(3)
    proof
      fix a
      assume a: "a \<in># VV G"
      have a\<Psi>: "a \<in> vars_problem \<Psi>"
        using VV_lhs[OF a] lhsG by blast
      have la: "l \<le> dep \<Delta> a" "dep \<Delta> a \<le> dep \<Delta>' a"
        using vars\<Psi>_dep[OF a\<Psi>] mono0 by blast+
      have "0 < count (VV G) a"
        using a by simp
      then have c: "count (SUMS G) a = 0" "count (VV G) a = 1"
        using cntG[of a] by linarith+
      have "a \<notin># SUMS (G + \<Gamma>r)" if "dep \<Delta>' a = l"
      proof
        assume "a \<in># SUMS (G + \<Gamma>r)"
        moreover have "a \<notin># SUMS G"
          using c(1) by (simp add: not_in_iff)
        ultimately have "a \<in># SUMS \<Gamma>r"
          unfolding K1(1) by simp
        then show False
          using SUMSr_lvl la that by fastforce
      qed
      then show "l \<le> dep \<Delta>' a \<and> (dep \<Delta>' a = l \<longrightarrow> a \<notin># SUMS (G + \<Gamma>r) \<and> count (VV G) a = 1)"
        using la c(2) by auto
    qed
    have rS: "\<And>i. i < l \<Longrightarrow> at_level \<Delta>' i (SUMS (G + \<Gamma>r)) = at_level \<Delta> i (SUMS (G + \<Gamma>r))"
      "at_level \<Delta>' l (SUMS (G + \<Gamma>r)) \<subseteq># at_level \<Delta> l (SUMS (G + \<Gamma>r))"
      using at_level_raise[OF mono0 keep0[of "SUMS (G + \<Gamma>r)"]] SUMS_lhs by blast+
    have rH: "\<And>i. i < l \<Longrightarrow> at_level \<Delta>' i (HS (G + \<Gamma>r)) = at_level \<Delta> i (HS (G + \<Gamma>r))"
      using at_level_raise[OF mono0 keep0[of "HS (G + \<Gamma>r)"]] HS_lhs by blast+
    have below: "counts (G + \<Gamma>r) \<Delta>' i = counts \<Gamma> \<Delta> i" if "i < l" for i
    proof -
      have "at_level \<Delta> i (SUMS G) = {#}" "at_level \<Delta> i (SUMS \<Psi>) = {#}"
        using SUMSG_dep SUMS\<Psi>_lvl that by (intro at_level_above; fastforce)+
      then show ?thesis
        using rS(1)[OF that] rH[OF that] unfolding counts_def K1 K0 by simp
    qed
    have lvl: "(counts (G + \<Gamma>r) \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
    proof -
      define A where "A = at_level \<Delta>' l (SUMS (G + \<Gamma>r))"
      have "at_level \<Delta> l (SUMS \<Gamma>r) = {#}"
        using SUMSr_lvl by (auto simp: at_level_def)
      then have "A \<subseteq># SUMS G"
        using rS(2) multiset_filter_subset[of _ "SUMS G"] unfolding A_def K1(1) at_level_def
        by (metis add.right_neutral at_level_def at_level_simps(3) subset_mset.order_trans)
      then have "count A a \<le> 1" for a
        using cntG[of a] mset_subset_eq_count[of A "SUMS G" a] by linarith
      then have e0: "excess A = 0"
        by (simp add: excess_zero)
      have c1: "counts (G + \<Gamma>r) \<Delta>' l = (excess A, size A, size (at_level \<Delta>' l (HS (G + \<Gamma>r))))"
        unfolding counts_def A_def ..
      show ?thesis
        unfolding c1 using e0 exc by (simp add: counts_def)
    qed
    have nf: "nfree (G + \<Gamma>r) = nfree \<Gamma>"
      using K1(4) K0(3) by simp
    show "pnormal (G + \<Gamma>r, \<Delta>', \<sigma>) \<and> merge_inv l (G + \<Gamma>r) \<Delta>' \<and> nfree (G + \<Gamma>r) = nfree \<Gamma> \<and>
        (\<forall>i < l. counts (G + \<Gamma>r) \<Delta>' i = counts \<Gamma> \<Delta> i) \<and> (counts (G + \<Gamma>r) \<Delta>' l, counts \<Gamma> \<Delta> l) \<in> R3"
      using pn1 inv nf below lvl by blast
  qed
qed

lemma ac_branch:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)" and l: "l \<le> \<kappa>"
    and exc: "0 < excess (at_level \<Delta> l (SUMS \<Gamma>))"
    and \<Psi>: "\<Psi> = filter_mset (\<lambda>e. flat_sum_eq e \<and> dep \<Delta> (lhsv e) = l) \<Gamma>"
    and \<theta>: "\<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>)"
  defines "N \<equiv> vars_problem (get_eqs \<theta>) - vars_problem \<Psi>"
  shows "reach (get_eqs \<theta> + (\<Gamma> - \<Psi>), add_zero_depths N \<Delta>, \<sigma>)
    (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  note F = ac_facts[OF N l exc \<Psi> \<theta>, folded N_def]
  show ?thesis
  proof (rule reach_trans[OF update_closure'[OF F(1-3)]], elim exE conjE)
    fix S' \<Delta>'
    assume S': "S' = (get_eqs \<theta> + (\<Gamma> - \<Psi>), \<Delta>', \<sigma>)"
      and cp: "close_post l (get_eqs \<theta> + (\<Gamma> - \<Psi>)) (add_zero_depths N \<Delta>) \<Delta>'"
    note P = F(4)[OF cp]
    show "reach S' (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
      unfolding S' using finish_level[OF vv_closure[of _ \<Delta>' \<sigma> l]] P l by blast
  qed
qed

text \<open>(AC) on all \<open>+\<close>-equations at a level \<open>l\<close> where the excess is positive.\<close>

lemma ac_step:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)" and l: "l \<le> \<kappa>"
    and exc: "0 < excess (at_level \<Delta> l (SUMS \<Gamma>))"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  define \<Psi> where "\<Psi> = filter_mset (\<lambda>e. flat_sum_eq e \<and> dep \<Delta> (lhsv e) = l) \<Gamma>"
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
    using N by simp
  have finV: "finite (vars_triple (\<Gamma>, \<Delta>, \<sigma>))"
    using pnormal_finite_vars[OF pn] .
  have \<Psi>sum: "\<forall>e \<in># \<Psi>. flat_sum_eq e"
    unfolding \<Psi>_def by simp
  have "at_level \<Delta> l (SUMS \<Gamma>) \<noteq> {#}"
    using exc by (auto simp: excess_def)
  then obtain z where z: "z \<in># SUMS \<Gamma>" "dep \<Delta> z = l"
    by (auto simp: at_level_def)
  then obtain e where "e \<in># \<Gamma>" "flat_sum_eq e" "z = lhsv e"
    using SUMS_lhsv by blast
  then have "e \<in># \<Psi>"
    using z(2) unfolding \<Psi>_def by simp
  then have \<Psi>ne: "\<Psi> \<noteq> {#}"
    by auto
  have step: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(get_eqs \<theta> + (\<Gamma> - \<Psi>), add_zero_depths (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) \<Delta>, \<sigma>)
        | \<theta>. \<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>)}"
  proof (rule step.AC)
    show "\<Psi> \<subseteq># \<Gamma>"
      unfolding \<Psi>_def by simp
    show "\<forall>\<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>).
        fresh_for (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) (\<Gamma>, \<Delta>, \<sigma>)"
      using ac_fresh[OF finV] by blast
  qed (use \<Psi>sum \<Psi>ne in simp_all)
  show ?thesis
  proof (rule reach_step[OF step])
    fix S'
    assume "S' \<in> {(get_eqs \<theta> + (\<Gamma> - \<Psi>),
        add_zero_depths (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) \<Delta>, \<sigma>)
      | \<theta>. \<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>)}"
    then obtain \<theta> where \<theta>: "\<theta> \<in> set (ac_unify (vars_triple (\<Gamma>, \<Delta>, \<sigma>)) \<Psi>)"
      and S': "S' = (get_eqs \<theta> + (\<Gamma> - \<Psi>),
        add_zero_depths (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) \<Delta>, \<sigma>)"
      by blast
    show "reach S' (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
      unfolding S' by (rule ac_branch[OF N l exc \<Psi>_def \<theta>])
  qed
qed

subsection \<open>The main loop terminates\<close>

lemma sum_terms_Fun: "2 \<le> length ys \<Longrightarrow> \<exists>us. sum_terms (map Var ys) = Fun plus us"
  by (cases ys rule: remdups_adj.cases) auto

lemma flat_cases:
  assumes "flat_eq (Var x, t)" and "\<not> vv_eq (Var x, t)"
  obtains (h) y where "t = H (Var y)"
    | (sum) ys where "t = sum_terms (map Var ys)" "2 \<le> length ys"
    | (free) f ys where "t = Fun f (map Var ys)" "f \<noteq> plus" "f \<noteq> hom" "length ys = arity f"
  using assms by (auto simp: flat_eq_def h_eq_def flat_sum_eq_def free_eq_def)

lemma reach_OC:
  assumes "x \<in> vars_term t" and "is_Fun t"
  shows "reach (add_mset (Var x, t) \<Gamma>, \<Delta>, \<sigma>) P"
proof -
  obtain f ts where t: "t = Fun f ts"
    using assms(2) by (cases t) auto
  show ?thesis
    unfolding t by (rule reach_fail, rule step.OC) (use assms(1) t in simp)
qed

lemma reach_Clash:
  assumes "f \<noteq> g" and "f \<notin> {plus, hom} \<or> g \<notin> {plus, hom}"
  shows "reach (add_mset (Var x, Fun f ss) (add_mset (Var x, Fun g ts) \<Gamma>), \<Delta>, \<sigma>) P"
  using assms by (intro reach_fail step.Clash)

lemma obtain_two:
  assumes "2 \<le> lhs_count \<Gamma> x"
  obtains t1 t2 \<Gamma>0 where "\<Gamma> = add_mset (Var x, t1) (add_mset (Var x, t2) \<Gamma>0)"
proof -
  have ex: "\<exists>t \<Gamma>'. \<Gamma> = add_mset (Var x, t) \<Gamma>' \<and> lhs_count \<Gamma>' x = lhs_count \<Gamma> x - 1"
    if one: "1 \<le> lhs_count \<Gamma> x" for \<Gamma>
  proof -
    have "filter_mset (\<lambda>e. fst e = Var x) \<Gamma> \<noteq> {#}"
      using one unfolding lhs_count_def by (metis not_one_le_zero size_empty)
    then obtain e where e: "e \<in># \<Gamma>" "fst e = Var x"
      by auto
    then have \<Gamma>e: "\<Gamma> = add_mset (Var x, snd e) (\<Gamma> - {#e#})"
      by (metis insert_DiffM prod.collapse)
    have "lhs_count \<Gamma> x = Suc (lhs_count (\<Gamma> - {#e#}) x)"
      by (subst \<Gamma>e) simp
    then show ?thesis
      using \<Gamma>e by auto
  qed
  have "1 \<le> lhs_count \<Gamma> x"
    using assms by simp
  then obtain t1 \<Gamma>1 where 1: "\<Gamma> = add_mset (Var x, t1) \<Gamma>1" "lhs_count \<Gamma>1 x = lhs_count \<Gamma> x - 1"
    using ex[of \<Gamma>] by blast
  have "1 \<le> lhs_count \<Gamma>1 x"
    using assms 1(2) by simp
  then obtain t2 \<Gamma>0 where 2: "\<Gamma>1 = add_mset (Var x, t2) \<Gamma>0"
    using ex[of \<Gamma>1] by blast
  show ?thesis
    using that 1(1) 2 by blast
qed

text \<open>
  One macro step: if a variable heads two equations of a normal state, a measure-decreasing
  macro step (or failure by (OC) or (Clash)) applies.
\<close>

lemma pair_step:
  assumes N: "normal (\<Gamma>, \<Delta>, \<sigma>)" and \<Gamma>: "\<Gamma> = add_mset (Var x, t1) (add_mset (Var x, t2) \<Gamma>0)"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) (\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel)"
proof -
  let ?P = "\<lambda>S'. normal S' \<and> (tmeasure S', tmeasure (\<Gamma>, \<Delta>, \<sigma>)) \<in> term_rel"
  have pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)" and nvv: "nvv \<Gamma> = 0"
    using N by simp_all
  have k1: "flat_eq (Var x, t1)" "\<not> vv_eq (Var x, t1)"
    and k2: "flat_eq (Var x, t2)" "\<not> vv_eq (Var x, t2)"
    using pn nvv \<Gamma> by (auto split: if_splits)
  have \<Gamma>': "\<Gamma> = add_mset (Var x, t2) (add_mset (Var x, t1) \<Gamma>0)"
    using \<Gamma> by (simp add: add_mset_commute)
  have hs: "reach (\<Gamma>, \<Delta>, \<sigma>) ?P"
    if \<Gamma>hs: "\<Gamma> = add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>1)"
      and len: "2 \<le> length xs" for y xs \<Gamma>1
  proof (cases "x = y \<or> x \<in> set xs")
    case True
    then show ?thesis
    proof
      assume "x = y"
      then show ?thesis
        unfolding \<Gamma>hs(1) by (intro reach_OC) auto
    next
      assume x: "x \<in> set xs"
      have "\<Gamma> = add_mset (Var x, sum_terms (map Var xs)) (add_mset (Var x, H (Var y)) \<Gamma>1)"
        using \<Gamma>hs by (simp add: add_mset_commute)
      moreover have "map Var xs \<noteq> []"
        using len by auto
      ultimately show ?thesis
        using reach_OC[of x "sum_terms (map Var xs)"] x vars_sum_terms[of "map Var xs"]
          sum_terms_Fun[OF len] by auto
    qed
  next
    case False
    then show ?thesis
      using split_step[OF N \<Gamma>hs len] by blast
  qed
  have fc: "reach (\<Gamma>, \<Delta>, \<sigma>) ?P"
    if "\<Gamma> = add_mset (Var x, Fun f ss) (add_mset (Var x, Fun g ts) \<Gamma>1)"
      and "f \<noteq> plus" "f \<noteq> hom" "g = plus \<or> g = hom" for f ss g ts \<Gamma>1
    unfolding that(1) by (rule reach_Clash) (use that in auto)
  have sum_fun: "\<exists>us. sum_terms (map Var zs) = Fun plus us" if "2 \<le> length zs" for zs :: "'v list"
    using sum_terms_Fun[OF that] .
  from k1 show ?thesis
  proof (cases rule: flat_cases)
    case (h y)
    from k2 show ?thesis
    proof (cases rule: flat_cases)
      case (h z)
      show ?thesis
      proof (cases "dep \<Delta> y \<le> dep \<Delta> z")
        case True
        then show ?thesis
          using dec_h_step[OF N _ True] \<Gamma> \<open>t1 = H (Var y)\<close> \<open>t2 = H (Var z)\<close> by blast
      next
        case False
        then have "dep \<Delta> z \<le> dep \<Delta> y"
          by simp
        then show ?thesis
          using dec_h_step[OF N \<Gamma>'[unfolded \<open>t1 = H (Var y)\<close> \<open>t2 = H (Var z)\<close>]] by blast
      qed
    next
      case (sum zs)
      then show ?thesis
        using hs \<Gamma> \<open>t1 = H (Var y)\<close> by blast
    next
      case (free g zs)
      then show ?thesis
        using fc[of g "map Var zs" hom "[Var y]" \<Gamma>0] \<Gamma>' \<open>t1 = H (Var y)\<close> by blast
    qed
  next
    case (sum ys)
    from k2 show ?thesis
    proof (cases rule: flat_cases)
      case (h z)
      then show ?thesis
        using hs \<Gamma>' sum by blast
    next
      case (sum zs)
      have S\<Gamma>: "SUMS \<Gamma> = add_mset x (add_mset x (SUMS \<Gamma>0))"
        using \<Gamma> \<open>t1 = sum_terms (map Var ys)\<close> \<open>2 \<le> length ys\<close> sum
          sum_kinds[of ys x] sum_kinds[of zs x] by simp
      have "2 \<le> count (at_level \<Delta> (dep \<Delta> x) (SUMS \<Gamma>)) x"
        unfolding S\<Gamma> by simp
      then have "0 < excess (at_level \<Delta> (dep \<Delta> x) (SUMS \<Gamma>))"
        by (rule excess_pos)
      moreover have "dep \<Delta> x \<le> \<kappa>"
        using pn dep_le_kappa by simp
      ultimately show ?thesis
        using ac_step[OF N] by blast
    next
      case (free g zs)
      obtain us where "sum_terms (map Var ys) = Fun plus us"
        using sum_fun[OF \<open>2 \<le> length ys\<close>] by blast
      then show ?thesis
        using fc[of g "map Var zs" plus us \<Gamma>0] \<Gamma>' free \<open>t1 = sum_terms (map Var ys)\<close> by auto
    qed
  next
    case (free f ys)
    from k2 show ?thesis
    proof (cases rule: flat_cases)
      case (h z)
      then show ?thesis
        using fc[of f "map Var ys" hom "[Var z]" \<Gamma>0] \<Gamma> free by blast
    next
      case (sum zs)
      obtain us where "sum_terms (map Var zs) = Fun plus us"
        using sum_fun[OF \<open>2 \<le> length zs\<close>] by blast
      then show ?thesis
        using fc[of f "map Var ys" plus us \<Gamma>0] \<Gamma> free sum by auto
    next
      case (free g zs)
      show ?thesis
      proof (cases "f = g")
        case True
        have "free_eq (Var x, Fun f (map Var ys))" "free_eq (Var x, Fun f (map Var zs))"
          using \<open>f \<noteq> plus\<close> \<open>f \<noteq> hom\<close> \<open>length ys = arity f\<close> free True by (auto simp: free_eq_def)
        moreover have "length ys = length zs"
          using \<open>length ys = arity f\<close> free True by simp
        ultimately show ?thesis
          using dec_free_step[OF N _ \<open>f \<noteq> plus\<close>] \<Gamma> \<open>t1 = Fun f (map Var ys)\<close> free True by blast
      next
        case False
        then show ?thesis
          unfolding \<Gamma> \<open>t1 = Fun f (map Var ys)\<close> \<open>t2 = Fun g (map Var zs)\<close>
          by (rule reach_Clash) (use \<open>f \<noteq> plus\<close> \<open>f \<noteq> hom\<close> in auto)
      qed
    qed
  qed
qed

text \<open>
  Termination of the main loop (Theorem 3.1, with the measure \<open>tmeasure\<close> instead of the one of
  Definition 3.3): from every normal state, a finite derivation tree reaches only irreducible
  states. Failing branches contribute no leaves.
\<close>

theorem main_loop_terminates:
  assumes "normal S"
  shows "reach S irreducible"
  using assms
proof (induction S rule: wf_induct_rule[OF wf_inv_image[OF wf_term_rel, of tmeasure]])
  case (1 S)
  obtain \<Gamma> \<Delta> \<sigma> where S: "S = (\<Gamma>, \<Delta>, \<sigma>)"
    by (cases S)
  have IH: "reach S' irreducible" if "normal S' \<and> (tmeasure S', tmeasure S) \<in> term_rel" for S'
    using 1 that by simp
  have N: "normal (\<Gamma>, \<Delta>, \<sigma>)" and pn: "pnormal (\<Gamma>, \<Delta>, \<sigma>)"
    using 1 S by simp_all
  show ?case
  proof (cases "\<forall>x. lhs_count \<Gamma> x \<le> 1")
    case True
    have "\<forall>e \<in># \<Gamma>. is_Var (fst e)"
      using pn by (auto simp: flat_eq_def vv_eq_def h_eq_def flat_sum_eq_def free_eq_def)
    then show ?thesis
      using final_phase[OF _ True] pn S by simp
  next
    case False
    then obtain x where "2 \<le> lhs_count \<Gamma> x"
      by (metis not_less_eq_eq numeral_2_eq_2 One_nat_def)
    then obtain t1 t2 \<Gamma>0 where \<Gamma>: "\<Gamma> = add_mset (Var x, t1) (add_mset (Var x, t2) \<Gamma>0)"
      by (rule obtain_two)
    show ?thesis
      unfolding S by (rule reach_trans[OF pair_step[OF N \<Gamma>]]) (use IH S in simp)
  qed
qed

subsection \<open>End-to-end termination\<close>

text \<open>
  Input problems must respect the arities (Definition 1.1); otherwise an equation such as
  \<open>X =\<^sup>? f(a, b)\<close> with \<open>arity f = 1\<close> is neither flat nor flattenable.
\<close>

fun arity_ok :: "('f, 'v) term \<Rightarrow> bool" where
  "arity_ok (Var x) = True"
| "arity_ok (Fun f ts) \<longleftrightarrow> length ts = arity f \<and> (\<forall>t \<in> set ts. arity_ok t)"

definition arity_ok_problem :: "('f, 'v) problem \<Rightarrow> bool" where
  "arity_ok_problem \<Gamma> \<longleftrightarrow> (\<forall>(s, t) \<in># \<Gamma>. arity_ok s \<and> arity_ok t)"

lemma arity_ok_problem_simps [simp]:
  "arity_ok_problem {#}"
  "arity_ok_problem (add_mset (s, t) \<Gamma>) \<longleftrightarrow> arity_ok s \<and> arity_ok t \<and> arity_ok_problem \<Gamma>"
  "arity_ok_problem (\<Gamma> + \<Gamma>') \<longleftrightarrow> arity_ok_problem \<Gamma> \<and> arity_ok_problem \<Gamma>'"
  by (auto simp: arity_ok_problem_def)

text \<open>The invariant of the flattening phase.\<close>

fun ready :: "('f, 'v) triple \<Rightarrow> bool" where
  "ready (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> arity_ok_problem \<Gamma> \<and> finite (dom \<Delta>) \<and> finite \<sigma> \<and> vars_problem \<Gamma> \<subseteq> dom \<Delta>"

lemma arity_ok_problem_zip:
  "length vs = length ts \<Longrightarrow> (\<forall>t \<in> set ts. arity_ok t) \<Longrightarrow>
    arity_ok_problem (mset (zip (map Var vs) ts))"
  by (induction vs ts rule: list_induct2) auto

lemma vars_problem_zip:
  "length vs = length ts \<Longrightarrow>
    vars_problem (mset (zip (map Var vs) ts)) = set vs \<union> (\<Union>t \<in> set ts. vars_term t)"
  by (induction vs ts rule: list_induct2) auto

lemma flat_step_ready: "S \<leadsto>\<^sub>F S' \<Longrightarrow> ready S \<Longrightarrow> ready S'"
proof (induction rule: flat_step.induct)
  case (FlFun f ts vs t \<Gamma> \<Delta> \<sigma>)
  then show ?case
    using arity_ok_problem_zip[of vs ts] vars_problem_zip[of vs ts]
    by auto
qed (auto simp: arity_plus arity_hom)

text \<open>An equation respecting the arities is flat or some flattening rule or (Orient) applies.\<close>

lemma nonflat_cases:
  assumes "arity_ok s" and "arity_ok t" and "\<not> flat_eq (s, t)"
  obtains (FBS) "is_Fun s" "is_Fun t"
    | (Orient) x where "is_Fun s" "t = Var x"
    | (FL) x t1 t2 where "s = Var x" "t = t1 \<oplus> t2" "is_Fun t1"
    | (FR) x t1 t2 where "s = Var x" "t = t1 \<oplus> t2" "is_Fun t2"
    | (FU) x t1 where "s = Var x" "t = H t1" "is_Fun t1"
    | (FlFun) x f ts where "s = Var x" "t = Fun f ts" "f \<noteq> plus" "f \<noteq> hom" "\<exists>u \<in> set ts. is_Fun u"
proof (cases s)
  case (Fun g ss)
  then show ?thesis
    using that(1,2) by (cases t) auto
next
  case (Var x)
  show ?thesis
  proof (cases t)
    case (Var y)
    then have "flat_eq (s, t)"
      using \<open>s = Var x\<close> by (simp add: flat_eq_def vv_eq_def)
    then show ?thesis
      using assms(3) by blast
  next
    case (Fun f ts)
    consider "f = plus" | "f = hom" | "f \<noteq> plus" "f \<noteq> hom"
      by blast
    then show ?thesis
    proof cases
      case 1
      then have "length ts = 2"
        using assms(2) Fun arity_plus by simp
      then obtain t1 t2 where ts: "ts = [t1, t2]"
        by (auto simp: length_Suc_conv numeral_2_eq_2)
      show ?thesis
      proof (cases "is_Fun t1 \<or> is_Fun t2")
        case True
        then show ?thesis
          using that(3,4) \<open>s = Var x\<close> Fun 1 ts by blast
      next
        case False
        then obtain a b where "t1 = Var a" "t2 = Var b"
          by (meson is_FunE is_Var_def term.disc(1) term.collapse(1))
        then have "flat_sum_eq (s, t)"
          unfolding flat_sum_eq_def using \<open>s = Var x\<close> Fun 1 ts
          by (intro exI[of _ x] exI[of _ "[a, b]"]) simp
        then show ?thesis
          using assms(3) by (simp add: flat_eq_def)
      qed
    next
      case 2
      then have "length ts = 1"
        using assms(2) Fun arity_hom by simp
      then obtain t1 where ts: "ts = [t1]"
        by (metis One_nat_def length_0_conv length_Suc_conv)
      show ?thesis
      proof (cases "is_Fun t1")
        case True
        then show ?thesis
          using that(5) \<open>s = Var x\<close> Fun 2 ts by blast
      next
        case False
        then obtain y where "t1 = Var y"
          by (cases t1) auto
        then have "h_eq (s, t)"
          using \<open>s = Var x\<close> Fun 2 ts by (simp add: h_eq_def)
        then show ?thesis
          using assms(3) by (simp add: flat_eq_def)
      qed
    next
      case 3
      show ?thesis
      proof (cases "\<exists>u \<in> set ts. is_Fun u")
        case True
        then show ?thesis
          using that(6) \<open>s = Var x\<close> Fun 3 by blast
      next
        case False
        then have "ts = map Var (map the_Var ts)"
          by (induction ts) auto
        moreover have "length (map the_Var ts) = arity f"
          using assms(2) Fun by simp
        ultimately have "free_eq (s, t)"
          unfolding free_eq_def using \<open>s = Var x\<close> Fun 3 by metis
        then show ?thesis
          using assms(3) by (simp add: flat_eq_def)
      qed
    qed
  qed
qed

definition fun_lhs :: "('f, 'v) problem \<Rightarrow> nat" where
  "fun_lhs \<Gamma> = size (filter_mset (\<lambda>e. is_Fun (fst e)) \<Gamma>)"

lemma fun_lhs_add [simp]:
  "fun_lhs (add_mset (s, t) \<Gamma>) = (if is_Fun s then Suc (fun_lhs \<Gamma>) else fun_lhs \<Gamma>)"
  by (simp add: fun_lhs_def)

fun flat_ready :: "('f, 'v) triple \<Rightarrow> bool" where
  "flat_ready (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> flat_problem \<Gamma> \<and> finite (dom \<Delta>) \<and> finite \<sigma> \<and> vars_problem \<Gamma> \<subseteq> dom \<Delta>"

lemma ready_finite_vars: "ready S \<Longrightarrow> finite (vars_triple S)"
  by (cases S) (auto simp: finite_vars_problem vars_bindings_def)

text \<open>
  The flattening phase (Algorithm 2), with (Orient) for equations \<open>t =\<^sup>? X\<close>: it reaches flat
  problems. (Orient) does not change the measure of Lemma 3.1 but decreases the number of
  equations with a non-variable left-hand side, which the flattening rules do not increase.
\<close>

lemma flatten_phase:
  assumes "ready S"
  shows "reach S flat_ready"
  using assms
proof (induction S rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_mult[OF wf_less_than]
        wf_less_than], of "\<lambda>S. (flat_measure (fst S), fun_lhs (fst S))"]])
  case (1 S)
  obtain \<Gamma> \<Delta> \<sigma> where S: "S = (\<Gamma>, \<Delta>, \<sigma>)"
    by (cases S)
  have R: "ready (\<Gamma>, \<Delta>, \<sigma>)"
    using 1 S by simp
  have IH: "reach S' flat_ready" if "ready S'"
    "(flat_measure (fst S'), flat_measure \<Gamma>) \<in> mult less_than \<or>
      flat_measure (fst S') = flat_measure \<Gamma> \<and> fun_lhs (fst S') < fun_lhs \<Gamma>" for S'
    using 1 that S by auto
  have flatstep: "reach (\<Gamma>, \<Delta>, \<sigma>) flat_ready" if st: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F S'" for S'
  proof -
    obtain \<Gamma>' \<Delta>' \<sigma>' where S': "S' = (\<Gamma>', \<Delta>', \<sigma>')"
      by (cases S')
    show ?thesis
      using reach_single[OF flat_step_step[OF st] IH] flat_step_ready[OF st R]
        flat_step_decreases[OF st[unfolded S']] S' by simp
  qed
  show ?case
    unfolding S
  proof (cases "flat_problem \<Gamma>")
    case True
    then show "reach (\<Gamma>, \<Delta>, \<sigma>) flat_ready"
      using R by (intro reach_refl) simp
  next
    case False
    then obtain s t \<Gamma>0 where \<Gamma>: "\<Gamma> = add_mset (s, t) \<Gamma>0" and nf: "\<not> flat_eq (s, t)"
      by (metis multi_member_split prod.collapse)
    have ok: "arity_ok s" "arity_ok t"
      using R \<Gamma> by simp_all
    have finV: "finite (vars_triple (\<Gamma>, \<Delta>, \<sigma>))"
      using ready_finite_vars[OF R] .
    obtain v where v: "v \<notin> vars_triple (\<Gamma>, \<Delta>, \<sigma>)"
      using ex_new_if_finite[OF infinite_vars finV] by blast
    from ok(1,2) nf show "reach (\<Gamma>, \<Delta>, \<sigma>) flat_ready"
    proof (cases rule: nonflat_cases)
      case FBS
      have "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (add_mset (Var v, s) (add_mset (Var v, t) \<Gamma>0), \<Delta>(v \<mapsto> 0), \<sigma>)"
        unfolding \<Gamma> by (rule flat_step.FBS) (use FBS v \<Gamma> in auto)
      then show ?thesis
        by (rule flatstep)
    next
      case (Orient x)
      have st: "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(add_mset (Var x, s) \<Gamma>0, \<Delta>, \<sigma>)}"
        unfolding \<Gamma> Orient(2) by (rule step.Orient) (use Orient in simp)
      show ?thesis
      proof (rule reach_single[OF st], rule IH)
        show "ready (add_mset (Var x, s) \<Gamma>0, \<Delta>, \<sigma>)"
          using R \<Gamma> Orient(2) by auto
        show "(flat_measure (fst (add_mset (Var x, s) \<Gamma>0, \<Delta>, \<sigma>)), flat_measure \<Gamma>) \<in> mult less_than \<or>
          flat_measure (fst (add_mset (Var x, s) \<Gamma>0, \<Delta>, \<sigma>)) = flat_measure \<Gamma> \<and>
          fun_lhs (fst (add_mset (Var x, s) \<Gamma>0, \<Delta>, \<sigma>)) < fun_lhs \<Gamma>"
          using \<Gamma> Orient by (simp add: add.commute)
      qed
    next
      case (FL x t1 t2)
      have "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (add_mset (s, Var v \<oplus> t2) (add_mset (Var v, t1) \<Gamma>0), \<Delta>(v \<mapsto> 0), \<sigma>)"
        unfolding \<Gamma> FL(2) by (rule flat_step.FL) (use FL v \<Gamma> in auto)
      then show ?thesis
        by (rule flatstep)
    next
      case (FR x t1 t2)
      have "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (add_mset (s, t1 \<oplus> Var v) (add_mset (Var v, t2) \<Gamma>0), \<Delta>(v \<mapsto> 0), \<sigma>)"
        unfolding \<Gamma> FR(2) by (rule flat_step.FR) (use FR v \<Gamma> in auto)
      then show ?thesis
        by (rule flatstep)
    next
      case (FU x t1)
      have "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (add_mset (s, H (Var v)) (add_mset (Var v, t1) \<Gamma>0), \<Delta>(v \<mapsto> 1), \<sigma>)"
        unfolding \<Gamma> FU(2) by (rule flat_step.FU) (use FU v \<Gamma> in auto)
      then show ?thesis
        by (rule flatstep)
    next
      case (FlFun x f ts)
      obtain vs :: "'v list" where vs: "length vs = length ts" "distinct vs"
        "set vs \<inter> vars_triple (\<Gamma>, \<Delta>, \<sigma>) = {}"
        using fresh_list[OF finV] by metis
      have "(\<Gamma>, \<Delta>, \<sigma>) \<leadsto>\<^sub>F (add_mset (s, Fun f (map Var vs)) (mset (zip (map Var vs) ts) + \<Gamma>0),
          \<Delta>(vs [\<mapsto>] replicate (length vs) 0), \<sigma>)"
        unfolding \<Gamma> FlFun(2) by (rule flat_step.FlFun) (use FlFun vs \<Gamma> in auto)
      then show ?thesis
        by (rule flatstep)
    qed
  qed
qed

text \<open>
  Termination of bounded ACh-unification (Theorem 3.1): from every problem respecting the
  arities, with \<open>\<Delta>\<close> covering its variables, the strategy (flattening, closing \<open>\<Delta>\<close> and merging,
  then the macro steps) builds a finite derivation tree all of whose leaves are irreducible.
\<close>

theorem ach_unification_terminates:
  assumes "arity_ok_problem \<Gamma>" and "finite (dom \<Delta>)" and "finite \<sigma>" and "vars_problem \<Gamma> \<subseteq> dom \<Delta>"
  shows "reach (\<Gamma>, \<Delta>, \<sigma>) irreducible"
proof (rule reach_trans[OF flatten_phase])
  show "ready (\<Gamma>, \<Delta>, \<sigma>)"
    using assms by simp
next
  fix S'
  assume F: "flat_ready S'"
  obtain \<Gamma>' \<Delta>' \<sigma>' where S': "S' = (\<Gamma>', \<Delta>', \<sigma>')"
    by (cases S')
  have "reach S' (\<lambda>S''. normal S'' \<and> nfree (fst S'') = nfree \<Gamma>')"
    using F close_merge[of \<Gamma>' \<Delta>' \<sigma>'] S' by simp
  then show "reach S' irreducible"
    by (rule reach_trans) (use main_loop_terminates in blast)
qed

text \<open>The initial triple \<open>\<Gamma> \<parallel> \<Delta>\<^sub>0 \<parallel> \<emptyset>\<close>, where every variable of \<open>\<Gamma>\<close> has h-depth 0.\<close>

corollary ach_unification_terminates_initial:
  assumes "arity_ok_problem \<Gamma>"
  shows "reach (\<Gamma>, \<lambda>x. if x \<in> vars_problem \<Gamma> then Some 0 else None, {}) irreducible"
proof (rule ach_unification_terminates[OF assms])
  have "dom (\<lambda>x. if x \<in> vars_problem \<Gamma> then Some (0::nat) else None) = vars_problem \<Gamma>"
    by (auto simp: dom_def)
  then show "finite (dom (\<lambda>x. if x \<in> vars_problem \<Gamma> then Some (0::nat) else None))"
    "vars_problem \<Gamma> \<subseteq> dom (\<lambda>x. if x \<in> vars_problem \<Gamma> then Some (0::nat) else None)"
    using finite_vars_problem by simp_all
qed simp

end

end
