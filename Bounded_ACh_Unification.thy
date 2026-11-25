(*
Author: Guilherme Borges Brandão
*)

theory Bounded_ACh_Unification
  imports ACh_Theory
begin

section \<open>Bounded ACh-unification: the inference system \<open>\<I>\<^sub>A\<^sub>C\<^sub>h\<close>\<close>

subsection \<open>Set triples\<close>

text \<open>
  Section 2.1 of the dissertation: the inference system works on triples \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<sigma>\<close>, where
  \<^item> \<open>\<Gamma>\<close> is the unification problem, a (multi)set of equations \<open>s =\<^sup>? t\<close>;
  \<^item> \<open>\<Delta>\<close> is the h-depth set, a set of pairs \<open>(X, d)\<close>, which we represent as a partial map from
    variables to natural numbers;
  \<^item> \<open>\<sigma>\<close> is the substitution computed so far, a set of bindings \<open>X \<mapsto> t\<close>.

  We use multisets of equations instead of sets so that the rules have the intended
  effect on the number of equations, which matters for the termination measure.
\<close>

type_synonym ('f, 'v) problem = "('f, 'v) equation multiset"
type_synonym 'v depth_set = "'v \<rightharpoonup> nat"
type_synonym ('f, 'v) bindings = "('v \<times> ('f, 'v) term) set"
type_synonym ('f, 'v) triple = "('f, 'v) problem \<times> 'v depth_set \<times> ('f, 'v) bindings"

definition vars_eq :: "('f, 'v) equation \<Rightarrow> 'v set" where
  "vars_eq e = vars_term (fst e) \<union> vars_term (snd e)"

definition vars_problem :: "('f, 'v) problem \<Rightarrow> 'v set" where
  "vars_problem \<Gamma> = (\<Union>e \<in> set_mset \<Gamma>. vars_eq e)"

definition vars_bindings :: "('f, 'v) bindings \<Rightarrow> 'v set" where
  "vars_bindings \<sigma> = fst ` \<sigma> \<union> (\<Union>b \<in> \<sigma>. vars_term (snd b))"

fun vars_triple :: "('f, 'v) triple \<Rightarrow> 'v set" where
  "vars_triple (\<Gamma>, \<Delta>, \<sigma>) = vars_problem \<Gamma> \<union> dom \<Delta> \<union> vars_bindings \<sigma>"

text \<open>A variable is fresh for a triple if it occurs nowhere in it.\<close>

abbreviation fresh_for :: "'v set \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" where
  "fresh_for Vs S \<equiv> Vs \<inter> vars_triple S = {}"

lemma vars_problem_simps [simp]:
  "vars_problem {#} = {}"
  "vars_problem (add_mset e \<Gamma>) = vars_eq e \<union> vars_problem \<Gamma>"
  "vars_problem (\<Gamma> + \<Gamma>') = vars_problem \<Gamma> \<union> vars_problem \<Gamma>'"
  by (auto simp: vars_problem_def)

lemma vars_eq_simp [simp]: "vars_eq (s, t) = vars_term s \<union> vars_term t"
  by (simp add: vars_eq_def)

text \<open>Applying the binding \<open>X \<mapsto> t\<close> to a problem and to a set of bindings.\<close>

definition subst_problem :: "('f, 'v) subst \<Rightarrow> ('f, 'v) problem \<Rightarrow> ('f, 'v) problem" where
  "subst_problem \<tau> \<Gamma> = image_mset (\<lambda>(s, t). (s \<cdot> \<tau>, t \<cdot> \<tau>)) \<Gamma>"

definition subst_bindings :: "('f, 'v) subst \<Rightarrow> ('f, 'v) bindings \<Rightarrow> ('f, 'v) bindings" where
  "subst_bindings \<tau> \<sigma> = (\<lambda>(x, s). (x, s \<cdot> \<tau>)) ` \<sigma>"

text \<open>
  Unifiers returned by the AC-unification algorithm are finite lists of bindings.
  \<open>get_eqs\<close> turns such a unifier into equations (\<open>GetEqs\<close> in the dissertation).
\<close>

definition subst_of_list :: "('v \<times> ('f, 'v) term) list \<Rightarrow> ('f, 'v) subst" where
  "subst_of_list \<theta> x = (case map_of \<theta> x of Some t \<Rightarrow> t | None \<Rightarrow> Var x)"

definition get_eqs :: "('v \<times> ('f, 'v) term) list \<Rightarrow> ('f, 'v) problem" where
  "get_eqs \<theta> = mset (map (\<lambda>(x, t). (Var x, t)) \<theta>)"

subsection \<open>Satisfiability of triples\<close>

text \<open>
  The AC-unification algorithm (Stickel's algorithm, formalised in [AFSS22]) is a parameter.
  For soundness we only need that it returns AC-unifiers of its input. Its first argument is a
  set of variables that the new variables of the unifiers should avoid; this is only used
  in the termination proof. We also fix the bound \<open>\<kappa>\<close> on h-depths.
\<close>

locale bounded_ach = ach_signature plus hom
  for plus :: 'f and hom :: 'f +
  fixes \<kappa> :: nat
    and ac_unify :: "'v set \<Rightarrow> ('f, 'v) problem \<Rightarrow> ('v \<times> ('f, 'v) term) list list"
  assumes ac_unify_sound:
    "\<theta> \<in> set (ac_unify V \<Psi>) \<Longrightarrow> (s, t) \<in># \<Psi> \<Longrightarrow> s \<cdot> subst_of_list \<theta> \<approx>\<^sub>A\<^sub>C t \<cdot> subst_of_list \<theta>"
begin

text \<open>Definition 1.15 and the satisfiability of triples from Section 2.1.\<close>

definition sat_problem :: "('f, 'v) subst \<Rightarrow> ('f, 'v) problem \<Rightarrow> bool" where
  "sat_problem \<theta> \<Gamma> \<longleftrightarrow> (\<forall>(s, t) \<in># \<Gamma>. s \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>)"

definition sat_bindings :: "('f, 'v) subst \<Rightarrow> ('f, 'v) bindings \<Rightarrow> bool" where
  "sat_bindings \<theta> \<sigma> \<longleftrightarrow> (\<forall>(x, t) \<in> \<sigma>. \<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>)"

text \<open>\<open>MaxVal(\<Delta>) \<le> \<kappa>\<close>.\<close>

definition bounded_depths :: "'v depth_set \<Rightarrow> bool" where
  "bounded_depths \<Delta> \<longleftrightarrow> (\<forall>x d. \<Delta> x = Some d \<longrightarrow> d \<le> \<kappa>)"

fun sat_triple :: "('f, 'v) subst \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" (infix \<open>\<Turnstile>\<close> 50) where
  "\<theta> \<Turnstile> (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow> sat_problem \<theta> \<Gamma> \<and> sat_bindings \<theta> \<sigma> \<and> bounded_depths \<Delta>"

lemma sat_problem_simps [simp]:
  "sat_problem \<theta> {#}"
  "sat_problem \<theta> (add_mset (s, t) \<Gamma>) \<longleftrightarrow> s \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta> \<and> sat_problem \<theta> \<Gamma>"
  "sat_problem \<theta> (\<Gamma> + \<Gamma>') \<longleftrightarrow> sat_problem \<theta> \<Gamma> \<and> sat_problem \<theta> \<Gamma>'"
  by (auto simp: sat_problem_def)

lemma sat_bindings_simps [simp]:
  "sat_bindings \<theta> {}"
  "sat_bindings \<theta> (insert (x, t) \<sigma>) \<longleftrightarrow> \<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta> \<and> sat_bindings \<theta> \<sigma>"
  "sat_bindings \<theta> (\<sigma> \<union> \<sigma>') \<longleftrightarrow> sat_bindings \<theta> \<sigma> \<and> sat_bindings \<theta> \<sigma>'"
  by (auto simp: sat_bindings_def)

text \<open>Equations whose right-hand side has \<open>+\<close> on top (the set \<open>\<Psi>\<close> of the (AC) rule).\<close>

definition is_sum_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "is_sum_eq e \<longleftrightarrow> (\<exists>ts. snd e = Fun plus ts)"

text \<open>Flat sum equations \<open>X =\<^sup>? X\<^sub>1 + \<dots> + X\<^sub>n\<close>, the only input given to the AC-unification algorithm.\<close>

definition flat_sum_eq :: "('f, 'v) equation \<Rightarrow> bool" where
  "flat_sum_eq e \<longleftrightarrow> (\<exists>x ys. e = (Var x, sum_terms (map Var ys)) \<and> length ys \<ge> 2)"

text \<open>The (AC) rule adds the variables introduced by the AC-unifier to \<open>\<Delta>\<close> with depth 0.\<close>

definition add_zero_depths :: "'v set \<Rightarrow> 'v depth_set \<Rightarrow> 'v depth_set" where
  "add_zero_depths N \<Delta> = (\<lambda>z. if z \<in> N then Some 0 else \<Delta> z)"

subsection \<open>The rules\<close>

text \<open>
  Figure 2.2 of the dissertation. One step \<open>S \<leadsto> Ss\<close> transforms the triple \<open>S\<close> into the
  disjunction of the triples in \<open>Ss\<close>. All rules except (AC) produce a single triple; the
  failure rules (OC), (Clash), and (BC) produce \<open>\<bottom>\<close>, the empty disjunction.

  \<^bold>\<open>Differences from the dissertation.\<close> All deviations from Figure 2.2 are listed here.

  Corrections (the rule as stated is wrong or underspecified):
  \<^item> (FlFun) requires that some argument is not a variable, as in its termination proof
    (Lemma 3.1); without this condition the rule could be applied forever.
  \<^item> (Clash) requires \<open>f \<noteq> g\<close>; as stated in the dissertation, it would also fire on
    \<open>X =\<^sup>? f(\<dots>), X =\<^sup>? f(\<dots>)\<close> for a free symbol \<open>f\<close>, which (Dec) should handle.
  \<^item> (OC) uses the standard condition \<open>X \<in> Var(f(t\<^sub>1,\<dots>,t\<^sub>n))\<close>.
  \<^item> In (AC), the variables introduced by the AC-unifiers must be fresh (the AC-unification
    algorithm receives the variables to avoid), and they get depth 0.
  \<^item> (AC) requires a non-empty \<open>\<Psi>\<close>. As stated in the dissertation it also applies when there
    are no \<open>+\<close>-equations, even to \<open>\<emptyset> \<parallel> \<Delta> \<parallel> \<sigma>\<close>, so no triple would ever be irreducible.

  Generalisations (the original rules are special cases):
  \<^item> (Dec) allows arbitrary arguments, not only variables.

  Changes needed for termination (Section 3.2 of the dissertation does not go through
  without them; see the theory \<open>Bounded_ACh_Termination\<close>):
  \<^item> (AC) applies to any non-empty sub-multiset \<open>\<Psi>\<close> of \<^emph>\<open>flat\<close> \<open>+\<close>-equations
    \<open>X =\<^sup>? X\<^sub>1 + \<dots> + X\<^sub>n\<close>, instead of to all \<open>+\<close>-equations. The termination strategy uses
    all \<open>+\<close>-equations whose left-hand side has a given h-depth. Applied to all
    \<open>+\<close>-equations at once, (AC) can create new work at smaller h-depths, which breaks the
    argument of Lemma 3.2. Flatness is also needed to invoke completeness of AC-unification.
  \<^item> New rule (UV): for \<open>X =\<^sup>? Y\<close>, raise the depth of \<open>Y\<close> to that of \<open>X\<close>. Without it,
    eliminating \<open>X\<close> by (VE1) can move equations of \<open>X\<close> to a smaller depth.
  \<^item> New rule (USum): (UL)/(UR) for sums with any number of summands, as produced by
    (Split) and (AC). The dissertation only gives them for \<open>X =\<^sup>? Y\<^sub>1 + Y\<^sub>2\<close>.
\<close>

inductive step :: "('f, 'v) triple \<Rightarrow> ('f, 'v) triple set \<Rightarrow> bool" (infix \<open>\<leadsto>\<close> 50) where
  \<comment> \<open>Flattening rules\<close>
  FBS: "\<lbrakk>is_Fun t\<^sub>1; is_Fun t\<^sub>2; fresh_for {v} (add_mset (t\<^sub>1, t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t\<^sub>1, t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (Var v, t\<^sub>1) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)}"
| FL: "\<lbrakk>is_Fun t\<^sub>1; fresh_for {v} (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (t, Var v \<oplus> t\<^sub>2) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)}"
| FR: "\<lbrakk>is_Fun t\<^sub>2; fresh_for {v} (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, t\<^sub>1 \<oplus> t\<^sub>2) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (t, t\<^sub>1 \<oplus> Var v) (add_mset (Var v, t\<^sub>2) \<Gamma>), \<Delta>(v \<mapsto> 0), \<sigma>)}"
| FU: "\<lbrakk>is_Fun t\<^sub>1; fresh_for {v} (add_mset (t, H t\<^sub>1) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, H t\<^sub>1) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (t, H (Var v)) (add_mset (Var v, t\<^sub>1) \<Gamma>), \<Delta>(v \<mapsto> 1), \<sigma>)}"
| FlFun: "\<lbrakk>f \<noteq> plus; f \<noteq> hom; \<exists>u \<in> set ts. is_Fun u; length vs = length ts; distinct vs;
      fresh_for (set vs) (add_mset (t, Fun f ts) \<Gamma>, \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (t, Fun f ts) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (t, Fun f (map Var vs)) (mset (zip (map Var vs) ts) + \<Gamma>),
        \<Delta>(vs [\<mapsto>] replicate (length vs) 0), \<sigma>)}"
  \<comment> \<open>Update h-depth set rules\<close>
| Uh: "\<lbrakk>(Var x, H (Var y)) \<in># \<Gamma>; \<Delta> x = Some k; \<Delta> y = Some l; l < k + 1\<rbrakk> \<Longrightarrow>
    (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y \<mapsto> k + 1), \<sigma>)}"
| UL: "\<lbrakk>(Var x, Var y\<^sub>1 \<oplus> Var y\<^sub>2) \<in># \<Gamma>; \<Delta> x = Some k; \<Delta> y\<^sub>1 = Some l; \<Delta> y\<^sub>2 = Some m; l < k\<rbrakk> \<Longrightarrow>
    (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y\<^sub>1 \<mapsto> k), \<sigma>)}"
| UR: "\<lbrakk>(Var x, Var y\<^sub>1 \<oplus> Var y\<^sub>2) \<in># \<Gamma>; \<Delta> x = Some k; \<Delta> y\<^sub>1 = Some l; \<Delta> y\<^sub>2 = Some m; m < k\<rbrakk> \<Longrightarrow>
    (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y\<^sub>2 \<mapsto> k), \<sigma>)}"
| USum: "\<lbrakk>(Var x, sum_terms (map Var ys)) \<in># \<Gamma>; y \<in> set ys; \<Delta> x = Some k; \<Delta> y = Some l; l < k\<rbrakk> \<Longrightarrow>
    (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y \<mapsto> k), \<sigma>)}"
| UV: "\<lbrakk>(Var x, Var y) \<in># \<Gamma>; \<Delta> x = Some k; \<Delta> y = Some l; l < k\<rbrakk> \<Longrightarrow>
    (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>(y \<mapsto> k), \<sigma>)}"
  \<comment> \<open>Variable elimination rules\<close>
| VE1: "x \<noteq> y \<Longrightarrow>
    (add_mset (Var x, Var y) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(subst_problem (Var(x := Var y)) \<Gamma>, \<Delta>, subst_bindings (Var(x := Var y)) \<sigma> \<union> {(x, Var y)})}"
| VE2: "x \<notin> vars_term t \<Longrightarrow>
    (add_mset (Var x, t) \<Gamma>, \<Delta>, \<sigma>) \<leadsto>
      {(subst_problem (Var(x := t)) \<Gamma>, \<Delta>, subst_bindings (Var(x := t)) \<sigma> \<union> {(x, t)})}"
  \<comment> \<open>Basic rules\<close>
| Triv: "(add_mset (t, t) \<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(\<Gamma>, \<Delta>, \<sigma>)}"
| Orient: "is_Fun t \<Longrightarrow> (add_mset (t, Var x) \<Gamma>, \<Delta>, \<sigma>) \<leadsto> {(add_mset (Var x, t) \<Gamma>, \<Delta>, \<sigma>)}"
| Dec: "\<lbrakk>f \<noteq> plus; length ss = length ts\<rbrakk> \<Longrightarrow>
    (add_mset (Var x, Fun f ss) (add_mset (Var x, Fun f ts) \<Gamma>), \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (Var x, Fun f ss) (mset (zip ss ts) + \<Gamma>), \<Delta>, \<sigma>)}"
  \<comment> \<open>Checking rules\<close>
| OC: "x \<in> vars_term (Fun f ts) \<Longrightarrow> (add_mset (Var x, Fun f ts) \<Gamma>, \<Delta>, \<sigma>) \<leadsto> {}"
| Clash: "\<lbrakk>f \<noteq> g; f \<notin> {plus, hom} \<or> g \<notin> {plus, hom}\<rbrakk> \<Longrightarrow>
    (add_mset (Var x, Fun f ss) (add_mset (Var x, Fun g ts) \<Gamma>), \<Delta>, \<sigma>) \<leadsto> {}"
| BC: "\<not> bounded_depths \<Delta> \<Longrightarrow> (\<Gamma>, \<Delta>, \<sigma>) \<leadsto> {}"
  \<comment> \<open>Splitting rule\<close>
| Split: "\<lbrakk>length xs > 1; x \<noteq> y; x \<notin> set xs; length vs = length xs; distinct vs;
      fresh_for (set vs)
        (add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>), \<Delta>, \<sigma>)\<rbrakk> \<Longrightarrow>
    (add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) \<Gamma>), \<Delta>, \<sigma>) \<leadsto>
      {(add_mset (Var x, H (Var y))
          (add_mset (Var y, sum_terms (map Var vs))
            (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs) + \<Gamma>)),
        \<Delta>(vs [\<mapsto>] replicate (length vs) 1), \<sigma>)}"
  \<comment> \<open>AC-unification rule\<close>
| AC: "\<lbrakk>\<Psi> \<subseteq># \<Gamma>\<^sub>0; \<Gamma> = \<Gamma>\<^sub>0 - \<Psi>;
      \<forall>\<theta> \<in> set (ac_unify (vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)) \<Psi>).
        fresh_for (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) (\<Gamma>\<^sub>0, \<Delta>, \<sigma>);
      \<forall>e \<in># \<Psi>. flat_sum_eq e; \<Psi> \<noteq> {#}\<rbrakk> \<Longrightarrow>
    (\<Gamma>\<^sub>0, \<Delta>, \<sigma>) \<leadsto>
      {(get_eqs \<theta> + \<Gamma>, add_zero_depths (vars_problem (get_eqs \<theta>) - vars_problem \<Psi>) \<Delta>, \<sigma>)
        | \<theta>. \<theta> \<in> set (ac_unify (vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)) \<Psi>)}"

section \<open>Soundness\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma bounded_depths_mono:
  assumes "bounded_depths \<Delta>'"
    and "\<And>z d. \<Delta> z = Some d \<Longrightarrow> \<exists>d'. \<Delta>' z = Some d' \<and> d \<le> d'"
  shows "bounded_depths \<Delta>"
  using assms unfolding bounded_depths_def by (meson order_trans)

lemma bounded_depths_upd:
  assumes "bounded_depths (\<Delta>(y \<mapsto> d))" and "\<And>d'. \<Delta> y = Some d' \<Longrightarrow> d' \<le> d"
  shows "bounded_depths \<Delta>"
  using assms by (intro bounded_depths_mono[OF assms(1)]) auto

lemma bounded_depths_upds:
  assumes "bounded_depths (\<Delta>(vs [\<mapsto>] ds))" and "set vs \<inter> dom \<Delta> = {}"
  shows "bounded_depths \<Delta>"
proof (rule bounded_depths_mono[OF assms(1)])
  fix z d
  assume "\<Delta> z = Some d"
  with assms(2) have "z \<notin> set vs"
    by auto
  with \<open>\<Delta> z = Some d\<close> show "\<exists>d'. (\<Delta>(vs [\<mapsto>] ds)) z = Some d' \<and> d \<le> d'"
    by simp
qed

lemma bounded_depths_add_zero_depths:
  assumes "bounded_depths (add_zero_depths N \<Delta>)" and "N \<inter> dom \<Delta> = {}"
  shows "bounded_depths \<Delta>"
  using assms by (intro bounded_depths_mono[OF assms(1)]) (auto simp: add_zero_depths_def)

text \<open>
  If \<open>\<theta>\<close> satisfies the binding \<open>X \<mapsto> t\<close>, then instantiating a term with \<open>{X \<mapsto> t}\<close> does not change
  its \<open>\<theta>\<close>-instance modulo ACh. This is the core of the (VE) cases of Lemma 3.3.
\<close>

lemma eq_ACh_eliminate:
  assumes "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
  shows "s \<cdot> Var(x := t) \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h s \<cdot> \<theta>"
proof -
  have "s \<cdot> (Var(x := t) \<circ>\<^sub>s \<theta>) \<approx>\<^sub>A\<^sub>C\<^sub>h s \<cdot> \<theta>"
    using assms by (intro eq_theory_subst_cong) (auto simp: subst_compose intro: eq_theory.sym)
  then show ?thesis
    by simp
qed

lemma sat_problem_eliminate:
  assumes "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
  shows "sat_problem \<theta> (subst_problem (Var(x := t)) \<Gamma>) \<longleftrightarrow> sat_problem \<theta> \<Gamma>"
proof -
  have "s \<cdot> Var(x := t) \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h u \<cdot> Var(x := t) \<cdot> \<theta> \<longleftrightarrow> s \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h u \<cdot> \<theta>" for s u
    using eq_ACh_eliminate[OF assms, of s] eq_ACh_eliminate[OF assms, of u]
    by (meson eq_theory.sym eq_theory.trans)
  then show ?thesis
    by (auto simp: sat_problem_def subst_problem_def)
qed

lemma sat_bindings_eliminate:
  assumes "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
  shows "sat_bindings \<theta> (subst_bindings (Var(x := t)) \<sigma>) \<longleftrightarrow> sat_bindings \<theta> \<sigma>"
proof -
  have "\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h s \<cdot> Var(x := t) \<cdot> \<theta> \<longleftrightarrow> \<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h s \<cdot> \<theta>" for y s
    using eq_ACh_eliminate[OF assms, of s]
    by (meson eq_theory.sym eq_theory.trans)
  then show ?thesis
    by (auto simp: sat_bindings_def subst_bindings_def)
qed

text \<open>A solution of \<open>GetEqs(\<rho>)\<close> agrees modulo ACh with its own instance by \<open>\<rho>\<close>.\<close>

lemma sat_get_eqs:
  assumes "sat_problem \<theta> (get_eqs \<rho>)"
  shows "\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h subst_of_list \<rho> y \<cdot> \<theta>"
proof (cases "map_of \<rho> y")
  case None
  then show ?thesis
    by (simp add: subst_of_list_def)
next
  case (Some t)
  then have "(Var y, t) \<in># get_eqs \<rho>"
    by (auto simp: get_eqs_def dest: map_of_SomeD)
  with assms Some show ?thesis
    by (auto simp: sat_problem_def subst_of_list_def)
qed

text \<open>Lemma 3.4: soundness of the (AC) rule.\<close>

lemma sat_problem_ac_unifier:
  assumes "\<rho> \<in> set (ac_unify V \<Psi>)" and "sat_problem \<theta> (get_eqs \<rho>)"
  shows "sat_problem \<theta> \<Psi>"
  unfolding sat_problem_def
proof safe
  fix s t
  assume "(s, t) \<in># \<Psi>"
  have pointwise: "u \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h u \<cdot> subst_of_list \<rho> \<cdot> \<theta>" for u
  proof -
    have "u \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h u \<cdot> (subst_of_list \<rho> \<circ>\<^sub>s \<theta>)"
      by (rule eq_theory_subst_cong) (simp add: subst_compose sat_get_eqs[OF assms(2)])
    then show ?thesis
      by simp
  qed
  have "s \<cdot> subst_of_list \<rho> \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> subst_of_list \<rho>"
    using ac_unify_sound[OF assms(1) \<open>(s, t) \<in># \<Psi>\<close>] by (rule eq_AC_imp_eq_ACh)
  then have "s \<cdot> subst_of_list \<rho> \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> subst_of_list \<rho> \<cdot> \<theta>"
    by (rule eq_theory_subst)
  then show "s \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
    using pointwise[of s] pointwise[of t] by (meson eq_theory.sym eq_theory.trans)
qed

text \<open>The (Split) case of Lemma 3.3, using the homomorphism identity.\<close>

lemma sat_split:
  assumes "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> y)"
    and "\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map Var vs) \<cdot> \<theta>"
    and "sat_problem \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    and "length vs = length xs" and "xs \<noteq> []"
  shows "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map Var xs) \<cdot> \<theta>"
proof -
  have "vs \<noteq> []"
    using assms(4,5) by auto
  have "list_all2 (\<approx>\<^sub>A\<^sub>C\<^sub>h) (map (\<lambda>v. H (\<theta> v)) vs) (map \<theta> xs)"
    unfolding list_all2_conv_all_nth
  proof safe
    fix i
    assume "i < length (map (\<lambda>v. H (\<theta> v)) vs)"
    then have "i < length xs"
      using assms(4) by simp
    then have "(Var (xs ! i), H (Var (vs ! i))) \<in># mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs)"
      using assms(4) by (force simp: in_set_conv_nth)
    then have "\<theta> (xs ! i) \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> (vs ! i))"
      using assms(3) by (auto simp: sat_problem_def)
    then show "map (\<lambda>v. H (\<theta> v)) vs ! i \<approx>\<^sub>A\<^sub>C\<^sub>h map \<theta> xs ! i"
      using \<open>i < length xs\<close> assms(4) by (simp add: eq_theory.sym)
  qed (use assms(4) in simp)
  have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h H (sum_terms (map \<theta> vs))"
    using assms(1,2) \<open>vs \<noteq> []\<close>
    by (auto simp: sum_terms_subst comp_def intro: eq_theory.trans eq_theory_cong1)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map (\<lambda>v. H (\<theta> v)) vs)"
    using eq_ACh_hom_sum[of "map \<theta> vs"] \<open>vs \<noteq> []\<close> by (simp add: comp_def)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map \<theta> xs)"
    by (rule sum_terms_cong) fact
  finally show ?thesis
    using \<open>xs \<noteq> []\<close> by (simp add: sum_terms_subst comp_def)
qed

lemma sat_problem_zip:
  assumes "sat_problem \<theta> (mset (zip ss ts))" and "length ss = length ts"
  shows "list_all2 (\<approx>\<^sub>A\<^sub>C\<^sub>h) (map (\<lambda>s. s \<cdot> \<theta>) ss) (map (\<lambda>t. t \<cdot> \<theta>) ts)"
  unfolding list_all2_conv_all_nth
proof (intro conjI allI impI)
  fix i
  assume "i < length (map (\<lambda>s. s \<cdot> \<theta>) ss)"
  with assms(2) have "(ss ! i, ts ! i) \<in># mset (zip ss ts)"
    by (auto simp: in_set_conv_nth)
  with assms(1) assms(2) \<open>i < _\<close> show "map (\<lambda>s. s \<cdot> \<theta>) ss ! i \<approx>\<^sub>A\<^sub>C\<^sub>h map (\<lambda>t. t \<cdot> \<theta>) ts ! i"
    by (auto simp: sat_problem_def)
qed (use assms(2) in simp)

subsection \<open>One step\<close>

text \<open>
  Lemma 3.5 (combining Lemmas 3.3 and 3.4): if \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<sigma> \<leadsto> \<Or>\<^sub>i (\<Gamma>\<^sub>i \<parallel> \<Delta>\<^sub>i \<parallel> \<sigma>\<^sub>i)\<close> and \<open>\<theta>\<close>
  satisfies some \<open>\<Gamma>\<^sub>i \<parallel> \<Delta>\<^sub>i \<parallel> \<sigma>\<^sub>i\<close>, then \<open>\<theta>\<close> satisfies \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<sigma>\<close>.
\<close>

lemma step_sound:
  assumes "S \<leadsto> Ss" and "S' \<in> Ss" and "\<theta> \<Turnstile> S'"
  shows "\<theta> \<Turnstile> S"
  using assms
proof (induction rule: step.induct)
  case (FBS t\<^sub>1 t\<^sub>2 v \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> v \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>1 \<cdot> \<theta>" "\<theta> v \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>2 \<cdot> \<theta>" "sat_problem \<theta> \<Gamma>" "sat_bindings \<theta> \<sigma>"
    "bounded_depths (\<Delta>(v \<mapsto> 0))" "\<Delta> v = None"
    by auto
  then show ?case
    by (auto intro: eq_theory.sym eq_theory.trans[OF eq_theory.sym] bounded_depths_upd)
next
  case (FL t\<^sub>1 v t t\<^sub>2 \<Gamma> \<Delta> \<sigma>)
  then have "t \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h \<theta> v \<oplus> t\<^sub>2 \<cdot> \<theta>" "\<theta> v \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>1 \<cdot> \<theta>" "sat_problem \<theta> \<Gamma>"
    "sat_bindings \<theta> \<sigma>" "bounded_depths (\<Delta>(v \<mapsto> 0))" "\<Delta> v = None"
    by auto
  then show ?case
    by (auto intro: eq_theory.trans eq_theory_cong2 bounded_depths_upd)
next
  case (FR t\<^sub>2 v t t\<^sub>1 \<Gamma> \<Delta> \<sigma>)
  then have "t \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>1 \<cdot> \<theta> \<oplus> \<theta> v" "\<theta> v \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>2 \<cdot> \<theta>" "sat_problem \<theta> \<Gamma>"
    "sat_bindings \<theta> \<sigma>" "bounded_depths (\<Delta>(v \<mapsto> 0))" "\<Delta> v = None"
    by auto
  then show ?case
    by (auto intro: eq_theory.trans eq_theory_cong2 bounded_depths_upd)
next
  case (FU t\<^sub>1 v t \<Gamma> \<Delta> \<sigma>)
  then have "t \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> v)" "\<theta> v \<approx>\<^sub>A\<^sub>C\<^sub>h t\<^sub>1 \<cdot> \<theta>" "sat_problem \<theta> \<Gamma>"
    "sat_bindings \<theta> \<sigma>" "bounded_depths (\<Delta>(v \<mapsto> 1))" "\<Delta> v = None"
    by auto
  then show ?case
    by (auto intro: eq_theory.trans eq_theory_cong1 bounded_depths_upd)
next
  case (FlFun f ts vs t \<Gamma> \<Delta> \<sigma>)
  then have "t \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f (map Var vs) \<cdot> \<theta>"
    and args: "sat_problem \<theta> (mset (zip (map Var vs) ts))"
    and "sat_problem \<theta> \<Gamma>" "sat_bindings \<theta> \<sigma>"
    and "bounded_depths (\<Delta>(vs [\<mapsto>] replicate (length vs) 0))" "set vs \<inter> dom \<Delta> = {}"
    by auto
  moreover have "Fun f (map Var vs) \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
    using sat_problem_zip[OF args] FlFun.hyps(4)
    by (auto simp: comp_def intro: eq_theory_cong_list)
  ultimately show ?case
    by (auto intro: eq_theory.trans bounded_depths_upds)
next
  case (Uh x y \<Gamma> \<Delta> k l \<sigma>)
  then show ?case
    by (auto intro: bounded_depths_upd)
next
  case (UL x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  then show ?case
    by (auto intro: bounded_depths_upd)
next
  case (UR x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  then show ?case
    by (auto intro: bounded_depths_upd)
next
  case (USum x ys \<Gamma> y \<Delta> k l \<sigma>)
  then show ?case
    by (auto intro: bounded_depths_upd)
next
  case (UV x y \<Gamma> \<Delta> k l \<sigma>)
  then show ?case
    by (auto intro: bounded_depths_upd)
next
  case (VE1 x y \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Var y \<cdot> \<theta>"
    by auto
  with VE1 show ?case
    by (auto simp: sat_problem_eliminate sat_bindings_eliminate)
next
  case (VE2 x t \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> \<theta>"
    by auto
  with VE2 show ?case
    by (auto simp: sat_problem_eliminate sat_bindings_eliminate)
next
  case (Triv t \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by auto
next
  case (Orient t x \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by (auto intro: eq_theory.sym)
next
  case (Dec f ss ts x \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ss \<cdot> \<theta>" and args: "sat_problem \<theta> (mset (zip ss ts))"
    by auto
  moreover have "Fun f ss \<cdot> \<theta> \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
    using sat_problem_zip[OF args Dec.hyps(2)] by (auto intro: eq_theory_cong_list)
  ultimately show ?case
    using Dec by (auto intro: eq_theory.trans)
next
  case (OC x f ts \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by simp
next
  case (Clash f g x ss ts \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by simp
next
  case (BC \<Delta> \<Gamma> \<sigma>)
  then show ?case
    by simp
next
  case (Split xs x y vs \<Gamma> \<Delta> \<sigma>)
  then have "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h H (\<theta> y)" "\<theta> y \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map Var vs) \<cdot> \<theta>"
    "sat_problem \<theta> (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs))"
    "sat_problem \<theta> \<Gamma>" "sat_bindings \<theta> \<sigma>"
    "bounded_depths (\<Delta>(vs [\<mapsto>] replicate (length vs) 1))" "set vs \<inter> dom \<Delta> = {}"
    by auto
  moreover have "xs \<noteq> []"
    using Split.hyps(1) by auto
  ultimately show ?case
    using sat_split[of \<theta> x y vs xs] Split.hyps(4) by (auto intro: bounded_depths_upds)
next
  case (AC \<Psi> \<Gamma>\<^sub>0 \<Gamma> \<Delta> \<sigma>)
  then obtain \<rho> where \<rho>: "\<rho> \<in> set (ac_unify (vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)) \<Psi>)"
    and S': "S' = (get_eqs \<rho> + \<Gamma>, add_zero_depths (vars_problem (get_eqs \<rho>) - vars_problem \<Psi>) \<Delta>, \<sigma>)"
    by auto
  have "sat_problem \<theta> \<Psi>"
    using AC.prems(2) S' sat_problem_ac_unifier[OF \<rho>] by auto
  moreover have "\<Gamma>\<^sub>0 = \<Psi> + \<Gamma>"
    using AC.hyps(1,2) by simp
  moreover have "(vars_problem (get_eqs \<rho>) - vars_problem \<Psi>) \<inter> dom \<Delta> = {}"
    using AC.hyps(3) \<rho> by auto
  ultimately show ?case
    using AC.prems(2) S' by (auto intro: bounded_depths_add_zero_depths)
qed

subsection \<open>Derivations\<close>

text \<open>\<open>S \<leadsto>\<^sup>* S'\<close>: \<open>S'\<close> is one of the triples obtained from \<open>S\<close> after zero or more steps.\<close>

definition step_one :: "('f, 'v) triple \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" where
  "step_one S S' \<longleftrightarrow> (\<exists>Ss. S \<leadsto> Ss \<and> S' \<in> Ss)"

abbreviation steps :: "('f, 'v) triple \<Rightarrow> ('f, 'v) triple \<Rightarrow> bool" (infix \<open>\<leadsto>\<^sup>*\<close> 50) where
  "S \<leadsto>\<^sup>* S' \<equiv> step_one\<^sup>*\<^sup>* S S'"

text \<open>Theorem 3.2.\<close>

theorem steps_sound:
  assumes "S \<leadsto>\<^sup>* S'" and "\<theta> \<Turnstile> S'"
  shows "\<theta> \<Turnstile> S"
  using assms
  by (induction rule: converse_rtranclp_induct) (auto simp: step_one_def intro: step_sound)

subsection \<open>The computed substitution\<close>

text \<open>
  To read off a unifier from a final triple \<open>\<emptyset> \<parallel> \<Delta> \<parallel> \<sigma>\<close>, the bindings in \<open>\<sigma>\<close> must form a
  substitution in solved form: every variable is bound at most once, and bound variables occur
  neither in the bound terms nor in the remaining problem. The dissertation uses this
  implicitly in the proof of Corollary 3.2 ("obviously \<open>\<sigma>\<^sub>i \<Turnstile> \<Gamma>\<^sub>i \<parallel> \<Delta>\<^sub>i \<parallel> \<sigma>\<^sub>i\<close>"); here we prove that
  every rule preserves it.
\<close>

fun solved_inv :: "('f, 'v) triple \<Rightarrow> bool" where
  "solved_inv (\<Gamma>, \<Delta>, \<sigma>) \<longleftrightarrow>
    (\<forall>x t t'. (x, t) \<in> \<sigma> \<longrightarrow> (x, t') \<in> \<sigma> \<longrightarrow> t = t') \<and>
    (\<forall>b \<in> \<sigma>. \<forall>b' \<in> \<sigma>. fst b \<notin> vars_term (snd b')) \<and>
    fst ` \<sigma> \<inter> vars_problem \<Gamma> = {}"

definition subst_of_bindings :: "('f, 'v) bindings \<Rightarrow> ('f, 'v) subst" where
  "subst_of_bindings \<sigma> x = (if \<exists>t. (x, t) \<in> \<sigma> then THE t. (x, t) \<in> \<sigma> else Var x)"

lemma solved_inv_same_bindings:
  assumes "solved_inv (\<Gamma>, \<Delta>, \<sigma>)"
    and "vars_problem \<Gamma>' \<subseteq> vars_problem \<Gamma> \<union> V" and "V \<inter> vars_bindings \<sigma> = {}"
  shows "solved_inv (\<Gamma>', \<Delta>', \<sigma>)"
proof -
  have "fst ` \<sigma> \<inter> vars_problem \<Gamma> = {}" and "V \<inter> fst ` \<sigma> = {}"
    using assms(1,3) by (auto simp: vars_bindings_def)
  then have "fst ` \<sigma> \<inter> vars_problem \<Gamma>' = {}"
    using assms(2) by blast
  then show ?thesis
    using assms(1) by simp
qed

lemma mem_subst_bindings:
  "b \<in> subst_bindings \<tau> \<sigma> \<longleftrightarrow> (\<exists>y s. (y, s) \<in> \<sigma> \<and> b = (y, s \<cdot> \<tau>))"
  by (auto simp: subst_bindings_def)

lemma vars_term_subst_upd:
  "vars_term (s \<cdot> Var(x := t)) \<subseteq> (vars_term s - {x}) \<union> vars_term t"
  by (induction s) auto

lemma vars_subst_problem_upd:
  "vars_problem (subst_problem (Var(x := t)) \<Gamma>) \<subseteq> (vars_problem \<Gamma> - {x}) \<union> vars_term t"
  using vars_term_subst_upd[of _ x t]
  by (fastforce simp: vars_problem_def subst_problem_def vars_eq_def)

lemma solved_inv_eliminate:
  assumes inv: "solved_inv (add_mset (Var x, t) \<Gamma>, \<Delta>, \<sigma>)" and "x \<notin> vars_term t"
  shows "solved_inv (subst_problem (Var(x := t)) \<Gamma>, \<Delta>',
    subst_bindings (Var(x := t)) \<sigma> \<union> {(x, t)})"
proof -
  let ?\<tau> = "Var(x := t)"
  let ?\<sigma>' = "subst_bindings ?\<tau> \<sigma> \<union> {(x, t)}"
  have inv': "\<forall>y s s'. (y, s) \<in> \<sigma> \<longrightarrow> (y, s') \<in> \<sigma> \<longrightarrow> s = s'"
    "\<forall>b \<in> \<sigma>. \<forall>b' \<in> \<sigma>. fst b \<notin> vars_term (snd b')"
    "fst ` \<sigma> \<inter> (insert x (vars_term t \<union> vars_problem \<Gamma>)) = {}"
    using inv by simp_all
  then have func: "\<And>y s s'. (y, s) \<in> \<sigma> \<Longrightarrow> (y, s') \<in> \<sigma> \<Longrightarrow> s = s'"
    and rng: "\<And>y s z u. (y, s) \<in> \<sigma> \<Longrightarrow> (z, u) \<in> \<sigma> \<Longrightarrow> y \<notin> vars_term u"
    and dom_\<Gamma>: "fst ` \<sigma> \<inter> vars_problem \<Gamma> = {}"
    and dom_t: "fst ` \<sigma> \<inter> vars_term t = {}"
    and x_dom: "x \<notin> fst ` \<sigma>"
    by (blast, metis fst_conv snd_conv, blast+)
  have dom': "fst ` ?\<sigma>' = insert x (fst ` \<sigma>)"
    by (force simp: subst_bindings_def)
  have "(\<forall>y s s'. (y, s) \<in> ?\<sigma>' \<longrightarrow> (y, s') \<in> ?\<sigma>' \<longrightarrow> s = s')"
  proof (intro allI impI)
    fix y s s'
    assume "(y, s) \<in> ?\<sigma>'" "(y, s') \<in> ?\<sigma>'"
    then show "s = s'"
      unfolding Un_iff mem_subst_bindings using func x_dom by (auto simp: image_iff)
  qed
  moreover have "\<forall>b \<in> ?\<sigma>'. \<forall>b' \<in> ?\<sigma>'. fst b \<notin> vars_term (snd b')"
  proof (intro ballI)
    fix b b'
    assume "b \<in> ?\<sigma>'" "b' \<in> ?\<sigma>'"
    then have b_dom: "fst b \<in> insert x (fst ` \<sigma>)"
      using dom' by (metis imageI)
    have b'_cases: "snd b' = t \<or> (\<exists>z u. (z, u) \<in> \<sigma> \<and> snd b' = u \<cdot> ?\<tau>)"
      using \<open>b' \<in> ?\<sigma>'\<close> unfolding Un_iff mem_subst_bindings by force
    have not_t: "fst b \<notin> vars_term t"
      using b_dom dom_t \<open>x \<notin> vars_term t\<close> by auto
    have "fst b \<notin> vars_term (u \<cdot> ?\<tau>)" if "(z, u) \<in> \<sigma>" for z u
    proof -
      have "fst b \<notin> vars_term u - {x}"
        using b_dom rng[OF _ that] by auto
      then show ?thesis
        using vars_term_subst_upd[of u x t] not_t by auto
    qed
    with b'_cases not_t show "fst b \<notin> vars_term (snd b')"
      by auto
  qed
  moreover have "fst ` ?\<sigma>' \<inter> vars_problem (subst_problem ?\<tau> \<Gamma>) = {}"
  proof -
    have "insert x (fst ` \<sigma>) \<inter> ((vars_problem \<Gamma> - {x}) \<union> vars_term t) = {}"
      using dom_\<Gamma> dom_t \<open>x \<notin> vars_term t\<close> by auto
    then show ?thesis
      unfolding dom' using vars_subst_problem_upd[of x t \<Gamma>] by auto
  qed
  ultimately show ?thesis
    by (simp only: solved_inv.simps)
qed

lemma vars_problem_mset_zip:
  "vars_problem (mset (zip ss ts)) \<subseteq> (\<Union>s \<in> set ss. vars_term s) \<union> (\<Union>t \<in> set ts. vars_term t)"
  by (auto simp: vars_problem_def vars_eq_def dest: set_zip_leftD set_zip_rightD)

lemma vars_problem_mset_map2:
  "vars_problem (mset (map2 (\<lambda>x\<^sub>i v\<^sub>i. (Var x\<^sub>i, H (Var v\<^sub>i))) xs vs)) \<subseteq> set xs \<union> set vs"
  by (auto simp: vars_problem_def vars_eq_def dest: set_zip_leftD set_zip_rightD)

lemma vars_problem_mono:
  "\<Gamma>' \<subseteq># \<Gamma> \<Longrightarrow> vars_problem \<Gamma>' \<subseteq> vars_problem \<Gamma>"
  by (auto simp: vars_problem_def dest: mset_subset_eqD)

declare solved_inv.simps [simp del]

lemma solved_inv_same_bindingsI:
  assumes "S' = (\<Gamma>', \<Delta>', \<sigma>)" and "solved_inv (\<Gamma>, \<Delta>, \<sigma>)"
    and "vars_problem \<Gamma>' \<subseteq> vars_problem \<Gamma> \<union> V" and "V \<inter> vars_bindings \<sigma> = {}"
  shows "solved_inv S'"
  using solved_inv_same_bindings[OF assms(2-4)] assms(1) by simp

text \<open>Every rule preserves the solved form of the computed bindings.\<close>

lemma step_solved_inv:
  assumes "S \<leadsto> Ss" and "S' \<in> Ss" and "solved_inv S"
  shows "solved_inv S'"
  using assms
proof (induction rule: step.induct)
  case (FBS t\<^sub>1 t\<^sub>2 v \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF FBS.prems(1)[simplified] FBS.prems(2), where V = "{v}"])
      (use FBS.hyps in auto)
next
  case (FL t\<^sub>1 v t t\<^sub>2 \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF FL.prems(1)[simplified] FL.prems(2), where V = "{v}"])
      (use FL.hyps in auto)
next
  case (FR t\<^sub>2 v t t\<^sub>1 \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF FR.prems(1)[simplified] FR.prems(2), where V = "{v}"])
      (use FR.hyps in auto)
next
  case (FU t\<^sub>1 v t \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF FU.prems(1)[simplified] FU.prems(2), where V = "{v}"])
      (use FU.hyps in auto)
next
  case (FlFun f ts vs t \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF FlFun.prems(1)[simplified] FlFun.prems(2),
          where V = "set vs"])
      (use FlFun.hyps vars_problem_mset_zip[of "map Var vs" ts] in auto)
next
  case (Uh x y \<Gamma> \<Delta> k l \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF Uh.prems(1)[simplified] Uh.prems(2), where V = "{}"])
      auto
next
  case (UL x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF UL.prems(1)[simplified] UL.prems(2), where V = "{}"])
      auto
next
  case (UR x y\<^sub>1 y\<^sub>2 \<Gamma> \<Delta> k l m \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF UR.prems(1)[simplified] UR.prems(2), where V = "{}"])
      auto
next
  case (USum x ys \<Gamma> y \<Delta> k l \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF USum.prems(1)[simplified] USum.prems(2), where V = "{}"])
      auto
next
  case (UV x y \<Gamma> \<Delta> k l \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF UV.prems(1)[simplified] UV.prems(2), where V = "{}"])
      auto
next
  case (VE1 x y \<Gamma> \<Delta> \<sigma>)
  then show ?case
    using solved_inv_eliminate[of x "Var y" \<Gamma> \<Delta> \<sigma>] by simp
next
  case (VE2 x t \<Gamma> \<Delta> \<sigma>)
  then show ?case
    using solved_inv_eliminate[of x t \<Gamma> \<Delta> \<sigma>] by simp
next
  case (Triv t \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF Triv.prems(1)[simplified] Triv.prems(2), where V = "{}"])
      auto
next
  case (Orient t x \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF Orient.prems(1)[simplified] Orient.prems(2),
          where V = "{}"])
      auto
next
  case (Dec f ss ts x \<Gamma> \<Delta> \<sigma>)
  show ?case
    by (rule solved_inv_same_bindingsI[OF Dec.prems(1)[simplified] Dec.prems(2), where V = "{}"])
      (use vars_problem_mset_zip[of ss ts] in auto)
next
  case (OC x f ts \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by simp
next
  case (Clash f g x ss ts \<Gamma> \<Delta> \<sigma>)
  then show ?case
    by simp
next
  case (BC \<Delta> \<Gamma> \<sigma>)
  then show ?case
    by simp
next
  case (Split xs x y vs \<Gamma> \<Delta> \<sigma>)
  have "xs \<noteq> []" "vs \<noteq> []"
    using Split.hyps(1,4) by auto
  show ?case
    by (rule solved_inv_same_bindingsI[OF Split.prems(1)[simplified] Split.prems(2),
          where V = "set vs"])
      (use Split.hyps \<open>xs \<noteq> []\<close> \<open>vs \<noteq> []\<close> vars_problem_mset_map2[of xs vs] in
        \<open>auto simp: vars_sum_terms\<close>)
next
  case (AC \<Psi> \<Gamma>\<^sub>0 \<Gamma> \<Delta> \<sigma>)
  then obtain \<rho> where \<rho>: "\<rho> \<in> set (ac_unify (vars_triple (\<Gamma>\<^sub>0, \<Delta>, \<sigma>)) \<Psi>)"
    and S': "S' = (get_eqs \<rho> + \<Gamma>, add_zero_depths (vars_problem (get_eqs \<rho>) - vars_problem \<Psi>) \<Delta>, \<sigma>)"
    by auto
  let ?N = "vars_problem (get_eqs \<rho>) - vars_problem \<Psi>"
  have "vars_problem \<Psi> \<subseteq> vars_problem \<Gamma>\<^sub>0" "vars_problem \<Gamma> \<subseteq> vars_problem \<Gamma>\<^sub>0"
    using AC.hyps(1,2) by (simp_all add: vars_problem_mono)
  then have "vars_problem (get_eqs \<rho> + \<Gamma>) \<subseteq> vars_problem \<Gamma>\<^sub>0 \<union> ?N"
    by auto
  moreover have "?N \<inter> vars_bindings \<sigma> = {}"
    using AC.hyps(3) \<rho> by auto
  ultimately show ?case
    by (rule solved_inv_same_bindingsI[OF S' AC.prems(2)])
qed

lemma steps_solved_inv:
  assumes "S \<leadsto>\<^sup>* S'" and "solved_inv S"
  shows "solved_inv S'"
  using assms
  by (induction rule: rtranclp_induct) (auto simp: step_one_def intro: step_solved_inv)

lemma solved_inv_initial: "solved_inv (\<Gamma>, \<Delta>, {})"
  by (simp add: solved_inv.simps)

text \<open>A set of bindings in solved form, read as a substitution, satisfies itself.\<close>

lemma sat_bindings_subst_of_bindings:
  assumes "solved_inv (\<Gamma>, \<Delta>, \<sigma>)"
  shows "sat_bindings (subst_of_bindings \<sigma>) \<sigma>"
  unfolding sat_bindings_def
proof safe
  fix x t
  assume "(x, t) \<in> \<sigma>"
  have inv: "\<forall>x t t'. (x, t) \<in> \<sigma> \<longrightarrow> (x, t') \<in> \<sigma> \<longrightarrow> t = t'"
    "\<forall>b \<in> \<sigma>. \<forall>b' \<in> \<sigma>. fst b \<notin> vars_term (snd b')"
    using assms by (simp_all add: solved_inv.simps)
  have func: "\<And>s. (x, s) \<in> \<sigma> \<Longrightarrow> s = t"
    using inv(1) \<open>(x, t) \<in> \<sigma>\<close> by blast
  have rng: "\<And>y s. (y, s) \<in> \<sigma> \<Longrightarrow> y \<notin> vars_term t"
    using inv(2) \<open>(x, t) \<in> \<sigma>\<close> by (metis fst_conv snd_conv)
  have "(THE s. (x, s) \<in> \<sigma>) = t"
    using \<open>(x, t) \<in> \<sigma>\<close> func by (rule the_equality)
  then have "subst_of_bindings \<sigma> x = t"
    unfolding subst_of_bindings_def using \<open>(x, t) \<in> \<sigma>\<close> by auto
  moreover have "t \<cdot> subst_of_bindings \<sigma> = t \<cdot> Var"
    using rng by (intro term_subst_eq) (auto simp: subst_of_bindings_def)
  ultimately show "subst_of_bindings \<sigma> x \<approx>\<^sub>A\<^sub>C\<^sub>h t \<cdot> subst_of_bindings \<sigma>"
    by simp
qed

text \<open>
  Corollary 3.2 (Soundness). If the triple \<open>\<Gamma> \<parallel> \<Delta> \<parallel> \<emptyset>\<close> is transformed into
  \<open>\<emptyset> \<parallel> \<Delta>' \<parallel> \<sigma>\<close> and no rule applies to the latter, then the substitution \<open>\<sigma>\<close> is an
  ACh-unifier of \<open>\<Gamma>\<close>. Irreducibility is only used to exclude (BC), i.e. to get
  \<open>MaxVal(\<Delta>') \<le> \<kappa>\<close>; the variant \<open>steps_sound_bounded\<close> assumes this directly.
\<close>

theorem steps_sound_bounded:
  assumes "(\<Gamma>, \<Delta>, {}) \<leadsto>\<^sup>* ({#}, \<Delta>', \<sigma>)" and "bounded_depths \<Delta>'"
  shows "sat_problem (subst_of_bindings \<sigma>) \<Gamma>" and "bounded_depths \<Delta>"
proof -
  have "solved_inv ({#}, \<Delta>', \<sigma>)"
    using steps_solved_inv[OF assms(1) solved_inv_initial] .
  then have "subst_of_bindings \<sigma> \<Turnstile> ({#}, \<Delta>', \<sigma>)"
    using assms(2) sat_bindings_subst_of_bindings by simp
  then have "subst_of_bindings \<sigma> \<Turnstile> (\<Gamma>, \<Delta>, {})"
    using steps_sound[OF assms(1)] by blast
  then show "sat_problem (subst_of_bindings \<sigma>) \<Gamma>" and "bounded_depths \<Delta>"
    by simp_all
qed

corollary soundness:
  assumes "(\<Gamma>, \<Delta>, {}) \<leadsto>\<^sup>* ({#}, \<Delta>', \<sigma>)" and "\<nexists>Ss. ({#}, \<Delta>', \<sigma>) \<leadsto> Ss"
  shows "sat_problem (subst_of_bindings \<sigma>) \<Gamma>"
proof -
  have "bounded_depths \<Delta>'"
    using assms(2) step.BC by blast
  then show ?thesis
    using steps_sound_bounded(1)[OF assms(1)] by blast
qed

text \<open>
  Sanity check: solved triples are irreducible, so hypotheses of the form
  "no rule applies to the leaves" can be satisfied.
\<close>

lemma irreducible_solved:
  "(\<nexists>Ss. ({#}, \<Delta>, \<sigma>) \<leadsto> Ss) \<longleftrightarrow> bounded_depths \<Delta>"
proof
  assume "\<nexists>Ss. ({#}, \<Delta>, \<sigma>) \<leadsto> Ss"
  then show "bounded_depths \<Delta>"
    using step.BC by blast
next
  assume "bounded_depths \<Delta>"
  show "\<nexists>Ss. ({#}, \<Delta>, \<sigma>) \<leadsto> Ss"
  proof
    assume "\<exists>Ss. ({#}, \<Delta>, \<sigma>) \<leadsto> Ss"
    then obtain Ss where "({#}, \<Delta>, \<sigma>) \<leadsto> Ss"
      by blast
    then show False
      using \<open>bounded_depths \<Delta>\<close> by (cases rule: step.cases) auto
  qed
qed

subsection \<open>Derivation trees\<close>

text \<open>
  A (partial) derivation tree from \<open>S\<close>: either \<open>S\<close> itself is a leaf, or a rule transforms \<open>S\<close>
  into the disjunction \<open>Ss\<close>, and each element of \<open>Ss\<close> is expanded further. \<open>L\<close> is the set
  of leaves. The algorithm \<open>UnifyACh\<close> computes such a tree; \<open>S \<parallel> \<Delta> \<parallel> \<sigma> \<Rightarrow>\<^sup>* \<Or>\<^sub>i (\<Gamma>\<^sub>i \<parallel> \<Delta>\<^sub>i \<parallel> \<sigma>\<^sub>i)\<close>
  in the dissertation corresponds to \<open>tree S L\<close> with \<open>L = {\<Gamma>\<^sub>i \<parallel> \<Delta>\<^sub>i \<parallel> \<sigma>\<^sub>i}\<close>.
\<close>

inductive tree :: "('f, 'v) triple \<Rightarrow> ('f, 'v) triple set \<Rightarrow> bool" where
  leaf: "tree S {S}"
| node: "\<lbrakk>S \<leadsto> Ss; \<And>S'. S' \<in> Ss \<Longrightarrow> tree S' (L S')\<rbrakk> \<Longrightarrow> tree S (\<Union>S' \<in> Ss. L S')"

lemma tree_invariant:
  assumes "tree S L" and "P S"
    and step: "\<And>S Ss S'. S \<leadsto> Ss \<Longrightarrow> S' \<in> Ss \<Longrightarrow> P S \<Longrightarrow> P S'"
  shows "\<forall>S' \<in> L. P S'"
  using assms(1,2) by (induction rule: tree.induct) (use step in blast)+

text \<open>
  \<open>reach S P\<close>: there is a finite derivation tree from \<open>S\<close> all of whose leaves satisfy \<open>P\<close>.
  Failing branches (empty disjunctions) contribute no leaves.
\<close>

definition reach :: "('f, 'v) triple \<Rightarrow> (('f, 'v) triple \<Rightarrow> bool) \<Rightarrow> bool" where
  "reach S P \<longleftrightarrow> (\<exists>L. tree S L \<and> (\<forall>S' \<in> L. P S'))"

lemma reach_refl: "P S \<Longrightarrow> reach S P"
  unfolding reach_def using tree.leaf by blast

lemma reach_step:
  assumes "S \<leadsto> Ss" and "\<And>S'. S' \<in> Ss \<Longrightarrow> reach S' P"
  shows "reach S P"
proof -
  obtain L where "\<And>S'. S' \<in> Ss \<Longrightarrow> tree S' (L S') \<and> (\<forall>S'' \<in> L S'. P S'')"
    using assms(2) unfolding reach_def by metis
  then show ?thesis
    unfolding reach_def using tree.node[OF assms(1), of L] by blast
qed

lemma reach_single: "S \<leadsto> {S'} \<Longrightarrow> reach S' P \<Longrightarrow> reach S P"
  by (rule reach_step) auto

lemma reach_fail: "S \<leadsto> {} \<Longrightarrow> reach S P"
  by (rule reach_step) auto

lemma tree_bind:
  assumes "tree S L" and "\<And>S'. S' \<in> L \<Longrightarrow> reach S' P"
  shows "reach S P"
  using assms
proof (induction rule: tree.induct)
  case (leaf S)
  then show ?case
    by simp
next
  case (node S Ss L)
  show ?case
    by (rule reach_step[OF node.hyps(1)]) (use node.IH node.prems in blast)
qed

lemma reach_trans:
  assumes "reach S Q" and "\<And>S'. Q S' \<Longrightarrow> reach S' P"
  shows "reach S P"
  using assms tree_bind unfolding reach_def by blast

lemma reach_mono:
  assumes "reach S Q" and "\<And>S'. Q S' \<Longrightarrow> P S'"
  shows "reach S P"
  using assms reach_refl reach_trans by metis

end

text \<open>The locale assumptions are satisfiable, so the results above are not vacuous.\<close>

lemma "bounded_ach (0 :: nat) (Suc 0) (\<lambda>_ (_ :: (nat, nat) problem). [])"
  by unfold_locales simp_all

end
