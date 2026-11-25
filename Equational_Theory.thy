(*
Author: Guilherme Borges Brandão
*)

theory Equational_Theory
  imports "First_Order_Terms.Unifiers"
begin

section \<open>Equational theories\<close>

text \<open>
  Definition 1.12 of the dissertation: the equational theory \<open>=\<^sub>E\<close> induced by a set \<open>E\<close> of
  identities is the least congruence relation that is closed under substitution and contains \<open>E\<close>.
  We define it inductively. The variables of the identities live in their own type \<open>'w\<close>,
  so that, e.g., the AC axioms can be stated with three distinct variables regardless of how
  many variables the term type \<open>'v\<close> provides.
\<close>

type_synonym ('f, 'w) identity = "('f, 'w) term \<times> ('f, 'w) term"

inductive eq_theory :: "('f, 'w) identity set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  for E :: "('f, 'w) identity set"
  where
    axiom: "(l, r) \<in> E \<Longrightarrow> eq_theory E (l \<cdot> \<sigma>) (r \<cdot> \<sigma>)"
  | refl [intro, simp]: "eq_theory E t t"
  | sym: "eq_theory E s t \<Longrightarrow> eq_theory E t s"
  | trans: "eq_theory E s t \<Longrightarrow> eq_theory E t u \<Longrightarrow> eq_theory E s u"
  | cong: "length ss = length ts \<Longrightarrow> (\<And>i. i < length ss \<Longrightarrow> eq_theory E (ss ! i) (ts ! i))
      \<Longrightarrow> eq_theory E (Fun f ss) (Fun f ts)"

subsection \<open>Basic properties\<close>

declare eq_theory.trans [trans]

lemma eq_theory_equivp: "equivp (eq_theory E)"
  by (intro equivpI reflpI sympI transpI) (blast intro: eq_theory.sym eq_theory.trans)+

lemma eq_theory_cong_list:
  assumes "list_all2 (eq_theory E) ss ts"
  shows "eq_theory E (Fun f ss) (Fun f ts)"
  using assms by (intro eq_theory.cong) (auto simp: list_all2_conv_all_nth)

lemma eq_theory_cong1:
  "eq_theory E s t \<Longrightarrow> eq_theory E (Fun f [s]) (Fun f [t])"
  by (rule eq_theory_cong_list) simp

lemma eq_theory_cong2:
  "eq_theory E s s' \<Longrightarrow> eq_theory E t t' \<Longrightarrow> eq_theory E (Fun f [s, t]) (Fun f [s', t'])"
  by (rule eq_theory_cong_list) simp

text \<open>\<open>=\<^sub>E\<close> is closed under substitution.\<close>

lemma eq_theory_subst:
  fixes \<sigma> :: "('f, 'v, 'u) gsubst"
  assumes "eq_theory E s t"
  shows "eq_theory E (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  using assms
proof (induction rule: eq_theory.induct)
  case (axiom l r \<tau>)
  then show ?case
    using eq_theory.axiom[of l r E "\<tau> \<circ>\<^sub>s \<sigma>"] by simp
next
  case (cong ss ts f)
  then show ?case
    by (auto intro!: eq_theory.cong)
qed (auto intro: eq_theory.sym eq_theory.trans)

text \<open>Applying pointwise \<open>=\<^sub>E\<close>-equal substitutions to a term gives \<open>=\<^sub>E\<close>-equal terms.\<close>

lemma eq_theory_subst_cong:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> eq_theory E (\<sigma> x) (\<tau> x)"
  shows "eq_theory E (t \<cdot> \<sigma>) (t \<cdot> \<tau>)"
  using assms
proof (induction t)
  case (Fun f ts)
  then show ?case
    by (auto intro!: eq_theory.cong) (meson nth_mem)
qed simp

lemma eq_theory_subst_both:
  assumes "eq_theory E s t"
    and "\<And>x. x \<in> vars_term t \<Longrightarrow> eq_theory E (\<sigma> x) (\<tau> x)"
  shows "eq_theory E (s \<cdot> \<sigma>) (t \<cdot> \<tau>)"
  using eq_theory.trans[OF eq_theory_subst[OF assms(1)] eq_theory_subst_cong[OF assms(2)]] .

lemma eq_theory_mono:
  assumes "E \<subseteq> E'" and "eq_theory E s t"
  shows "eq_theory E' s t"
  using assms(2)
  by (induction rule: eq_theory.induct)
    (use assms(1) in \<open>auto intro: eq_theory.axiom eq_theory.sym eq_theory.trans eq_theory.cong\<close>)

end
