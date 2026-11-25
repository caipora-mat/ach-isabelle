(*
Author: Guilherme Borges Brandão
*)

theory ACh_Theory
  imports Equational_Theory
begin

section \<open>The theories AC and ACh\<close>

text \<open>
  Section 1.4 of the dissertation: the signature contains a binary symbol \<open>+\<close>, which is
  associative and commutative, a unary symbol \<open>h\<close>, which is a homomorphism over \<open>+\<close>, and
  arbitrary uninterpreted (free) symbols.
\<close>

text \<open>Variables used to state the axioms.\<close>

datatype ax_var = X | Y | Z

locale ach_signature =
  fixes plus :: 'f
    and hom :: 'f
  assumes plus_neq_hom: "plus \<noteq> hom"
begin

abbreviation Plus :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixl \<open>\<oplus>\<close> 65)
  where "s \<oplus> t \<equiv> Fun plus [s, t]"

abbreviation H :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where "H t \<equiv> Fun hom [t]"

definition AC_axioms :: "('f, ax_var) identity set" where
  "AC_axioms =
    {(Var X \<oplus> (Var Y \<oplus> Var Z), (Var X \<oplus> Var Y) \<oplus> Var Z),
     (Var X \<oplus> Var Y, Var Y \<oplus> Var X)}"

definition ACh_axioms :: "('f, ax_var) identity set" where
  "ACh_axioms = AC_axioms \<union> {(H (Var X \<oplus> Var Y), H (Var X) \<oplus> H (Var Y))}"

abbreviation eq_AC :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix \<open>\<approx>\<^sub>A\<^sub>C\<close> 50)
  where "s \<approx>\<^sub>A\<^sub>C t \<equiv> eq_theory AC_axioms s t"

abbreviation eq_ACh :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix \<open>\<approx>\<^sub>A\<^sub>C\<^sub>h\<close> 50)
  where "s \<approx>\<^sub>A\<^sub>C\<^sub>h t \<equiv> eq_theory ACh_axioms s t"

subsection \<open>The axioms as derived rules\<close>

lemma eq_AC_assoc: "s \<oplus> (t \<oplus> u) \<approx>\<^sub>A\<^sub>C (s \<oplus> t) \<oplus> u"
  using eq_theory.axiom[of "Var X \<oplus> (Var Y \<oplus> Var Z)" "(Var X \<oplus> Var Y) \<oplus> Var Z" AC_axioms
      "\<lambda>x. case x of X \<Rightarrow> s | Y \<Rightarrow> t | Z \<Rightarrow> u"]
  by (simp add: AC_axioms_def)

lemma eq_AC_comm: "s \<oplus> t \<approx>\<^sub>A\<^sub>C t \<oplus> s"
  using eq_theory.axiom[of "Var X \<oplus> Var Y" "Var Y \<oplus> Var X" AC_axioms
      "\<lambda>x. case x of X \<Rightarrow> s | Y \<Rightarrow> t | Z \<Rightarrow> t"]
  by (simp add: AC_axioms_def)

lemma eq_AC_imp_eq_ACh: "s \<approx>\<^sub>A\<^sub>C t \<Longrightarrow> s \<approx>\<^sub>A\<^sub>C\<^sub>h t"
  by (rule eq_theory_mono[of AC_axioms]) (auto simp: ACh_axioms_def)

lemma eq_ACh_hom: "H (s \<oplus> t) \<approx>\<^sub>A\<^sub>C\<^sub>h H s \<oplus> H t"
  using eq_theory.axiom[of "H (Var X \<oplus> Var Y)" "H (Var X) \<oplus> H (Var Y)" ACh_axioms
      "\<lambda>x. case x of X \<Rightarrow> s | Y \<Rightarrow> t | Z \<Rightarrow> t"]
  by (simp add: ACh_axioms_def)

lemma eq_ACh_assoc: "s \<oplus> (t \<oplus> u) \<approx>\<^sub>A\<^sub>C\<^sub>h (s \<oplus> t) \<oplus> u"
  by (rule eq_AC_imp_eq_ACh[OF eq_AC_assoc])

lemma eq_ACh_comm: "s \<oplus> t \<approx>\<^sub>A\<^sub>C\<^sub>h t \<oplus> s"
  by (rule eq_AC_imp_eq_ACh[OF eq_AC_comm])

subsection \<open>Sums of several terms\<close>

text \<open>
  \<open>sum_terms [t\<^sub>1, \<dots>, t\<^sub>n]\<close> is the term \<open>t\<^sub>1 + \<dots> + t\<^sub>n\<close>, associated to the right. It is only
  meaningful for non-empty lists. Modulo AC the chosen association does not matter.
\<close>

fun sum_terms :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term" where
  "sum_terms [] = undefined"
| "sum_terms [t] = t"
| "sum_terms (t # u # ts) = t \<oplus> sum_terms (u # ts)"

lemma sum_terms_subst:
  "ts \<noteq> [] \<Longrightarrow> sum_terms ts \<cdot> \<sigma> = sum_terms (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
  by (induction ts rule: sum_terms.induct) auto

lemma vars_sum_terms:
  "ts \<noteq> [] \<Longrightarrow> vars_term (sum_terms ts) = (\<Union>t \<in> set ts. vars_term t)"
  by (induction ts rule: sum_terms.induct) auto

lemma sum_terms_cong:
  assumes "list_all2 (eq_theory E) ss ts"
  shows "eq_theory E (sum_terms ss) (sum_terms ts)"
  using assms
proof (induction ss arbitrary: ts rule: sum_terms.induct)
  case 1
  then show ?case by simp
next
  case (2 s)
  then show ?case by (auto simp: list_all2_Cons1)
next
  case (3 s u ss)
  then obtain t v ts' where "ts = t # v # ts'"
    by (auto simp: list_all2_Cons1)
  with 3 show ?case
    by (auto intro: eq_theory_cong2)
qed

lemma eq_ACh_hom_sum:
  "ts \<noteq> [] \<Longrightarrow> H (sum_terms ts) \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map H ts)"
proof (induction ts rule: sum_terms.induct)
  case (3 t u ts)
  have "H (t \<oplus> sum_terms (u # ts)) \<approx>\<^sub>A\<^sub>C\<^sub>h H t \<oplus> H (sum_terms (u # ts))"
    by (rule eq_ACh_hom)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h H t \<oplus> sum_terms (map H (u # ts))"
    using 3 by (intro eq_theory_cong2) auto
  finally show ?case
    by simp
qed auto

end

end
