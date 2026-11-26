(*
Author: Guilherme Borges Brandão
*)

theory ACh_Theory
  imports "../AC_Unif/AC_Theory"
begin

section \<open>The theory ACh\<close>

text \<open>
  Section 1.4 of the dissertation: ACh extends AC (\<open>AC_Theory\<close>) with a unary symbol \<open>h\<close>,
  which is a homomorphism over \<open>+\<close>.
\<close>

locale ach_signature = ac_signature plus
  for plus :: 'f +
  fixes hom :: 'f
  assumes plus_neq_hom: "plus \<noteq> hom"
begin

abbreviation H :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where "H t \<equiv> Fun hom [t]"

definition ACh_axioms :: "('f, 'v) identity set" where
  "ACh_axioms = AC_axioms \<union> {(H (s \<oplus> t), H s \<oplus> H t) | s t. True}"

abbreviation eq_ACh :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix \<open>\<approx>\<^sub>A\<^sub>C\<^sub>h\<close> 50)
  where "s \<approx>\<^sub>A\<^sub>C\<^sub>h t \<equiv> eq_theory (ACh_axioms :: ('f, 'v) identity set) s t"

text \<open>ACh is an instance of an equational theory, with identities \<open>ACh_axioms\<close>.\<close>

sublocale ach: equational_theory ACh_axioms .

subsection \<open>The axioms as derived rules\<close>

lemma eq_AC_imp_eq_ACh: "s \<approx>\<^sub>A\<^sub>C t \<Longrightarrow> s \<approx>\<^sub>A\<^sub>C\<^sub>h t"
  by (rule eq_theory_mono[of AC_axioms]) (auto simp: ACh_axioms_def)

lemma eq_ACh_hom: "H (s \<oplus> t) \<approx>\<^sub>A\<^sub>C\<^sub>h H s \<oplus> H t"
  using eq_theory.axiom[of "H (s \<oplus> t)" "H s \<oplus> H t" ACh_axioms Var]
  by (auto simp: ACh_axioms_def)

lemma eq_ACh_assoc: "s \<oplus> (t \<oplus> u) \<approx>\<^sub>A\<^sub>C\<^sub>h (s \<oplus> t) \<oplus> u"
  by (rule eq_AC_imp_eq_ACh[OF eq_AC_assoc])

lemma eq_ACh_comm: "s \<oplus> t \<approx>\<^sub>A\<^sub>C\<^sub>h t \<oplus> s"
  by (rule eq_AC_imp_eq_ACh[OF eq_AC_comm])

subsection \<open>Sums of several terms\<close>

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
