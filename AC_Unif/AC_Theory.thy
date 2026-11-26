(*
Author: Guilherme Borges Brandão
*)

theory AC_Theory
  imports "../Equational_Theory"
begin

section ‹The theory AC›

text ‹
  Section 1.4 of the dissertation: the signature contains a binary symbol ‹+›, which is
  associative and commutative, and arbitrary uninterpreted (free) symbols. The theory ACh
  (‹ACh_Theory›) extends this one with a homomorphism over ‹+›.
›

locale ac_signature =
  fixes plus :: 'f
begin

abbreviation Plus :: "('f, 'v) term ⇒ ('f, 'v) term ⇒ ('f, 'v) term" (infixl ‹⊕› 65)
  where "s ⊕ t ≡ Fun plus [s, t]"

text ‹The axioms, given by all their instances.›

definition AC_axioms :: "('f, 'v) identity set" where
  "AC_axioms =
    {(s ⊕ (t ⊕ u), (s ⊕ t) ⊕ u) | s t u. True} ∪ {(s ⊕ t, t ⊕ s) | s t. True}"

abbreviation eq_AC :: "('f, 'v) term ⇒ ('f, 'v) term ⇒ bool" (infix ‹≈⇩A⇩C› 50)
  where "s ≈⇩A⇩C t ≡ eq_theory (AC_axioms :: ('f, 'v) identity set) s t"

text ‹AC is an instance of an equational theory, with identities ‹AC_axioms›.›

sublocale ac: equational_theory AC_axioms .

subsection ‹The axioms as derived rules›

lemma eq_AC_assoc: "s ⊕ (t ⊕ u) ≈⇩A⇩C (s ⊕ t) ⊕ u"
  using eq_theory.axiom[of "s ⊕ (t ⊕ u)" "(s ⊕ t) ⊕ u" AC_axioms Var]
  by (auto simp: AC_axioms_def)

lemma eq_AC_comm: "s ⊕ t ≈⇩A⇩C t ⊕ s"
  using eq_theory.axiom[of "s ⊕ t" "t ⊕ s" AC_axioms Var]
  by (auto simp: AC_axioms_def)

subsection ‹Sums of several terms›

text ‹
  ‹sum_terms [t⇩1, …, t⇩n]› is the term ‹t⇩1 + … + t⇩n›, associated to the right. It is only
  meaningful for non-empty lists. Modulo AC the chosen association does not matter.
›

fun sum_terms :: "('f, 'v) term list ⇒ ('f, 'v) term" where
  "sum_terms [] = undefined"
| "sum_terms [t] = t"
| "sum_terms (t # u # ts) = t ⊕ sum_terms (u # ts)"

lemma sum_terms_subst:
  "ts ≠ [] ⟹ sum_terms ts ⋅ σ = sum_terms (map (λt. t ⋅ σ) ts)"
  by (induction ts rule: sum_terms.induct) auto

lemma vars_sum_terms:
  "ts ≠ [] ⟹ vars_term (sum_terms ts) = (⋃t ∈ set ts. vars_term t)"
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

text ‹Sanity check: the generic facts are available for AC.›

lemma "s ≈⇩A⇩C t ⟹ s ⋅ σ ≈⇩A⇩C t ⋅ σ" for σ :: "('f, 'v) subst"
  by (rule eq_theory_subst)

end

end
