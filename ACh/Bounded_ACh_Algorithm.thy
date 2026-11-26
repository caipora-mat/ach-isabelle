(*
Author: Guilherme Borges Brandão
*)

theory Bounded_ACh_Algorithm
  imports Bounded_ACh_Termination Bounded_ACh_Completeness
begin

section ‹A recursive, executable version of the algorithm›

text ‹
  The function ‹unify› below implements the strategy of the termination proof: flattening,
  closing ‹Δ›, merging the equations ‹X =⇧? Y›, then the macro steps until no variable heads two
  equations, and finally variable elimination. It works on lists; ‹abst› maps a list triple to a
  triple of the rule system. Its result is the list of leaves of a derivation, all irreducible.
›

datatype ('g, 'w) rkind = KH 'w | KSum "'w list" | KFree 'g "'w list" | KOther

subsection ‹Derivations with alternatives›

text ‹
  Two list triples with the same abstraction may be processed differently, so the leaves of the
  computed derivation form a union of derivation trees. ‹gtree› allows such unions; every
  ‹gtree› contains a ‹tree›, so soundness and completeness carry over.
›

context bounded_ach
begin

inductive gtree :: "('f, 'v) triple ⇒ ('f, 'v) triple set ⇒ bool" where
  leaf: "gtree S {S}"
| node: "⟦S ↝ Ss; ⋀S'. S' ∈ Ss ⟹ gtree S' (L S')⟧ ⟹ gtree S (⋃S' ∈ Ss. L S')"
| union: "⟦gtree S L1; gtree S L2⟧ ⟹ gtree S (L1 ∪ L2)"

lemma gtree_tree: "gtree S L ⟹ ∃L' ⊆ L. tree S L'"
proof (induction rule: gtree.induct)
  case (leaf S)
  then show ?case
    using tree.leaf by blast
next
  case (node S Ss L)
  then obtain M where M: "⋀S'. S' ∈ Ss ⟹ M S' ⊆ L S' ∧ tree S' (M S')"
    by metis
  then have "tree S (⋃S' ∈ Ss. M S')"
    using tree.node[OF node.hyps(1)] by blast
  moreover have "(⋃S' ∈ Ss. M S') ⊆ (⋃S' ∈ Ss. L S')"
    using M by blast
  ultimately show ?case
    by blast
next
  case (union S L1 L2)
  then show ?case
    by blast
qed

lemma gtree_steps: "gtree S L ⟹ T ∈ L ⟹ S ↝⇧* T"
proof (induction arbitrary: T rule: gtree.induct)
  case (node S Ss L)
  then obtain S' where "S' ∈ Ss" "T ∈ L S'"
    by blast
  then show ?case
    using node.IH node.hyps(1) by (meson converse_rtranclp_into_rtranclp step_one_def)
qed auto

lemma gtree_trans:
  assumes "gtree S L" and "⋀T. T ∈ L ⟹ gtree T (F T)"
  shows "gtree S (⋃T ∈ L. F T)"
  using assms
proof (induction rule: gtree.induct)
  case (leaf S)
  then show ?case
    by simp
next
  case (node S Ss L)
  have "gtree S (⋃S' ∈ Ss. ⋃T ∈ L S'. F T)"
    by (rule gtree.node[OF node.hyps(1)]) (use node in blast)
  then show ?case
    by (simp add: UN_UN_flatten)
next
  case (union S L1 L2)
  then show ?case
    using gtree.union[of S "⋃T ∈ L1. F T" "⋃T ∈ L2. F T"] by simp
qed

lemma gtree_Union:
  assumes "Ls ≠ []" and "⋀L. L ∈ set Ls ⟹ gtree S L"
  shows "gtree S (⋃ (set Ls))"
  using assms
proof (induction Ls)
  case (Cons L Ls)
  then show ?case
    by (cases "Ls = []") (auto intro: gtree.union)
qed simp

end

subsection ‹The locale›

locale bounded_ach_alg = bounded_ach_term plus hom κ ac_unify arity
  for plus :: 'f and hom :: 'f and κ :: nat
    and ac_unify :: "'v set ⇒ ('f, 'v) problem ⇒ ('v × ('f, 'v) term) list list"
    and arity :: "'f ⇒ nat" +
  fixes fresh :: "'v list ⇒ 'v"
  assumes fresh: "fresh xs ∉ set xs"
begin

fun fresh_vars :: "nat ⇒ 'v list ⇒ 'v list" where
  "fresh_vars 0 xs = []"
| "fresh_vars (Suc n) xs = (let v = fresh xs in v # fresh_vars n (v # xs))"

lemma fresh_vars:
  shows "length (fresh_vars n xs) = n" and "set (fresh_vars n xs) ∩ set xs = {}"
    and "distinct (fresh_vars n xs)"
proof -
  show "length (fresh_vars n xs) = n"
    by (induction n arbitrary: xs) (simp_all add: Let_def)
  show disj: "set (fresh_vars n xs) ∩ set xs = {}" for n xs
  proof (induction n arbitrary: xs)
    case (Suc n)
    have "set (fresh_vars n (fresh xs # xs)) ∩ set (fresh xs # xs) = {}"
      by (rule Suc.IH)
    then show ?case
      using fresh[of xs] by (auto simp: Let_def)
  qed simp
  show "distinct (fresh_vars n xs)"
  proof (induction n arbitrary: xs)
    case (Suc n)
    then show ?case
      using disj[of n "fresh xs # xs"] by (auto simp: Let_def)
  qed simp
qed

subsection ‹List triples›

type_synonym ('g, 'w) ltriple =
  "('g, 'w) equation list × ('w × nat) list × ('w × ('g, 'w) term) list"

fun abst :: "('f, 'v) ltriple ⇒ ('f, 'v) triple" where
  "abst (Γ, Δ, σ) = (mset Γ, map_of Δ, set σ)"

fun vars_tl :: "('f, 'v) term ⇒ 'v list" where
  "vars_tl (Var x) = [x]"
| "vars_tl (Fun f ts) = concat (map vars_tl ts)"

lemma set_vars_tl [simp]: "set (vars_tl t) = vars_term t"
  by (induction t) auto

fun used :: "('f, 'v) ltriple ⇒ 'v list" where
  "used (Γ, Δ, σ) = concat (map (λ(s, t). vars_tl s @ vars_tl t) Γ) @ map fst Δ @
    concat (map (λ(x, t). x # vars_tl t) σ)"

lemma vars_problem_list:
  "set (concat (map (λ(s, t). vars_tl s @ vars_tl t) Γ)) = vars_problem (mset Γ)"
  by (induction Γ) (auto split: prod.splits)

lemma vars_bindings_list:
  "set (concat (map (λ(x, t). x # vars_tl t) σ)) = vars_bindings (set σ)"
  by (induction σ) (auto simp: vars_bindings_def split: prod.splits)

lemma set_used: "set (used S) = vars_triple (abst S)"
proof (cases S)
  case (fields Γ Δ σ)
  then show ?thesis
    using vars_problem_list[of Γ] vars_bindings_list[of σ]
    by (simp add: dom_map_of_conv_image_fst Un_assoc)
qed

text ‹‹lsteps S Ls›: the abstractions of ‹Ls› are the leaves of a derivation from ‹S›.›

definition lsteps :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list ⇒ bool" where
  "lsteps S Ls ⟷ gtree (abst S) (abst ` set Ls)"

lemma lsteps_refl: "lsteps S [S]"
  by (simp add: lsteps_def gtree.leaf)

lemma lsteps_bind:
  assumes "lsteps S Ls" and "⋀S'. S' ∈ set Ls ⟹ lsteps S' (f S')"
  shows "lsteps S (concat (map f Ls))"
proof -
  define F where "F T = (⋃S' ∈ {S' ∈ set Ls. abst S' = T}. abst ` set (f S'))" for T
  have "gtree T (F T)" if "T ∈ abst ` set Ls" for T
  proof -
    let ?Ls = "map (λS'. abst ` set (f S')) (filter (λS'. abst S' = T) Ls)"
    have eq: "F T = ⋃ (set ?Ls)"
      unfolding F_def by auto
    have "?Ls ≠ []"
      using that by (auto simp: filter_empty_conv)
    moreover have "gtree T L" if L: "L ∈ set ?Ls" for L
    proof -
      obtain S' where "S' ∈ set Ls" "abst S' = T" "L = abst ` set (f S')"
        using L by auto
      then show ?thesis
        using assms(2) unfolding lsteps_def by metis
    qed
    ultimately show ?thesis
      unfolding eq by (rule gtree_Union)
  qed
  then have "gtree (abst S) (⋃T ∈ abst ` set Ls. F T)"
    using gtree_trans assms(1) unfolding lsteps_def by blast
  moreover have "(⋃T ∈ abst ` set Ls. F T) = abst ` set (concat (map f Ls))"
    unfolding F_def by auto
  ultimately show ?thesis
    unfolding lsteps_def by simp
qed

lemma lsteps_step:
  assumes "abst S ↝ abst ` set Ss" and "⋀S'. S' ∈ set Ss ⟹ lsteps S' (f S')"
  shows "lsteps S (concat (map f Ss))"
proof (rule lsteps_bind[OF _ assms(2)])
  have "gtree (abst S) (⋃T ∈ abst ` set Ss. {T})"
    by (rule gtree.node[OF assms(1)]) (rule gtree.leaf)
  then show "lsteps S Ss"
    unfolding lsteps_def by simp
qed

lemma lsteps_single: "abst S ↝ {abst S'} ⟹ lsteps S' Ls ⟹ lsteps S Ls"
  using lsteps_step[of S "[S']" "λ_. Ls"] by simp

lemma lsteps_fail: "abst S ↝ {} ⟹ lsteps S []"
  using lsteps_step[of S "[]"] by simp

lemma lsteps_concat:
  "lsteps S Ls ⟹ (⋀S'. S' ∈ set Ls ⟹ lsteps S' (f S')) ⟹ lsteps S (concat (map f Ls))"
  by (rule lsteps_bind)

subsection ‹Closing ‹Δ››

fun sum_vars :: "('f, 'v) term ⇒ 'v list option" where
  "sum_vars (Var y) = Some [y]"
| "sum_vars (Fun f [Var y, t]) = (if f = plus then map_option (Cons y) (sum_vars t) else None)"
| "sum_vars (Fun f ts) = None"

lemma sum_vars_Some: "sum_vars t = Some ys ⟹ ys ≠ [] ∧ t = sum_terms (map Var ys)"
proof (induction t arbitrary: ys rule: sum_vars.induct)
  case (2 f y t)
  then obtain zs where zs: "sum_vars t = Some zs" "ys = y # zs" "f = plus"
    by (auto split: if_splits)
  then have "zs ≠ []" "t = sum_terms (map Var zs)"
    using 2 by auto
  then show ?case
    using zs by (cases zs) auto
qed auto

lemma sum_vars_sum_terms: "ys ≠ [] ⟹ sum_vars (sum_terms (map Var ys)) = Some ys"
  by (induction ys rule: induct_list012) auto

fun h_target :: "('f, 'v) term ⇒ 'v option" where
  "h_target (Fun f [Var y]) = (if f = hom then Some y else None)"
| "h_target t = None"

lemma h_target_Some: "h_target t = Some y ⟷ t = H (Var y)"
  by (induction t rule: h_target.induct) auto

lemma h_target_Some': "Some y = h_target t ⟷ t = H (Var y)"
  using h_target_Some by metis

fun eq_edges :: "('f, 'v) equation ⇒ ('v × 'v × nat) list" where
  "eq_edges (Var x, t) = (case h_target t of Some y ⇒ [(x, y, 1)] | None ⇒ []) @
    (case sum_vars t of Some ys ⇒ map (λy. (x, y, 0)) ys | None ⇒ [])"
| "eq_edges (Fun f ss, t) = []"

lemma eq_edges_iff:
  "(a, b, i) ∈ set (eq_edges e) ⟷
    (e = (Var a, H (Var b)) ∧ i = 1) ∨ (∃ys. e = (Var a, sum_terms (map Var ys)) ∧ b ∈ set ys ∧ i = 0)"
proof (cases e rule: eq_edges.cases)
  case (1 x t)
  show ?thesis
  proof
    assume "(a, b, i) ∈ set (eq_edges e)"
    then show "(e = (Var a, H (Var b)) ∧ i = 1) ∨
        (∃ys. e = (Var a, sum_terms (map Var ys)) ∧ b ∈ set ys ∧ i = 0)"
      using 1 h_target_Some'[of _ t] sum_vars_Some[of t]
      by (auto split: option.splits)
  next
    assume "(e = (Var a, H (Var b)) ∧ i = 1) ∨
        (∃ys. e = (Var a, sum_terms (map Var ys)) ∧ b ∈ set ys ∧ i = 0)"
    then show "(a, b, i) ∈ set (eq_edges e)"
    proof
      assume "e = (Var a, H (Var b)) ∧ i = 1"
      then show ?thesis
        using 1 by simp
    next
      assume "∃ys. e = (Var a, sum_terms (map Var ys)) ∧ b ∈ set ys ∧ i = 0"
      then obtain ys where ys: "e = (Var a, sum_terms (map Var ys))" "b ∈ set ys" "i = 0"
        by blast
      then have "ys ≠ []"
        by auto
      then show ?thesis
        using ys 1 sum_vars_sum_terms by (auto split: option.splits)
    qed
  qed
qed auto

lemma edge_list: "edge (mset Γ) a b i ⟷ (a, b, i) ∈ set (concat (map eq_edges Γ))"
proof -
  have "(a, b, i) ∈ set (concat (map eq_edges Γ)) ⟷ (∃e ∈ set Γ. (a, b, i) ∈ set (eq_edges e))"
    by simp
  also have "… ⟷ edge (mset Γ) a b i"
    unfolding edge_def eq_edges_iff by auto
  finally show ?thesis ..
qed

lemma eq_edges_le1: "(a, b, i) ∈ set (concat (map eq_edges Γ)) ⟹ i ≤ 1"
  by (auto simp: eq_edges_iff)

definition bounded_l :: "('v × nat) list ⇒ bool" where
  "bounded_l Δ ⟷ (∀x ∈ set (map fst Δ). dep (map_of Δ) x ≤ κ)"

lemma bounded_l_iff: "bounded_l Δ ⟷ bounded_depths (map_of Δ)"
proof
  assume B: "bounded_l Δ"
  show "bounded_depths (map_of Δ)"
    unfolding bounded_depths_def
  proof (intro allI impI)
    fix x d
    assume "map_of Δ x = Some d"
    then have "x ∈ set (map fst Δ)" "dep (map_of Δ) x = d"
      by (auto dest: map_of_SomeD intro: rev_image_eqI)
    then show "d ≤ κ"
      using B unfolding bounded_l_def by auto
  qed
next
  assume "bounded_depths (map_of Δ)"
  then show "bounded_l Δ"
    unfolding bounded_l_def by (simp add: dep_le_kappa)
qed

definition viol :: "('v × nat) list ⇒ 'v × 'v × nat ⇒ bool" where
  "viol Δ e ⟷ (case e of (x, y, i) ⇒ x ∈ set (map fst Δ) ∧ y ∈ set (map fst Δ) ∧
    dep (map_of Δ) y < dep (map_of Δ) x + i)"

function close_fun :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list" where
  "close_fun (Γ, Δ, σ) = (if ¬ bounded_l Δ then [] else
    (case find (viol Δ) (concat (map eq_edges Γ)) of
      None ⇒ [(Γ, Δ, σ)]
    | Some (x, y, i) ⇒ close_fun (Γ, (y, dep (map_of Δ) x + i) # Δ, σ)))"
  by pat_completeness auto
termination
proof (relation "measure (λ(Γ, Δ, σ). potential (map_of Δ))")
  fix Γ :: "('f, 'v) equation list" and Δ :: "('v × nat) list"
    and σ :: "('v × ('f, 'v) term) list" and e x yi y i
  assume b: "¬ ¬ bounded_l Δ" and f: "find (viol Δ) (concat (map eq_edges Γ)) = Some e"
    and e: "(x, yi) = e" "(y, i) = yi"
  have mem: "(x, y, i) ∈ set (concat (map eq_edges Γ))" and v: "viol Δ (x, y, i)"
    using f e[symmetric] by (auto simp: find_Some_iff dest: nth_mem)
  have "dep (map_of Δ) x ≤ κ" "i ≤ 1"
    using b v eq_edges_le1[OF mem] by (auto simp: bounded_l_def viol_def)
  then have "potential ((map_of Δ)(y ↦ dep (map_of Δ) x + i)) < potential (map_of Δ)"
    using v by (intro potential_upd) (auto simp: viol_def dom_map_of_conv_image_fst)
  then show "((Γ, (y, dep (map_of Δ) x + i) # Δ, σ), Γ, Δ, σ) ∈
      measure (λ(Γ, Δ, σ). potential (map_of Δ))"
    by simp
qed simp

declare close_fun.simps [simp del]

lemma close_fun_shape: "S' ∈ set (close_fun (Γ, Δ, σ)) ⟹ ∃Δ'. S' = (Γ, Δ', σ)"
proof (induction "(Γ, Δ, σ)" arbitrary: Γ Δ σ rule: close_fun.induct)
  case (1 Γ Δ σ)
  then show ?case
    by (subst (asm) close_fun.simps) (auto split: if_splits option.splits)
qed

text ‹‹close_fun› computes what ‹update_closure› promises.›

lemma close_fun_spec:
  assumes "vars_problem (mset Γ) ⊆ dom (map_of Δ)" and "prot L (mset Γ) (map_of Δ)"
  shows "lsteps (Γ, Δ, σ) (close_fun (Γ, Δ, σ)) ∧
    (∀S' ∈ set (close_fun (Γ, Δ, σ)). ∃Δ'. S' = (Γ, Δ', σ) ∧
      close_post L (mset Γ) (map_of Δ) (map_of Δ'))"
  using assms
proof (induction "(Γ, Δ, σ)" arbitrary: Γ Δ σ rule: close_fun.induct)
  case (1 Γ Δ σ)
  show ?case
  proof (cases "bounded_l Δ")
    case False
    then have "close_fun (Γ, Δ, σ) = []"
      by (simp add: close_fun.simps)
    moreover have "lsteps (Γ, Δ, σ) []"
      using step.BC[of "map_of Δ" "mset Γ" "set σ"] False
      by (intro lsteps_fail) (simp add: bounded_l_iff)
    ultimately show ?thesis
      by simp
  next
    case bnd: True
    show ?thesis
    proof (cases "find (viol Δ) (concat (map eq_edges Γ))")
      case None
      then have res: "close_fun (Γ, Δ, σ) = [(Γ, Δ, σ)]"
        using bnd by (simp add: close_fun.simps)
      have "closed (mset Γ) (map_of Δ)"
        unfolding closed_def
      proof (intro allI impI)
        fix a b i
        assume e: "edge (mset Γ) a b i"
        then have "a ∈ dom (map_of Δ)" "b ∈ dom (map_of Δ)"
          using edge_vars(1,2)[OF e] 1(2) by auto
        moreover have "¬ viol Δ (a, b, i)"
          using None e unfolding edge_list find_None_iff by blast
        ultimately show "dep (map_of Δ) a + i ≤ dep (map_of Δ) b"
          by (auto simp: viol_def dom_map_of_conv_image_fst)
      qed
      then show ?thesis
        unfolding res using bnd lsteps_refl by (auto simp: close_post_def bounded_l_iff)
    next
      case (Some e)
      obtain x y i where e: "e = (x, y, i)"
        by (cases e)
      have mem: "(x, y, i) ∈ set (concat (map eq_edges Γ))" and v: "viol Δ (x, y, i)"
        using Some e by (auto simp: find_Some_iff dest: nth_mem)
      have ed: "edge (mset Γ) x y i"
        using mem edge_list by blast
      let ?n = "dep (map_of Δ) x + i"
      have xy: "x ∈ dom (map_of Δ)" "y ∈ dom (map_of Δ)" and lt: "dep (map_of Δ) y < ?n"
        using v by (auto simp: viol_def dom_map_of_conv_image_fst)
      have res: "close_fun (Γ, Δ, σ) = close_fun (Γ, (y, ?n) # Δ, σ)"
        using bnd Some e by (subst close_fun.simps) simp
      have step: "abst (Γ, Δ, σ) ↝ {abst (Γ, (y, ?n) # Δ, σ)}"
        using edge_step[OF ed dom_dep[OF xy(1)] dom_dep[OF xy(2)] lt] by simp
      have IH: "lsteps (Γ, (y, ?n) # Δ, σ) (close_fun (Γ, (y, ?n) # Δ, σ)) ∧
          (∀S' ∈ set (close_fun (Γ, (y, ?n) # Δ, σ)). ∃Δ'. S' = (Γ, Δ', σ) ∧
            close_post L (mset Γ) (map_of ((y, ?n) # Δ)) (map_of Δ'))"
      proof (rule 1(1)[of "(x, y, i)" x "(y, i)" y i])
        show "¬ ¬ bounded_l Δ"
          using bnd by simp
        show "find (viol Δ) (concat (map eq_edges Γ)) = Some (x, y, i)"
          using Some e by simp
        show "vars_problem (mset Γ) ⊆ dom (map_of ((y, ?n) # Δ))"
          using 1(2) by auto
        show "prot L (mset Γ) (map_of ((y, ?n) # Δ))"
          using prot_upd[OF 1(3) ed lt] by simp
      qed simp_all
      have y_prot: "y ∈ lhs_vars (mset Γ) ⟹ L ≤ dep (map_of Δ) y"
        using 1(3) ed lt unfolding prot_def by force
      have post: "close_post L (mset Γ) (map_of Δ) Δ'"
        if "close_post L (mset Γ) ((map_of Δ)(y ↦ ?n)) Δ'" for Δ'
      proof -
        have props: "closed (mset Γ) Δ'" "bounded_depths Δ'" "dom Δ' = dom ((map_of Δ)(y ↦ ?n))"
          "∀z. dep ((map_of Δ)(y ↦ ?n)) z ≤ dep Δ' z"
          "∀z ∈ lhs_vars (mset Γ). dep ((map_of Δ)(y ↦ ?n)) z < L ⟶ Δ' z = ((map_of Δ)(y ↦ ?n)) z"
          using that unfolding close_post_def by blast+
        have "dom Δ' = dom (map_of Δ)"
          using props(3) xy(2) by auto
        moreover have "dep (map_of Δ) z ≤ dep Δ' z" for z
          using props(4)[rule_format, of z] lt by (auto simp: dep_upd split: if_splits)
        moreover have "Δ' z = map_of Δ z" if "z ∈ lhs_vars (mset Γ)" "dep (map_of Δ) z < L" for z
        proof -
          have "z ≠ y"
            using y_prot that by fastforce
          then show ?thesis
            using props(5) that by (simp add: dep_upd)
        qed
        ultimately show ?thesis
          using props(1,2) unfolding close_post_def by blast
      qed
      show ?thesis
        unfolding res using lsteps_single[OF step] IH post by auto
    qed
  qed
qed

subsection ‹Merging the equations ‹X =⇧? Y››

text ‹The facts behind one merge, as in ‹merge_step›.›

lemma merge_facts:
  assumes pn: "pnormal (Γ, Δ, σ)" and mem: "(Var x, Var y) ∈# Γ" and "x ≠ y"
  defines "Γ' ≡ image_mset (rename_eq (ren x y)) (Γ - {#(Var x, Var y)#})"
  shows "vars_problem Γ' ⊆ dom Δ" and "prot (dep Δ x) Γ' Δ" and "dep Δ x ≤ dep Δ y"
    and "⋀Δ' σ'. close_post (dep Δ x) Γ' Δ Δ' ⟹ finite σ' ⟹ pnormal (Γ', Δ', σ')"
proof -
  let ?Γ0 = "Γ - {#(Var x, Var y)#}"
  have flat0: "flat_problem ?Γ0" and closed: "closed Γ Δ"
    using pn by (auto dest: in_diffD)
  show xy: "dep Δ x ≤ dep Δ y"
    using closed edge_vv[OF mem] unfolding closed_def by fastforce
  show cover: "vars_problem Γ' ⊆ dom Δ"
  proof -
    have "vars_problem Γ' ⊆ (vars_problem ?Γ0 - {x}) ∪ {y}"
      using vars_subst_problem_upd[of x "Var y" ?Γ0]
      by (simp add: Var_upd_ren subst_problem_rename Γ'_def)
    moreover have "vars_problem ?Γ0 ⊆ vars_problem Γ"
      by (rule vars_problem_mono) simp
    moreover have "y ∈ vars_problem Γ"
      using mem by (force simp: vars_problem_def)
    moreover have "vars_problem Γ ⊆ dom Δ"
      using pn by simp
    ultimately show ?thesis
      by blast
  qed
  show "prot (dep Δ x) Γ' Δ"
    unfolding prot_def
  proof (intro allI impI)
    fix a' b' i
    assume e': "edge Γ' a' b' i" and unsat: "dep Δ b' < dep Δ a' + i"
    obtain a b where e: "edge ?Γ0 a b i" and ab: "a' = ren x y a" "b' = ren x y b"
      using edge_rename[OF flat0 e'[unfolded Γ'_def]] by blast
    have sat: "dep Δ a + i ≤ dep Δ b"
      using closed edge_mono[OF e] unfolding closed_def by (meson diff_subset_eq_self)
    show "dep Δ x ≤ dep Δ a' ∧ (dep Δ b' < dep Δ x ⟶ b' ∉ lhs_vars Γ')"
      using sat unsat xy ab by (auto simp: ren_def split: if_splits)
  qed
  fix Δ' and σ' :: "('v × ('f, 'v) term) set"
  assume "close_post (dep Δ x) Γ' Δ Δ'" and "finite σ'"
  then show "pnormal (Γ', Δ', σ')"
    using pn cover flat_rename[OF flat0] unfolding close_post_def Γ'_def by auto
qed

definition is_vv :: "('f, 'v) equation ⇒ bool" where
  "is_vv e ⟷ is_Var (fst e) ∧ is_Var (snd e)"

lemma is_vv_iff: "is_vv e ⟷ vv_eq e"
  by (cases e) (auto simp: is_vv_def vv_eq_def is_Var_def)

lemma is_vv_rename: "is_vv (rename_eq r e) ⟷ is_vv e"
  by (cases e; cases "fst e"; cases "snd e") (auto simp: is_vv_def rename_eq_def)

lemma subst_bindings_list:
  "subst_bindings τ (set σ) = set (map (λ(z, u). (z, u ⋅ τ)) σ)"
  by (simp add: subst_bindings_def)

lemma length_filter_remove1_less:
  "x ∈ set xs ⟹ P x ⟹ length (filter P (remove1 x xs)) < length (filter P xs)"
  by (induction xs) auto

lemma length_filter_rename:
  "length (filter is_vv (map (rename_eq r) xs)) = length (filter is_vv xs)"
  by (induction xs) (simp_all add: is_vv_rename)

function merge_fun :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list" where
  "merge_fun (Γ, Δ, σ) = (case find is_vv Γ of
     None ⇒ [(Γ, Δ, σ)]
   | Some e ⇒ (let x = the_Var (fst e); y = the_Var (snd e); Γ0 = remove1 e Γ in
       if x = y then merge_fun (Γ0, Δ, σ)
       else concat (map merge_fun (close_fun (map (rename_eq (ren x y)) Γ0, Δ,
         (x, Var y) # map (λ(z, u). (z, u ⋅ Var(x := Var y))) σ)))))"
  by pat_completeness auto
termination
proof (relation "measure (λ(Γ, Δ, σ). length (filter is_vv Γ))", goal_cases)
  case 1
  show ?case
    by simp
next
  case (2 Γ Δ σ e x y Γ0)
  then show ?case
    using length_filter_remove1_less[of e Γ is_vv] by (auto simp: find_Some_iff dest: nth_mem)
next
  case (3 Γ Δ σ e x y Γ0 S')
  have "e ∈ set Γ" "is_vv e"
    using 3(1) by (auto simp: find_Some_iff dest: nth_mem)
  then show ?case
    using close_fun_shape[OF 3(6)] length_filter_remove1_less[of e Γ is_vv] 3(4)
    by (auto simp: comp_def is_vv_rename)
qed

declare merge_fun.simps [simp del]

text ‹‹merge_fun› computes what ‹vv_closure_basic› and ‹vv_closure› promise.›

definition merge_post ::
    "nat ⇒ ('f, 'v) problem ⇒ 'v depth_set ⇒ ('f, 'v) triple ⇒ bool" where
  "merge_post L Γ Δ S' ⟷ normal S' ∧ nfree (fst S') = nfree Γ ∧
    (merge_inv L Γ Δ ⟶ (∀i < L. tcounts S' i = counts Γ Δ i) ∧ le3 (tcounts S' L) (counts Γ Δ L))"

lemma merge_fun_spec:
  assumes "pnormal (abst (Γ, Δ, σ))"
  shows "lsteps (Γ, Δ, σ) (merge_fun (Γ, Δ, σ)) ∧
    (∀S' ∈ set (merge_fun (Γ, Δ, σ)). merge_post L (mset Γ) (map_of Δ) (abst S'))"
  using assms
proof (induction "(Γ, Δ, σ)" arbitrary: Γ Δ σ rule: merge_fun.induct)
  case (1 Γ Δ σ)
  have pn: "pnormal (mset Γ, map_of Δ, set σ)"
    using 1(3) by simp
  show ?case
  proof (cases "find is_vv Γ")
    case None
    then have res: "merge_fun (Γ, Δ, σ) = [(Γ, Δ, σ)]"
      by (simp add: merge_fun.simps)
    have "∀e ∈ set Γ. ¬ vv_eq e"
      using None by (metis find_None_iff is_vv_iff)
    then have "nvv (mset Γ) = 0"
      by (simp add: nvv_def)
    then show ?thesis
      unfolding res using pn lsteps_refl by (simp add: merge_post_def)
  next
    case (Some e)
    have e: "e ∈ set Γ" "is_vv e"
      using Some by (auto simp: find_Some_iff dest: nth_mem)
    obtain x y where exy: "e = (Var x, Var y)"
      using e(2) unfolding is_vv_def by (metis is_Var_def prod.collapse)
    let ?Γ0 = "remove1 e Γ"
    have Γm: "mset Γ = add_mset (Var x, Var y) (mset ?Γ0)"
      using e(1) exy by simp
    have vv: "vv_eq (Var x, Var y)"
      by (simp add: vv_eq_def)
    have flat0: "flat_problem (mset ?Γ0)"
      using pn Γm by (metis pnormal.simps pnormal_sub)
    show ?thesis
    proof (cases "x = y")
      case True
      have res: "merge_fun (Γ, Δ, σ) = merge_fun (?Γ0, Δ, σ)"
        using Some exy True by (subst merge_fun.simps) simp
      have step: "abst (Γ, Δ, σ) ↝ {abst (?Γ0, Δ, σ)}"
        using step.Triv[of "Var y" "mset ?Γ0" "map_of Δ" "set σ"] True
        unfolding abst.simps Γm by simp
      have pn0: "pnormal (abst (?Γ0, Δ, σ))"
        using pnormal_sub[of "(Var x, Var y)" "mset ?Γ0" "map_of Δ" "set σ"] pn
        unfolding abst.simps Γm by blast
      have IH: "lsteps (?Γ0, Δ, σ) (merge_fun (?Γ0, Δ, σ)) ∧
          (∀S' ∈ set (merge_fun (?Γ0, Δ, σ)). merge_post L (mset ?Γ0) (map_of Δ) (abst S'))"
        by (rule 1(1)[of e x y ?Γ0]) (use Some exy True pn0 in simp_all)
      have eq: "nfree (mset ?Γ0) = nfree (mset Γ)"
        "counts (mset ?Γ0) (map_of Δ) = counts (mset Γ) (map_of Δ)"
        using remove_vv[OF vv, of "mset ?Γ0"] unfolding Γm by (simp_all add: counts_def fun_eq_iff)
      have inv: "merge_inv L (mset ?Γ0) (map_of Δ)" if "merge_inv L (mset Γ) (map_of Δ)"
        using merge_inv_Triv[of L y "mset ?Γ0" "map_of Δ"] that True unfolding Γm by simp
      show ?thesis
        unfolding res using lsteps_single[OF step] IH eq inv by (auto simp: merge_post_def)
    next
      case False
      let ?Γ' = "map (rename_eq (ren x y)) ?Γ0"
      let ?σ1 = "(x, Var y) # map (λ(z, u). (z, u ⋅ Var(x := Var y))) σ"
      let ?l = "dep (map_of Δ) x"
      have res: "merge_fun (Γ, Δ, σ) = concat (map merge_fun (close_fun (?Γ', Δ, ?σ1)))"
        using Some exy False by (subst merge_fun.simps) simp
      have mem: "(Var x, Var y) ∈# mset Γ"
        using e(1) exy by simp
      have Γ'eq: "mset ?Γ' = image_mset (rename_eq (ren x y)) (mset Γ - {#(Var x, Var y)#})"
        using exy by simp
      have sp: "subst_problem (Var(x := Var y)) (mset ?Γ0) = mset ?Γ'"
        by (simp add: Var_upd_ren subst_problem_rename)
      have step: "abst (Γ, Δ, σ) ↝ {abst (?Γ', Δ, ?σ1)}"
        using step.VE1[OF False, of "mset ?Γ0" "map_of Δ" "set σ"]
        unfolding abst.simps Γm sp by (simp add: subst_bindings_list)
      note MF = merge_facts[OF pn mem False, folded Γ'eq]
      have CF: "lsteps (?Γ', Δ, ?σ1) (close_fun (?Γ', Δ, ?σ1)) ∧
          (∀S' ∈ set (close_fun (?Γ', Δ, ?σ1)). ∃Δ'. S' = (?Γ', Δ', ?σ1) ∧
            close_post ?l (mset ?Γ') (map_of Δ) (map_of Δ'))"
        using close_fun_spec[OF MF(1,2)] .
      have nf: "nfree (mset ?Γ') = nfree (mset Γ)"
        using nfree_rename[OF flat0] remove_vv(3)[OF vv, of "mset ?Γ0"] unfolding Γm by simp
      have sub: "lsteps S1 (merge_fun S1) ∧
          (∀S' ∈ set (merge_fun S1). merge_post L (mset Γ) (map_of Δ) (abst S'))"
        if S1: "S1 ∈ set (close_fun (?Γ', Δ, ?σ1))" for S1
      proof -
        obtain Δ1 where S1eq: "S1 = (?Γ', Δ1, ?σ1)"
          and cp: "close_post ?l (mset ?Γ') (map_of Δ) (map_of Δ1)"
          using CF S1 by blast
        have pn1: "pnormal (abst S1)"
          unfolding S1eq abst.simps by (rule MF(4)[OF cp finite_set])
        have IH: "lsteps (?Γ', Δ1, ?σ1) (merge_fun (?Γ', Δ1, ?σ1)) ∧
            (∀S' ∈ set (merge_fun (?Γ', Δ1, ?σ1)). merge_post L (mset ?Γ') (map_of Δ1) (abst S'))"
        proof (rule 1(2)[of e x y ?Γ0 ?Γ' Δ1 ?σ1])
          show "(?Γ', Δ1, ?σ1) ∈ set (close_fun (map (rename_eq (ren x y)) ?Γ0, Δ,
              (x, Var y) # map (λ(z, u). (z, u ⋅ Var(x := Var y))) σ))"
            using S1 S1eq by simp
          show "pnormal (abst (?Γ', Δ1, ?σ1))"
            using pn1 S1eq by simp
        qed (use Some exy False in simp_all)
        have mono: "∀z. dep (map_of Δ) z ≤ dep (map_of Δ1) z"
          and keep: "∀z ∈ lhs_vars (image_mset (rename_eq (ren x y)) (mset ?Γ0)).
            dep (map_of Δ) z < ?l ⟶ map_of Δ1 z = map_of Δ z"
          using cp by (simp_all add: close_post_def)
        have post: "merge_post L (mset Γ) (map_of Δ) T"
          if T: "merge_post L (mset ?Γ') (map_of Δ1) T" for T
        proof -
          have "merge_inv L (mset Γ) (map_of Δ) ⟹
              (∀i < L. tcounts T i = counts (mset Γ) (map_of Δ) i) ∧
              le3 (tcounts T L) (counts (mset Γ) (map_of Δ) L)"
          proof -
            assume inv: "merge_inv L (mset Γ) (map_of Δ)"
            note mc = merge_counts[OF Γm False flat0 MF(3) inv mono keep]
            have "merge_inv L (mset ?Γ') (map_of Δ1)"
              using mc(3) by simp
            then show ?thesis
              using T mc(1,2) le3_trans[OF _ mc(2)] by (simp add: merge_post_def)
          qed
          then show ?thesis
            using T nf by (simp add: merge_post_def)
        qed
        show ?thesis
          unfolding S1eq using IH post by blast
      qed
      have "lsteps (?Γ', Δ, ?σ1) (concat (map merge_fun (close_fun (?Γ', Δ, ?σ1))))"
        using lsteps_concat[of _ _ merge_fun] CF sub by blast
      then show ?thesis
        unfolding res using lsteps_single[OF step] sub by auto
    qed
  qed
qed

subsection ‹The final phase›

function final_fun :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list" where
  "final_fun ([], Δ, σ) = [([], Δ, σ)]"
| "final_fun ((s, t) # Γ, Δ, σ) = (case s of
     Var z ⇒ if t = Var z then final_fun (Γ, Δ, σ)
       else if z ∈ set (vars_tl t) then []
       else final_fun (map (λ(a, b). (a ⋅ Var(z := t), b ⋅ Var(z := t))) Γ, Δ,
         (z, t) # map (λ(x, u). (x, u ⋅ Var(z := t))) σ)
   | Fun f ss ⇒ [((s, t) # Γ, Δ, σ)])"
  by pat_completeness auto
termination
  by (relation "measure (λ(Γ, Δ, σ). length Γ)") auto

lemma subst_problem_list:
  "subst_problem τ (mset Γ) = mset (map (λ(a, b). (a ⋅ τ, b ⋅ τ)) Γ)"
  by (simp add: subst_problem_def)

text ‹‹final_fun› computes what ‹final_phase› promises.›

lemma final_fun_spec:
  assumes "∀e ∈ set Γ. is_Var (fst e)" and "∀x. lhs_count (mset Γ) x ≤ 1"
    and "bounded_depths (map_of Δ)"
  shows "lsteps (Γ, Δ, σ) (final_fun (Γ, Δ, σ)) ∧
    (∀S' ∈ set (final_fun (Γ, Δ, σ)). irreducible (abst S'))"
  using assms
proof (induction "(Γ, Δ, σ)" arbitrary: Γ Δ σ rule: final_fun.induct)
  case (1 Δ σ)
  then show ?case
    using lsteps_refl irreducible_solved by simp
next
  case (2 s t Γ Δ σ)
  obtain z where s: "s = Var z"
    using 2(3) by (auto simp: is_Var_def)
  have sub: "lhs_count (mset Γ) x ≤ 1" for x
    using 2(4)[rule_format, of x] by (simp split: if_splits)
  have z_once: "lhs_count (mset Γ) z = 0"
    using 2(4)[rule_format, of z] s by simp
  have lhsV: "∀e ∈ set Γ. is_Var (fst e)"
    using 2(3) by simp
  show ?case
  proof (cases "t = Var z")
    case True
    have step: "abst ((s, t) # Γ, Δ, σ) ↝ {abst (Γ, Δ, σ)}"
      using step.Triv[of "Var z" "mset Γ" "map_of Δ" "set σ"] s True by simp
    have IH: "lsteps (Γ, Δ, σ) (final_fun (Γ, Δ, σ)) ∧
        (∀S' ∈ set (final_fun (Γ, Δ, σ)). irreducible (abst S'))"
      using 2(1)[OF s True lhsV] sub 2(5) by blast
    show ?thesis
      using s True lsteps_single[OF step] IH by simp
  next
    case tz: False
    show ?thesis
    proof (cases "z ∈ vars_term t")
      case True
      then obtain f ts where t: "t = Fun f ts"
        using tz by (cases t) auto
      have "abst ((s, t) # Γ, Δ, σ) ↝ {}"
        using step.OC[of z f ts "mset Γ" "map_of Δ" "set σ"] True s t by simp
      then show ?thesis
        using s tz True lsteps_fail by simp
    next
      case z: False
      let ?τ = "Var(z := t)"
      let ?Γ' = "map (λ(a, b). (a ⋅ ?τ, b ⋅ ?τ)) Γ"
      let ?σ' = "(z, t) # map (λ(x, u). (x, u ⋅ ?τ)) σ"
      have step: "abst ((s, t) # Γ, Δ, σ) ↝ {abst (?Γ', Δ, ?σ')}"
        using step.VE2[OF z, of "mset Γ" "map_of Δ" "set σ"] s
        by (simp add: subst_problem_list subst_bindings_list)
      have lhs: "fst e' ⋅ ?τ = fst e'" if e': "e' ∈ set Γ" for e'
      proof -
        obtain w where w: "fst e' = Var w"
          using lhsV e' by (auto simp: is_Var_def)
        moreover have "w ≠ z"
        proof
          assume "w = z"
          then have "e' ∈# filter_mset (λe. fst e = Var z) (mset Γ)"
            using e' w by simp
          then show False
            using z_once by (simp add: lhs_count_def) (metis prod.collapse)
        qed
        ultimately show ?thesis
          by simp
      qed
      have lhsV': "∀e ∈ set ?Γ'. is_Var (fst e)"
        using lhs lhsV by auto
      have count: "lhs_count (mset ?Γ') x = lhs_count (mset Γ) x" for x
      proof -
        have "size (filter_mset (λe. fst e = Var x) (mset (map (λ(a, b). (a ⋅ ?τ, b ⋅ ?τ)) M))) =
            size (filter_mset (λe. fst e = Var x) (mset M))" if "∀e' ∈ set M. fst e' ⋅ ?τ = fst e'" for M
          using that by (induction M) (auto split: prod.splits)
        then show ?thesis
          using lhs by (simp add: lhs_count_def)
      qed
      have IH: "lsteps (?Γ', Δ, ?σ') (final_fun (?Γ', Δ, ?σ')) ∧
          (∀S' ∈ set (final_fun (?Γ', Δ, ?σ')). irreducible (abst S'))"
        using 2(2)[OF s tz] z lhsV' count sub 2(5) by simp
      show ?thesis
        using s tz z lsteps_single[OF step] IH by simp
    qed
  qed
qed

subsection ‹Flattening›

fun flat_one :: "'v list ⇒ ('f, 'v) equation ⇒ (('f, 'v) equation list × ('v × nat) list) option" where
  "flat_one us (Fun f ss, Fun g ts) =
    (let v = fresh us in Some ([(Var v, Fun f ss), (Var v, Fun g ts)], [(v, 0)]))"
| "flat_one us (Fun f ss, Var x) = Some ([(Var x, Fun f ss)], [])"
| "flat_one us (Var x, Var y) = None"
| "flat_one us (Var x, Fun f ts) =
    (if f = plus ∧ length ts = 2 then
       (if is_Fun (ts ! 0) then
          let v = fresh us in Some ([(Var x, Var v ⊕ ts ! 1), (Var v, ts ! 0)], [(v, 0)])
        else if is_Fun (ts ! 1) then
          let v = fresh us in Some ([(Var x, ts ! 0 ⊕ Var v), (Var v, ts ! 1)], [(v, 0)])
        else None)
     else if f = hom ∧ length ts = 1 then
       (if is_Fun (ts ! 0) then
          let v = fresh us in Some ([(Var x, H (Var v)), (Var v, ts ! 0)], [(v, 1)])
        else None)
     else if f ≠ plus ∧ f ≠ hom ∧ (∃u ∈ set ts. is_Fun u) then
       let vs = fresh_vars (length ts) us in
       Some ((Var x, Fun f (map Var vs)) # zip (map Var vs) ts, map (λv. (v, 0)) vs)
     else None)"

lemma map_of_const: "map_of (map (λv. (v, c)) vs) z = (if z ∈ set vs then Some c else None)"
  by (induction vs) auto

lemma map_of_zero_depths:
  "map_of (map (λv. (v, c)) vs @ Δ) = (map_of Δ)(vs [↦] replicate (length vs) c)"
proof
  fix z
  show "map_of (map (λv. (v, c)) vs @ Δ) z = ((map_of Δ)(vs [↦] replicate (length vs) c)) z"
    using map_upds_replicate[of "map_of Δ" vs c z] by (simp add: map_add_def map_of_const)
qed

text ‹One step of ‹flat_one› is a flattening step, or an (Orient) step.›

lemma flat_one_spec:
  assumes "flat_one us e = Some (new, d)" and "e ∈# Γ"
    and "vars_triple (Γ, map_of Δ, σ) ⊆ set us"
  shows "(Γ, map_of Δ, σ) ↝⇩F (mset new + (Γ - {#e#}), map_of (d @ Δ), σ) ∨
    ((Γ, map_of Δ, σ) ↝ {(mset new + (Γ - {#e#}), map_of (d @ Δ), σ)} ∧
      flat_measure (mset new + (Γ - {#e#})) = flat_measure Γ ∧
      fun_lhs (mset new + (Γ - {#e#})) < fun_lhs Γ ∧
      (ready (Γ, map_of Δ, σ) ⟶ ready (mset new + (Γ - {#e#}), map_of (d @ Δ), σ)))"
proof -
  obtain Γ0 where Γ: "Γ = add_mset e Γ0"
    using assms(2) by (metis insert_DiffM)
  have fr: "fresh us ∉ vars_triple (Γ, map_of Δ, σ)"
    using assms(3) fresh by blast
  obtain s t where e: "e = (s, t)"
    by (cases e)
  show ?thesis
  proof (cases s)
    case (Fun f ss)
    show ?thesis
    proof (cases t)
      case (Var x)
      then have "new = [(Var x, Fun f ss)]" "d = []"
        using assms(1) e Fun by simp_all
      then show ?thesis
        using step.Orient[of "Fun f ss" x Γ0 "map_of Δ" σ] Γ e Fun Var
        by (auto simp: add.commute)
    next
      case (Fun g ts)
      let ?v = "fresh us"
      have nd: "new = [(Var ?v, s), (Var ?v, t)]" "d = [(?v, 0)]"
        using assms(1) e ‹s = Fun f ss› Fun by (simp_all add: Let_def)
      have "(Γ, map_of Δ, σ) ↝⇩F
          (add_mset (Var ?v, s) (add_mset (Var ?v, t) Γ0), (map_of Δ)(?v ↦ 0), σ)"
        unfolding Γ e by (rule flat_step.FBS) (use ‹s = Fun f ss› Fun fr Γ e in auto)
      then show ?thesis
        using nd Γ by simp
    qed
  next
    case (Var x)
    show ?thesis
    proof (cases t)
      case (Var y)
      then show ?thesis
        using assms(1) e ‹s = Var x› by simp
    next
      case (Fun f ts)
      let ?v = "fresh us"
      consider (plus) "f = plus" "length ts = 2" | (hom) "f = hom" "length ts = 1"
        | (free) "¬ (f = plus ∧ length ts = 2)" "¬ (f = hom ∧ length ts = 1)"
        by blast
      then show ?thesis
      proof cases
        case plus
        then obtain t1 t2 where ts: "ts = [t1, t2]"
          by (auto simp: length_Suc_conv numeral_2_eq_2)
        show ?thesis
        proof (cases "is_Fun t1")
          case True
          have nd: "new = [(Var x, Var ?v ⊕ t2), (Var ?v, t1)]" "d = [(?v, 0)]"
            using assms(1) e ‹s = Var x› Fun plus ts True by (simp_all add: Let_def)
          have "(Γ, map_of Δ, σ) ↝⇩F
              (add_mset (s, Var ?v ⊕ t2) (add_mset (Var ?v, t1) Γ0), (map_of Δ)(?v ↦ 0), σ)"
            unfolding Γ e Fun plus ts by (rule flat_step.FL) (use True fr Γ e Fun plus ts in auto)
          then show ?thesis
            using nd Γ ‹s = Var x› by simp
        next
          case f1: False
          show ?thesis
          proof (cases "is_Fun t2")
            case True
            have nd: "new = [(Var x, t1 ⊕ Var ?v), (Var ?v, t2)]" "d = [(?v, 0)]"
              using assms(1) e ‹s = Var x› Fun plus ts True f1 by (simp_all add: Let_def)
            have "(Γ, map_of Δ, σ) ↝⇩F
                (add_mset (s, t1 ⊕ Var ?v) (add_mset (Var ?v, t2) Γ0), (map_of Δ)(?v ↦ 0), σ)"
              unfolding Γ e Fun plus ts by (rule flat_step.FR) (use True fr Γ e Fun plus ts in auto)
            then show ?thesis
              using nd Γ ‹s = Var x› by simp
          next
            case False
            then show ?thesis
              using assms(1) e ‹s = Var x› Fun plus ts f1 by simp
          qed
        qed
      next
        case hom
        then obtain t1 where ts: "ts = [t1]"
          by (auto simp: length_Suc_conv)
        show ?thesis
        proof (cases "is_Fun t1")
          case True
          have nd: "new = [(Var x, H (Var ?v)), (Var ?v, t1)]" "d = [(?v, 1)]"
            using assms(1) e ‹s = Var x› Fun hom ts True plus_neq_hom by (simp_all add: Let_def)
          have "(Γ, map_of Δ, σ) ↝⇩F
              (add_mset (s, H (Var ?v)) (add_mset (Var ?v, t1) Γ0), (map_of Δ)(?v ↦ 1), σ)"
            unfolding Γ e Fun hom ts by (rule flat_step.FU) (use True fr Γ e Fun hom ts in auto)
          then show ?thesis
            using nd Γ ‹s = Var x› by simp
        next
          case False
          then show ?thesis
            using assms(1) e ‹s = Var x› Fun hom ts plus_neq_hom by simp
        qed
      next
        case free
        let ?vs = "fresh_vars (length ts) us"
        have cond: "f ≠ plus" "f ≠ hom" "∃u ∈ set ts. is_Fun u"
          using assms(1) e ‹s = Var x› Fun free by (auto split: if_splits)
        have nd: "new = (Var x, Fun f (map Var ?vs)) # zip (map Var ?vs) ts"
          "d = map (λv. (v, 0)) ?vs"
          using assms(1) e ‹s = Var x› Fun free cond by (simp_all add: Let_def)
        have frs: "set ?vs ∩ vars_triple (Γ, map_of Δ, σ) = {}"
          using fresh_vars(2)[of "length ts" us] assms(3) by blast
        have "(Γ, map_of Δ, σ) ↝⇩F
            (add_mset (s, Fun f (map Var ?vs)) (mset (zip (map Var ?vs) ts) + Γ0),
              (map_of Δ)(?vs [↦] replicate (length ?vs) 0), σ)"
          unfolding Γ e Fun
          by (rule flat_step.FlFun) (use cond frs fresh_vars(1,3) Γ e Fun in auto)
        then show ?thesis
          using nd Γ ‹s = Var x› by (simp add: map_of_zero_depths add.assoc del: map_of_append)
      qed
    qed
  qed
qed

fun find_rule ::
    "'v list ⇒ ('f, 'v) equation list ⇒ (('f, 'v) equation list × ('v × nat) list) option" where
  "find_rule us [] = None"
| "find_rule us (e # es) = (case flat_one us e of
     Some (new, d) ⇒ Some (new @ es, d)
   | None ⇒ map_option (λ(es', d). (e # es', d)) (find_rule us es))"

lemma find_rule_Some:
  "find_rule us Γ = Some (Γ', d) ⟹
    ∃e new. e ∈ set Γ ∧ flat_one us e = Some (new, d) ∧ mset Γ' = mset new + (mset Γ - {#e#})"
proof (induction Γ arbitrary: Γ')
  case (Cons e es)
  show ?case
  proof (cases "flat_one us e")
    case None
    then obtain es' where es': "find_rule us es = Some (es', d)" "Γ' = e # es'"
      using Cons.prems by (auto split: option.splits)
    then obtain e' new where "e' ∈ set es" "flat_one us e' = Some (new, d)"
      "mset es' = mset new + (mset es - {#e'#})"
      using Cons.IH by blast
    then show ?thesis
      using es' by (intro exI[of _ e'] exI[of _ new]) (auto simp: add_mset_diff_bothsides)
  next
    case (Some a)
    then obtain new d' where nd: "flat_one us e = Some (new, d')"
      by (cases a) auto
    then have "Γ' = new @ es" "d' = d"
      using Cons.prems by simp_all
    then show ?thesis
      using nd by (intro exI[of _ e] exI[of _ new]) simp
  qed
qed simp

lemma find_rule_None: "find_rule us Γ = None ⟹ ∀e ∈ set Γ. flat_one us e = None"
  by (induction Γ) (auto split: option.splits)

lemma flat_one_None:
  assumes "arity_ok s" and "arity_ok t" and "flat_one us (s, t) = None"
  shows "flat_eq (s, t)"
proof (rule ccontr)
  assume nf: "¬ flat_eq (s, t)"
  from assms(1,2) nf show False
  proof (cases rule: nonflat_cases)
    case FBS
    then show ?thesis
      using assms(3) by (cases s; cases t) (auto simp: Let_def)
  next
    case (Orient x)
    then show ?thesis
      using assms(3) by (cases s) auto
  next
    case (FL x t1 t2)
    then show ?thesis
      using assms(3) by (auto simp: Let_def)
  next
    case (FR x t1 t2)
    then show ?thesis
      using assms(3) by (auto simp: Let_def split: if_splits)
  next
    case (FU x t1)
    then show ?thesis
      using assms(3) plus_neq_hom by (auto simp: Let_def)
  next
    case (FlFun x f ts)
    then show ?thesis
      using assms(3) by (auto simp: Let_def split: if_splits)
  qed
qed

function flatten :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple" where
  "flatten (Γ, Δ, σ) = (case find_rule (used (Γ, Δ, σ)) Γ of
     None ⇒ (Γ, Δ, σ)
   | Some (Γ', d) ⇒ flatten (Γ', d @ Δ, σ))"
  by pat_completeness auto
termination
proof (relation "inv_image (mult less_than <*lex*> less_than)
    (λ(Γ, Δ, σ). (flat_measure (mset Γ), fun_lhs (mset Γ)))", goal_cases)
  case 1
  show ?case
    by (intro wf_inv_image wf_lex_prod wf_mult wf_less_than)
next
  case (2 Γ Δ σ x2 Γ' d)
  then obtain e new where e: "e ∈ set Γ" "flat_one (used (Γ, Δ, σ)) e = Some (new, d)"
    "mset Γ' = mset new + (mset Γ - {#e#})"
    using find_rule_Some by metis
  have vs: "vars_triple (mset Γ, map_of Δ, set σ) ⊆ set (used (Γ, Δ, σ))"
    using set_used[of "(Γ, Δ, σ)"] by simp
  have e1: "e ∈# mset Γ"
    using e(1) by simp
  note F = flat_one_spec[OF e(2) e1 vs, folded e(3)]
  show ?case
    using F flat_step_decreases by fastforce
qed

declare flatten.simps [simp del]

lemma flatten_spec: "lsteps S [flatten S] ∧ (ready (abst S) ⟶ flat_ready (abst (flatten S)))"
proof (induction S rule: flatten.induct)
  case (1 Γ Δ σ)
  show ?case
  proof (cases "find_rule (used (Γ, Δ, σ)) Γ")
    case None
    have "ready (abst (Γ, Δ, σ)) ⟹ flat_problem (mset Γ)"
      using find_rule_None[OF None] flat_one_None
      by (auto simp: arity_ok_problem_def) (metis case_prodD)
    then show ?thesis
      using None lsteps_refl by (simp add: flatten.simps)
  next
    case (Some a)
    then obtain Γ' d where a: "a = (Γ', d)"
      by (cases a)
    obtain e new where e: "e ∈ set Γ" "flat_one (used (Γ, Δ, σ)) e = Some (new, d)"
      "mset Γ' = mset new + (mset Γ - {#e#})"
      using find_rule_Some Some a by metis
    have vs: "vars_triple (mset Γ, map_of Δ, set σ) ⊆ set (used (Γ, Δ, σ))"
      using set_used[of "(Γ, Δ, σ)"] by simp
    have e1: "e ∈# mset Γ"
      using e(1) by simp
    note F = flat_one_spec[OF e(2) e1 vs, folded e(3)]
    have res: "flatten (Γ, Δ, σ) = flatten (Γ', d @ Δ, σ)"
      using Some a by (simp add: flatten.simps)
    have step: "abst (Γ, Δ, σ) ↝ {abst (Γ', d @ Δ, σ)}"
      unfolding abst.simps using F flat_step_step by blast
    have rd: "ready (abst (Γ, Δ, σ)) ⟹ ready (abst (Γ', d @ Δ, σ))"
      unfolding abst.simps using F flat_step_ready by blast
    show ?thesis
      unfolding res using 1[OF Some a[symmetric]] lsteps_single[OF step] rd by blast
  qed
qed

subsection ‹Recognising flat equations›

text ‹The kind of the right-hand side of a flat equation ‹X =⇧? t›.›

definition kind :: "('f, 'v) term ⇒ ('f, 'v) rkind" where
  "kind t = (case h_target t of Some y ⇒ KH y | None ⇒
    (case sum_vars t of Some ys ⇒ if 2 ≤ length ys then KSum ys else KOther | None ⇒
      (case t of Fun f ts ⇒
          if f ≠ plus ∧ f ≠ hom ∧ list_all is_Var ts then KFree f (map the_Var ts) else KOther
        | Var y ⇒ KOther)))"

lemma sum_vars_H: "sum_vars (H t) = None"
  using plus_neq_hom by (cases t) auto

lemma h_target_sum: "2 ≤ length ys ⟹ h_target (sum_terms (map Var ys)) = None"
  using plus_neq_hom by (cases ys rule: remdups_adj.cases) auto

lemma kind_H [simp]: "kind (H (Var y)) = KH y"
  by (simp add: kind_def)

lemma kind_sum [simp]: "2 ≤ length ys ⟹ kind (sum_terms (map Var ys)) = KSum ys"
proof -
  assume l: "2 ≤ length ys"
  then have "ys ≠ []"
    by auto
  then show ?thesis
    using h_target_sum[OF l] sum_vars_sum_terms[of ys] l by (simp add: kind_def)
qed

lemma sum_vars_Fun: "f ≠ plus ⟹ sum_vars (Fun f ts) = None"
  by (cases "Fun f ts" rule: sum_vars.cases) auto

lemma map_Var_the_Var: "list_all is_Var ts ⟹ map Var (map the_Var ts) = ts"
  by (induction ts) (auto simp: is_Var_def)

lemma kind_free [simp]:
  "f ≠ plus ⟹ f ≠ hom ⟹ kind (Fun f (map Var ys)) = KFree f ys"
proof -
  assume f: "f ≠ plus" "f ≠ hom"
  have "h_target (Fun f (map Var ys)) = None"
    using f h_target_Some[of "Fun f (map Var ys)"] by (cases "h_target (Fun f (map Var ys))") auto
  moreover have "sum_vars (Fun f (map Var ys)) = None"
    using sum_vars_Fun[OF f(1)] .
  ultimately show ?thesis
    using f by (simp add: kind_def list_all_iff comp_def)
qed

lemma kind_KH: "kind t = KH y ⟹ t = H (Var y)"
  by (auto simp: kind_def h_target_Some split: option.splits if_splits term.splits)

lemma kind_KSum: "kind t = KSum ys ⟹ t = sum_terms (map Var ys) ∧ 2 ≤ length ys"
  using sum_vars_Some by (auto simp: kind_def split: option.splits if_splits term.splits)

lemma kind_KFree: "kind t = KFree f ys ⟹ t = Fun f (map Var ys) ∧ f ≠ plus ∧ f ≠ hom"
proof -
  assume k: "kind t = KFree f ys"
  then obtain ts where t: "t = Fun f ts" "f ≠ plus" "f ≠ hom" "list_all is_Var ts"
    "ys = map the_Var ts"
    by (auto simp: kind_def split: option.splits if_splits term.splits)
  then have "map Var ys = ts"
    using map_Var_the_Var by blast
  then show ?thesis
    using t by simp
qed

text ‹An executable test for ‹flat_eq›.›

definition flat_eqb :: "('f, 'v) equation ⇒ bool" where
  "flat_eqb e ⟷ is_Var (fst e) ∧ (case kind (snd e) of
     KOther ⇒ is_Var (snd e) | KFree f ys ⇒ length ys = arity f | _ ⇒ True)"

lemma flat_eqb_iff: "flat_eqb e ⟷ flat_eq e"
proof
  assume F: "flat_eqb e"
  then obtain x where x: "fst e = Var x"
    by (auto simp: flat_eqb_def is_Var_def)
  show "flat_eq e"
  proof (cases "kind (snd e)")
    case (KH y)
    then show ?thesis
      using x kind_KH[OF KH] by (cases e) (simp add: flat_eq_def h_eq_def)
  next
    case (KSum ys)
    then show ?thesis
      using x kind_KSum[OF KSum] by (cases e) (auto simp: flat_eq_def flat_sum_eq_def)
  next
    case (KFree f ys)
    then show ?thesis
      using x kind_KFree[OF KFree] F by (cases e) (auto simp: flat_eq_def free_eq_def flat_eqb_def)
  next
    case KOther
    then show ?thesis
      using x F by (cases e) (auto simp: flat_eq_def vv_eq_def flat_eqb_def is_Var_def)
  qed
next
  assume "flat_eq e"
  then show "flat_eqb e"
    unfolding flat_eq_def
  proof (elim disjE)
    assume "vv_eq e"
    then show ?thesis
      by (auto simp: vv_eq_def flat_eqb_def kind_def)
  next
    assume "h_eq e"
    then show ?thesis
      by (auto simp: h_eq_def flat_eqb_def)
  next
    assume "flat_sum_eq e"
    then show ?thesis
      by (auto simp: flat_sum_eq_def flat_eqb_def)
  next
    assume "free_eq e"
    then show ?thesis
      by (auto simp: free_eq_def flat_eqb_def)
  qed
qed

lemma flat_nonvv_kind:
  assumes "flat_eq (Var x, t)" and "¬ vv_eq (Var x, t)"
  shows "kind t ≠ KOther"
  using assms by (cases rule: flat_cases) auto

lemma free_kind:
  assumes "flat_eq (Var x, t)" and "kind t = KFree f ys"
  shows "free_eq (Var x, t)"
proof -
  have t: "t = Fun f (map Var ys)" "f ≠ plus" "f ≠ hom"
    using kind_KFree[OF assms(2)] by auto
  have "¬ vv_eq (Var x, t)"
    using t by (simp add: vv_eq_def)
  with assms(1) show ?thesis
  proof (cases rule: flat_cases)
    case (h y)
    then show ?thesis
      using t by simp
  next
    case (sum zs)
    then show ?thesis
      using t sum_terms_Fun[of zs] by auto
  next
    case (free g zs)
    then show ?thesis
      using t by (auto simp: free_eq_def)
  qed
qed

text ‹An executable test for ‹normal›.›

fun normal_l :: "('f, 'v) ltriple ⇒ bool" where
  "normal_l (Γ, Δ, σ) ⟷ list_all flat_eqb Γ ∧
    set (concat (map (λ(s, t). vars_tl s @ vars_tl t) Γ)) ⊆ set (map fst Δ) ∧
    list_all (λ(a, b, i). dep (map_of Δ) a + i ≤ dep (map_of Δ) b) (concat (map eq_edges Γ)) ∧
    bounded_l Δ ∧ ¬ list_ex is_vv Γ"

lemma normal_l_iff: "normal_l S ⟷ normal (abst S)"
proof (cases S)
  case (fields Γ Δ σ)
  have "closed (mset Γ) (map_of Δ) ⟷
      list_all (λ(a, b, i). dep (map_of Δ) a + i ≤ dep (map_of Δ) b) (concat (map eq_edges Γ))"
    unfolding closed_def edge_list list_all_iff by auto
  moreover have "nvv (mset Γ) = 0 ⟷ ¬ list_ex is_vv Γ"
    by (auto simp: nvv_def list_ex_iff is_vv_iff)
  ultimately show ?thesis
    using fields vars_problem_list[of Γ]
    by (auto simp: list_all_iff flat_eqb_iff bounded_l_iff dom_map_of_conv_image_fst)
qed

subsection ‹Variables heading two equations›

fun find_pair ::
    "('f, 'v) equation list ⇒ (('f, 'v) equation × ('f, 'v) equation × ('f, 'v) equation list) option"
  where
  "find_pair [] = None"
| "find_pair (e # es) = (case find (λe'. fst e' = fst e ∧ is_Var (fst e)) es of
     Some e' ⇒ Some (e, e', remove1 e' es)
   | None ⇒ map_option (λ(a, b, r). (a, b, e # r)) (find_pair es))"

lemma find_pair_Some:
  "find_pair Γ = Some (e1, e2, R) ⟹
    mset Γ = add_mset e1 (add_mset e2 (mset R)) ∧ fst e1 = fst e2 ∧ is_Var (fst e1)"
proof (induction Γ arbitrary: R)
  case (Cons e es)
  show ?case
  proof (cases "find (λe'. fst e' = fst e ∧ is_Var (fst e)) es")
    case None
    then obtain R' where "find_pair es = Some (e1, e2, R')" "R = e # R'"
      using Cons.prems by auto
    then show ?thesis
      using Cons.IH by (auto simp: add_mset_commute)
  next
    case (Some e')
    then have "e' ∈ set es" "fst e' = fst e" "is_Var (fst e)"
      by (auto simp: find_Some_iff dest: nth_mem)
    then show ?thesis
      using Cons.prems Some by auto
  qed
qed simp

lemma find_pair_None: "find_pair Γ = None ⟹ ∀x. lhs_count (mset Γ) x ≤ 1"
proof (induction Γ)
  case (Cons e es)
  then have none: "find (λe'. fst e' = fst e ∧ is_Var (fst e)) es = None" "find_pair es = None"
    by (auto split: option.splits)
  show ?case
  proof
    fix x
    show "lhs_count (mset (e # es)) x ≤ 1"
    proof (cases "fst e = Var x")
      case True
      then have "∀e' ∈ set es. fst e' ≠ Var x"
        using none(1) by (auto simp: find_None_iff)
      then have "lhs_count (mset es) x = 0"
        by (simp add: lhs_count_def)
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
        using Cons.IH[OF none(2)] by simp
    qed
  qed
qed (simp add: lhs_count_def)

text ‹The common end of the macro steps at a level, without derivations.›

lemma finish_pure:
  assumes "merge_post l Γ1 Δ1 S'" and "merge_inv l Γ1 Δ1" and "nfree Γ1 = nfree Γ"
    and "l ≤ κ" and "∀i < l. counts Γ1 Δ1 i = counts Γ Δ i"
    and "(counts Γ1 Δ1 l, counts Γ Δ l) ∈ R3"
  shows "normal S' ∧ (tmeasure S', tmeasure (Γ, Δ, σ)) ∈ term_rel"
proof -
  obtain Γ' Δ' σ' where S': "S' = (Γ', Δ', σ')"
    by (cases S')
  have P: "normal S'" "nfree Γ' = nfree Γ1" "∀i < l. counts Γ' Δ' i = counts Γ1 Δ1 i"
    "le3 (counts Γ' Δ' l) (counts Γ1 Δ1 l)"
    using assms(1,2) S' by (simp_all add: merge_post_def)
  have le: "le3 (counts Γ' Δ' l) (counts Γ1 Δ1 l)"
    using P(4) .
  have "(tmeasure (Γ', Δ', σ'), tmeasure (Γ, Δ, σ)) ∈ term_rel"
    using P(2,3) assms(3-5) R3_le3[OF le assms(6)] by (intro term_rel_level) auto
  then show ?thesis
    using P(1) S' by simp
qed

subsection ‹The macro steps›

definition macro_ok :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list ⇒ bool" where
  "macro_ok S Ss ⟷ lsteps S Ss ∧
    (∀S' ∈ set Ss. normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst S)) ∈ term_rel)"

lemma macro_ok_fail: "abst S ↝ {} ⟹ macro_ok S []"
  by (simp add: macro_ok_def lsteps_fail)

text ‹(Dec) on ‹X =⇧? h(Y)› and ‹X =⇧? h(Z)›, then merging.›

definition dec_h_fun :: "('f, 'v) ltriple ⇒ 'v ⇒ 'v ⇒ 'v ⇒ ('f, 'v) equation list ⇒
    ('f, 'v) ltriple list" where
  "dec_h_fun S x y z R = (case S of (Γ, Δ, σ) ⇒
    merge_fun ((Var y, Var z) # (Var x, H (Var y)) # R, Δ, σ))"

lemma dec_h_fun_ok:
  assumes N: "normal (abst (Γ, Δ, σ))"
    and Γ: "mset Γ = add_mset (Var x, H (Var y)) (add_mset (Var x, H (Var z)) (mset R))"
    and yz: "dep (map_of Δ) y ≤ dep (map_of Δ) z"
  shows "macro_ok (Γ, Δ, σ) (dec_h_fun (Γ, Δ, σ) x y z R)"
proof -
  let ?T = "((Var y, Var z) # (Var x, H (Var y)) # R, Δ, σ)"
  let ?l = "dep (map_of Δ) x"
  note F = dec_h_facts[OF N[unfolded abst.simps] Γ yz]
  have step: "abst (Γ, Δ, σ) ↝ {abst ?T}"
    using F(1) Γ by simp
  have pn: "pnormal (abst ?T)"
    using F(2) by simp
  note M = merge_fun_spec[OF pn, of ?l]
  have "normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel"
    if "S' ∈ set (merge_fun ?T)" for S'
    using finish_pure[of ?l "add_mset (Var y, Var z) (add_mset (Var x, H (Var y)) (mset R))"
        "map_of Δ" "abst S'" "mset Γ" "map_of Δ" "set σ"] M that F(3-7) Γ by simp
  then show ?thesis
    unfolding macro_ok_def dec_h_fun_def using lsteps_single[OF step] M by simp
qed

text ‹(Split) on ‹X =⇧? h(Y)› and ‹X =⇧? X⇩1 + ⋯ + X⇩n›, or failure by (OC).›

definition split_fun :: "('f, 'v) ltriple ⇒ 'v ⇒ 'v ⇒ 'v list ⇒ ('f, 'v) equation list ⇒
    ('f, 'v) ltriple list" where
  "split_fun S x y xs R = (case S of (Γ, Δ, σ) ⇒
    if x = y ∨ x ∈ set xs then [] else
    (let vs = fresh_vars (length xs) (used S) in
     close_fun ((Var x, H (Var y)) # (Var y, sum_terms (map Var vs)) #
       map2 (λa v. (Var a, H (Var v))) xs vs @ R, map (λv. (v, 1)) vs @ Δ, σ)))"

lemma split_fun_ok:
  assumes N: "normal (abst (Γ, Δ, σ))"
    and Γ: "mset Γ = add_mset (Var x, H (Var y)) (add_mset (Var x, sum_terms (map Var xs)) (mset R))"
    and len: "2 ≤ length xs"
  shows "macro_ok (Γ, Δ, σ) (split_fun (Γ, Δ, σ) x y xs R)"
proof (cases "x = y ∨ x ∈ set xs")
  case True
  have "abst (Γ, Δ, σ) ↝ {}"
  proof (cases "x = y")
    case True
    then show ?thesis
      using step.OC[of x hom "[Var y]" "add_mset (Var x, sum_terms (map Var xs)) (mset R)"
          "map_of Δ" "set σ"] Γ by simp
  next
    case False
    then have x: "x ∈ set xs"
      using ‹x = y ∨ x ∈ set xs› by simp
    obtain us where us: "sum_terms (map Var xs) = Fun plus us"
      using sum_terms_Fun[OF len] by blast
    have "map Var xs ≠ []"
      using len by auto
    then have "x ∈ vars_term (Fun plus us)"
      using x us vars_sum_terms[of "map Var xs"] by auto
    then show ?thesis
      using step.OC[of x plus us "add_mset (Var x, H (Var y)) (mset R)" "map_of Δ" "set σ"] Γ us
      by (simp add: add_mset_commute)
  qed
  then show ?thesis
    using True macro_ok_fail by (simp add: split_fun_def)
next
  case False
  then have xy: "x ≠ y" and x_xs: "x ∉ set xs"
    by auto
  define vs where "vs = fresh_vars (length xs) (used (Γ, Δ, σ))"
  have vs: "length vs = length xs" "distinct vs"
    "set vs ∩ vars_triple (mset Γ, map_of Δ, set σ) = {}"
    using fresh_vars[of "length xs" "used (Γ, Δ, σ)"] set_used[of "(Γ, Δ, σ)"]
    unfolding vs_def by auto
  note F = split_facts[OF N[unfolded abst.simps] Γ len xy x_xs vs]
  define Γl where "Γl = (Var x, H (Var y)) # (Var y, sum_terms (map Var vs)) #
    map2 (λa v. (Var a, H (Var v))) xs vs @ R"
  define Δl where "Δl = map (λv. (v, 1::nat)) vs @ Δ"
  have m: "mset Γl = split_problem x y vs xs (mset R)"
    "map_of Δl = (map_of Δ)(vs [↦] replicate (length vs) 1)"
    unfolding Γl_def Δl_def split_problem_def
    by (simp_all add: map_of_zero_depths del: map_of_append)
  have res: "split_fun (Γ, Δ, σ) x y xs R = close_fun (Γl, Δl, σ)"
    using False unfolding split_fun_def Γl_def Δl_def vs_def by (simp add: Let_def)
  have step: "abst (Γ, Δ, σ) ↝ {abst (Γl, Δl, σ)}"
    using F(1) m by simp
  have C: "lsteps (Γl, Δl, σ) (close_fun (Γl, Δl, σ)) ∧
      (∀S' ∈ set (close_fun (Γl, Δl, σ)). ∃Δ'. S' = (Γl, Δ', σ) ∧
        close_post (dep (map_of Δ) x) (mset Γl) (map_of Δl) (map_of Δ'))"
    by (rule close_fun_spec) (use F(3,4) m in simp_all)
  have "normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel"
    if S'in: "S' ∈ set (close_fun (Γl, Δl, σ))" for S'
  proof -
    obtain Δ' where S': "S' = (Γl, Δ', σ)"
      and cp: "close_post (dep (map_of Δ) x) (mset Γl) (map_of Δl) (map_of Δ')"
      using C[THEN conjunct2, rule_format, OF S'in] by blast
    show ?thesis
      using F(5)[of "map_of Δ'"] cp m S' by simp
  qed
  then show ?thesis
    unfolding macro_ok_def res using lsteps_single[OF step] C by simp
qed

text ‹(Dec) on ‹X =⇧? f(Y⇩1, …, Y⇩n)› and ‹X =⇧? f(Z⇩1, …, Z⇩n)›, then closing ‹Δ› and merging.›

definition dec_free_fun :: "('f, 'v) ltriple ⇒ 'v ⇒ 'f ⇒ 'v list ⇒ 'v list ⇒
    ('f, 'v) equation list ⇒ ('f, 'v) ltriple list" where
  "dec_free_fun S x f ys zs R = (case S of (Γ, Δ, σ) ⇒
    concat (map merge_fun
      (close_fun ((Var x, Fun f (map Var ys)) # zip (map Var ys) (map Var zs) @ R, Δ, σ))))"

lemma dec_free_fun_ok:
  assumes N: "normal (abst (Γ, Δ, σ))"
    and Γ: "mset Γ = add_mset (Var x, Fun f (map Var ys)) (add_mset (Var x, Fun f (map Var zs)) (mset R))"
    and f: "f ≠ plus"
    and fr: "free_eq (Var x, Fun f (map Var ys))" "free_eq (Var x, Fun f (map Var zs))"
  shows "macro_ok (Γ, Δ, σ) (dec_free_fun (Γ, Δ, σ) x f ys zs R)"
proof -
  have "length ys = arity f" "length zs = arity f"
    using fr by (auto simp: free_eq_def dest: arg_cong[of _ _ length])
  then have len: "length ys = length zs"
    by simp
  define Γl where "Γl = (Var x, Fun f (map Var ys)) # zip (map Var ys) (map Var zs) @ R"
  let ?Z = "mset (zip (map Var ys) (map Var zs)) :: ('f, 'v) problem"
  have mΓl: "mset Γl = add_mset (Var x, Fun f (map Var ys)) (?Z + mset R)"
    unfolding Γl_def by simp
  have step: "abst (Γ, Δ, σ) ↝ {abst (Γl, Δ, σ)}"
    using step.Dec[of f "map Var ys" "map Var zs" x "mset R" "map_of Δ" "set σ"] f len Γ mΓl
    by simp
  have pn: "pnormal (mset Γ, map_of Δ, set σ)"
    using N by simp
  have Z_vv: "∀e ∈# ?Z. vv_eq e"
    by (auto simp: vv_eq_def set_zip)
  have nfree_Z: "nfree ?Z = 0"
    using Z_vv kinds_vv(3) unfolding nfree_def by simp
  have vars_Z: "vars_problem ?Z ⊆ set ys ∪ set zs"
    by (auto simp: vars_problem_def set_zip in_set_conv_nth)
  have flat1: "flat_problem (mset Γl)"
    using pn Z_vv kinds_vv(4) Γ mΓl by auto
  have vars1: "vars_problem (mset Γl) ⊆ dom (map_of Δ)"
    using pn vars_Z Γ mΓl by auto
  have nfree1: "nfree (mset Γl) < nfree (mset Γ)"
    using fr nfree_Z Γ mΓl by simp
  have C: "lsteps (Γl, Δ, σ) (close_fun (Γl, Δ, σ)) ∧
      (∀S' ∈ set (close_fun (Γl, Δ, σ)). ∃Δ'. S' = (Γl, Δ', σ) ∧
        close_post 0 (mset Γl) (map_of Δ) (map_of Δ'))"
    by (rule close_fun_spec[OF vars1 prot_zero])
  have sub: "lsteps S1 (merge_fun S1) ∧ (∀S' ∈ set (merge_fun S1).
      normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel)"
    if S1in: "S1 ∈ set (close_fun (Γl, Δ, σ))" for S1
  proof -
    obtain Δ1 where S1: "S1 = (Γl, Δ1, σ)"
      and cp: "close_post 0 (mset Γl) (map_of Δ) (map_of Δ1)"
      using C[THEN conjunct2, rule_format, OF S1in] by blast
    have pn1: "pnormal (abst S1)"
      using cp pn flat1 vars1 S1 unfolding close_post_def by auto
    note M = merge_fun_spec[OF pn1[unfolded S1], of 0]
    have "normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel"
      if "S' ∈ set (merge_fun S1)" for S'
    proof -
      obtain Γ' Δ' σ' where S': "abst S' = (Γ', Δ', σ')"
        by (cases "abst S'")
      have "merge_post 0 (mset Γl) (map_of Δ1) (abst S')"
        using M that S1 by simp
      then have nm: "normal (abst S')" and nf: "nfree Γ' = nfree (mset Γl)"
        using S' by (simp_all add: merge_post_def)
      have "(tmeasure (Γ', Δ', σ'), tmeasure (mset Γ, map_of Δ, set σ)) ∈ term_rel"
        by (rule term_rel_free) (use nf nfree1 in simp)
      then show ?thesis
        using nm S' by simp
    qed
    then show ?thesis
      using M S1 by simp
  qed
  have "lsteps (Γl, Δ, σ) (concat (map merge_fun (close_fun (Γl, Δ, σ))))"
    using lsteps_concat[of _ _ merge_fun] C sub by blast
  then show ?thesis
    unfolding macro_ok_def dec_free_fun_def Γl_def[symmetric]
    using lsteps_single[OF step] sub by auto
qed

text ‹(AC) on all ‹+›-equations at a level ‹l›, then closing ‹Δ› and merging, in every branch.›

definition is_sum_b :: "('f, 'v) equation ⇒ bool" where
  "is_sum_b e ⟷ is_Var (fst e) ∧ (case kind (snd e) of KSum _ ⇒ True | _ ⇒ False)"

lemma is_sum_b_iff: "is_sum_b e ⟷ flat_sum_eq e"
proof
  assume "is_sum_b e"
  then obtain x ys where "fst e = Var x" "kind (snd e) = KSum ys"
    by (auto simp: is_sum_b_def is_Var_def split: rkind.splits)
  then show "flat_sum_eq e"
    using kind_KSum by (cases e) (auto simp: flat_sum_eq_def)
next
  assume "flat_sum_eq e"
  then show "is_sum_b e"
    by (auto simp: flat_sum_eq_def is_sum_b_def)
qed

lemma map_of_add_zero_depths:
  "map_of (map (λv. (v, 0)) N @ Δ) = add_zero_depths (set N) (map_of Δ)"
  by (rule ext) (simp add: add_zero_depths_def map_add_def map_of_const split: option.splits)

definition ac_fun :: "('f, 'v) ltriple ⇒ nat ⇒ ('f, 'v) ltriple list" where
  "ac_fun S l = (case S of (Γ, Δ, σ) ⇒
    (let P = (λe. is_sum_b e ∧ dep (map_of Δ) (lhsv e) = l);
         Ψ = filter P Γ; Γr = filter (λe. ¬ P e) Γ;
         VΨ = concat (map (λ(s, t). vars_tl s @ vars_tl t) Ψ)
     in concat (map (λθ.
          let G = map (λ(x, t). (Var x, t)) θ;
              N = filter (λv. v ∉ set VΨ) (concat (map (λ(s, t). vars_tl s @ vars_tl t) G))
          in concat (map merge_fun (close_fun (G @ Γr, map (λv. (v, 0)) N @ Δ, σ))))
        (ac_unify (set (used S)) (mset Ψ)))))"

lemma ac_fun_ok:
  assumes N: "normal (abst (Γ, Δ, σ))" and l: "l ≤ κ"
    and exc: "0 < excess (at_level (map_of Δ) l (SUMS (mset Γ)))"
  shows "macro_ok (Γ, Δ, σ) (ac_fun (Γ, Δ, σ) l)"
proof -
  define P where "P = (λe. is_sum_b e ∧ dep (map_of Δ) (lhsv e) = l)"
  define Ψ where "Ψ = filter_mset P (mset Γ)"
  have Ψeq: "Ψ = filter_mset (λe. flat_sum_eq e ∧ dep (map_of Δ) (lhsv e) = l) (mset Γ)"
    unfolding Ψ_def P_def by (simp add: is_sum_b_iff)
  define Γr where "Γr = filter (λe. ¬ P e) Γ"
  define V where "V = vars_triple (mset Γ, map_of Δ, set σ)"
  have mΨ: "mset (filter P Γ) = Ψ"
    unfolding Ψ_def by simp
  have mΓr: "mset Γr = mset Γ - Ψ"
    unfolding Γr_def Ψ_def by (simp, metis add_diff_cancel_left' multiset_partition)
  have VΨ: "set (concat (map (λ(s, t). vars_tl s @ vars_tl t) (filter P Γ))) = vars_problem Ψ"
    using vars_problem_list[of "filter P Γ"] mΨ by simp
  have V: "set (used (Γ, Δ, σ)) = V"
    unfolding V_def using set_used[of "(Γ, Δ, σ)"] by simp
  define G :: "('v × ('f, 'v) term) list ⇒ ('f, 'v) equation list"
    where "G θ = map (λ(x, t). (Var x, t)) θ" for θ
  define T where "T θ = (G θ @ Γr, map (λv. (v, 0::nat))
      (filter (λv. v ∉ vars_problem Ψ) (concat (map (λ(s, t). vars_tl s @ vars_tl t) (G θ)))) @ Δ,
      σ)" for θ
  have eq1: "(λe. is_sum_b e ∧ dep (map_of Δ) (lhsv e) = l) = P"
    unfolding P_def ..
  have eq2: "filter (λe. ¬ (is_sum_b e ∧ dep (map_of Δ) (lhsv e) = l)) Γ = Γr"
    unfolding Γr_def P_def ..
  have res0: "ac_fun (Γ, Δ, σ) l =
      concat (map (λθ. concat (map merge_fun (close_fun (T θ)))) (ac_unify V Ψ))"
    unfolding ac_fun_def Let_def prod.case eq2 eq1 mΨ VΨ V T_def G_def ..
  have res: "ac_fun (Γ, Δ, σ) l =
      concat (map (λS1. concat (map merge_fun (close_fun S1))) (map T (ac_unify V Ψ)))"
    unfolding res0 by (simp add: comp_def)
  have absT: "abst (T θ) = (get_eqs θ + (mset Γ - Ψ),
      add_zero_depths (vars_problem (get_eqs θ) - vars_problem Ψ) (map_of Δ), set σ)" for θ
  proof -
    have "set (filter (λv. v ∉ vars_problem Ψ) (concat (map (λ(s, t). vars_tl s @ vars_tl t) (G θ))))
        = vars_problem (get_eqs θ) - vars_problem Ψ"
      using vars_problem_list[of "G θ"] unfolding G_def get_eqs_def by auto
    then show ?thesis
      unfolding T_def abst.simps using mΓr
      by (simp add: map_of_add_zero_depths get_eqs_def G_def del: map_of_append)
  qed
  have pn: "pnormal (mset Γ, map_of Δ, set σ)"
    using N by simp
  have finV: "finite V"
    unfolding V_def using pnormal_finite_vars[OF pn] .
  have Ψsum: "∀e ∈# Ψ. flat_sum_eq e"
    unfolding Ψeq by simp
  have "at_level (map_of Δ) l (SUMS (mset Γ)) ≠ {#}"
    using exc by (auto simp: excess_def)
  then obtain z where z: "z ∈# SUMS (mset Γ)" "dep (map_of Δ) z = l"
    by (auto simp: at_level_def)
  then obtain e where "e ∈# mset Γ" "flat_sum_eq e" "z = lhsv e"
    using SUMS_lhsv by blast
  then have "e ∈# Ψ"
    using z(2) unfolding Ψeq by simp
  then have Ψne: "Ψ ≠ {#}"
    by auto
  have step: "abst (Γ, Δ, σ) ↝ abst ` set (map T (ac_unify V Ψ))"
  proof -
    have "(mset Γ, map_of Δ, set σ) ↝
        {(get_eqs θ + (mset Γ - Ψ),
          add_zero_depths (vars_problem (get_eqs θ) - vars_problem Ψ) (map_of Δ), set σ)
          | θ. θ ∈ set (ac_unify (vars_triple (mset Γ, map_of Δ, set σ)) Ψ)}"
    proof (rule step.AC)
      show "Ψ ⊆# mset Γ"
        unfolding Ψ_def by simp
      show "∀θ ∈ set (ac_unify (vars_triple (mset Γ, map_of Δ, set σ)) Ψ).
          fresh_for (vars_problem (get_eqs θ) - vars_problem Ψ) (mset Γ, map_of Δ, set σ)"
        using ac_fresh[OF finV] unfolding V_def by blast
    qed (use Ψsum Ψne in simp_all)
    moreover have "abst ` set (map T (ac_unify V Ψ)) =
        {(get_eqs θ + (mset Γ - Ψ),
          add_zero_depths (vars_problem (get_eqs θ) - vars_problem Ψ) (map_of Δ), set σ)
          | θ. θ ∈ set (ac_unify (vars_triple (mset Γ, map_of Δ, set σ)) Ψ)}"
      using absT unfolding V_def by (auto simp: image_image)
    ultimately show ?thesis
      by simp
  qed
  have sub: "lsteps (T θ) (concat (map merge_fun (close_fun (T θ)))) ∧
      (∀S' ∈ set (concat (map merge_fun (close_fun (T θ)))).
        normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel)"
    if θ: "θ ∈ set (ac_unify V Ψ)" for θ
  proof -
    note F = ac_facts[OF N[unfolded abst.simps] l exc Ψeq θ[unfolded V_def]]
    obtain Γt Δt where Tθ: "T θ = (Γt, Δt, σ)"
      unfolding T_def by simp
    have m: "mset Γt = get_eqs θ + (mset Γ - Ψ)"
      "map_of Δt = add_zero_depths (vars_problem (get_eqs θ) - vars_problem Ψ) (map_of Δ)"
      using absT[of θ] Tθ by simp_all
    have C: "lsteps (Γt, Δt, σ) (close_fun (Γt, Δt, σ)) ∧
        (∀S' ∈ set (close_fun (Γt, Δt, σ)). ∃Δ'. S' = (Γt, Δ', σ) ∧
          close_post l (mset Γt) (map_of Δt) (map_of Δ'))"
      by (rule close_fun_spec) (use F(2,3) m in simp_all)
    have sub1: "lsteps S1 (merge_fun S1) ∧ (∀S' ∈ set (merge_fun S1).
        normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel)"
      if S1in: "S1 ∈ set (close_fun (Γt, Δt, σ))" for S1
    proof -
      obtain Δ1 where S1: "S1 = (Γt, Δ1, σ)"
        and cp: "close_post l (mset Γt) (map_of Δt) (map_of Δ1)"
        using C[THEN conjunct2, rule_format, OF S1in] by blast
      note P1 = F(4)[OF cp[unfolded m]]
      have pn1: "pnormal (abst (Γt, Δ1, σ))"
        using P1 m by simp
      note M = merge_fun_spec[OF pn1, of l]
      have "normal (abst S') ∧ (tmeasure (abst S'), tmeasure (abst (Γ, Δ, σ))) ∈ term_rel"
        if "S' ∈ set (merge_fun S1)" for S'
        using finish_pure[of l "mset Γt" "map_of Δ1" "abst S'" "mset Γ" "map_of Δ" "set σ"]
          M that S1 P1 m l by simp
      then show ?thesis
        using M S1 by simp
    qed
    have "lsteps (Γt, Δt, σ) (concat (map merge_fun (close_fun (Γt, Δt, σ))))"
      using lsteps_concat[of _ _ merge_fun] C sub1 by blast
    then show ?thesis
      unfolding Tθ using sub1 by auto
  qed
  have "lsteps (Γ, Δ, σ) (concat (map (λS1. concat (map merge_fun (close_fun S1))) (map T (ac_unify V Ψ))))"
    by (rule lsteps_step[OF step]) (use sub in auto)
  then show ?thesis
    unfolding macro_ok_def res using sub by auto
qed

text ‹Dispatch on the kinds of the two equations ‹X =⇧? t⇩1› and ‹X =⇧? t⇩2›.›

definition macro :: "('f, 'v) ltriple ⇒ 'v ⇒ ('f, 'v) term ⇒ ('f, 'v) term ⇒
    ('f, 'v) equation list ⇒ ('f, 'v) ltriple list option" where
  "macro S x t1 t2 R = (case S of (Γ, Δ, σ) ⇒ (case (kind t1, kind t2) of
      (KOther, _) ⇒ None
    | (_, KOther) ⇒ None
    | (KH y, KH z) ⇒ Some (if dep (map_of Δ) y ≤ dep (map_of Δ) z
        then dec_h_fun S x y z R else dec_h_fun S x z y R)
    | (KH y, KSum xs) ⇒ Some (split_fun S x y xs R)
    | (KSum xs, KH y) ⇒ Some (split_fun S x y xs R)
    | (KSum xs, KSum ys) ⇒ Some (ac_fun S (dep (map_of Δ) x))
    | (KFree f ys, KFree g zs) ⇒ Some (if f = g then dec_free_fun S x f ys zs R else [])
    | _ ⇒ Some []))"

lemma clash_ok:
  assumes "mset Γ = add_mset (Var x, Fun f ss) (add_mset (Var x, Fun g ts) (mset R))"
    and "f ≠ g" and "f ∉ {plus, hom} ∨ g ∉ {plus, hom}"
  shows "macro_ok (Γ, Δ, σ) []"
  using step.Clash[OF assms(2,3), of x ss ts "mset R" "map_of Δ" "set σ"] assms(1)
  by (intro macro_ok_fail) simp

lemma macro_spec:
  assumes N: "normal (abst (Γ, Δ, σ))"
    and Γ: "mset Γ = add_mset (Var x, t1) (add_mset (Var x, t2) (mset R))"
  shows "∃Ss. macro (Γ, Δ, σ) x t1 t2 R = Some Ss ∧ macro_ok (Γ, Δ, σ) Ss"
proof -
  have pn: "pnormal (mset Γ, map_of Δ, set σ)" and nvv: "nvv (mset Γ) = 0"
    using N by simp_all
  have k: "flat_eq (Var x, t1)" "¬ vv_eq (Var x, t1)" "flat_eq (Var x, t2)" "¬ vv_eq (Var x, t2)"
    using pn nvv Γ by (auto split: if_splits)
  have Γ': "mset Γ = add_mset (Var x, t2) (add_mset (Var x, t1) (mset R))"
    using Γ by (simp add: add_mset_commute)
  have K: "kind t1 ≠ KOther" "kind t2 ≠ KOther"
    using flat_nonvv_kind k by auto
  show ?thesis
  proof (cases "kind t1")
    case (KH y)
    note t1 = kind_KH[OF KH]
    show ?thesis
    proof (cases "kind t2")
      case (KH z)
      note t2 = kind_KH[OF KH]
      show ?thesis
      proof (cases "dep (map_of Δ) y ≤ dep (map_of Δ) z")
        case True
        then show ?thesis
          using dec_h_fun_ok[OF N Γ[unfolded t1 t2] True] ‹kind t1 = KH y› KH
          by (simp add: macro_def)
      next
        case False
        then have "dep (map_of Δ) z ≤ dep (map_of Δ) y"
          by simp
        then show ?thesis
          using dec_h_fun_ok[OF N Γ'[unfolded t1 t2]] ‹kind t1 = KH y› KH False
          by (simp add: macro_def)
      qed
    next
      case (KSum xs)
      note t2 = kind_KSum[OF KSum]
      then show ?thesis
        using split_fun_ok[OF N Γ[unfolded t1 conjunct1[OF t2]] conjunct2[OF t2]]
          ‹kind t1 = KH y› KSum by (simp add: macro_def)
    next
      case (KFree g zs)
      note t2 = kind_KFree[OF KFree]
      then show ?thesis
        using clash_ok[OF Γ[unfolded t1 conjunct1[OF t2]]] ‹kind t1 = KH y› KFree
        by (auto simp: macro_def)
    next
      case KOther
      then show ?thesis
        using K by simp
    qed
  next
    case (KSum xs)
    note t1 = kind_KSum[OF KSum]
    show ?thesis
    proof (cases "kind t2")
      case (KH y)
      note t2 = kind_KH[OF KH]
      then show ?thesis
        using split_fun_ok[OF N Γ'[unfolded conjunct1[OF t1] t2] conjunct2[OF t1]]
          ‹kind t1 = KSum xs› KH by (simp add: macro_def)
    next
      case (KSum ys)
      note t2 = kind_KSum[OF KSum]
      have l: "dep (map_of Δ) x ≤ κ"
        using pn dep_le_kappa by simp
      have "SUMS (mset Γ) = add_mset x (add_mset x (SUMS (mset R)))"
        using Γ t1 t2 sum_kinds[of xs x] sum_kinds[of ys x] by simp
      then have "2 ≤ count (at_level (map_of Δ) (dep (map_of Δ) x) (SUMS (mset Γ))) x"
        by simp
      then have "0 < excess (at_level (map_of Δ) (dep (map_of Δ) x) (SUMS (mset Γ)))"
        by (rule excess_pos)
      then show ?thesis
        using ac_fun_ok[OF N l] ‹kind t1 = KSum xs› KSum by (simp add: macro_def)
    next
      case (KFree g zs)
      note t2 = kind_KFree[OF KFree]
      obtain us where us: "sum_terms (map Var xs) = Fun plus us"
        using sum_terms_Fun t1 by blast
      show ?thesis
        using clash_ok[OF Γ[unfolded conjunct1[OF t1] us conjunct1[OF t2]]] t2
          ‹kind t1 = KSum xs› KFree by (auto simp: macro_def)
    next
      case KOther
      then show ?thesis
        using K by simp
    qed
  next
    case (KFree f ys)
    note t1 = kind_KFree[OF KFree]
    show ?thesis
    proof (cases "kind t2")
      case (KH z)
      note t2 = kind_KH[OF KH]
      then show ?thesis
        using clash_ok[OF Γ[unfolded conjunct1[OF t1] t2]] t1 ‹kind t1 = KFree f ys› KH
        by (simp add: macro_def)
    next
      case (KSum zs)
      note t2 = kind_KSum[OF KSum]
      obtain us where us: "sum_terms (map Var zs) = Fun plus us"
        using sum_terms_Fun t2 by blast
      show ?thesis
        using clash_ok[OF Γ[unfolded conjunct1[OF t1] conjunct1[OF t2] us]] t1
          ‹kind t1 = KFree f ys› KSum by (simp add: macro_def)
    next
      case (KFree g zs)
      note t2 = kind_KFree[OF KFree]
      show ?thesis
      proof (cases "f = g")
        case True
        have "free_eq (Var x, Fun f (map Var ys))" "free_eq (Var x, Fun f (map Var zs))"
          using free_kind[OF k(1) ‹kind t1 = KFree f ys›] free_kind[OF k(3) KFree] t1 t2 True
          by simp_all
        then show ?thesis
          using dec_free_fun_ok[OF N Γ[unfolded conjunct1[OF t1] conjunct1[OF t2] True[symmetric]]]
            t1 True ‹kind t1 = KFree f ys› KFree by (simp add: macro_def)
      next
        case False
        then show ?thesis
          using clash_ok[OF Γ[unfolded conjunct1[OF t1] conjunct1[OF t2]] False] t1
            ‹kind t1 = KFree f ys› KFree by (simp add: macro_def)
      qed
    next
      case KOther
      then show ?thesis
        using K by simp
    qed
  next
    case KOther
    then show ?thesis
      using K by simp
  qed
qed

subsection ‹The main loop›

lemma main_pair:
  assumes N: "normal (abst S)" and fp: "find_pair (fst S) = Some (e1, e2, R)"
  shows "∃Ss. macro S (the_Var (fst e1)) (snd e1) (snd e2) R = Some Ss ∧ macro_ok S Ss"
proof -
  obtain Γ Δ σ where S: "S = (Γ, Δ, σ)"
    by (cases S)
  have m: "mset Γ = add_mset e1 (add_mset e2 (mset R))" "fst e1 = fst e2" "is_Var (fst e1)"
    using find_pair_Some[of Γ e1 e2 R] fp S by auto
  then obtain x where x: "fst e1 = Var x"
    by (auto simp: is_Var_def)
  have "mset Γ = add_mset (Var x, snd e1) (add_mset (Var x, snd e2) (mset R))"
    using m x by (metis prod.collapse)
  then show ?thesis
    using macro_spec[OF N[unfolded S]] x S by simp
qed

lemma main_dec:
  assumes "normal_l S" and "find_pair (fst S) = Some (e1, e2, R)"
    and "macro S (the_Var (fst e1)) (snd e1) (snd e2) R = Some Ss" and "S' ∈ set Ss"
  shows "(tmeasure (abst S'), tmeasure (abst S)) ∈ term_rel"
  using main_pair[OF assms(1)[unfolded normal_l_iff] assms(2)] assms(3,4)
  by (auto simp: macro_ok_def)

function main_fun :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list" where
  "main_fun S = (if ¬ normal_l S then [S] else
     (case find_pair (fst S) of
        None ⇒ final_fun S
      | Some (e1, e2, R) ⇒ (case macro S (the_Var (fst e1)) (snd e1) (snd e2) R of
          None ⇒ [S]
        | Some Ss ⇒ concat (map main_fun Ss))))"
  by pat_completeness auto
termination
  by (relation "inv_image term_rel (λS. tmeasure (abst S))")
    (auto intro: wf_term_rel main_dec)

declare main_fun.simps [simp del]

text ‹From a normal state, ‹main_fun› computes the leaves of a derivation, all irreducible.›

lemma main_fun_spec:
  "normal (abst S) ⟹ lsteps S (main_fun S) ∧ (∀S' ∈ set (main_fun S). irreducible (abst S'))"
proof (induction S rule: main_fun.induct)
  case (1 S)
  have nl: "normal_l S"
    using 1(2) normal_l_iff by blast
  obtain Γ Δ σ where S: "S = (Γ, Δ, σ)"
    by (cases S)
  show ?case
  proof (cases "find_pair (fst S)")
    case None
    have res: "main_fun S = final_fun S"
      using nl None by (simp add: main_fun.simps)
    have pn: "pnormal (mset Γ, map_of Δ, set σ)"
      using 1(2) S by simp
    have "∀e ∈ set Γ. is_Var (fst e)"
      using pn by (auto simp: flat_eq_def vv_eq_def h_eq_def flat_sum_eq_def free_eq_def)
    moreover have "∀x. lhs_count (mset Γ) x ≤ 1"
      using find_pair_None None S by simp
    moreover have "bounded_depths (map_of Δ)"
      using pn by simp
    ultimately show ?thesis
      unfolding res unfolding S by (rule final_fun_spec)
  next
    case (Some p)
    obtain e1 e2 R where p: "p = (e1, e2, R)"
      by (cases p)
    obtain Ss where mac: "macro S (the_Var (fst e1)) (snd e1) (snd e2) R = Some Ss"
      and ok: "macro_ok S Ss"
      using main_pair[OF 1(2), of e1 e2 R] Some p by auto
    have res: "main_fun S = concat (map main_fun Ss)"
      using nl Some p mac by (simp add: main_fun.simps)
    have IH: "lsteps S' (main_fun S') ∧ (∀S'' ∈ set (main_fun S'). irreducible (abst S''))"
      if S'in: "S' ∈ set Ss" for S'
    proof -
      have "normal (abst S')"
        using ok S'in by (simp add: macro_ok_def)
      then show ?thesis
        using 1(1)[of "(e1, e2, R)" e1 "(e2, R)" e2 R Ss S'] nl Some p mac S'in by simp
    qed
    have "lsteps S (concat (map main_fun Ss))"
      using lsteps_concat[of S Ss main_fun] ok IH by (simp add: macro_ok_def)
    then show ?thesis
      unfolding res using IH by auto
  qed
qed

subsection ‹The algorithm›

definition unify :: "('f, 'v) ltriple ⇒ ('f, 'v) ltriple list" where
  "unify S = concat (map main_fun (concat (map merge_fun (close_fun (flatten S)))))"

theorem unify_spec:
  assumes "ready (abst S)"
  shows "lsteps S (unify S)" and "∀S' ∈ set (unify S). irreducible (abst S')"
proof -
  note F = flatten_spec[of S]
  obtain Γ Δ σ where fl: "flatten S = (Γ, Δ, σ)"
    by (cases "flatten S")
  have fr: "flat_problem (mset Γ)" "vars_problem (mset Γ) ⊆ dom (map_of Δ)"
    using F assms fl by simp_all
  note C = close_fun_spec[OF fr(2) prot_zero, of σ]
  have M: "lsteps S1 (merge_fun S1) ∧ (∀S2 ∈ set (merge_fun S1). normal (abst S2))"
    if S1in: "S1 ∈ set (close_fun (Γ, Δ, σ))" for S1
  proof -
    obtain Δ1 where S1: "S1 = (Γ, Δ1, σ)" and cp: "close_post 0 (mset Γ) (map_of Δ) (map_of Δ1)"
      using C[THEN conjunct2, rule_format, OF S1in] by blast
    have "pnormal (abst S1)"
      using cp fr S1 unfolding close_post_def by (auto simp: finite_dom_map_of)
    then show ?thesis
      using merge_fun_spec[of Γ Δ1 σ 0] S1 by (auto simp: merge_post_def)
  qed
  define L2 where "L2 = concat (map merge_fun (close_fun (Γ, Δ, σ)))"
  have L2: "lsteps (Γ, Δ, σ) L2"
    unfolding L2_def using lsteps_concat[of _ _ merge_fun] C M by blast
  have L2n: "normal (abst S2)" if "S2 ∈ set L2" for S2
    using that M unfolding L2_def by auto
  have L3: "lsteps (Γ, Δ, σ) (concat (map main_fun L2))"
    using lsteps_concat[OF L2, of main_fun] main_fun_spec L2n by blast
  have "lsteps S (concat (map (λ_. concat (map main_fun L2)) [flatten S]))"
    using lsteps_concat[of S "[flatten S]"] F L3 fl by simp
  then show "lsteps S (unify S)"
    unfolding unify_def fl L2_def by simp
  show "∀S' ∈ set (unify S). irreducible (abst S')"
  proof
    fix S'
    assume "S' ∈ set (unify S)"
    then obtain S2 where "S2 ∈ set L2" "S' ∈ set (main_fun S2)"
      unfolding unify_def fl L2_def by auto
    then show "irreducible (abst S')"
      using main_fun_spec L2n by blast
  qed
qed

text ‹Soundness: every solved leaf gives a unifier of the input problem.›

theorem unify_sound:
  assumes "ready (abst (Γ, Δ, []))" and "([], Δ', σ') ∈ set (unify (Γ, Δ, []))"
  shows "sat_problem (subst_of_bindings (set σ')) (mset Γ)"
proof -
  have "gtree (mset Γ, map_of Δ, {}) (abst ` set (unify (Γ, Δ, [])))"
    using unify_spec(1)[OF assms(1)] unfolding lsteps_def by simp
  then have "(mset Γ, map_of Δ, {}) ↝⇧* ({#}, map_of Δ', set σ')"
    using gtree_steps assms(2) by force
  moreover have "∄Ss. ({#}, map_of Δ', set σ') ↝ Ss"
    using unify_spec(2)[OF assms(1)] assms(2) by fastforce
  ultimately show ?thesis
    by (rule soundness)
qed

end

text ‹Completeness needs the completeness of the AC-unification algorithm as well.›

locale bounded_ach_alg_complete =
  bounded_ach_alg plus hom κ ac_unify arity fresh + bounded_ach_complete plus hom κ ac_unify
  for plus :: 'f and hom :: 'f and κ :: nat
    and ac_unify :: "'v set ⇒ ('f, 'v) problem ⇒ ('v × ('f, 'v) term) list list"
    and arity :: "'f ⇒ nat" and fresh :: "'v list ⇒ 'v"
begin

theorem unify_complete:
  assumes R: "ready (abst (Γ, Δ, []))" and sol: "bsol θ (mset Γ, map_of Δ, {})"
  shows "∃Δ' σ'. ([], Δ', σ') ∈ set (unify (Γ, Δ, [])) ∧
    (∃τ. ∀x ∈ vars_problem (mset Γ). θ x ≈⇩A⇩C⇩h subst_of_bindings (set σ') x ⋅ τ)"
proof -
  have "gtree (mset Γ, map_of Δ, {}) (abst ` set (unify (Γ, Δ, [])))"
    using unify_spec(1)[OF R] unfolding lsteps_def by simp
  then obtain L where L: "L ⊆ abst ` set (unify (Γ, Δ, []))" "tree (mset Γ, map_of Δ, {}) L"
    using gtree_tree by blast
  have final: "∀S ∈ L. ∄Ss. S ↝ Ss"
    using L(1) unify_spec(2)[OF R] by blast
  have dom: "vars_problem (mset Γ) ⊆ dom (map_of Δ)" "finite (dom (map_of Δ))"
    using R by auto
  obtain Δ' σ' τ where in_L: "({#}, Δ', σ') ∈ L"
    and inst: "∀x ∈ vars_problem (mset Γ). θ x ≈⇩A⇩C⇩h subst_of_bindings σ' x ⋅ τ"
    using completeness[OF infinite_vars L(2) final dom sol] by blast
  have "({#}, Δ', σ') ∈ abst ` set (unify (Γ, Δ, []))"
    using L(1) in_L by (rule subsetD)
  then obtain S'' where S''0: "({#}, Δ', σ') = abst S''" "S'' ∈ set (unify (Γ, Δ, []))"
    by (rule imageE)
  then have S'': "S'' ∈ set (unify (Γ, Δ, []))" "abst S'' = ({#}, Δ', σ')"
    by simp_all
  obtain Δ'' σ'' where "S'' = ([], Δ'', σ'')" "set σ'' = σ'"
    using S''(2) by (cases S'') auto
  then show ?thesis
    using S''(1) inst by blast
qed

end

section ‹An executable instance›

text ‹
  A check that ‹unify› executes: natural numbers as function symbols (‹0› is ‹+›, ‹1› is ‹h›,
  ‹2› is a binary ‹f›, ‹3› a constant ‹a›) and as variables, ‹κ = 2›, and the trivial
  AC-unification algorithm that returns no unifiers. The latter is sound but not complete, so
  this instance only exercises the parts of the algorithm other than (AC). A real instance plugs
  in Stickel's algorithm.
›

definition ex_arity :: "nat ⇒ nat" where
  "ex_arity f = (if f = 0 then 2 else if f = 1 then 1 else if f = 2 then 2 else if f = 3 then 0
    else 1)"

definition ex_fresh :: "nat list ⇒ nat" where
  "ex_fresh xs = Suc (foldr max xs 0)"

lemma ex_fresh: "ex_fresh xs ∉ set xs"
proof -
  have "x ≤ foldr max xs 0" if "x ∈ set xs" for x
    using that by (induction xs) auto
  then show ?thesis
    unfolding ex_fresh_def by (meson Suc_n_not_le_n)
qed

global_interpretation ex: bounded_ach_alg 0 1 2 "λ_ _. []" ex_arity ex_fresh
  defines ex_sum_terms = ex.sum_terms and ex_fresh_vars = ex.fresh_vars
    and ex_sum_vars = ex.sum_vars and ex_h_target = ex.h_target and ex_eq_edges = ex.eq_edges
    and ex_bounded_l = ex.bounded_l and ex_close_fun = ex.close_fun
    and ex_merge_fun = ex.merge_fun and ex_flat_one = ex.flat_one
    and ex_find_rule = ex.find_rule and ex_flatten = ex.flatten and ex_kind = ex.kind
    and ex_flat_eqb = ex.flat_eqb and ex_normal_l = ex.normal_l and ex_dec_h_fun = ex.dec_h_fun
    and ex_split_fun = ex.split_fun and ex_dec_free_fun = ex.dec_free_fun
    and ex_is_sum_b = ex.is_sum_b and ex_ac_fun = ex.ac_fun and ex_macro = ex.macro
    and ex_main_fun = ex.main_fun and ex_unify = ex.unify and ex_rename_eq = ex.rename_eq
    and ex_find_pair = ex.find_pair and ex_final_fun = ex.final_fun and ex_lhsv = ex.lhsv
    and ex_vars_tl = ex.vars_tl and ex_ren = ex.ren and ex_dep = ex.dep and ex_is_vv = ex.is_vv
    and ex_viol = ex.viol and ex_used = ex.used
proof unfold_locales
qed (auto simp: ex_arity_def ex_fresh)

text ‹‹X =⇧? f(Y, a)›: flattening, merging and elimination give one solved leaf.›
value "ex_unify ([(Var (10::nat), Fun (2::nat) [Var 11, Fun 3 []])], [(10, 0), (11, 0)], [])"

text ‹‹X =⇧? h(Y)›, ‹X =⇧? h(Z)›: (Dec), then merging ‹Y› and ‹Z›.›
value "ex_unify ([(Var (1::nat), Fun (1::nat) [Var 2]), (Var 1, Fun 1 [Var 3])],
  [(1, 0), (2, 0), (3, 0)], [])"

text ‹‹X =⇧? f(Y, Y)›, ‹X =⇧? a›: (Clash), no leaves.›
value "ex_unify ([(Var (1::nat), Fun (2::nat) [Var 2, Var 2]), (Var 1, Fun 3 [])],
  [(1, 0), (2, 0)], [])"

text ‹‹X =⇧? h(h(h(Y)))› with ‹κ = 2›: (BC), no leaves.›
value "ex_unify ([(Var (1::nat), Fun (1::nat) [Fun 1 [Fun 1 [Var 2]]])], [(1, 0), (2, 0)], [])"

text ‹‹X =⇧? h(Y)›, ‹X =⇧? Z⇩1 + Z⇩2›: (Split) gives ‹X ↦ h(V⇩1 + V⇩2)›, ‹Z⇩i ↦ h(V⇩i)›.›
value "ex_unify ([(Var (1::nat), Fun (1::nat) [Var 2]), (Var 1, Fun 0 [Var 3, Var 4])],
  [(1, 0), (2, 0), (3, 0), (4, 0)], [])"

end
