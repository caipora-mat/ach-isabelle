(*
Author: Guilherme Borges Brandão
*)

theory AC_Unif_Soundness
  imports AC_Unif_Algorithm
begin

section ‹Soundness of the AC-unification algorithm›

subsection ‹Auxiliary facts›

lemma subst_upd_not_in: "x ∉ vars_term t ⟹ t ⋅ Var(x := u) = t"
  by (induction t) (auto intro: map_idI)

lemma count_sum_list: "count (sum_list Ms) a = sum_list (map (λM. count M a) Ms)"
  by (induction Ms) auto

lemma sum_list_map_mset: "sum_list (map g xs) = (∑u∈#mset xs. g u)"
  by (induction xs) auto

lemma sum_mset_count: "(∑u∈#M. g u) = (∑u∈set_mset M. count M u * g u)" for g :: "'a ⇒ nat"
proof -
  obtain xs where M: "M = mset xs" by (metis ex_mset)
  have "(∑u∈#M. g u) = sum_list (map g xs)"
    unfolding M by (rule sum_list_map_mset[symmetric])
  also have "… = (∑u∈set xs. count_list xs u * g u)" by (rule sum_list_map_eq_sum_count)
  finally show ?thesis unfolding M by (simp add: count_mset)
qed

lemma grp_sum:
  fixes g :: "'a ⇒ nat"
  assumes "set_mset M ⊆ set xs"
  shows "sum_list (map (λ(u, a). a * g u) (grp xs M)) = (∑u∈#M. g u)"
proof -
  let ?ds = "remdups (filter (λu. 0 < count M u) xs)"
  have set_ds: "set ?ds = set_mset M" using assms by auto
  have "sum_list (map (λ(u, a). a * g u) (grp xs M)) = sum_list (map (λu. count M u * g u) ?ds)"
    by (simp add: grp_def comp_def)
  also have "… = (∑u∈set ?ds. count M u * g u)"
    by (rule sum_list_distinct_conv_sum_set) simp
  also have "… = (∑u∈set_mset M. count M u * g u)"
    by (simp only: set_ds)
  finally show ?thesis by (simp add: sum_mset_count)
qed

lemma sum_lessThan_add: "(∑j<m + n. h j) = (∑j<m. h j) + (∑j<n. h (m + j))"
  for h :: "nat ⇒ 'a :: comm_monoid_add"
  by (induction n) (simp_all add: add.assoc)

lemma sum_list_nth: "sum_list (map h xs) = (∑j<length xs. h (xs ! j))"
  by (simp add: sum_list_sum_nth atLeast0LessThan)

lemma sum_list_map_concat: "sum_list (map g (concat xss)) = sum_list (map (λxs. sum_list (map g xs)) xss)"
  by (induction xss) auto

lemma set_subseqs_subset: "D ∈ set (subseqs B) ⟹ set D ⊆ set B"
  by (metis Pow_iff image_eqI subseqs_powset)

lemma length_grp: "length (grp xs M) = length (remdups (filter (λu. 0 < count M u) xs))"
  by (simp add: grp_def)

text ‹One side of the Diophantine equation, evaluated at a combination of the chosen solutions.›

lemma side_sum:
  fixes c :: "'a ⇒ nat" and z :: "nat ⇒ nat"
  assumes "⋀j. j < length us ⟹ c (fst (us ! j)) = (∑i<l. D ! i ! (k0 + j) * z i)"
  shows "sum_list (map (λ(u, a). a * c u) us) =
    (∑i<l. z i * (∑j<length us. snd (us ! j) * D ! i ! (k0 + j)))"
proof -
  have "sum_list (map (λ(u, a). a * c u) us) = (∑j<length us. snd (us ! j) * c (fst (us ! j)))"
    by (simp add: sum_list_nth case_prod_beta)
  also have "… = (∑j<length us. ∑i<l. snd (us ! j) * (D ! i ! (k0 + j) * z i))"
    using assms by (simp add: sum_distrib_left)
  also have "… = (∑i<l. ∑j<length us. z i * (snd (us ! j) * D ! i ! (k0 + j)))"
    by (subst sum.swap) (simp add: mult_ac)
  also have "… = (∑i<l. z i * (∑j<length us. snd (us ! j) * D ! i ! (k0 + j)))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

text ‹A solution of ‹a ∙ x = b ∙ y›, written as one row with the coefficients of ‹b› negated.›

lemma dot_split:
  assumes "length y = length a + length b"
    and "dot (map int a @ map (λx. - int x) b) y = 0"
  shows "(∑j<length a. a ! j * y ! j) = (∑j<length b. b ! j * y ! (length a + j))"
proof -
  let ?r = "map int a @ map (λx. - int x) b"
  have "dot ?r y = (∑j<length a + length b. ?r ! j * int (y ! j))"
    using assms(1) by (simp add: dot_conv)
  also have "… = (∑j<length a. int (a ! j) * int (y ! j)) -
      (∑j<length b. int (b ! j) * int (y ! (length a + j)))"
    by (simp add: sum_lessThan_add nth_append sum_negf)
  finally have eq: "(∑j<length a. int (a ! j) * int (y ! j)) =
      (∑j<length b. int (b ! j) * int (y ! (length a + j)))"
    using assms(2) by simp
  have "int (∑j<length a. a ! j * y ! j) = (∑j<length a. int (a ! j) * int (y ! j))"
    by (simp add: of_nat_sum)
  also have "… = (∑j<length b. int (b ! j) * int (y ! (length a + j)))" by (rule eq)
  also have "… = int (∑j<length b. b ! j * y ! (length a + j))"
    by (simp add: of_nat_sum)
  finally show ?thesis by (rule of_nat_eq_iff[THEN iffD1])
qed

context ac_unif
begin

lemma unifies_simps [simp]:
  "unifies σ []"
  "unifies σ ((s, t) # P) ⟷ s ⋅ σ ≈ t ⋅ σ ∧ unifies σ P"
  "unifies σ (P @ Q) ⟷ unifies σ P ∧ unifies σ Q"
  by (auto simp: unifies_def)

lemma unifies_subst_eqs: "unifies τ (subst_eqs σ P) ⟷ unifies (σ ∘⇩s τ) P"
  by (induction P) auto

lemma unifies_remove1:
  assumes "e ∈ set P"
  shows "unifies τ P ⟷ unifies τ (e # remove1 e P)"
proof -
  have "set (e # remove1 e P) = set P"
    using assms by (induction P) auto
  then show ?thesis unfolding unifies_def by (metis (no_types))
qed

lemma unifies_zip:
  assumes "length ts = length ss" "unifies τ (zip ts ss)"
  shows "Fun f ts ⋅ τ ≈ Fun f ss ⋅ τ"
proof -
  have "ts ! i ⋅ τ ≈ ss ! i ⋅ τ" if "i < length ts" for i
  proof -
    have "(ts ! i, ss ! i) ∈ set (zip ts ss)" using that assms(1) by (metis in_set_zip fst_conv snd_conv)
    then show ?thesis using assms(2) by (auto simp: unifies_def)
  qed
  then show ?thesis using assms(1) by (auto intro!: eq_theory.cong)
qed

subsection ‹Normal forms below an AC symbol, under a substitution›

lemma nfa_subst_args:
  "ac f ⟹ nfa f (nf (t ⋅ τ)) = sum_list (map (λu. nfa f (nf (u ⋅ τ))) (args_ac f t))"
proof (induction f t rule: args_ac.induct)
  case (1 f g s t)
  show ?case
  proof (cases "g = f")
    case False
    then show ?thesis by simp
  qed (use 1 in simp)
qed simp_all

lemma nfa_subst_mk_ac:
  "ac f ⟹ xs ≠ [] ⟹ nfa f (nf (mk_ac f xs ⋅ τ)) = sum_list (map (λu. nfa f (nf (u ⋅ τ))) xs)"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases xs) (simp_all add: mk_ac_Cons)
qed simp

lemma sum_new_vars:
  "sum_list (map g (new_vars nv D j)) = (∑i<length D. D ! i ! j * g (Var (nv + i)))"
  for g :: "('f, nat) term ⇒ nat"
  by (simp add: new_vars_def sum_list_map_concat comp_def interv_sum_list_conv_sum_set_nat
      atLeast0LessThan sum_list_replicate)

lemma new_vars_nonempty:
  assumes "0 < col_sum D j"
  shows "new_vars nv D j ≠ []"
proof -
  have "∃b∈set D. b ! j ≠ 0"
  proof (rule ccontr)
    assume "¬ (∃b∈set D. b ! j ≠ 0)"
    then have "col_sum D j = 0" by (simp add: col_sum_def sum_list_eq_0_iff)
    then show False using assms by simp
  qed
  then obtain i where "i < length D" "D ! i ! j ≠ 0" by (auto simp: in_set_conv_nth)
  then show ?thesis by (auto simp: new_vars_def)
qed

text ‹The arguments of an AC application, split into the arguments not in the other side and the common ones.›

lemma mset_split: "A = (A - B) + (A ∩# B)"
  by (rule multiset_eqI) simp

lemma set_dio_L: "set_mset (dio_L f t s) ⊆ set (args_ac f t)"
  by (auto simp: dio_L_def dest: in_diffD)

lemma basis_sol:
  assumes "v ∈ set (basis a b)"
  shows "length v = length a + length b" "dot (map int a @ map (λx. - int x) b) v = 0"
proof -
  let ?k = "length a + length b" and ?r = "map int a @ map (λx. - int x) b"
  obtain B where B: "dsolve ?k [?r] = Some B" "v ∈ set B" "length v = ?k"
  proof (cases "dsolve ?k [?r]")
    case None
    then show ?thesis using assms by (simp add: basis_def)
  next
    case (Some B)
    then show ?thesis using assms that by (simp add: basis_def)
  qed
  show "length v = length a + length b" by (rule B(3))
  show "dot (map int a @ map (λx. - int x) b) v = 0"
    using dsolve_sol[OF B(1,2)] by (simp add: is_sol_def)
qed

lemma basis_dot:
  assumes "v ∈ set (basis a b)"
  shows "(∑j<length a. a ! j * v ! j) = (∑j<length b. b ! j * v ! (length a + j))"
  using dot_split[OF basis_sol[OF assms]] .

lemma mem_solve_ac:
  assumes "(C, nv') ∈ set (solve_ac f t s nv)"
  shows "(dio_L f t s = {#} ∧ dio_L f s t = {#} ∧ C = [] ∧ nv' = nv) ∨
    (∃D. D ∈ set (subseqs (dio_basis f t s)) ∧ valid_sub (dio_ws f t s) D ∧
      C = sol_eqs f nv (dio_ws f t s) D ∧ nv' = nv + length D)"
  using assms by (auto simp: solve_ac_def split: if_splits)

lemma length_sol_eqs [simp]: "length (sol_eqs f nv ws D) = length ws"
  by (simp add: sol_eqs_def)

lemma nth_sol_eqs: "j < length ws ⟹ sol_eqs f nv ws D ! j = (ws ! j, mk_ac f (new_vars nv D j))"
  by (simp add: sol_eqs_def)

lemma set_sol_eqs:
  "set (sol_eqs f nv ws D) = (λj. (ws ! j, mk_ac f (new_vars nv D j))) ` {..<length ws}"
  by (auto simp: sol_eqs_def)

text ‹Counting the AC arguments of an instance: the left side minus the common part.›

lemma count_sum_list_map: "count (sum_list (map N xs)) e = (∑u∈#mset xs. count (N u) e)"
  by (induction xs) auto

lemma count_nfa_args:
  assumes "ac f"
  shows "count (nfa f (nf (x ⋅ τ))) e = (∑u∈#mset (args_ac f x). count (nfa f (nf (u ⋅ τ))) e)"
  using arg_cong[where f = "λM. count M e", OF nfa_subst_args[OF assms, of x τ]]
  unfolding count_sum_list_map .

lemma count_nfa_split:
  assumes "ac f"
  shows "count (nfa f (nf (t ⋅ τ))) e =
    (∑u∈#dio_L f t s. count (nfa f (nf (u ⋅ τ))) e) +
    (∑u∈#mset (args_ac f t) ∩# mset (args_ac f s). count (nfa f (nf (u ⋅ τ))) e)"
proof -
  let ?A = "mset (args_ac f t)" and ?B = "mset (args_ac f s)"
  let ?c = "λu. count (nfa f (nf (u ⋅ τ))) e"
  have A: "?A = dio_L f t s + (?A ∩# ?B)"
    unfolding dio_L_def by (rule mset_split)
  have "count (nfa f (nf (t ⋅ τ))) e = (∑u∈#?A. ?c u)" by (rule count_nfa_args[OF assms])
  also have "… = (∑u∈#dio_L f t s + (?A ∩# ?B). ?c u)"
    by (rule arg_cong[where f = "λM. ∑u∈#M. ?c u", OF A])
  also have "… = (∑u∈#dio_L f t s. ?c u) + (∑u∈#?A ∩# ?B. ?c u)"
    by (simp only: image_mset_union sum_mset.union)
  finally show ?thesis .
qed

subsection ‹Soundness of the AC step›

text ‹PVS Theorem 1 (soundness of ‹solveAC›).›

lemma solve_ac_sound:
  assumes f: "ac f" and t: "is_ac_app f t" and s: "is_ac_app f s"
    and C: "(C, nv') ∈ set (solve_ac f t s nv)" and u: "unifies τ C"
  shows "t ⋅ τ ≈ s ⋅ τ"
proof -
  let ?c = "λe u. count (nfa f (nf (u ⋅ τ))) e"
  have sides: "(∑u∈#dio_L f t s. ?c e u) = (∑u∈#dio_L f s t. ?c e u)" for e
    using mem_solve_ac[OF C]
  proof
    assume "dio_L f t s = {#} ∧ dio_L f s t = {#} ∧ C = [] ∧ nv' = nv"
    then show ?thesis by simp
  next
    assume "∃D. D ∈ set (subseqs (dio_basis f t s)) ∧ valid_sub (dio_ws f t s) D ∧
      C = sol_eqs f nv (dio_ws f t s) D ∧ nv' = nv + length D"
    then obtain D where D: "D ∈ set (subseqs (dio_basis f t s))" "valid_sub (dio_ws f t s) D"
      "C = sol_eqs f nv (dio_ws f t s) D" by blast
    define us where "us = dio_us f t s"
    define vs where "vs = dio_us f s t"
    define ws where "ws = dio_ws f t s"
    define z where "z i = ?c e (Var (nv + i))" for i
    have ws: "ws = map fst us @ map fst vs" by (simp add: ws_def us_def vs_def dio_ws_def)
    have col: "?c e (ws ! j) = (∑i<length D. D ! i ! j * z i)" if j: "j < length ws" for j
    proof -
      have pos: "0 < col_sum D j" using D(2) j by (simp add: valid_sub_def ws_def)
      have "(ws ! j, mk_ac f (new_vars nv D j)) ∈ set C"
        using j D(3) by (auto simp: set_sol_eqs ws_def)
      then have "ws ! j ⋅ τ ≈ mk_ac f (new_vars nv D j) ⋅ τ" using u by (auto simp: unifies_def)
      then have "nfa f (nf (ws ! j ⋅ τ)) = nfa f (nf (mk_ac f (new_vars nv D j) ⋅ τ))"
        by (simp add: eq_AC_iff_nf)
      also have "… = sum_list (map (λu. nfa f (nf (u ⋅ τ))) (new_vars nv D j))"
        by (rule nfa_subst_mk_ac[OF f new_vars_nonempty[OF pos]])
      finally have "?c e (ws ! j) = sum_list (map (?c e) (new_vars nv D j))"
        by (simp add: count_sum_list comp_def)
      then show ?thesis by (simp add: sum_new_vars z_def)
    qed
    have L: "(∑u∈#dio_L f t s. ?c e u) =
        (∑i<length D. z i * (∑j<length us. snd (us ! j) * D ! i ! (0 + j)))"
    proof -
      have "(∑u∈#dio_L f t s. ?c e u) = sum_list (map (λ(u, a). a * ?c e u) us)"
        unfolding us_def dio_us_def by (rule grp_sum[symmetric, OF set_dio_L])
      also have "… = (∑i<length D. z i * (∑j<length us. snd (us ! j) * D ! i ! (0 + j)))"
      proof (rule side_sum)
        fix j
        assume "j < length us"
        then show "?c e (fst (us ! j)) = (∑i<length D. D ! i ! (0 + j) * z i)"
          using col[of j] by (simp add: ws nth_append)
      qed
      finally show ?thesis .
    qed
    have R: "(∑u∈#dio_L f s t. ?c e u) =
        (∑i<length D. z i * (∑j<length vs. snd (vs ! j) * D ! i ! (length us + j)))"
    proof -
      have "(∑u∈#dio_L f s t. ?c e u) = sum_list (map (λ(u, a). a * ?c e u) vs)"
        unfolding vs_def dio_us_def by (rule grp_sum[symmetric, OF set_dio_L])
      also have "… = (∑i<length D. z i * (∑j<length vs. snd (vs ! j) * D ! i ! (length us + j)))"
      proof (rule side_sum)
        fix j
        assume "j < length vs"
        then show "?c e (fst (vs ! j)) = (∑i<length D. D ! i ! (length us + j) * z i)"
          using col[of "length us + j"] by (simp add: ws nth_append)
      qed
      finally show ?thesis .
    qed
    have "(∑j<length us. snd (us ! j) * D ! i ! (0 + j)) =
        (∑j<length vs. snd (vs ! j) * D ! i ! (length us + j))" if i: "i < length D" for i
    proof -
      have "D ! i ∈ set (basis (map snd us) (map snd vs))"
        using set_subseqs_subset[OF D(1)] i by (auto simp: dio_basis_def us_def vs_def)
      from basis_dot[OF this] show ?thesis by simp
    qed
    then show ?thesis unfolding L R by (intro sum.cong) simp_all
  qed
  have "nfa f (nf (t ⋅ τ)) = nfa f (nf (s ⋅ τ))"
  proof (rule multiset_eqI)
    fix e
    show "count (nfa f (nf (t ⋅ τ))) e = count (nfa f (nf (s ⋅ τ))) e"
      unfolding count_nfa_split[OF f, of t τ e s] count_nfa_split[OF f, of s τ e t] sides
      by (simp add: subset_mset.inf_commute)
  qed
  then have "nf (t ⋅ τ) = nf (s ⋅ τ)" by (rule nfa_eq_imp_nf_eq)
  then show ?thesis by (simp add: eq_AC_iff_nf)
qed

subsection ‹Soundness of variable instantiation›

lemma inst_sound:
  "inst E = Some (R, θ) ⟹ unifies τ R ⟹ unifies (θ ∘⇩s τ) E"
proof (induction E arbitrary: R θ τ rule: inst.induct)
  case 1
  then show ?case by simp
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then show ?thesis using 2 by simp
  next
    case ts: False
    show ?thesis
    proof (cases s)
      case (Var z)
      let ?σ = "Var(z := t)"
      obtain θ' where z: "z ∉ vars_term t" and rec: "inst (subst_eqs ?σ E) = Some (R, θ')"
        and θ: "θ = ?σ ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      have "unifies (θ' ∘⇩s τ) (subst_eqs ?σ E)" by (rule "2.IH"(2)[OF ts Var z rec "2.prems"(2)])
      then have E: "unifies (θ ∘⇩s τ) E" by (simp add: unifies_subst_eqs θ subst_compose_assoc)
      have "t ⋅ (θ ∘⇩s τ) = s ⋅ (θ ∘⇩s τ)"
        using z by (simp add: θ Var subst_upd_not_in subst_compose)
      then show ?thesis using E by simp
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        let ?σ = "Var(x := s)"
        obtain θ' where x: "x ∉ vars_term s" and rec: "inst (subst_eqs ?σ E) = Some (R, θ')"
          and θ: "θ = ?σ ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        have "unifies (θ' ∘⇩s τ) (subst_eqs ?σ E)" by (rule "2.IH"(3)[OF ts Fun Var x rec "2.prems"(2)])
        then have E: "unifies (θ ∘⇩s τ) E" by (simp add: unifies_subst_eqs θ subst_compose_assoc)
        have "t ⋅ (θ ∘⇩s τ) = s ⋅ (θ ∘⇩s τ)"
          using x by (simp add: θ Var subst_upd_not_in subst_compose)
        then show ?thesis using E by simp
      next
        case (Fun f ts')
        obtain R0 where rec: "inst E = Some (R0, θ)" and R: "R = (t ⋅ θ, s ⋅ θ) # R0"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        have "unifies τ R0" using "2.prems"(2) R by simp
        then have "unifies (θ ∘⇩s τ) E" by (rule "2.IH"(4)[OF ts ‹s = Fun g ss› Fun rec])
        then show ?thesis using "2.prems"(2) R by simp
      qed
    qed
  qed
qed

subsection ‹Soundness of the AC round›

lemma ac_pair_iff:
  "ac_pair ac (t, s) ⟷ (∃f a b c d. t = Fun f [a, b] ∧ s = Fun f [c, d] ∧ ac f)"
  by (cases "(ac, (t, s))" rule: ac_pair.cases) auto

lemma ac_pair_subst: "ac_pair ac e ⟹ ac_pair ac (fst e ⋅ σ, snd e ⋅ σ)"
  by (cases e) (auto simp: ac_pair_iff)

lemma ac_pairs_subst_eqs: "∀e∈set P. ac_pair ac e ⟹ ∀e∈set (subst_eqs σ P). ac_pair ac e"
  by (fastforce simp: subst_eqs_def ac_pair_iff)

lemma ac_round_Cons_Fun:
  assumes "t = Fun f ts" "(R', σ', nv') ∈ set (ac_round ((t, s) # P) R σ nv)"
  obtains C nv1 R1 θ1 where "(C, nv1) ∈ set (solve_ac f t s nv)" "inst C = Some (R1, θ1)"
    "(R', σ', nv') ∈ set (ac_round (subst_eqs θ1 P) (subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1)"
proof -
  from assms obtain x where x: "x ∈ set (solve_ac f t s nv)"
    and m: "(R', σ', nv') ∈ set (case x of (C, nv1) ⇒ (case inst C of None ⇒ []
      | Some (R1, θ1) ⇒ ac_round (subst_eqs θ1 P) (subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1))"
    by (simp only: ac_round.simps term.case set_concat set_map) blast
  obtain C nv1 where x': "x = (C, nv1)" by (cases x)
  show ?thesis
  proof (cases "inst C")
    case None
    then show ?thesis using m x' by simp
  next
    case (Some r)
    obtain R1 θ1 where "r = (R1, θ1)" by (cases r)
    then show ?thesis using that x x' m Some by simp
  qed
qed

text ‹PVS Theorem 2 (soundness of ‹applyACStep›).›

lemma ac_round_sound:
  "(R', σ', nv') ∈ set (ac_round P R σ nv) ⟹ ∀e∈set P. ac_pair ac e ⟹
    ∃θ. σ' = σ ∘⇩s θ ∧ (∀τ. unifies τ R' ⟶ unifies (θ ∘⇩s τ) (P @ R))"
proof (induction P R σ nv rule: ac_round.induct)
  case (1 R σ nv)
  then show ?case by (intro exI[of _ Var]) auto
next
  case (2 t s P R σ nv)
  obtain f a b c d where ts: "t = Fun f [a, b]" "s = Fun f [c, d]" "ac f"
    using "2.prems"(2) by (auto simp: ac_pair_iff)
  obtain C nv1 R1 θ1 where C: "(C, nv1) ∈ set (solve_ac f t s nv)" and i: "inst C = Some (R1, θ1)"
    and rec: "(R', σ', nv') ∈ set (ac_round (subst_eqs θ1 P) (subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1)"
    using ac_round_Cons_Fun[OF ts(1) "2.prems"(1)] by blast
  have P1: "∀e∈set (subst_eqs θ1 P). ac_pair ac e"
    using "2.prems"(2) by (intro ac_pairs_subst_eqs) simp
  obtain θ2 where θ2: "σ' = (σ ∘⇩s θ1) ∘⇩s θ2"
    and u: "⋀τ. unifies τ R' ⟹ unifies (θ2 ∘⇩s τ) (subst_eqs θ1 P @ subst_eqs θ1 R @ R1)"
    using "2.IH"(2)[OF ts(1) C HOL.refl i HOL.refl rec P1] by blast
  show ?case
  proof (intro exI conjI allI impI)
    show "σ' = σ ∘⇩s (θ1 ∘⇩s θ2)" by (simp add: θ2 subst_compose_assoc)
  next
    fix τ
    assume "unifies τ R'"
    then have u': "unifies (θ2 ∘⇩s τ) (subst_eqs θ1 P @ subst_eqs θ1 R @ R1)" by (rule u)
    then have uC: "unifies (θ1 ∘⇩s (θ2 ∘⇩s τ)) C" using inst_sound[OF i] by simp
    have h: "t ⋅ (θ1 ∘⇩s (θ2 ∘⇩s τ)) ≈ s ⋅ (θ1 ∘⇩s (θ2 ∘⇩s τ))"
      by (rule solve_ac_sound[OF ts(3) _ _ C uC]) (simp_all add: ts)
    then show "unifies (θ1 ∘⇩s θ2 ∘⇩s τ) (((t, s) # P) @ R)"
      using u' by (simp add: unifies_subst_eqs subst_compose_assoc del: subst_subst_compose)
  qed
qed

subsection ‹Soundness of the algorithm›

text ‹PVS Theorem 4: every computed substitution extends ‹σ› by a unifier of ‹P›.›

lemma acunif_sound:
  assumes "acunif_dom (P, σ, nv)" "θ ∈ set (acunif P σ nv)"
  shows "∃τ. θ = σ ∘⇩s τ ∧ unifies τ P"
  using assms
proof (induction P σ nv arbitrary: θ rule: acunif.pinduct)
  case (1 P σ nv)
  show ?case
  proof (cases "P = []")
    case True
    then show ?thesis using "1.prems" 1(1) by (auto simp: acunif.psimps intro: exI[of _ Var])
  next
    case nonempty: False
    show ?thesis
    proof (cases "find (λe. ¬ ac_pair ac e) P")
      case None
      then have all: "∀e∈set P. ac_pair ac e" by (auto simp: find_None_iff)
      obtain P' σ' nv' where r: "(P', σ', nv') ∈ set (ac_round P [] σ nv)"
        and θ: "θ ∈ set (acunif P' σ' nv')"
        using "1.prems" 1(1) nonempty None by (auto simp: acunif.psimps)
      obtain τ' where τ': "θ = σ' ∘⇩s τ'" "unifies τ' P'"
        using 1(2)[OF nonempty None r HOL.refl HOL.refl θ] by blast
      obtain θ1 where "σ' = σ ∘⇩s θ1" "∀τ. unifies τ P' ⟶ unifies (θ1 ∘⇩s τ) (P @ [])"
        using ac_round_sound[OF r all] by blast
      then show ?thesis using τ' by (intro exI[of _ "θ1 ∘⇩s τ'"]) (simp add: subst_compose_assoc)
    next
      case (Some e)
      obtain t s where e: "e = (t, s)" by fastforce
      have mem: "(t, s) ∈ set P" using Some e by (auto simp: find_Some_iff)
      define P1 where "P1 = remove1 (t, s) P"
      have uP: "unifies τ P ⟷ unifies τ ((t, s) # P1)" for τ
        unfolding P1_def by (rule unifies_remove1[OF mem])
      have psimp: "acunif P σ nv =
        (if t = s then acunif P1 σ nv
         else (case t of
           Var x ⇒ if x ∈ vars_term s then []
             else acunif (subst_eqs (Var(x := s)) P1) (σ ∘⇩s Var(x := s)) nv
         | Fun f ts ⇒ (case s of
             Var x ⇒ if x ∈ vars_term t then []
               else acunif (subst_eqs (Var(x := t)) P1) (σ ∘⇩s Var(x := t)) nv
           | Fun g ss ⇒ if f = g ∧ length ts = length ss then acunif (zip ts ss @ P1) σ nv
               else [])))"
        unfolding P1_def using 1(1) nonempty Some e by (simp add: acunif.psimps Let_def)
      show ?thesis
      proof (cases "t = s")
        case True
        then have "θ ∈ set (acunif P1 σ nv)" using "1.prems" psimp by simp
        from 1(3)[OF nonempty Some e[symmetric] P1_def True this] show ?thesis
          using True uP by auto
      next
        case ts: False
        show ?thesis
        proof (cases t)
          case (Var x)
          let ?σ = "Var(x := s)"
          have x: "x ∉ vars_term s" and θ: "θ ∈ set (acunif (subst_eqs ?σ P1) (σ ∘⇩s ?σ) nv)"
            using "1.prems" psimp ts Var by (auto split: if_splits)
          obtain τ where τ: "θ = (σ ∘⇩s ?σ) ∘⇩s τ" "unifies τ (subst_eqs ?σ P1)"
            using 1(4)[OF nonempty Some e[symmetric] P1_def ts Var x θ] by blast
          have "t ⋅ (?σ ∘⇩s τ) = s ⋅ (?σ ∘⇩s τ)" using x Var by (simp add: subst_upd_not_in subst_compose)
          then show ?thesis using τ uP
            by (intro exI[of _ "?σ ∘⇩s τ"]) (simp add: subst_compose_assoc unifies_subst_eqs)
        next
          case (Fun f ts')
          show ?thesis
          proof (cases s)
            case (Var x)
            let ?σ = "Var(x := t)"
            have x: "x ∉ vars_term t" and θ: "θ ∈ set (acunif (subst_eqs ?σ P1) (σ ∘⇩s ?σ) nv)"
              using "1.prems" psimp ts Var Fun by (auto split: if_splits)
            obtain τ where τ: "θ = (σ ∘⇩s ?σ) ∘⇩s τ" "unifies τ (subst_eqs ?σ P1)"
              using 1(5)[OF nonempty Some e[symmetric] P1_def ts Fun Var x θ] by blast
            have "t ⋅ (?σ ∘⇩s τ) = s ⋅ (?σ ∘⇩s τ)" using x Var by (simp add: subst_upd_not_in subst_compose)
            then show ?thesis using τ uP
              by (intro exI[of _ "?σ ∘⇩s τ"]) (simp add: subst_compose_assoc unifies_subst_eqs)
          next
            case (Fun g ss)
            have fg: "f = g ∧ length ts' = length ss" and θ: "θ ∈ set (acunif (zip ts' ss @ P1) σ nv)"
              using "1.prems" psimp ts ‹t = Fun f ts'› Fun by (auto split: if_splits)
            obtain τ where τ: "θ = σ ∘⇩s τ" "unifies τ (zip ts' ss @ P1)"
              using 1(6)[OF nonempty Some e[symmetric] P1_def ts ‹t = Fun f ts'› Fun fg θ] by blast
            have "t ⋅ τ ≈ s ⋅ τ"
              using unifies_zip[of ts' ss τ f] fg τ(2) ‹t = Fun f ts'› Fun by simp
            then show ?thesis using τ uP by auto
          qed
        qed
      qed
    qed
  qed
qed

end

end
