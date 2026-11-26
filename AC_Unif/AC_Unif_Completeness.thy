(*
Author: Guilherme Borges Brandão
*)

theory AC_Unif_Completeness
  imports AC_Unif_Soundness
begin

section ‹Completeness of the AC-unification algorithm›

subsection ‹Auxiliary facts›

lemma subseqs_idx: "map (nth xs) (filter Q [0..<length xs]) ∈ set (subseqs xs)"
proof (induction xs arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have upt: "[0..<length (x # xs)] = 0 # map Suc [0..<length xs]"
    by (simp add: upt_conv_Cons map_Suc_upt del: upt_Suc)
  have "map (nth (x # xs)) (filter Q [0..<length (x # xs)]) =
      (if Q 0 then x # map (nth xs) (filter (Q ∘ Suc) [0..<length xs])
       else map (nth xs) (filter (Q ∘ Suc) [0..<length xs]))"
    unfolding upt by (simp add: filter_map comp_def)
  then show ?case using Cons.IH[of "Q ∘ Suc"] by (simp add: Let_def comp_def del: upt_Suc)
qed

lemma length_lc_simps [simp]:
  "lc [] [] j = 0"
  "lc (c # ks) (b # B) j = c * b ! j + lc ks B j"
  by (simp_all add: lc_def)

lemma lc_filter:
  assumes "length ks = length B" "∀b∈set B. ¬ P b ⟶ (∀j<n. b ! j = 0)"
  shows "∃ks'. length ks' = length (filter P B) ∧ (∀j<n. lc ks B j = lc ks' (filter P B) j)"
  using assms
proof (induction B arbitrary: ks)
  case Nil
  then show ?case by simp
next
  case (Cons b B)
  obtain c ks0 where ks: "ks = c # ks0" using Cons.prems(1) by (cases ks) auto
  obtain ks0' where ks0': "length ks0' = length (filter P B)" "∀j<n. lc ks0 B j = lc ks0' (filter P B) j"
    using Cons.IH[of ks0] Cons.prems ks by auto
  show ?case
  proof (cases "P b")
    case True
    then show ?thesis using ks ks0' by (intro exI[of _ "c # ks0'"]) simp
  next
    case False
    then show ?thesis using ks ks0' Cons.prems(2) by (intro exI[of _ ks0']) simp
  qed
qed

lemma sum_idx:
  fixes g :: "nat ⇒ 'a :: comm_monoid_add"
  assumes "⋀i. i < n ⟹ ¬ Q i ⟹ g i = 0"
  shows "(∑i<n. g i) = (∑d<length (filter Q [0..<n]). g (filter Q [0..<n] ! d))"
proof -
  let ?idx = "filter Q [0..<n]"
  have "(∑i<n. g i) = (∑i∈set ?idx. g i)"
    using assms by (intro sum.mono_neutral_right) auto
  also have "… = sum_list (map g ?idx)"
    by (simp add: sum_list_distinct_conv_sum_set)
  also have "… = (∑d<length ?idx. g (?idx ! d))" by (rule sum_list_nth)
  finally show ?thesis .
qed

lemma size_subst_occurs:
  "x ∈ vars_term t ⟹ t ≠ Var x ⟹ size (δ x) < size (t ⋅ δ)"
proof (induction t)
  case (Fun f ts)
  then obtain u where u: "u ∈ set ts" "x ∈ vars_term u" by auto
  have lt: "size (u ⋅ δ) < size (Fun f ts ⋅ δ)"
    using ac_sig.size_arg_less[of "u ⋅ δ" "map (λs. s ⋅ δ) ts"] u(1) by (simp add: size_list_map)
  show ?case
  proof (cases "u = Var x")
    case True
    then show ?thesis using lt by simp
  next
    case False
    then show ?thesis using Fun.IH[OF u] lt by simp
  qed
qed simp

context ac_unif
begin

lemma occurs_not_unifiable:
  assumes "x ∈ vars_term t" "t ≠ Var x"
  shows "¬ δ x ≈ t ⋅ δ"
proof
  assume "δ x ≈ t ⋅ δ"
  then have "size (δ x) = size (t ⋅ δ)" by (rule eq_AC_size)
  with size_subst_occurs[OF assms, of δ] show False by simp
qed

subsection ‹Substitutions fixed by a unifier›

text ‹
  ‹δ› is a fixpoint of ‹θ› modulo AC: ‹δ x ≈ θ x ⋅ δ› for all ‹x›. Then ‹θ› is more
  general than ‹δ›, with ‹δ› itself as the instantiating substitution. This invariant replaces
  the hypotheses ‹σ ≤ δ› and ‹δ ⊆ V› of PVS and avoids its renaming argument.
›

definition fixes_ac :: "('f, 'v) subst ⇒ ('f, 'v) subst ⇒ bool" where
  "fixes_ac δ θ ⟷ (∀x. δ x ≈ θ x ⋅ δ)"

lemma fixes_ac_Var [simp]: "fixes_ac δ Var"
  by (simp add: fixes_ac_def)

lemma fixes_ac_term: "fixes_ac δ θ ⟹ u ⋅ θ ⋅ δ ≈ u ⋅ δ"
proof -
  assume h: "fixes_ac δ θ"
  have "u ⋅ (θ ∘⇩s δ) ≈ u ⋅ δ"
    by (rule eq_theory_subst_cong) (use h in ‹auto simp: fixes_ac_def subst_compose intro: eq_theory.sym›)
  then show ?thesis by simp
qed

lemma fixes_ac_upd:
  assumes "δ x ≈ t ⋅ δ"
  shows "fixes_ac δ (Var(x := t))"
  using assms by (auto simp: fixes_ac_def)

lemma fixes_ac_compose:
  assumes "fixes_ac δ σ" "fixes_ac δ θ"
  shows "fixes_ac δ (σ ∘⇩s θ)"
  unfolding fixes_ac_def
proof
  fix x
  have "δ x ≈ σ x ⋅ δ" using assms(1) by (simp add: fixes_ac_def)
  also have "… ≈ σ x ⋅ θ ⋅ δ" by (rule eq_theory.sym[OF fixes_ac_term[OF assms(2)]])
  finally show "δ x ≈ (σ ∘⇩s θ) x ⋅ δ" by (simp add: subst_compose)
qed

lemma unifies_subst_eqs_fixes:
  assumes "fixes_ac δ θ" "unifies δ P"
  shows "unifies δ (subst_eqs θ P)"
  unfolding unifies_def subst_eqs_def
proof (clarsimp)
  fix s t
  assume "(s, t) ∈ set P"
  then have "s ⋅ δ ≈ t ⋅ δ" using assms(2) by (auto simp: unifies_def)
  then show "s ⋅ θ ⋅ δ ≈ t ⋅ θ ⋅ δ"
    using fixes_ac_term[OF assms(1), of s] fixes_ac_term[OF assms(1), of t]
    by (meson eq_theory.sym eq_theory.trans)
qed

lemma unifies_agree:
  assumes "vars_eqs P ⊆ V" "∀x∈V. δ' x = δ x" "unifies δ P"
  shows "unifies δ' P"
proof -
  have "s ⋅ δ' = s ⋅ δ" "t ⋅ δ' = t ⋅ δ" if "(s, t) ∈ set P" for s t
    using that assms(1,2) by (auto simp: vars_eqs_def intro!: term_subst_eq)
  then show ?thesis using assms(3) by (auto simp: unifies_def)
qed

subsection ‹Completeness of variable instantiation›

text ‹PVS Lemma 8 for ‹instantiateStep›.›

lemma inst_complete:
  "unifies δ E ⟹ ∃R θ. inst E = Some (R, θ) ∧ unifies δ R ∧ fixes_ac δ θ"
proof (induction E rule: inst.induct)
  case 1
  then show ?case by simp
next
  case (2 t s E)
  have ts: "t ⋅ δ ≈ s ⋅ δ" and E: "unifies δ E" using "2.prems" by auto
  show ?case
  proof (cases "t = s")
    case True
    then show ?thesis using "2.IH"(1)[OF True E] by simp
  next
    case neq: False
    show ?thesis
    proof (cases s)
      case (Var z)
      have z: "z ∉ vars_term t"
        using occurs_not_unifiable[of z t δ] ts neq Var by (auto intro: eq_theory.sym)
      have fx: "fixes_ac δ (Var(z := t))"
        using ts Var by (intro fixes_ac_upd) (auto intro: eq_theory.sym)
      obtain R θ where r: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ)" "unifies δ R" "fixes_ac δ θ"
        using "2.IH"(2)[OF neq Var z unifies_subst_eqs_fixes[OF fx E]] by blast
      then show ?thesis using neq Var z fixes_ac_compose[OF fx r(3)] by simp
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        have x: "x ∉ vars_term s"
          using occurs_not_unifiable[of x s δ] ts neq Var by auto
        have fx: "fixes_ac δ (Var(x := s))"
          using ts Var by (intro fixes_ac_upd) auto
        obtain R θ where r: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ)" "unifies δ R" "fixes_ac δ θ"
          using "2.IH"(3)[OF neq Fun Var x unifies_subst_eqs_fixes[OF fx E]] by blast
        then show ?thesis using neq Var Fun x fixes_ac_compose[OF fx r(3)] by simp
      next
        case (Fun f ts')
        obtain R θ where r: "inst E = Some (R, θ)" "unifies δ R" "fixes_ac δ θ"
          using "2.IH"(4)[OF neq ‹s = Fun g ss› Fun E] by blast
        have "t ⋅ θ ⋅ δ ≈ s ⋅ θ ⋅ δ"
          using fixes_ac_term[OF r(3), of t] fixes_ac_term[OF r(3), of s] ts
          by (meson eq_theory.sym eq_theory.trans)
        then show ?thesis using neq Fun ‹s = Fun g ss› r by simp
      qed
    qed
  qed
qed

text ‹Variables of the result of ‹inst›.›

lemma inst_vars:
  "inst E = Some (R, θ) ⟹
    vars_eqs R ⊆ vars_eqs E ∧ (∀x. vars_term (θ x) ⊆ vars_eqs E ∪ {x}) ∧
    (∀x. x ∉ vars_eqs E ⟶ θ x = Var x)"
proof (induction E arbitrary: R θ rule: inst.induct)
  case 1
  then show ?case by simp
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then show ?thesis using "2.prems" "2.IH"(1) by fastforce
  next
    case neq: False
    show ?thesis
    proof (cases s)
      case (Var z)
      let ?σ = "Var(z := t)"
      obtain θ' where z: "z ∉ vars_term t" and rec: "inst (subst_eqs ?σ E) = Some (R, θ')"
        and θ: "θ = ?σ ∘⇩s θ'"
        using "2.prems" neq Var by (auto split: if_splits)
      have IH: "vars_eqs R ⊆ vars_eqs (subst_eqs ?σ E)"
        "⋀x. vars_term (θ' x) ⊆ vars_eqs (subst_eqs ?σ E) ∪ {x}"
        "⋀x. x ∉ vars_eqs (subst_eqs ?σ E) ⟹ θ' x = Var x"
        using "2.IH"(2)[OF neq Var z rec] by blast+
      have VE: "vars_eqs (subst_eqs ?σ E) ⊆ vars_eqs E ∪ vars_term t"
        by (auto simp: vars_eqs_def subst_eqs_def vars_term_subst split: if_splits)
      have "vars_term (θ x) ⊆ vars_eqs ((t, s) # E) ∪ {x}" for x
      proof (cases "x = z")
        case True
        have "vars_term (t ⋅ θ') ⊆ vars_eqs E ∪ vars_term t"
          using IH(2) VE by (fastforce simp: vars_term_subst)
        then show ?thesis using True Var by (auto simp: θ subst_compose)
      next
        case False
        then show ?thesis using IH(2)[of x] VE Var by (auto simp: θ subst_compose)
      qed
      moreover have "θ x = Var x" if "x ∉ vars_eqs ((t, s) # E)" for x
        using that IH(3)[of x] VE Var by (auto simp: θ subst_compose)
      ultimately show ?thesis using IH(1) VE Var by auto
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        let ?σ = "Var(x := s)"
        obtain θ' where x: "x ∉ vars_term s" and rec: "inst (subst_eqs ?σ E) = Some (R, θ')"
          and θ: "θ = ?σ ∘⇩s θ'"
          using "2.prems" neq Var Fun by (auto split: if_splits)
        have IH: "vars_eqs R ⊆ vars_eqs (subst_eqs ?σ E)"
          "⋀y. vars_term (θ' y) ⊆ vars_eqs (subst_eqs ?σ E) ∪ {y}"
          "⋀y. y ∉ vars_eqs (subst_eqs ?σ E) ⟹ θ' y = Var y"
          using "2.IH"(3)[OF neq Fun Var x rec] by blast+
        have VE: "vars_eqs (subst_eqs ?σ E) ⊆ vars_eqs E ∪ vars_term s"
          by (auto simp: vars_eqs_def subst_eqs_def vars_term_subst split: if_splits)
        have "vars_term (θ y) ⊆ vars_eqs ((t, s) # E) ∪ {y}" for y
        proof (cases "y = x")
          case True
          have "vars_term (s ⋅ θ') ⊆ vars_eqs E ∪ vars_term s"
            using IH(2) VE by (fastforce simp: vars_term_subst)
          then show ?thesis using True Var by (auto simp: θ subst_compose)
        next
          case False
          then show ?thesis using IH(2)[of y] VE Var by (auto simp: θ subst_compose)
        qed
        moreover have "θ y = Var y" if "y ∉ vars_eqs ((t, s) # E)" for y
          using that IH(3)[of y] VE Var by (auto simp: θ subst_compose)
        ultimately show ?thesis using IH(1) VE Var by auto
      next
        case (Fun f ts')
        obtain R0 where rec: "inst E = Some (R0, θ)" and R: "R = (t ⋅ θ, s ⋅ θ) # R0"
          using "2.prems" neq ‹s = Fun g ss› Fun by auto
        have IH: "vars_eqs R0 ⊆ vars_eqs E" "⋀y. vars_term (θ y) ⊆ vars_eqs E ∪ {y}"
          "⋀y. y ∉ vars_eqs E ⟹ θ y = Var y"
          using "2.IH"(4)[OF neq ‹s = Fun g ss› Fun rec] by blast+
        have "vars_term (t ⋅ θ) ∪ vars_term (s ⋅ θ) ⊆ vars_eqs ((t, s) # E)"
          using IH(2) by (fastforce simp: vars_term_subst)
        then show ?thesis using IH R by auto
      qed
    qed
  qed
qed

subsection ‹Completeness of the AC step›

lemma dot_row:
  assumes "length y = length a + length b"
  shows "dot (map int a @ map (λx. - int x) b) y =
    int (∑j<length a. a ! j * y ! j) - int (∑j<length b. b ! j * y ! (length a + j))"
  using assms by (simp add: dot_conv sum_lessThan_add nth_append sum_negf of_nat_sum)

lemma nfa_mk_ac:
  "ac f ⟹ xs ≠ [] ⟹ nfa f (nf (mk_ac f xs)) = sum_list (map (λu. nfa f (nf u)) xs)"
  using nfa_subst_mk_ac[of f xs Var] by simp

lemma nfa_split_mset:
  assumes "ac f"
  shows "nfa f (nf (t ⋅ δ)) = (∑u∈#dio_L f t s. nfa f (nf (u ⋅ δ))) +
    (∑u∈#mset (args_ac f t) ∩# mset (args_ac f s). nfa f (nf (u ⋅ δ)))"
proof -
  let ?A = "mset (args_ac f t)" and ?B = "mset (args_ac f s)"
  let ?N = "λu. nfa f (nf (u ⋅ δ))"
  have A: "?A = dio_L f t s + (?A ∩# ?B)" unfolding dio_L_def by (rule mset_split)
  have "nfa f (nf (t ⋅ δ)) = (∑u∈#?A. ?N u)"
    using nfa_subst_args[OF assms, of t δ] by (simp add: sum_list_map_mset)
  also have "… = (∑u∈#dio_L f t s + (?A ∩# ?B). ?N u)"
    by (rule arg_cong[where f = "λM. ∑u∈#M. ?N u", OF A])
  also have "… = (∑u∈#dio_L f t s. ?N u) + (∑u∈#?A ∩# ?B. ?N u)"
    by (simp only: image_mset_union sum_mset.union)
  finally show ?thesis .
qed

lemma count_sum_mset_image: "count (∑u∈#M. N u) e = (∑u∈#M. count (N u) e)"
  by (induction M) auto

lemma set_grp_fst: "fst ` set (grp xs M) ⊆ set xs"
  by (auto simp: grp_def)

lemma set_dio_ws: "set (dio_ws f t s) ⊆ set (args_ac f t) ∪ set (args_ac f s)"
  using set_grp_fst[of "args_ac f t" "dio_L f t s"] set_grp_fst[of "args_ac f s" "dio_L f s t"]
  by (auto simp: dio_ws_def dio_us_def)

lemma vars_dio_ws: "u ∈ set (dio_ws f t s) ⟹ vars_term u ⊆ vars_term t ∪ vars_term s"
  using set_dio_ws vars_args_ac[of t f] vars_args_ac[of s f] by blast

lemma not_app_dio_ws: "u ∈ set (dio_ws f t s) ⟹ ¬ is_ac_app f u"
  using set_dio_ws args_ac_no_app by blast

lemma not_app_subst: "¬ is_ac_app f u ⟹ is_Fun u ⟹ ¬ is_ac_app f (u ⋅ δ)"
  by (cases u) auto

lemma length_dio_ws:
  "length (dio_ws f t s) = length (map snd (dio_us f t s)) + length (map snd (dio_us f s t))"
  by (simp add: dio_ws_def)

lemma col_sum_conv: "col_sum D j = (∑d<length D. D ! d ! j)"
  by (simp add: col_sum_def sum_list_nth)

text ‹
  The vector of multiplicities of an atom ‹e› in the instances of the arguments is a solution
  of the Diophantine equation (PVS, proof of Theorem 6, step 3).
›

lemma mult_vector_sol:
  assumes f: "ac f" and u: "t ⋅ δ ≈ s ⋅ δ"
  defines "a ≡ map snd (dio_us f t s)" and "b ≡ map snd (dio_us f s t)" and "ws ≡ dio_ws f t s"
  shows "is_sol (length ws) [map int a @ map (λx. - int x) b]
    (map (λj. count (nfa f (nf (ws ! j ⋅ δ))) e) [0..<length ws])"
proof -
  let ?c = "λu. count (nfa f (nf (u ⋅ δ))) e"
  let ?y = "map (λj. ?c (ws ! j)) [0..<length ws]"
  have len: "length ws = length a + length b" by (simp add: ws_def a_def b_def length_dio_ws)
  have "nfa f (nf (t ⋅ δ)) = nfa f (nf (s ⋅ δ))" using u by (simp add: eq_AC_iff_nf)
  then have "(∑u∈#dio_L f t s. nfa f (nf (u ⋅ δ))) = (∑u∈#dio_L f s t. nfa f (nf (u ⋅ δ)))"
    unfolding nfa_split_mset[OF f, of t δ s] nfa_split_mset[OF f, of s δ t]
    by (simp add: subset_mset.inf_commute)
  then have "count (∑u∈#dio_L f t s. nfa f (nf (u ⋅ δ))) e =
      count (∑u∈#dio_L f s t. nfa f (nf (u ⋅ δ))) e" by simp
  then have sides: "(∑u∈#dio_L f t s. ?c u) = (∑u∈#dio_L f s t. ?c u)"
    by (simp add: count_sum_mset_image)
  have L: "(∑u∈#dio_L f t s. ?c u) = (∑j<length a. a ! j * ?y ! j)"
  proof -
    have "(∑u∈#dio_L f t s. ?c u) = sum_list (map (λ(u, a). a * ?c u) (dio_us f t s))"
      unfolding dio_us_def by (rule grp_sum[symmetric, OF set_dio_L])
    also have "… = (∑j<length a. a ! j * ?y ! j)"
      by (simp add: sum_list_nth case_prod_beta a_def ws_def dio_ws_def nth_append len)
    finally show ?thesis .
  qed
  have R: "(∑u∈#dio_L f s t. ?c u) = (∑j<length b. b ! j * ?y ! (length a + j))"
  proof -
    have "(∑u∈#dio_L f s t. ?c u) = sum_list (map (λ(u, a). a * ?c u) (dio_us f s t))"
      unfolding dio_us_def by (rule grp_sum[symmetric, OF set_dio_L])
    also have "… = (∑j<length b. b ! j * ?y ! (length a + j))"
      using len by (simp add: sum_list_nth case_prod_beta b_def a_def ws_def dio_ws_def nth_append)
    finally show ?thesis .
  qed
  have eq: "(∑j<length a. a ! j * ?y ! j) = (∑j<length b. b ! j * ?y ! (length a + j))"
    using sides L R by simp
  have lenY: "length ?y = length a + length b" using len by simp
  have "dot (map int a @ map (λx. - int x) b) ?y =
      int (∑j<length a. a ! j * ?y ! j) - int (∑j<length b. b ! j * ?y ! (length a + j))"
    by (rule dot_row[OF lenY])
  also have "… = 0" by (simp only: eq diff_self)
  finally show ?thesis using len by (simp add: is_sol_def)
qed

text ‹Every solution is a combination of the computed generators (zero vectors removed).›

lemma basis_gen:
  assumes total: "dsolve (length a + length b) [map int a @ map (λx. - int x) b] ≠ None"
    and sol: "is_sol (length a + length b) [map int a @ map (λx. - int x) b] y"
  shows "∃c. length c = length (basis a b) ∧ (∀j < length a + length b. y ! j = lc c (basis a b) j)"
proof -
  let ?k = "length a + length b" and ?r = "map int a @ map (λx. - int x) b"
  let ?P = "λv. length v = ?k ∧ 0 < sum_list v"
  obtain B where B: "dsolve ?k [?r] = Some B" using total by auto
  have basis: "basis a b = filter ?P B" by (simp add: basis_def B)
  obtain ks where ks: "length ks = length B" "∀j<?k. y ! j = lc ks B j"
    using dsolve_gen[OF B sol] by blast
  have zero: "∀v∈set B. ¬ ?P v ⟶ (∀j<?k. v ! j = 0)"
  proof (intro ballI impI allI)
    fix v j
    assume v: "v ∈ set B" "¬ ?P v" and j: "j < ?k"
    have "length v = ?k" using dsolve_sol[OF B v(1)] by (simp add: is_sol_def)
    then have "sum_list v = 0" using v(2) by simp
    then show "v ! j = 0" using j ‹length v = ?k› by (simp add: sum_list_eq_0_iff)
  qed
  obtain ks' where "length ks' = length (filter ?P B)" "∀j<?k. lc ks B j = lc ks' (filter ?P B) j"
    using lc_filter[OF ks(1) zero] by blast
  then show ?thesis using ks(2) basis by (intro exI[of _ ks']) simp
qed

lemma size_sum_list: "size (sum_list Ms) = sum_list (map size Ms)" for Ms :: "'a multiset list"
  by (induction Ms) (auto simp: size_union)

lemma solve_ac_complete:
  assumes total: "⋀n A. dsolve n A ≠ None"
    and f: "ac f" and t: "is_ac_app f t" and s: "is_ac_app f s"
    and u: "t ⋅ δ ≈ s ⋅ δ" and V: "vars_term t ∪ vars_term s ⊆ {..<nv}"
  shows "∃C nv'. (C, nv') ∈ set (solve_ac f t s nv) ∧ nv ≤ nv' ∧ vars_eqs C ⊆ {..<nv'} ∧
    (∃δ'. (∀x<nv. δ' x = δ x) ∧ unifies δ' C)"
proof (cases "dio_L f t s = {#} ∧ dio_L f s t = {#}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"] exI[of _ nv] conjI exI[of _ δ]) (auto simp: solve_ac_def)
next
  case False
  define a where "a = map snd (dio_us f t s)"
  define b where "b = map snd (dio_us f s t)"
  define ws where "ws = dio_ws f t s"
  define k where "k = length ws"
  define Bs where "Bs = dio_basis f t s"
  have Bs: "Bs = basis a b" by (simp add: Bs_def dio_basis_def a_def b_def)
  have k: "k = length a + length b" by (simp add: k_def ws_def a_def b_def length_dio_ws)
  let ?N = "λu. nfa f (nf (u ⋅ δ))"
  define A where "A = (⋃j<k. set_mset (?N (ws ! j)))"
  have finA: "finite A" by (simp add: A_def)
  have "∀e∈A. ∃c. length c = length Bs ∧ (∀j<k. count (?N (ws ! j)) e = lc c Bs j)"
  proof
    fix e
    have sol: "is_sol k [map int a @ map (λx. - int x) b] (map (λj. count (?N (ws ! j)) e) [0..<k])"
      using mult_vector_sol[OF f u, of e] unfolding k_def ws_def a_def b_def .
    obtain c where "length c = length (basis a b)"
      "∀j<length a + length b. map (λj. count (?N (ws ! j)) e) [0..<length a + length b] ! j =
        lc c (basis a b) j"
      using basis_gen[OF total sol[unfolded k]] by blast
    then show "∃c. length c = length Bs ∧ (∀j<k. count (?N (ws ! j)) e = lc c Bs j)"
      by (intro exI[of _ c]) (simp add: Bs k)
  qed
  then obtain cf where cf0: "∀e∈A. length (cf e) = length Bs ∧ (∀j<k. count (?N (ws ! j)) e = lc (cf e) Bs j)"
    by (rule bchoice[THEN exE]) blast
  have cf_len: "⋀e. e ∈ A ⟹ length (cf e) = length Bs"
    and cf: "⋀e j. e ∈ A ⟹ j < k ⟹ count (?N (ws ! j)) e = lc (cf e) Bs j"
    using cf0 by blast+
  define Q where "Q i ⟷ (∃e∈A. 0 < cf e ! i)" for i
  define idx where "idx = filter Q [0..<length Bs]"
  define D where "D = map (nth Bs) idx"
  have D_sub: "D ∈ set (subseqs Bs)" unfolding D_def idx_def by (rule subseqs_idx)
  have lenD: "length D = length idx" by (simp add: D_def)
  have Dnth: "d < length D ⟹ D ! d = Bs ! (idx ! d)" for d by (simp add: D_def)
  have Qidx: "d < length D ⟹ Q (idx ! d)" for d
    using nth_mem[of d idx] lenD by (simp add: idx_def)
  obtain es where es: "set es = A" "distinct es" using finite_distinct_list[OF finA] by blast
  have "∀e∈A. ∃u. ¬ is_ac_app f u ∧ nf u = e"
  proof
    fix e
    assume "e ∈ A"
    then obtain j where j: "j < k" "e ∈# ?N (ws ! j)" by (auto simp: A_def)
    then have "e ∈# mset (map nf (args_ac f (ws ! j ⋅ δ)))" by (simp add: nfa_nf_args[OF f])
    then obtain u where "u ∈ set (args_ac f (ws ! j ⋅ δ))" "nf u = e" by auto
    then show "∃u. ¬ is_ac_app f u ∧ nf u = e" using args_ac_no_app by blast
  qed
  then obtain rep where rep: "⋀e. e ∈ A ⟹ ¬ is_ac_app f (rep e) ∧ nf (rep e) = e" by metis
  define γ where "γ d = mk_ac f (concat (map (λe. replicate (cf e ! (idx ! d)) (rep e)) es))" for d
  define δ' where "δ' x = (if nv ≤ x ∧ x < nv + length D then γ (x - nv) else δ x)" for x
  have γ_count: "count (nfa f (nf (γ d))) e' = (if e' ∈ A then cf e' ! (idx ! d) else 0)"
    if d: "d < length D" for d e'
  proof -
    let ?i = "idx ! d"
    let ?xs = "concat (map (λe. replicate (cf e ! ?i) (rep e)) es)"
    obtain e0 where e0: "e0 ∈ A" "0 < cf e0 ! ?i" using Qidx[OF d] by (auto simp: Q_def)
    have ne: "?xs ≠ []" using e0 es(1) by auto
    have rep1: "count (nfa f (nf (rep e))) e' = (if e = e' then 1 else 0)" if "e ∈ A" for e
      using rep[OF that] nfa_nf_not_app[of f "rep e"] by simp
    have "count (nfa f (nf (γ d))) e' = sum_list (map (λu. count (nfa f (nf u)) e') ?xs)"
      unfolding γ_def nfa_mk_ac[OF f ne] count_sum_list map_map comp_def ..
    also have "… = sum_list (map (λe. cf e ! ?i * count (nfa f (nf (rep e))) e') es)"
      by (simp add: sum_list_map_concat comp_def sum_list_replicate)
    also have "… = sum_list (map (λe. if e = e' then cf e ! ?i else 0) es)"
      using es(1) rep1 by (intro arg_cong[where f = sum_list] map_cong) auto
    also have "… = (if e' ∈ A then cf e' ! ?i else 0)"
      using es finA by (simp add: sum_list_distinct_conv_sum_set sum.delta)
    finally show ?thesis .
  qed
  have δ'_old: "x < nv ⟹ δ' x = δ x" for x by (simp add: δ'_def)
  have ws_mem: "j < k ⟹ ws ! j ∈ set (dio_ws f t s)" for j by (simp add: k_def ws_def)
  have ws_δ': "ws ! j ⋅ δ' = ws ! j ⋅ δ" if "j < k" for j
  proof (rule term_subst_eq)
    fix x
    assume "x ∈ vars_term (ws ! j)"
    then have "x < nv" using vars_dio_ws[OF ws_mem[OF that]] V by auto
    then show "δ' x = δ x" by (rule δ'_old)
  qed
  have lhs_count: "count (?N (ws ! j)) e' =
      (∑d<length D. D ! d ! j * (if e' ∈ A then cf e' ! (idx ! d) else 0))" if j: "j < k" for j e'
  proof (cases "e' ∈ A")
    case True
    have "count (?N (ws ! j)) e' = lc (cf e') Bs j" by (rule cf[OF True j])
    also have "… = (∑i<length Bs. cf e' ! i * Bs ! i ! j)" by (simp add: lc_conv cf_len[OF True])
    also have "… = (∑d<length idx. cf e' ! (idx ! d) * Bs ! (idx ! d) ! j)"
      unfolding idx_def by (rule sum_idx) (use True in ‹auto simp: Q_def›)
    also have "… = (∑d<length D. D ! d ! j * (if e' ∈ A then cf e' ! (idx ! d) else 0))"
      using True lenD Dnth by (intro sum.cong) (simp_all add: mult.commute)
    finally show ?thesis .
  next
    case False
    have "e' ∉# ?N (ws ! j)" using False j by (auto simp: A_def)
    then show ?thesis using False by (simp add: count_eq_zero_iff)
  qed
  have rhs_count: "count (nfa f (nf (mk_ac f (new_vars nv D j) ⋅ δ'))) e' =
      (∑d<length D. D ! d ! j * (if e' ∈ A then cf e' ! (idx ! d) else 0))"
    if ne: "(new_vars nv D j :: ('f, nat) term list) ≠ []" for j e'
  proof -
    have "count (nfa f (nf (mk_ac f (new_vars nv D j) ⋅ δ'))) e' =
        sum_list (map (λu. count (nfa f (nf (u ⋅ δ'))) e') (new_vars nv D j))"
      unfolding nfa_subst_mk_ac[OF f ne] count_sum_list map_map comp_def ..
    also have "… = (∑d<length D. D ! d ! j * count (nfa f (nf (Var (nv + d) ⋅ δ'))) e')"
      by (rule sum_new_vars)
    also have "… = (∑d<length D. D ! d ! j * (if e' ∈ A then cf e' ! (idx ! d) else 0))"
      by (intro sum.cong) (simp_all add: δ'_def γ_count)
    finally show ?thesis .
  qed
  have colpos: "0 < col_sum D j" if j: "j < k" for j
  proof -
    obtain e where e: "e ∈# ?N (ws ! j)" using nfa_nf_nonempty[of f "ws ! j ⋅ δ"]
      by (metis multiset_nonemptyE)
    then have eA: "e ∈ A" using j by (auto simp: A_def)
    have "0 < count (?N (ws ! j)) e" using e by simp
    then have pos: "0 < (∑d<length D. D ! d ! j * cf e ! (idx ! d))"
      using lhs_count[OF j, of e] eA by simp
    have "∃d<length D. 0 < D ! d ! j"
    proof (rule ccontr)
      assume "¬ (∃d<length D. 0 < D ! d ! j)"
      then have "∀d<length D. D ! d ! j = 0" by auto
      then have "(∑d<length D. D ! d ! j * cf e ! (idx ! d)) = 0" by simp
      then show False using pos by linarith
    qed
    then obtain d where d: "d < length D" "0 < D ! d ! j" by blast
    have "D ! d ! j ≤ (∑d<length D. D ! d ! j)" by (rule member_le_sum) (use d in auto)
    then show ?thesis using d(2) by (simp add: col_sum_conv)
  qed
  have unif_j: "ws ! j ⋅ δ' ≈ mk_ac f (new_vars nv D j) ⋅ δ'" if j: "j < k" for j
  proof -
    have ne: "(new_vars nv D j :: ('f, nat) term list) ≠ []"
      by (rule new_vars_nonempty[OF colpos[OF j]])
    have "nfa f (nf (ws ! j ⋅ δ')) = nfa f (nf (mk_ac f (new_vars nv D j) ⋅ δ'))"
      by (rule multiset_eqI) (simp add: ws_δ'[OF j] lhs_count[OF j] rhs_count[OF ne])
    then have "nf (ws ! j ⋅ δ') = nf (mk_ac f (new_vars nv D j) ⋅ δ')" by (rule nfa_eq_imp_nf_eq)
    then show ?thesis by (simp only: eq_AC_iff_nf)
  qed
  have one: "col_sum D j = 1" if j: "j < k" and fn: "is_Fun (ws ! j)" for j
  proof -
    have ne: "(new_vars nv D j :: ('f, nat) term list) ≠ []"
      by (rule new_vars_nonempty[OF colpos[OF j]])
    have "¬ is_ac_app f (ws ! j ⋅ δ')"
      using not_app_subst[OF not_app_dio_ws[OF ws_mem[OF j]] fn] by (simp add: ws_def)
    then have "size (nfa f (nf (ws ! j ⋅ δ'))) = 1" by (simp add: nfa_nf_not_app)
    then have "1 = size (nfa f (nf (mk_ac f (new_vars nv D j) ⋅ δ')))"
      using unif_j[OF j] by (simp add: eq_AC_iff_nf)
    also have "… = sum_list (map (λu. size (nfa f (nf (u ⋅ δ')))) (new_vars nv D j))"
      unfolding nfa_subst_mk_ac[OF f ne] size_sum_list map_map comp_def ..
    also have "… = (∑d<length D. D ! d ! j * size (nfa f (nf (Var (nv + d) ⋅ δ'))))"
      by (rule sum_new_vars)
    also have "… ≥ (∑d<length D. D ! d ! j)"
      by (intro sum_mono) (simp add: size_nfa_nf_pos Suc_le_eq)
    finally have "col_sum D j ≤ 1" by (simp add: col_sum_conv)
    then show ?thesis using colpos[OF j] by simp
  qed
  have valid: "valid_sub ws D" using colpos one by (simp add: valid_sub_def k_def)
  have mem: "(sol_eqs f nv ws D, nv + length D) ∈ set (solve_ac f t s nv)"
    using False D_sub valid by (auto simp: solve_ac_def ws_def Bs_def)
  have unif: "unifies δ' (sol_eqs f nv ws D)"
    using unif_j by (auto simp: unifies_def set_sol_eqs k_def)
  have vars: "vars_eqs (sol_eqs f nv ws D) ⊆ {..<nv + length D}"
  proof -
    have "vars_term (ws ! j) ⊆ {..<nv + length D}" if "j < k" for j
    proof -
      have "vars_term (ws ! j) ⊆ {..<nv}"
        using vars_dio_ws[OF ws_mem[OF that]] V unfolding ws_def by blast
      then show ?thesis by auto
    qed
    moreover have "vars_term (mk_ac f (new_vars nv D j)) ⊆ {..<nv + length D}" if "j < k" for j
      using new_vars_nonempty[OF colpos[OF that]]
      by (auto simp: vars_mk_ac new_vars_def)
    ultimately show ?thesis by (fastforce simp: vars_eqs_def set_sol_eqs k_def)
  qed
  show ?thesis using mem unif vars δ'_old by (intro exI conjI) auto
qed

subsection ‹Variables in use›

text ‹
  The variables of the problem and of the substitution are below ‹nv›, and the substitution
  does not touch the variables from ‹nv› on (PVS: ‹Vars(P) ⊆ V›, ‹σ ⊆ V›).
›

definition inv_vars :: "('f, nat) eqs ⇒ ('f, nat) subst ⇒ nat ⇒ bool" where
  "inv_vars P σ nv ⟷ vars_eqs P ⊆ {..<nv} ∧ (∀x. nv ≤ x ⟶ σ x = Var x) ∧
    (∀x<nv. vars_term (σ x) ⊆ {..<nv})"

lemma vars_subst_eqs: "vars_eqs (subst_eqs θ P) = (⋃y∈vars_eqs P. vars_term (θ y))"
proof (induction P)
  case (Cons p P)
  then show ?case by (cases p) (auto simp: vars_term_subst)
qed simp

lemma fixes_ac_agree:
  fixes nv :: nat
  assumes "fixes_ac δ σ" "∀x. nv ≤ x ⟶ σ x = Var x" "∀x<nv. vars_term (σ x) ⊆ {..<nv}"
    "∀x<nv. δ' x = δ x"
  shows "fixes_ac δ' σ"
  unfolding fixes_ac_def
proof
  fix x
  show "δ' x ≈ σ x ⋅ δ'"
  proof (cases "x < nv")
    case True
    have "σ x ⋅ δ' = σ x ⋅ δ"
      using assms(3,4) True by (intro term_subst_eq) auto
    then show ?thesis using assms(1,4) True by (simp add: fixes_ac_def)
  next
    case False
    then have "σ x = Var x" using assms(2) by (simp add: not_less)
    then show ?thesis by simp
  qed
qed

lemma inv_vars_inst:
  assumes inv: "inv_vars P σ nv" and nv: "nv ≤ nv1" and C: "vars_eqs C ⊆ {..<nv1}"
    and i: "inst C = Some (R1, θ1)"
  shows "inv_vars (subst_eqs θ1 P @ R1) (σ ∘⇩s θ1) nv1"
proof -
  have iv: "vars_eqs R1 ⊆ vars_eqs C" "⋀y. vars_term (θ1 y) ⊆ vars_eqs C ∪ {y}"
    "⋀y. y ∉ vars_eqs C ⟹ θ1 y = Var y"
    using inst_vars[OF i] by blast+
  have θlow: "vars_term (θ1 y) ⊆ {..<nv1}" if "y < nv1" for y
    using iv(2)[of y] C that by auto
  have "vars_eqs (subst_eqs θ1 P) ⊆ {..<nv1}"
  proof
    fix z
    assume "z ∈ vars_eqs (subst_eqs θ1 P)"
    then obtain y where y: "y ∈ vars_eqs P" "z ∈ vars_term (θ1 y)" by (auto simp: vars_subst_eqs)
    then have "y < nv1" using inv nv by (auto simp: inv_vars_def)
    then show "z ∈ {..<nv1}" using θlow y(2) by auto
  qed
  moreover have "(σ ∘⇩s θ1) x = Var x" if "nv1 ≤ x" for x
  proof -
    have "σ x = Var x" using inv nv that by (simp add: inv_vars_def)
    moreover have "x ∉ vars_eqs C" using C that by auto
    ultimately show ?thesis using iv(3) by (simp add: subst_compose)
  qed
  moreover have "vars_term ((σ ∘⇩s θ1) x) ⊆ {..<nv1}" if x1: "x < nv1" for x
  proof -
    have "vars_term (σ x) ⊆ {..<nv1}"
    proof (cases "x < nv")
      case True
      then have "vars_term (σ x) ⊆ {..<nv}" using inv by (simp add: inv_vars_def)
      then show ?thesis using nv by auto
    next
      case False
      then show ?thesis using inv x1 by (simp add: inv_vars_def not_less)
    qed
    then show ?thesis using θlow by (fastforce simp: subst_compose vars_term_subst)
  qed
  ultimately show ?thesis using iv(1) C by (auto simp: inv_vars_def)
qed

subsection ‹Completeness of the AC round›

lemma ac_round_Cons_Fun_intro:
  assumes "t = Fun f ts" "(C, nv1) ∈ set (solve_ac f t s nv)" "inst C = Some (R1, θ1)"
    "r ∈ set (ac_round (subst_eqs θ1 P) (subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1)"
  shows "r ∈ set (ac_round ((t, s) # P) R σ nv)"
  using assms by (auto intro!: bexI[of _ "(C, nv1)"])

text ‹PVS Theorem 7 (completeness of ‹applyACStep›).›

lemma ac_round_complete:
  assumes total: "⋀n A. dsolve n A ≠ None"
  shows "∀e∈set P. ac_pair ac e ⟹ unifies δ (P @ R) ⟹ fixes_ac δ σ ⟹ inv_vars (P @ R) σ nv ⟹
    ∃R' σ' nv' δ'. (R', σ', nv') ∈ set (ac_round P R σ nv) ∧ nv ≤ nv' ∧ (∀x<nv. δ' x = δ x) ∧
      unifies δ' R' ∧ fixes_ac δ' σ' ∧ inv_vars R' σ' nv'"
proof (induction P R σ nv arbitrary: δ rule: ac_round.induct)
  case (1 R σ nv)
  then show ?case by (intro exI[of _ R] exI[of _ σ] exI[of _ nv] exI[of _ δ]) simp
next
  case (2 t s P R σ nv)
  obtain f a b c d where ts: "t = Fun f [a, b]" "s = Fun f [c, d]" "ac f"
    using "2.prems"(1) by (auto simp: ac_pair_iff)
  have u: "t ⋅ δ ≈ s ⋅ δ" using "2.prems"(2) by simp
  have V: "vars_term t ∪ vars_term s ⊆ {..<nv}" using "2.prems"(4) by (auto simp: inv_vars_def)
  obtain C nv1 δ1 where C: "(C, nv1) ∈ set (solve_ac f t s nv)" "nv ≤ nv1" "vars_eqs C ⊆ {..<nv1}"
    and δ1: "∀x<nv. δ1 x = δ x" "unifies δ1 C"
    using solve_ac_complete[OF total ts(3) _ _ u V] ts by auto
  obtain R1 θ1 where i: "inst C = Some (R1, θ1)" "unifies δ1 R1" "fixes_ac δ1 θ1"
    using inst_complete[OF δ1(2)] by blast
  have inv0: "inv_vars (P @ R) σ nv" using "2.prems"(4) by (auto simp: inv_vars_def)
  have PR1: "unifies δ1 (P @ R)"
    using unifies_agree[of "P @ R" "{..<nv}" δ1 δ] "2.prems"(2) inv0 δ1(1)
    by (auto simp: inv_vars_def)
  have fix1: "fixes_ac δ1 σ"
    using fixes_ac_agree[OF "2.prems"(3) _ _ δ1(1)] inv0 by (simp add: inv_vars_def)
  have pairs: "∀e∈set (subst_eqs θ1 P). ac_pair ac e"
    using "2.prems"(1) by (intro ac_pairs_subst_eqs) simp
  have unif: "unifies δ1 (subst_eqs θ1 P @ subst_eqs θ1 R @ R1)"
    using unifies_subst_eqs_fixes[OF i(3), of "P @ R"] PR1 i(2) by simp
  have inv1: "inv_vars (subst_eqs θ1 P @ subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1"
    using inv_vars_inst[OF inv0 C(2,3) i(1)] by simp
  obtain R' σ' nv' δ' where r: "(R', σ', nv') ∈ set (ac_round (subst_eqs θ1 P) (subst_eqs θ1 R @ R1) (σ ∘⇩s θ1) nv1)"
    "nv1 ≤ nv'" "∀x<nv1. δ' x = δ1 x" "unifies δ' R'" "fixes_ac δ' σ'" "inv_vars R' σ' nv'"
    using "2.IH"(2)[OF ts(1) C(1) HOL.refl i(1) HOL.refl pairs unif fixes_ac_compose[OF fix1 i(3)] inv1]
    by blast
  show ?case
  proof (intro exI conjI)
    show "(R', σ', nv') ∈ set (ac_round ((t, s) # P) R σ nv)"
      by (rule ac_round_Cons_Fun_intro[OF ts(1) C(1) i(1) r(1)])
    show "∀x<nv. δ' x = δ x" using r(3) δ1(1) C(2) by simp
  qed (use r C(2) in auto)
qed

subsection ‹Decomposition of equations that are not AC pairs›

lemma decompose_unifiable:
  assumes "¬ ac_pair ac (Fun f ts, Fun g ss)" "Fun f ts ⋅ δ ≈ Fun g ss ⋅ δ"
  shows "f = g ∧ length ts = length ss ∧ unifies δ (zip ts ss)"
proof -
  let ?ts = "map (λt. t ⋅ δ) ts" and ?ss = "map (λt. t ⋅ δ) ss"
  have eq: "nf (Fun f ?ts) = nf (Fun g ?ss)" using assms(2) by (simp add: eq_AC_iff_nf)
  have notA: "¬ (ac f ∧ length ts = 2)"
  proof
    assume A: "ac f ∧ length ts = 2"
    then obtain M where "nf (Fun f ?ts) = NA f M" by (auto simp: nf_Fun nf_app_def)
    then obtain c d where "Fun g ?ss = Fun f [c, d]" using eq nf_NA[of "Fun g ?ss" f M] by auto
    then have "g = f" "length ss = 2" by auto
    then show False using assms(1) A
      by (auto simp: ac_pair_iff numeral_2_eq_2 length_Suc_conv)
  qed
  then have "nf (Fun f ?ts) = NF f (map nf ?ts)" by (simp add: nf_Fun nf_app_def)
  then obtain us where us: "Fun g ?ss = Fun f us" "map nf ?ts = map nf us"
    using eq nf_NF[of "Fun g ?ss" f "map nf ?ts"] by auto
  then have fg: "g = f" and ss: "us = ?ss" by auto
  have len: "length ts = length ss" using us(2) ss by (metis length_map)
  have "ts ! i ⋅ δ ≈ ss ! i ⋅ δ" if "i < length ts" for i
    using that len arg_cong[OF us(2), of "λxs. xs ! i"] ss by (simp add: eq_AC_iff_nf)
  then have "unifies δ (zip ts ss)" using len by (auto simp: unifies_def set_zip)
  then show ?thesis using fg len by simp
qed

subsection ‹Completeness of the algorithm›

text ‹PVS Lemma 9 (completeness for nice inputs).›

lemma acunif_complete:
  assumes total: "⋀n A. dsolve n A ≠ None"
  shows "acunif_dom (P, σ, nv) ⟹ unifies δ P ⟹ fixes_ac δ σ ⟹ inv_vars P σ nv ⟹
    ∃θ∈set (acunif P σ nv). ∃δ'. (∀x<nv. δ' x = δ x) ∧ fixes_ac δ' θ"
proof (induction P σ nv arbitrary: δ rule: acunif.pinduct)
  case (1 P σ nv)
  show ?case
  proof (cases "P = []")
    case True
    then show ?thesis using 1(1) "1.prems"(2) by (auto simp: acunif.psimps)
  next
    case nonempty: False
    show ?thesis
    proof (cases "find (λe. ¬ ac_pair ac e) P")
      case None
      then have all: "∀e∈set P. ac_pair ac e" by (auto simp: find_None_iff)
      obtain P' σ' nv' δ1 where r: "(P', σ', nv') ∈ set (ac_round P [] σ nv)" "nv ≤ nv'"
        "∀x<nv. δ1 x = δ x" "unifies δ1 P'" "fixes_ac δ1 σ'" "inv_vars P' σ' nv'"
        using ac_round_complete[OF total all, of δ "[]" σ nv] "1.prems" by auto
      obtain θ δ2 where θ: "θ ∈ set (acunif P' σ' nv')" "∀x<nv'. δ2 x = δ1 x" "fixes_ac δ2 θ"
        using 1(2)[OF nonempty None r(1) HOL.refl HOL.refl r(4,5,6)] by blast
      have "θ ∈ set (acunif P σ nv)"
        using 1(1) nonempty None r(1) θ(1) by (auto simp: acunif.psimps)
      then show ?thesis using θ(2,3) r(2,3) by (intro bexI[of _ θ] exI[of _ δ2]) auto
    next
      case (Some e)
      obtain t s where e: "e = (t, s)" by fastforce
      have mem: "(t, s) ∈ set P" and notac: "¬ ac_pair ac (t, s)"
        using Some e by (auto simp: find_Some_iff)
      define P1 where "P1 = remove1 (t, s) P"
      have uP: "unifies δ P ⟷ unifies δ ((t, s) # P1)"
        unfolding P1_def by (rule unifies_remove1[OF mem])
      have ts: "t ⋅ δ ≈ s ⋅ δ" and uP1: "unifies δ P1" using uP "1.prems"(1) by auto
      have setP: "set ((t, s) # P1) = set P"
        unfolding P1_def using mem by (induction P) auto
      have vP: "vars_eqs P = vars_eqs ((t, s) # P1)"
        unfolding vars_eqs_def setP ..
      have inv: "vars_eqs ((t, s) # P1) ⊆ {..<nv}" "∀x. nv ≤ x ⟶ σ x = Var x"
        "∀x<nv. vars_term (σ x) ⊆ {..<nv}"
        using "1.prems"(3) vP by (auto simp: inv_vars_def)
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
      text ‹Eliminating a variable ‹x› bound to ‹u›.›
      have elim: "∃θ∈set (acunif (subst_eqs (Var(x := u)) P1) (σ ∘⇩s Var(x := u)) nv).
          ∃δ'. (∀x<nv. δ' x = δ x) ∧ fixes_ac δ' θ"
        if xu: "δ x ≈ u ⋅ δ" "x ∉ vars_term u" "x < nv" "vars_term u ⊆ {..<nv}"
          and IH: "⋀δ. unifies δ (subst_eqs (Var(x := u)) P1) ⟹ fixes_ac δ (σ ∘⇩s Var(x := u)) ⟹
            inv_vars (subst_eqs (Var(x := u)) P1) (σ ∘⇩s Var(x := u)) nv ⟹
            ∃θ∈set (acunif (subst_eqs (Var(x := u)) P1) (σ ∘⇩s Var(x := u)) nv).
              ∃δ'. (∀x<nv. δ' x = δ x) ∧ fixes_ac δ' θ"
        for x u
      proof (rule IH)
        have fx: "fixes_ac δ (Var(x := u))" by (rule fixes_ac_upd[OF xu(1)])
        show "unifies δ (subst_eqs (Var(x := u)) P1)" by (rule unifies_subst_eqs_fixes[OF fx uP1])
        show "fixes_ac δ (σ ∘⇩s Var(x := u))" by (rule fixes_ac_compose[OF "1.prems"(2) fx])
        show "inv_vars (subst_eqs (Var(x := u)) P1) (σ ∘⇩s Var(x := u)) nv"
          unfolding inv_vars_def
        proof (intro conjI allI impI)
          show "vars_eqs (subst_eqs (Var(x := u)) P1) ⊆ {..<nv}"
            using inv(1) xu(4) by (fastforce simp: vars_subst_eqs split: if_splits)
        next
          fix y
          assume "nv ≤ y"
          then show "(σ ∘⇩s Var(x := u)) y = Var y" using inv(2) xu(3) by (simp add: subst_compose)
        next
          fix y
          assume "y < nv"
          then show "vars_term ((σ ∘⇩s Var(x := u)) y) ⊆ {..<nv}"
            using inv(3) xu(4) by (fastforce simp: subst_compose vars_term_subst split: if_splits)
        qed
      qed
      show ?thesis
      proof (cases "t = s")
        case True
        have "inv_vars P1 σ nv" using inv by (simp add: inv_vars_def)
        then show ?thesis
          using 1(3)[OF nonempty Some e[symmetric] P1_def True uP1 "1.prems"(2)] psimp True by simp
      next
        case neq: False
        show ?thesis
        proof (cases t)
          case (Var x)
          have x: "x ∉ vars_term s"
            using occurs_not_unifiable[of x s δ] ts neq Var by auto
          have "x < nv" "vars_term s ⊆ {..<nv}" using inv(1) Var by auto
          then show ?thesis
            using elim[of x s] ts Var x 1(4)[OF nonempty Some e[symmetric] P1_def neq Var x] psimp neq
            by simp
        next
          case (Fun f ts')
          show ?thesis
          proof (cases s)
            case (Var x)
            have x: "x ∉ vars_term t"
              using occurs_not_unifiable[of x t δ] ts neq Var by (auto intro: eq_theory.sym)
            have "x < nv" "vars_term t ⊆ {..<nv}" using inv(1) Var by auto
            moreover have "δ x ≈ t ⋅ δ" using ts Var by (auto intro: eq_theory.sym)
            ultimately show ?thesis
              using elim[of x t] Fun Var x 1(5)[OF nonempty Some e[symmetric] P1_def neq Fun Var x] psimp neq
              by simp
          next
            case (Fun g ss)
            obtain fg: "f = g" and len: "length ts' = length ss" and z: "unifies δ (zip ts' ss)"
              using decompose_unifiable[of f ts' g ss δ] notac ts ‹t = Fun f ts'› Fun by auto
            have "vars_eqs (zip ts' ss) ⊆ vars_term t ∪ vars_term s"
              using ‹t = Fun f ts'› Fun by (auto simp: vars_eqs_def set_zip)
            then have "inv_vars (zip ts' ss @ P1) σ nv" using inv by (auto simp: inv_vars_def)
            moreover have "unifies δ (zip ts' ss @ P1)" using z uP1 by simp
            ultimately show ?thesis
              using 1(6)[OF nonempty Some e[symmetric] P1_def neq ‹t = Fun f ts'› Fun _ _ "1.prems"(2)]
                psimp neq ‹t = Fun f ts'› Fun fg len by simp
          qed
        qed
      qed
    qed
  qed
qed

subsection ‹Correctness of ‹ac_unifiers››

definition nv0 :: "('f, nat) term ⇒ ('f, nat) term ⇒ nat" where
  "nv0 s t = Suc (Max (insert 0 (vars_term s ∪ vars_term t)))"

lemma ac_unifiers_eq: "ac_unifiers s t = acunif [(s, t)] Var (nv0 s t)"
  by (simp add: ac_unifiers_def nv0_def)

lemma vars_below_nv0: "vars_term s ∪ vars_term t ⊆ {..<nv0 s t}"
proof -
  have "x ≤ Max (insert 0 (vars_term s ∪ vars_term t))" if "x ∈ vars_term s ∪ vars_term t" for x
    using that by (intro Max_ge) auto
  then show ?thesis by (auto simp: nv0_def less_Suc_eq_le)
qed

text ‹Soundness (PVS Corollary 5), assuming termination of the run.›

theorem ac_unifiers_sound_dom:
  assumes "acunif_dom ([(s, t)], Var, nv0 s t)" "θ ∈ set (ac_unifiers s t)"
  shows "s ⋅ θ ≈ t ⋅ θ"
  using acunif_sound[OF assms(1)] assms(2) by (auto simp: ac_unifiers_eq)

text ‹
  Completeness (PVS Lemma 10, without the hypothesis ‹δ ⊆ V›), assuming termination of the run
  and a solver that never gives up: every AC-unifier ‹δ› is an instance of a computed one.
›

theorem ac_unifiers_complete_dom:
  fixes δ :: "('f, nat) subst"
  assumes total: "⋀n A. dsolve n A ≠ None"
    and dom: "acunif_dom ([(s, t)], Var, nv0 s t)" and u: "s ⋅ δ ≈ t ⋅ δ"
  shows "∃θ∈set (ac_unifiers s t). ∃ρ. ∀x∈vars_term s ∪ vars_term t. δ x ≈ θ x ⋅ ρ"
proof -
  have "inv_vars [(s, t)] Var (nv0 s t)" using vars_below_nv0[of s t] by (simp add: inv_vars_def)
  then obtain θ δ' where θ: "θ ∈ set (acunif [(s, t)] Var (nv0 s t))"
    "∀x<nv0 s t. δ' x = δ x" "fixes_ac δ' θ"
    using acunif_complete[OF total dom, of δ] u by auto
  have "δ x ≈ θ x ⋅ δ'" if "x ∈ vars_term s ∪ vars_term t" for x
  proof -
    have "x < nv0 s t" using vars_below_nv0[of s t] that by auto
    then have "δ x = δ' x" using θ(2) by simp
    then show ?thesis using θ(3) by (simp add: fixes_ac_def)
  qed
  then show ?thesis using θ(1) by (auto simp: ac_unifiers_eq)
qed

end

end
