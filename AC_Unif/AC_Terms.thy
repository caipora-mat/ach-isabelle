(*
Author: Guilherme Borges Brandão
*)

theory AC_Terms
  imports AC_Theory
begin

section ‹Terms with several AC symbols›

text ‹
  The signature has any number of AC symbols, given by a predicate ‹ac›. An AC symbol is
  binary: ‹Fun f [s, t]› with ‹ac f› is an AC application. An AC symbol applied to a
  different number of arguments behaves as a free symbol (the AC axioms do not apply to it), so
  every term is meaningful and no well-formedness restriction is needed. AC equality is the
  equational theory (‹Equational_Theory›) of the AC axioms of all AC symbols.
›

datatype ('f, 'v) nf = NV 'v | NF 'f "('f, 'v) nf list" | NA 'f "('f, 'v) nf multiset"

text ‹The arguments of a normal form below the AC symbol ‹f›.›

fun nfa :: "'f ⇒ ('f, 'v) nf ⇒ ('f, 'v) nf multiset" where
  "nfa f (NA g M) = (if g = f then M else {#NA g M#})"
| "nfa f n = {#n#}"

locale ac_sig =
  fixes ac :: "'f ⇒ bool"
begin

definition AC_ids :: "('f, 'v) identity set" where
  "AC_ids = (⋃f ∈ Collect ac. ac_signature.AC_axioms f)"

abbreviation eq_AC :: "('f, 'v) term ⇒ ('f, 'v) term ⇒ bool" (infix ‹≈› 50)
  where "s ≈ t ≡ eq_theory (AC_ids :: ('f, 'v) identity set) s t"

sublocale acs: equational_theory AC_ids .

lemma ac_assoc: "ac f ⟹ Fun f [s, Fun f [t, u]] ≈ Fun f [Fun f [s, t], u]"
  using eq_theory.axiom[of "Fun f [s, Fun f [t, u]]" "Fun f [Fun f [s, t], u]" AC_ids Var]
  by (auto simp: AC_ids_def ac_signature.AC_axioms_def)

lemma ac_comm: "ac f ⟹ Fun f [s, t] ≈ Fun f [t, s]"
  using eq_theory.axiom[of "Fun f [s, t]" "Fun f [t, s]" AC_ids Var]
  by (auto simp: AC_ids_def ac_signature.AC_axioms_def)

lemma ac_left_comm: "ac f ⟹ Fun f [a, Fun f [b, c]] ≈ Fun f [b, Fun f [a, c]]"
proof -
  assume f: "ac f"
  have "Fun f [a, Fun f [b, c]] ≈ Fun f [Fun f [a, b], c]"
    by (rule ac_assoc[OF f])
  also have "… ≈ Fun f [Fun f [b, a], c]"
    by (intro eq_theory_cong2 ac_comm[OF f] eq_theory.refl)
  also have "… ≈ Fun f [b, Fun f [a, c]]"
    by (rule eq_theory.sym[OF ac_assoc[OF f]])
  finally show ?thesis .
qed

subsection ‹Normal forms›

fun nf :: "('f, 'v) term ⇒ ('f, 'v) nf" where
  "nf (Var x) = NV x"
| "nf (Fun f [s, t]) = (if ac f then NA f (nfa f (nf s) + nfa f (nf t)) else NF f [nf s, nf t])"
| "nf (Fun f ts) = NF f (map nf ts)"

definition nf_app :: "'f ⇒ ('f, 'v) nf list ⇒ ('f, 'v) nf" where
  "nf_app f ns = (if ac f ∧ length ns = 2 then NA f (nfa f (ns ! 0) + nfa f (ns ! 1)) else NF f ns)"

lemma nf_Fun: "nf (Fun f ts) = nf_app f (map nf ts)"
proof (cases ts)
  case (Cons a ts')
  then show ?thesis
  proof (cases ts')
    case (Cons b ts'')
    then show ?thesis using ‹ts = a # ts'› by (cases ts'') (auto simp: nf_app_def)
  qed (auto simp: nf_app_def)
qed (auto simp: nf_app_def)

lemma nf_NV: "nf t = NV x ⟹ t = Var x"
  by (cases t) (auto simp: nf_Fun nf_app_def split: if_splits)

lemma nf_NA: "nf t = NA f M ⟹ ∃a b. t = Fun f [a, b] ∧ ac f ∧ M = nfa f (nf a) + nfa f (nf b)"
proof (cases t)
  case (Fun g ts)
  assume "nf t = NA f M"
  then show ?thesis using Fun
    by (auto simp: nf_Fun nf_app_def numeral_2_eq_2 length_Suc_conv split: if_splits)
qed simp

lemma nf_NF: "nf t = NF f ns ⟹ ∃ts. t = Fun f ts ∧ ns = map nf ts ∧ ¬ (ac f ∧ length ts = 2)"
proof (cases t)
  case (Fun g ts)
  assume "nf t = NF f ns"
  then show ?thesis using Fun
    by (auto simp: nf_Fun nf_app_def split: if_splits)
qed simp

lemma nfa_nf_nonempty [simp]: "nfa f (nf t) ≠ {#}"
proof (induction t arbitrary: f rule: nf.induct)
  case (2 g s t)
  then show ?case by auto
qed auto

lemma size_nfa_nf_pos: "size (nfa f (nf t)) > 0"
  using nfa_nf_nonempty[of f t] nonempty_has_size by blast

lemma size_NA: "nf t = NA f M ⟹ size M ≥ 2"
proof -
  assume "nf t = NA f M"
  then obtain a b where "M = nfa f (nf a) + nfa f (nf b)" using nf_NA by blast
  then show ?thesis using size_nfa_nf_pos[of f a] size_nfa_nf_pos[of f b] by simp
qed

subsection ‹AC-equal terms have the same normal form›

lemma nf_axiom:
  assumes "(l, r) ∈ AC_ids"
  shows "nf (l ⋅ σ) = nf (r ⋅ σ)"
  using assms by (auto simp: AC_ids_def ac_signature.AC_axioms_def ac_simps)

lemma eq_AC_imp_nf_eq:
  assumes "s ≈ t"
  shows "nf s = nf t"
  using assms
proof (induction rule: eq_theory.induct)
  case (axiom l r σ)
  then show ?case by (rule nf_axiom)
next
  case (cong ss ts f)
  then have "map nf ss = map nf ts" by (auto intro: nth_equalityI)
  then show ?case by (simp add: nf_Fun)
qed simp_all

text ‹AC equality preserves the size of terms, hence it is regular for the occurs check.›

lemma eq_AC_size:
  assumes "s ≈ t"
  shows "size s = size t"
  using assms
proof (induction rule: eq_theory.induct)
  case (axiom l r σ)
  then show ?case by (auto simp: AC_ids_def ac_signature.AC_axioms_def)
next
  case (cong ss ts f)
  then have "map size ss = map size ts" by (auto intro: nth_equalityI)
  then have "size_list size ss = size_list size ts"
    by (simp add: size_list_conv_sum_list) (metis length_map)
  then show ?case by simp
qed simp_all

subsection ‹Arguments of AC applications›

fun args_ac :: "'f ⇒ ('f, 'v) term ⇒ ('f, 'v) term list" where
  "args_ac f (Fun g [s, t]) = (if g = f ∧ ac f then args_ac f s @ args_ac f t else [Fun g [s, t]])"
| "args_ac f t = [t]"

text ‹The right-nested AC application of ‹f› to a non-empty list of arguments.›

fun mk_ac :: "'f ⇒ ('f, 'v) term list ⇒ ('f, 'v) term" where
  "mk_ac f [] = undefined"
| "mk_ac f [t] = t"
| "mk_ac f (t # u # ts) = Fun f [t, mk_ac f (u # ts)]"

text ‹‹t› is an AC application of ‹f›.›

definition is_ac_app :: "'f ⇒ ('f, 'v) term ⇒ bool" where
  "is_ac_app f t ⟷ ac f ∧ (∃a b. t = Fun f [a, b])"

lemma is_ac_app_simps [simp]:
  "¬ is_ac_app f (Var x)"
  "is_ac_app f (Fun g ts) ⟷ ac f ∧ g = f ∧ length ts = 2"
  by (auto simp: is_ac_app_def numeral_2_eq_2 length_Suc_conv)

lemma args_ac_nonempty [simp]: "args_ac f t ≠ []"
  by (induction f t rule: args_ac.induct) auto

lemma args_ac_not_app [simp]: "¬ is_ac_app f t ⟹ args_ac f t = [t]"
  by (cases "(f, t)" rule: args_ac.cases) auto

lemma args_ac_app: "ac f ⟹ args_ac f (Fun f [s, t]) = args_ac f s @ args_ac f t"
  by simp

lemma args_ac_no_app: "u ∈ set (args_ac f t) ⟹ ¬ is_ac_app f u"
  by (induction f t rule: args_ac.induct) (auto split: if_splits)

lemma size_args_ac_le: "u ∈ set (args_ac f t) ⟹ size u ≤ size t"
  by (induction f t rule: args_ac.induct) (fastforce split: if_splits)+

lemma size_args_ac_less:
  assumes "is_ac_app f t" "u ∈ set (args_ac f t)"
  shows "size u < size t"
proof -
  obtain a b where t: "t = Fun f [a, b]" "ac f" using assms(1) by (auto simp: is_ac_app_def)
  then have "u ∈ set (args_ac f a) ∨ u ∈ set (args_ac f b)" using assms(2) by simp
  then show ?thesis using t size_args_ac_le[of u f a] size_args_ac_le[of u f b] by auto
qed

lemma vars_args_ac: "vars_term t = (⋃u ∈ set (args_ac f t). vars_term u)"
  by (induction f t rule: args_ac.induct) auto

lemma nfa_nf_not_app: "¬ is_ac_app f t ⟹ nfa f (nf t) = {#nf t#}"
proof -
  assume h: "¬ is_ac_app f t"
  show ?thesis
  proof (cases "nf t")
    case (NA g M)
    then obtain a b where "t = Fun g [a, b]" "ac g" using nf_NA by blast
    then show ?thesis using h NA by auto
  qed auto
qed

lemma nfa_nf_args: "ac f ⟹ nfa f (nf t) = mset (map nf (args_ac f t))"
proof (induction f t rule: args_ac.induct)
  case (1 f g s t)
  then show ?case by (auto simp: nfa_nf_not_app)
qed (simp_all add: nfa_nf_not_app)

lemma mk_ac_Cons: "ts ≠ [] ⟹ mk_ac f (t # ts) = Fun f [t, mk_ac f ts]"
  by (cases ts) auto

lemma mk_ac_single [simp]: "mk_ac f [t] = t"
  by simp

lemma mk_ac_cong:
  assumes "list_all2 (≈) xs ys"
  shows "mk_ac f xs ≈ mk_ac f ys"
  using assms
proof (induction xs arbitrary: ys rule: mk_ac.induct)
  case (2 f t)
  then show ?case by (auto simp: list_all2_Cons1)
next
  case (3 f t u ts)
  then obtain t' u' ts' where "ys = t' # u' # ts'" by (auto simp: list_all2_Cons1)
  with 3 show ?case by (auto intro: eq_theory_cong2)
qed simp

lemma mk_ac_rotate:
  assumes "ac f" "A @ B ≠ []"
  shows "mk_ac f (A @ x # B) ≈ mk_ac f (x # A @ B)"
  using assms(2)
proof (induction A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  show ?case
  proof (cases "A @ B = []")
    case True
    then show ?thesis by (simp add: ac_comm[OF assms(1)])
  next
    case False
    have "mk_ac f ((a # A) @ x # B) = Fun f [a, mk_ac f (A @ x # B)]"
      by (simp add: mk_ac_Cons)
    also have "… ≈ Fun f [a, mk_ac f (x # A @ B)]"
      using Cons.IH[OF False] by (intro eq_theory_cong2) auto
    also have "… = Fun f [a, Fun f [x, mk_ac f (A @ B)]]"
      using False by (simp add: mk_ac_Cons)
    also have "… ≈ Fun f [x, Fun f [a, mk_ac f (A @ B)]]"
      by (rule ac_left_comm[OF assms(1)])
    also have "… = mk_ac f (x # (a # A) @ B)"
      using False by (simp add: mk_ac_Cons)
    finally show ?thesis .
  qed
qed

lemma mk_ac_perm:
  assumes "ac f" "mset xs = mset ys"
  shows "mk_ac f xs ≈ mk_ac f ys"
  using assms(2)
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have "x ∈ set ys" by (metis list.set_intros(1) set_mset_mset)
  then obtain A B where ys: "ys = A @ x # B" by (meson split_list)
  with Cons.prems have mset_xs: "mset xs = mset (A @ B)" by simp
  show ?case
  proof (cases "xs = []")
    case True
    with mset_xs ys show ?thesis by simp
  next
    case False
    then have "A @ B ≠ []" using mset_xs by auto
    have "mk_ac f (x # xs) = Fun f [x, mk_ac f xs]"
      using False by (simp add: mk_ac_Cons)
    also have "… ≈ Fun f [x, mk_ac f (A @ B)]"
      using Cons.IH[OF mset_xs] by (intro eq_theory_cong2) auto
    also have "… = mk_ac f (x # A @ B)"
      using ‹A @ B ≠ []› by (simp add: mk_ac_Cons)
    also have "… ≈ mk_ac f ys"
      unfolding ys by (rule eq_theory.sym[OF mk_ac_rotate[OF assms(1) ‹A @ B ≠ []›]])
    finally show ?thesis .
  qed
qed

lemma mk_ac_append:
  assumes "ac f" "xs ≠ []" "ys ≠ []"
  shows "mk_ac f (xs @ ys) ≈ Fun f [mk_ac f xs, mk_ac f ys]"
  using assms(2)
proof (induction xs)
  case (Cons t xs)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis using assms(3) by (simp add: mk_ac_Cons)
  next
    case False
    have "mk_ac f ((t # xs) @ ys) = Fun f [t, mk_ac f (xs @ ys)]"
      using False by (simp add: mk_ac_Cons)
    also have "… ≈ Fun f [t, Fun f [mk_ac f xs, mk_ac f ys]]"
      using Cons.IH[OF False] by (intro eq_theory_cong2) auto
    also have "… ≈ Fun f [Fun f [t, mk_ac f xs], mk_ac f ys]"
      by (rule ac_assoc[OF assms(1)])
    also have "… = Fun f [mk_ac f (t # xs), mk_ac f ys]"
      using False by (simp add: mk_ac_Cons)
    finally show ?thesis .
  qed
qed simp

lemma mk_ac_args: "ac f ⟹ mk_ac f (args_ac f t) ≈ t"
proof (induction f t rule: args_ac.induct)
  case (1 f g s t)
  show ?case
  proof (cases "g = f")
    case True
    have "mk_ac f (args_ac f s @ args_ac f t) ≈ Fun f [mk_ac f (args_ac f s), mk_ac f (args_ac f t)]"
      by (rule mk_ac_append[OF 1(3)]) simp_all
    also have "… ≈ Fun f [s, t]"
      using 1 True by (intro eq_theory_cong2) auto
    finally show ?thesis using True 1(3) by simp
  qed simp
qed simp_all

lemma subst_mk_ac: "ts ≠ [] ⟹ mk_ac f ts ⋅ σ = mk_ac f (map (λt. t ⋅ σ) ts)"
  by (induction f ts rule: mk_ac.induct) auto

lemma vars_mk_ac: "ts ≠ [] ⟹ vars_term (mk_ac f ts) = (⋃t ∈ set ts. vars_term t)"
  by (induction f ts rule: mk_ac.induct) auto

lemma is_ac_app_mk_ac: "ac f ⟹ length ts ≥ 2 ⟹ is_ac_app f (mk_ac f ts)"
  by (cases "(f, ts)" rule: mk_ac.cases) auto

lemma args_ac_mk_ac:
  assumes "ac f" "ts ≠ []" "∀t ∈ set ts. ¬ is_ac_app f t"
  shows "args_ac f (mk_ac f ts) = ts"
  using assms(2,3)
proof (induction ts)
  case (Cons t ts)
  then show ?case using assms(1) by (cases ts) (auto simp: mk_ac_Cons)
qed simp

subsection ‹Terms with the same normal form are AC-equal›

lemma mset_map_match:
  assumes "mset (map h xs) = mset (map h ys)"
  shows "∃zs. mset zs = mset ys ∧ list_all2 (λa b. h a = h b) xs zs"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have "h x ∈# mset (map h ys)" by (metis list.set_intros(1) list.simps(9) set_mset_mset)
  then obtain y where y: "y ∈ set ys" "h y = h x" by auto
  obtain A B where AB: "ys = A @ y # B" "y ∉ set A" using split_list_first[OF y(1)] by blast
  then have rm: "remove1 y ys = A @ B" by (simp add: remove1_append)
  have "mset (map h ys) = mset (map h (remove1 y ys)) + {#h y#}"
    unfolding rm AB(1) by simp
  then have "mset (map h xs) = mset (map h (remove1 y ys))"
    using Cons.prems y(2) by simp
  from Cons.IH[OF this] obtain zs
    where "mset zs = mset (remove1 y ys)" "list_all2 (λa b. h a = h b) xs zs" by blast
  then show ?case using y
    by (intro exI[of _ "y # zs"]) (auto simp: mset_remove1)
qed

lemma size_arg_less: "x ∈ set xs ⟹ size x < Suc (size_list size xs)"
  by (induction xs) auto

lemma nf_eq_imp_eq_AC: "nf s = nf t ⟹ s ≈ t"
proof (induction "size s + size t" arbitrary: s t rule: less_induct)
  case less
  show ?case
  proof (cases "nf s")
    case (NV x)
    then show ?thesis using less.prems by (auto dest!: nf_NV)
  next
    case (NA f M)
    obtain a b where s: "s = Fun f [a, b]" "ac f" using nf_NA[OF NA] by blast
    obtain c d where t: "t = Fun f [c, d]" using nf_NA[of t f M] NA less.prems by auto
    have M: "M = mset (map nf (args_ac f s))" "M = mset (map nf (args_ac f t))"
      using nfa_nf_args[OF s(2), of s] nfa_nf_args[OF s(2), of t] NA less.prems by auto
    then obtain zs where zs: "mset zs = mset (args_ac f t)" "list_all2 (λa b. nf a = nf b) (args_ac f s) zs"
      using mset_map_match[of nf "args_ac f s" "args_ac f t"] by auto
    have len: "length (args_ac f s) = length zs"
      and nfeq: "⋀i. i < length zs ⟹ nf (args_ac f s ! i) = nf (zs ! i)"
      using zs(2) by (auto simp: list_all2_conv_all_nth)
    have app: "is_ac_app f s" "is_ac_app f t" using s t by auto
    have "list_all2 (≈) (args_ac f s) zs"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (args_ac f s) = length zs" by (rule len)
      fix i
      assume i: "i < length (args_ac f s)"
      have u: "args_ac f s ! i ∈ set (args_ac f s)" using i by simp
      have "zs ! i ∈ set zs" using i len by simp
      then have z: "zs ! i ∈ set (args_ac f t)" using zs(1) by (metis set_mset_mset)
      have "size (args_ac f s ! i) + size (zs ! i) < size s + size t"
        using size_args_ac_less[OF app(1) u] size_args_ac_less[OF app(2) z] by simp
      then show "args_ac f s ! i ≈ zs ! i"
        using less.hyps nfeq[of i] i len by simp
    qed
    then have "mk_ac f (args_ac f s) ≈ mk_ac f zs" by (rule mk_ac_cong)
    also have "… ≈ mk_ac f (args_ac f t)" by (rule mk_ac_perm[OF s(2) zs(1)])
    finally have st: "mk_ac f (args_ac f s) ≈ mk_ac f (args_ac f t)" .
    have "s ≈ mk_ac f (args_ac f s)" by (rule eq_theory.sym[OF mk_ac_args[OF s(2)]])
    also have "… ≈ mk_ac f (args_ac f t)" by (rule st)
    also have "… ≈ t" by (rule mk_ac_args[OF s(2)])
    finally show ?thesis .
  next
    case (NF f ns)
    obtain ss where s: "s = Fun f ss" "ns = map nf ss" using nf_NF[OF NF] by blast
    obtain ts where t: "t = Fun f ts" "ns = map nf ts" using nf_NF[of t f ns] NF less.prems by auto
    have len: "length ss = length ts" using s(2) t(2) by (metis length_map)
    show ?thesis unfolding s(1) t(1)
    proof (rule eq_theory.cong[OF len])
      fix i
      assume i: "i < length ss"
      have "nf (ss ! i) = nf (ts ! i)" using s(2) t(2) i len by (metis nth_map)
      moreover have "size (ss ! i) < size s" "size (ts ! i) < size t"
        using i len s(1) t(1) size_arg_less[of "ss ! i" ss] size_arg_less[of "ts ! i" ts] by auto
      ultimately show "ss ! i ≈ ts ! i" using less.hyps by fastforce
    qed
  qed
qed

theorem eq_AC_iff_nf: "s ≈ t ⟷ nf s = nf t"
  using eq_AC_imp_nf_eq nf_eq_imp_eq_AC by blast

lemma nfa_eq_imp_nf_eq:
  assumes "nfa f (nf x) = nfa f (nf y)"
  shows "nf x = nf y"
proof (cases "∃M. nf x = NA f M")
  case True
  then obtain M where M: "nf x = NA f M" by blast
  then have "size (nfa f (nf y)) ≥ 2" using size_NA[OF M] assms by simp
  then obtain M' where "nf y = NA f M'" by (cases "nf y") (auto split: if_splits)
  then show ?thesis using M assms by simp
next
  case False
  then have x: "nfa f (nf x) = {#nf x#}" by (cases "nf x") auto
  show ?thesis
  proof (cases "∃M. nf y = NA f M")
    case True
    then obtain M where M: "nf y = NA f M" by blast
    then have "size (nfa f (nf x)) ≥ 2" using size_NA[OF M] assms by simp
    then show ?thesis using x by simp
  next
    case False
    then have "nfa f (nf y) = {#nf y#}" by (cases "nf y") auto
    then show ?thesis using x assms by simp
  qed
qed

end

end
