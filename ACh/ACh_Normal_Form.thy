(*
Author: Guilherme Borges Brandão
*)

theory ACh_Normal_Form
  imports ACh_Theory
begin

section \<open>Normal forms modulo ACh\<close>

text \<open>
  Orienting the homomorphism identity as \<open>h(x + y) \<rightarrow> h(x) + h(y)\<close> and working modulo AC,
  every term becomes a sum of \<^emph>\<open>atoms\<close>: terms of the form \<open>h\<^sup>n(x)\<close> or \<open>h\<^sup>n(f(t\<^sub>1, \<dots>, t\<^sub>m))\<close>,
  where \<open>f\<close> is neither \<open>+\<close> nor \<open>h\<close> and the arguments \<open>t\<^sub>i\<close> are again in normal form.
  Modulo AC, a sum is determined by the multiset of its summands. So we represent normal
  forms directly as multisets of atoms, which makes AC-equality syntactic equality.

  The main result is \<open>s =\<^sub>A\<^sub>C\<^sub>h t \<longleftrightarrow> nf s = nf t\<close>. It is the basis for the completeness proof of
  the inference system: injectivity of \<open>h\<close>, decomposition for free symbols, the clash cases,
  and the Splitting lemma (equation (3.1) of the dissertation) all follow from it.
\<close>

datatype ('f, 'v) atom =
  AVar nat 'v
| AFun nat 'f "('f, 'v) atom multiset list"

text \<open>\<open>AVar n x\<close> stands for \<open>h\<^sup>n(x)\<close> and \<open>AFun n f [M\<^sub>1, \<dots>, M\<^sub>m]\<close> for \<open>h\<^sup>n(f(M\<^sub>1, \<dots>, M\<^sub>m))\<close>.\<close>

fun level :: "('f, 'v) atom \<Rightarrow> nat" where
  "level (AVar n x) = n"
| "level (AFun n f Ms) = n"

text \<open>Applying \<open>h\<close> to an atom, and removing one \<open>h\<close> from it.\<close>

fun hinc :: "('f, 'v) atom \<Rightarrow> ('f, 'v) atom" where
  "hinc (AVar n x) = AVar (Suc n) x"
| "hinc (AFun n f Ms) = AFun (Suc n) f Ms"

fun hdec :: "('f, 'v) atom \<Rightarrow> ('f, 'v) atom" where
  "hdec (AVar n x) = AVar (n - 1) x"
| "hdec (AFun n f Ms) = AFun (n - 1) f Ms"

lemma level_hinc [simp]: "level (hinc a) = Suc (level a)"
  by (cases a) auto

lemma hdec_hinc [simp]: "hdec (hinc a) = a"
  by (cases a) auto

lemma hinc_hdec: "level a > 0 \<Longrightarrow> hinc (hdec a) = a"
  by (cases a) auto

lemma inj_hinc: "inj hinc"
  by (metis hdec_hinc injI)

context ach_signature
begin

text \<open>
  Applications \<open>f(t\<^sub>1, \<dots>, t\<^sub>m)\<close> whose root is not an interpreted symbol with its intended arity.
  The function \<open>nf_app f [nf t\<^sub>1, \<dots>, nf t\<^sub>m]\<close> computes the normal form of \<open>f(t\<^sub>1, \<dots>, t\<^sub>m)\<close>.
\<close>

definition free_app :: "'f \<Rightarrow> nat \<Rightarrow> bool" where
  "free_app f n \<longleftrightarrow> \<not> (f = plus \<and> n = 2) \<and> \<not> (f = hom \<and> n = 1)"

definition nf_app :: "'f \<Rightarrow> ('f, 'v) atom multiset list \<Rightarrow> ('f, 'v) atom multiset" where
  "nf_app f Ms =
    (if f = plus \<and> length Ms = 2 then Ms ! 0 + Ms ! 1
     else if f = hom \<and> length Ms = 1 then image_mset hinc (Ms ! 0)
     else {#AFun 0 f Ms#})"

fun nf :: "('f, 'v) term \<Rightarrow> ('f, 'v) atom multiset" where
  "nf (Var x) = {#AVar 0 x#}"
| "nf (Fun f ts) = nf_app f (map nf ts)"

lemma nf_Plus [simp]: "nf (s \<oplus> t) = nf s + nf t"
  by (simp add: nf_app_def)

lemma nf_H [simp]: "nf (H t) = image_mset hinc (nf t)"
  using plus_neq_hom by (simp add: nf_app_def)

lemma nf_free_app [simp]: "free_app f (length ts) \<Longrightarrow> nf (Fun f ts) = {#AFun 0 f (map nf ts)#}"
  by (auto simp: nf_app_def free_app_def)

lemma nf_nonempty [simp]: "nf t \<noteq> {#}"
proof (induction t)
  case (Fun f ts)
  then show ?case
    by (cases ts rule: remdups_adj.cases) (auto simp: nf_app_def)
qed simp

text \<open>From now on, \<open>nf\<close> on applications is unfolded only through the lemmas above.\<close>

declare nf.simps(2) [simp del]

lemma nf_Fun: "nf (Fun f ts) = nf_app f (map nf ts)"
  by (fact nf.simps(2))

subsection \<open>ACh-equal terms have the same normal form\<close>

lemma nf_axiom:
  assumes "(l, r) \<in> ACh_axioms"
  shows "nf (l \<cdot> \<sigma>) = nf (r \<cdot> \<sigma>)"
  using assms by (auto simp: ACh_axioms_def AC_axioms_def ac_simps)

lemma eq_ACh_imp_nf_eq:
  assumes "s \<approx>\<^sub>A\<^sub>C\<^sub>h t"
  shows "nf s = nf t"
  using assms
proof (induction rule: eq_theory.induct)
  case (axiom l r \<sigma>)
  then show ?case
    by (rule nf_axiom)
next
  case (cong ss ts f)
  then have "map nf ss = map nf ts"
    by (simp add: map_equality_iff)
  then show ?case
    by (simp add: nf_Fun)
qed simp_all

subsection \<open>Sums modulo AC depend only on the multiset of summands\<close>

lemma eq_AC_left_comm: "a \<oplus> (b \<oplus> c) \<approx>\<^sub>A\<^sub>C b \<oplus> (a \<oplus> c)"
proof -
  have "a \<oplus> (b \<oplus> c) \<approx>\<^sub>A\<^sub>C (a \<oplus> b) \<oplus> c"
    by (rule eq_AC_assoc)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C (b \<oplus> a) \<oplus> c"
    by (intro eq_theory_cong2 eq_AC_comm eq_theory.refl)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C b \<oplus> (a \<oplus> c)"
    by (rule eq_theory.sym[OF eq_AC_assoc])
  finally show ?thesis .
qed

lemma sum_terms_Cons: "ts \<noteq> [] \<Longrightarrow> sum_terms (t # ts) = t \<oplus> sum_terms ts"
  by (cases ts) auto

lemma sum_terms_rotate:
  assumes "A @ B \<noteq> []"
  shows "sum_terms (A @ x # B) \<approx>\<^sub>A\<^sub>C sum_terms (x # A @ B)"
  using assms
proof (induction A)
  case Nil
  then show ?case
    by simp
next
  case (Cons a A)
  show ?case
  proof (cases "A @ B = []")
    case True
    then show ?thesis
      by (simp add: eq_AC_comm)
  next
    case False
    have "sum_terms ((a # A) @ x # B) = a \<oplus> sum_terms (A @ x # B)"
      by (simp add: sum_terms_Cons)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C a \<oplus> sum_terms (x # A @ B)"
      using Cons.IH[OF False] by (intro eq_theory_cong2) auto
    also have "\<dots> = a \<oplus> (x \<oplus> sum_terms (A @ B))"
      using False by (simp add: sum_terms_Cons)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C x \<oplus> (a \<oplus> sum_terms (A @ B))"
      by (rule eq_AC_left_comm)
    also have "\<dots> = sum_terms (x # (a # A) @ B)"
      using False by (simp add: sum_terms_Cons)
    finally show ?thesis .
  qed
qed

lemma sum_terms_perm:
  assumes "mset xs = mset ys"
  shows "sum_terms xs \<approx>\<^sub>A\<^sub>C sum_terms ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then have "x \<in> set ys"
    by (metis list.set_intros(1) set_mset_mset)
  then obtain A B where ys: "ys = A @ x # B"
    by (meson split_list)
  with Cons.prems have mset_xs: "mset xs = mset (A @ B)"
    by simp
  show ?case
  proof (cases "xs = []")
    case True
    with mset_xs ys show ?thesis
      by simp
  next
    case False
    then have "A @ B \<noteq> []"
      using mset_xs by auto
    have "sum_terms (x # xs) = x \<oplus> sum_terms xs"
      using False by (simp add: sum_terms_Cons)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C x \<oplus> sum_terms (A @ B)"
      using Cons.IH[OF mset_xs] by (intro eq_theory_cong2) auto
    also have "\<dots> = sum_terms (x # A @ B)"
      using \<open>A @ B \<noteq> []\<close> by (simp add: sum_terms_Cons)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C sum_terms ys"
      unfolding ys by (rule eq_theory.sym[OF sum_terms_rotate[OF \<open>A @ B \<noteq> []\<close>]])
    finally show ?thesis .
  qed
qed

lemma sum_terms_append:
  assumes "xs \<noteq> []" and "ys \<noteq> []"
  shows "sum_terms (xs @ ys) \<approx>\<^sub>A\<^sub>C sum_terms xs \<oplus> sum_terms ys"
  using assms(1)
proof (induction xs rule: sum_terms.induct)
  case (2 t)
  then show ?case
    using assms(2) by (simp add: sum_terms_Cons)
next
  case (3 t u ts)
  have "sum_terms ((t # u # ts) @ ys) = t \<oplus> sum_terms ((u # ts) @ ys)"
    by simp
  also have "\<dots> \<approx>\<^sub>A\<^sub>C t \<oplus> (sum_terms (u # ts) \<oplus> sum_terms ys)"
    using 3 by (intro eq_theory_cong2) auto
  also have "\<dots> \<approx>\<^sub>A\<^sub>C sum_terms (t # u # ts) \<oplus> sum_terms ys"
    by (simp add: eq_AC_assoc)
  finally show ?case .
qed simp

text \<open>
  The sum of a non-empty multiset of terms, in some order. By \<open>sum_terms_perm\<close> the chosen
  order is irrelevant modulo AC.
\<close>

definition msum :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term" where
  "msum M = sum_terms (SOME L. mset L = M)"

lemma mset_list_of: "mset (SOME L. mset L = M) = M"
  by (rule someI_ex) (use ex_mset in blast)

lemma msum_eq: "mset L = M \<Longrightarrow> msum M \<approx>\<^sub>A\<^sub>C sum_terms L"
  unfolding msum_def by (rule sum_terms_perm) (simp add: mset_list_of)

lemma msum_single [simp]: "msum {#t#} = t"
proof -
  have "(SOME L. mset L = {#t#}) = [t]"
    using mset_list_of[of "{#t#}"]
    by (cases "SOME L. mset L = {#t#}") auto
  then show ?thesis
    by (simp add: msum_def)
qed

lemma msum_union:
  assumes "M \<noteq> {#}" and "N \<noteq> {#}"
  shows "msum (M + N) \<approx>\<^sub>A\<^sub>C msum M \<oplus> msum N"
proof -
  obtain LM LN where LM: "mset LM = M" and LN: "mset LN = N"
    by (meson ex_mset)
  then have "LM \<noteq> []" "LN \<noteq> []"
    using assms by auto
  have "msum (M + N) \<approx>\<^sub>A\<^sub>C sum_terms (LM @ LN)"
    by (rule msum_eq) (simp add: LM LN)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C sum_terms LM \<oplus> sum_terms LN"
    by (rule sum_terms_append) fact+
  also have "\<dots> \<approx>\<^sub>A\<^sub>C msum M \<oplus> msum N"
    using eq_theory_cong2[OF eq_theory.sym[OF msum_eq[OF LM]] eq_theory.sym[OF msum_eq[OF LN]]] .
  finally show ?thesis .
qed

lemma msum_image_H:
  assumes "M \<noteq> {#}"
  shows "msum (image_mset H M) \<approx>\<^sub>A\<^sub>C\<^sub>h H (msum M)"
proof -
  obtain L where L: "mset L = M"
    by (meson ex_mset)
  then have "L \<noteq> []"
    using assms by auto
  have "msum (image_mset H M) \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map H L)"
    using msum_eq[of "map H L"] L by (simp add: eq_AC_imp_eq_ACh)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h H (sum_terms L)"
    using eq_ACh_hom_sum[OF \<open>L \<noteq> []\<close>] by (rule eq_theory.sym)
  also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h H (msum M)"
    using eq_theory_cong1[OF eq_theory.sym[OF eq_AC_imp_eq_ACh[OF msum_eq[OF L]]]] .
  finally show ?thesis .
qed

subsection \<open>From normal forms back to terms\<close>

primrec atom_term :: "('f, 'v) atom \<Rightarrow> ('f, 'v) term" where
  "atom_term (AVar n x) = (H ^^ n) (Var x)"
| "atom_term (AFun n f Ms) = (H ^^ n) (Fun f (map msum (map (image_mset atom_term) Ms)))"

definition rep :: "('f, 'v) atom multiset \<Rightarrow> ('f, 'v) term" where
  "rep M = msum (image_mset atom_term M)"

lemma atom_term_hinc [simp]: "atom_term (hinc a) = H (atom_term a)"
  by (cases a) simp_all

lemma rep_union:
  assumes "M \<noteq> {#}" and "N \<noteq> {#}"
  shows "rep (M + N) \<approx>\<^sub>A\<^sub>C\<^sub>h rep M \<oplus> rep N"
  using msum_union[of "image_mset atom_term M" "image_mset atom_term N"] assms
  by (simp add: rep_def eq_AC_imp_eq_ACh)

lemma rep_image_hinc:
  assumes "M \<noteq> {#}"
  shows "rep (image_mset hinc M) \<approx>\<^sub>A\<^sub>C\<^sub>h H (rep M)"
proof -
  have "image_mset atom_term (image_mset hinc M) = image_mset H (image_mset atom_term M)"
    by (simp add: multiset.map_comp comp_def)
  then show ?thesis
    using msum_image_H[of "image_mset atom_term M"] assms by (simp add: rep_def)
qed

lemma rep_free:
  "rep {#AFun 0 f Ms#} = Fun f (map rep Ms)"
  by (simp add: rep_def comp_def)

text \<open>Every term is ACh-equal to the term read back from its normal form.\<close>

lemma eq_ACh_rep_nf: "t \<approx>\<^sub>A\<^sub>C\<^sub>h rep (nf t)"
proof (induction t)
  case (Var x)
  then show ?case
    by (simp add: rep_def)
next
  case (Fun f ts)
  consider (plus) a b where "f = plus" "ts = [a, b]"
    | (hom) a where "f = hom" "ts = [a]"
    | (free) "free_app f (length ts)"
    by (cases ts rule: remdups_adj.cases) (auto simp: free_app_def)
  then show ?case
  proof cases
    case plus
    have "a \<oplus> b \<approx>\<^sub>A\<^sub>C\<^sub>h rep (nf a) \<oplus> rep (nf b)"
      using Fun.IH plus by (intro eq_theory_cong2) auto
    also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h rep (nf a + nf b)"
      by (rule eq_theory.sym[OF rep_union]) simp_all
    finally show ?thesis
      using plus by simp
  next
    case hom
    have "H a \<approx>\<^sub>A\<^sub>C\<^sub>h H (rep (nf a))"
      using Fun.IH hom by (intro eq_theory_cong1) auto
    also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h rep (image_mset hinc (nf a))"
      by (rule eq_theory.sym[OF rep_image_hinc]) simp
    finally show ?thesis
      using hom by simp
  next
    case free
    have "list_all2 (\<approx>\<^sub>A\<^sub>C\<^sub>h) ts (map rep (map nf ts))"
      using Fun.IH by (auto simp: list_all2_conv_all_nth)
    then show ?thesis
      using free by (simp add: rep_free eq_theory_cong_list)
  qed
qed

text \<open>The main theorem: ACh-equality is decided by comparing normal forms.\<close>

theorem eq_ACh_iff_nf: "s \<approx>\<^sub>A\<^sub>C\<^sub>h t \<longleftrightarrow> nf s = nf t"
proof
  assume "nf s = nf t"
  then show "s \<approx>\<^sub>A\<^sub>C\<^sub>h t"
    using eq_ACh_rep_nf[of s] eq_ACh_rep_nf[of t] by (metis eq_theory.sym eq_theory.trans)
qed (rule eq_ACh_imp_nf_eq)

lemma nf_sum_terms: "us \<noteq> [] \<Longrightarrow> nf (sum_terms us) = sum_list (map nf us)"
  by (induction us rule: sum_terms.induct) auto

lemma rep_sum_list:
  assumes "Ms \<noteq> []" and "\<And>M. M \<in> set Ms \<Longrightarrow> M \<noteq> {#}"
  shows "rep (sum_list Ms) \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map rep Ms)"
  using assms
proof (induction Ms)
  case (Cons M Ms)
  show ?case
  proof (cases "Ms = []")
    case False
    have "sum_list Ms \<noteq> {#}"
      using Cons.prems(2) False by (cases Ms) auto
    then have "rep (sum_list (M # Ms)) \<approx>\<^sub>A\<^sub>C\<^sub>h rep M \<oplus> rep (sum_list Ms)"
      using Cons.prems(2) by (simp add: rep_union)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h rep M \<oplus> sum_terms (map rep Ms)"
      using Cons.IH Cons.prems(2) False by (intro eq_theory_cong2) auto
    finally show ?thesis
      using False by (simp add: sum_terms_Cons)
  qed simp
qed simp

section \<open>Consequences used in the completeness proof\<close>

subsection \<open>Injectivity of \<open>h\<close>\<close>

lemma image_mset_hinc_inj: "image_mset hinc M = image_mset hinc N \<Longrightarrow> M = N"
  by (metis (no_types) hdec_hinc multiset.map_comp multiset.map_ident_strong comp_apply)

lemma eq_ACh_H_inj: "H s \<approx>\<^sub>A\<^sub>C\<^sub>h H t \<Longrightarrow> s \<approx>\<^sub>A\<^sub>C\<^sub>h t"
  by (simp add: eq_ACh_iff_nf image_mset_hinc_inj)

subsection \<open>Decomposition and clash\<close>

text \<open>Completeness of (Dec): equal applications of a symbol other than \<open>+\<close> have equal arguments.\<close>

lemma eq_ACh_decompose:
  assumes "Fun f ss \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts" and "f \<noteq> plus" and "length ss = length ts"
    and "i < length ss"
  shows "ss ! i \<approx>\<^sub>A\<^sub>C\<^sub>h ts ! i"
proof (cases "f = hom \<and> length ss = 1")
  case True
  then obtain s t where "ss = [s]" "ts = [t]"
    using assms(3) by (metis One_nat_def length_0_conv length_Suc_conv)
  with assms(1,4) True show ?thesis
    by (auto intro: eq_ACh_H_inj)
next
  case False
  then have "free_app f (length ss)" "free_app f (length ts)"
    using assms(2,3) by (auto simp: free_app_def)
  then have "map nf ss = map nf ts"
    using assms(1) by (simp add: eq_ACh_iff_nf)
  then show ?thesis
    using assms(3,4) by (metis eq_ACh_iff_nf nth_map)
qed

lemma level_nf_H: "a \<in># nf (H t) \<Longrightarrow> level a > 0"
  by auto

lemma size_nf_pos: "size (nf t) > 0"
  using nf_nonempty[of t] by (metis neq0_conv size_eq_0_iff_empty)

lemma size_nf_Plus: "size (nf (s \<oplus> t)) \<ge> 2"
  using size_nf_pos[of s] size_nf_pos[of t] by simp

text \<open>Completeness of (Clash): applications of different symbols, one of them free, differ.\<close>

lemma eq_ACh_clash:
  assumes "f \<noteq> g" and "f \<notin> {plus, hom}"
  shows "\<not> Fun f ss \<approx>\<^sub>A\<^sub>C\<^sub>h Fun g ts"
proof
  assume eq: "Fun f ss \<approx>\<^sub>A\<^sub>C\<^sub>h Fun g ts"
  have nf_f: "nf (Fun f ss) = {#AFun 0 f (map nf ss)#}"
    using assms(2) by (simp add: free_app_def)
  consider (plus) a b where "g = plus" "ts = [a, b]"
    | (hom) a where "g = hom" "ts = [a]"
    | (free) "free_app g (length ts)"
    by (cases ts rule: remdups_adj.cases) (auto simp: free_app_def)
  then show False
  proof cases
    case plus
    then have "size (nf (Fun f ss)) = size (nf (a \<oplus> b))"
      using eq by (simp add: eq_ACh_iff_nf)
    then show False
      using size_nf_Plus[of a b] nf_f by simp
  next
    case hom
    then have "nf (H a) = {#AFun 0 f (map nf ss)#}"
      using eq nf_f by (metis eq_ACh_iff_nf)
    then have "AFun 0 f (map nf ss) \<in># nf (H a)"
      by simp
    then show False
      using level_nf_H by fastforce
  next
    case free
    then show False
      using eq nf_f assms(1) by (simp add: eq_ACh_iff_nf)
  qed
qed

subsection \<open>Splitting\<close>

lemma image_mset_sum_list:
  "image_mset f (sum_list Ms) = sum_list (map (image_mset f) Ms)"
  by (induction Ms) auto

text \<open>
  Equation (3.1) of the dissertation, in the generality needed for (Split):
  if \<open>h(s) =\<^sub>A\<^sub>C\<^sub>h u\<^sub>1 + \<dots> + u\<^sub>n\<close>, then every \<open>u\<^sub>i\<close> is ACh-equal to some \<open>h(v\<^sub>i)\<close>, and
  \<open>s =\<^sub>A\<^sub>C\<^sub>h v\<^sub>1 + \<dots> + v\<^sub>n\<close>.
\<close>

lemma eq_ACh_H_sum:
  assumes eq: "H s \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms us" and "us \<noteq> []"
  obtains vs where "length vs = length us"
    and "\<And>i. i < length us \<Longrightarrow> us ! i \<approx>\<^sub>A\<^sub>C\<^sub>h H (vs ! i)"
    and "s \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms vs"
proof -
  let ?N = "\<lambda>u. image_mset hdec (nf u)"
  let ?vs = "map (\<lambda>u. rep (?N u)) us"
  have nf_eq: "image_mset hinc (nf s) = sum_list (map nf us)"
    using eq \<open>us \<noteq> []\<close> by (simp add: eq_ACh_iff_nf nf_sum_terms)
  have hinc_N: "image_mset hinc (?N u) = nf u" if "u \<in> set us" for u
  proof -
    have "nf u \<subseteq># image_mset hinc (nf s)"
      using that unfolding nf_eq by (induction us) (auto simp: subset_mset.add_increasing2 subset_mset.add_increasing)
    then have "\<forall>a \<in># nf u. level a > 0"
      by (auto dest!: mset_subset_eqD)
    then show ?thesis
      by (simp add: multiset.map_comp comp_def hinc_hdec cong: image_mset_cong)
  qed
  have "us ! i \<approx>\<^sub>A\<^sub>C\<^sub>h H (?vs ! i)" if "i < length us" for i
  proof -
    let ?u = "us ! i"
    have "?u \<in> set us"
      using that by simp
    have "?u \<approx>\<^sub>A\<^sub>C\<^sub>h rep (nf ?u)"
      by (rule eq_ACh_rep_nf)
    also have "\<dots> = rep (image_mset hinc (?N ?u))"
      using hinc_N[OF \<open>?u \<in> set us\<close>] by simp
    also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h H (rep (?N ?u))"
      by (rule rep_image_hinc) simp
    finally show ?thesis
      using that by simp
  qed
  moreover have "s \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms ?vs"
  proof -
    have "nf s = image_mset hdec (image_mset hinc (nf s))"
      by (simp add: multiset.map_comp comp_def)
    also have "\<dots> = sum_list (map ?N us)"
      unfolding nf_eq by (simp add: image_mset_sum_list comp_def)
    finally have nf_s: "nf s = sum_list (map ?N us)" .
    have "s \<approx>\<^sub>A\<^sub>C\<^sub>h rep (nf s)"
      by (rule eq_ACh_rep_nf)
    also have "\<dots> \<approx>\<^sub>A\<^sub>C\<^sub>h sum_terms (map rep (map ?N us))"
      unfolding nf_s using \<open>us \<noteq> []\<close> by (intro rep_sum_list) auto
    finally show ?thesis
      by (simp add: comp_def)
  qed
  ultimately show ?thesis
    by (intro that[of ?vs]) auto
qed

subsection \<open>Occurs check\<close>

text \<open>
  A weight on normal forms: every atom weighs at least 1, every \<open>h\<close> and every free symbol adds 1.
  A term weighs strictly more than each of its arguments, so \<open>X =\<^sub>A\<^sub>C\<^sub>h t\<close> has no solution when
  \<open>X\<close> occurs properly in \<open>t\<close>.
\<close>

primrec aw :: "('f, 'v) atom \<Rightarrow> nat" where
  "aw (AVar n x) = Suc n"
| "aw (AFun n f Ms) = Suc n + sum_list (map sum_mset (map (image_mset aw) Ms))"

definition weight :: "('f, 'v) atom multiset \<Rightarrow> nat" where
  "weight M = sum_mset (image_mset aw M)"

lemma aw_hinc [simp]: "aw (hinc a) = Suc (aw a)"
  by (cases a) auto

lemma weight_union [simp]: "weight (M + N) = weight M + weight N"
  by (simp add: weight_def)

lemma weight_image_hinc: "weight (image_mset hinc M) = weight M + size M"
  by (induction M) (auto simp: weight_def)

lemma weight_nf_pos: "weight (nf t) > 0"
proof -
  obtain a N where "nf t = add_mset a N"
    using nf_nonempty by (metis multiset_cases)
  moreover have "aw a > 0"
    by (cases a) auto
  ultimately show ?thesis
    by (simp add: weight_def)
qed

lemma weight_nf_arg:
  assumes "u \<in> set us"
  shows "weight (nf u) < weight (nf (Fun f us))"
proof -
  consider (plus) a b where "f = plus" "us = [a, b]"
    | (hom) a where "f = hom" "us = [a]"
    | (free) "free_app f (length us)"
    by (cases us rule: remdups_adj.cases) (auto simp: free_app_def)
  then show ?thesis
  proof cases
    case plus
    then show ?thesis
      using assms weight_nf_pos[of a] weight_nf_pos[of b] by auto
  next
    case hom
    then show ?thesis
      using assms size_nf_pos[of a] by (auto simp: weight_image_hinc)
  next
    case free
    have "weight (nf u) \<le> sum_list (map (weight \<circ> nf) us)"
      using assms by (simp add: member_le_sum_list)
    then show ?thesis
      using free by (simp add: weight_def comp_def)
  qed
qed

lemma weight_nf_subst_less:
  assumes "x \<in> vars_term (Fun f ts)"
    and IH: "\<And>u. u \<in> set ts \<Longrightarrow> x \<in> vars_term u \<Longrightarrow> weight (nf (\<theta> x)) \<le> weight (nf (u \<cdot> \<theta>))"
  shows "weight (nf (\<theta> x)) < weight (nf (Fun f ts \<cdot> \<theta>))"
proof -
  obtain u where u: "u \<in> set ts" "x \<in> vars_term u"
    using assms(1) by auto
  then have "weight (nf (\<theta> x)) \<le> weight (nf (u \<cdot> \<theta>))"
    by (rule IH)
  also have "\<dots> < weight (nf (Fun f ts \<cdot> \<theta>))"
    using u(1) by (simp add: weight_nf_arg)
  finally show ?thesis .
qed

lemma weight_nf_subst_le:
  "x \<in> vars_term t \<Longrightarrow> weight (nf (\<theta> x)) \<le> weight (nf (t \<cdot> \<theta>))"
proof (induction t)
  case (Fun f ts)
  then show ?case
    using weight_nf_subst_less[of x f ts \<theta>] by fastforce
qed simp

text \<open>Completeness of (OC).\<close>

lemma eq_ACh_occurs:
  assumes "x \<in> vars_term (Fun f ts)"
  shows "\<not> \<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
proof
  assume "\<theta> x \<approx>\<^sub>A\<^sub>C\<^sub>h Fun f ts \<cdot> \<theta>"
  then have "nf (\<theta> x) = nf (Fun f ts \<cdot> \<theta>)"
    by (simp only: eq_ACh_iff_nf)
  moreover have "weight (nf (\<theta> x)) < weight (nf (Fun f ts \<cdot> \<theta>))"
    using assms weight_nf_subst_le by (rule weight_nf_subst_less)
  ultimately show False
    by simp
qed

end

section \<open>The h-height of a term\<close>

text \<open>
  Definition 1.21 of the dissertation. We compute the h-height on normal forms, which makes it
  invariant under ACh by construction (\<open>hh_eq_ACh\<close>). The lemmas \<open>hh_Var\<close>, \<open>hh_H\<close>, \<open>hh_Plus\<close> and
  \<open>hh_free\<close> show that it satisfies the defining equations of Definition 1.21.
\<close>

definition mmax :: "nat multiset \<Rightarrow> nat" where
  "mmax B = Max (insert 0 (set_mset B))"

primrec ah :: "('f, 'v) atom \<Rightarrow> nat" where
  "ah (AVar n x) = n"
| "ah (AFun n f Ms) = n + Max (insert 0 (set (map mmax (map (image_mset ah) Ms))))"

lemma ah_hinc [simp]: "ah (hinc a) = Suc (ah a)"
  by (cases a) auto

lemma mmax_union [simp]: "mmax (A + B) = max (mmax A) (mmax B)"
proof -
  have "insert 0 (set_mset (A + B)) = insert 0 (set_mset A) \<union> insert 0 (set_mset B)"
    by auto
  then show ?thesis
    unfolding mmax_def by (simp only:) (rule Max_Un; simp)
qed

lemma mmax_single [simp]: "mmax {#a#} = a"
  by (simp add: mmax_def)

lemma mmax_image_Suc:
  assumes "B \<noteq> {#}"
  shows "mmax (image_mset Suc B) = Suc (mmax B)"
proof -
  have "set_mset B \<noteq> {}"
    using assms by simp
  then have "Max (Suc ` set_mset B) = Suc (Max (set_mset B))"
    by (simp add: mono_Max_commute[symmetric] mono_Suc)
  moreover have "Max (insert 0 (Suc ` set_mset B)) = Max (Suc ` set_mset B)"
    using \<open>set_mset B \<noteq> {}\<close> by simp
  moreover have "Max (insert 0 (set_mset B)) = Max (set_mset B)"
    using \<open>set_mset B \<noteq> {}\<close> by simp
  ultimately show ?thesis
    by (simp add: mmax_def)
qed

lemma mmax_ge: "a \<in># B \<Longrightarrow> a \<le> mmax B"
  by (simp add: mmax_def)

context ach_signature
begin

definition hh :: "('f, 'v) term \<Rightarrow> nat" where
  "hh t = mmax (image_mset ah (nf t))"

lemma hh_eq_ACh: "s \<approx>\<^sub>A\<^sub>C\<^sub>h t \<Longrightarrow> hh s = hh t"
  by (simp add: hh_def eq_ACh_iff_nf)

lemma hh_Var [simp]: "hh (Var x) = 0"
  by (simp add: hh_def)

lemma hh_Plus [simp]: "hh (s \<oplus> t) = max (hh s) (hh t)"
  by (simp add: hh_def)

lemma hh_H [simp]: "hh (H t) = Suc (hh t)"
  using mmax_image_Suc[of "image_mset ah (nf t)"]
  by (simp add: hh_def multiset.map_comp comp_def)

lemma hh_free:
  assumes "free_app f (length ts)"
  shows "hh (Fun f ts) = Max (insert 0 (hh ` set ts))"
  using assms by (simp add: hh_def image_image comp_def)

lemma hh_arg_le:
  assumes "u \<in> set us"
  shows "hh u \<le> hh (Fun f us)"
proof -
  consider (plus) a b where "f = plus" "us = [a, b]"
    | (hom) a where "f = hom" "us = [a]"
    | (free) "free_app f (length us)"
    by (cases us rule: remdups_adj.cases) (auto simp: free_app_def)
  then show ?thesis
  proof cases
    case free
    then show ?thesis
      using assms by (simp add: hh_free)
  qed (use assms in auto)
qed

lemma hh_subst_le: "x \<in> vars_term t \<Longrightarrow> hh (\<theta> x) \<le> hh (t \<cdot> \<theta>)"
proof (induction t)
  case (Fun f ts)
  then obtain u where "u \<in> set ts" "x \<in> vars_term u"
    by auto
  with Fun.IH have "hh (\<theta> x) \<le> hh (u \<cdot> \<theta>)"
    by blast
  also have "\<dots> \<le> hh (Fun f ts \<cdot> \<theta>)"
    using \<open>u \<in> set ts\<close> by (simp add: hh_arg_le)
  finally show ?case .
qed simp

lemma hh_sum_terms_le: "u \<in> set us \<Longrightarrow> hh u \<le> hh (sum_terms us)"
  by (induction us rule: sum_terms.induct) auto

end

end
