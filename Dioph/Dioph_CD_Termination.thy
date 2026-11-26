section \<open>Termination of the Contejean--Devie algorithm\<close>

theory Dioph_CD_Termination
  imports Dioph_CD Farkas.Farkas
begin

text \<open>
  Proposition 3 of Boudet, Contejean and Devie (LICS 1990): the search of
  \<^file>\<open>Dioph_CD.thy\<close> reaches an empty frontier. The paper argues by compactness
  of \<open>[0,1]\<^sup>q\<close> and rational approximation. We use instead:
  \<^item> König's lemma: a non-terminating search has an infinite branch \<open>b\<^sub>0, b\<^sub>1, \<dots>\<close>;
  \<^item> condition \<open>(C\<^sub>p)\<close> gives \<open>\<parallel>A b\<^sub>n\<parallel>\<^sup>2 \<le> (n + 1) C\<close>;
  \<^item> Gordan's alternative (from Farkas' lemma, AFP entry \<^emph>\<open>Farkas\<close>) on the unbounded
    coordinates \<open>J\<close> of the branch: either some nonzero solution is supported on \<open>J\<close>, and
    the branch eventually lies above it, so it is cut; or some \<open>z\<close> has \<open>z \<cdot> A e\<^sub>j \<ge> 1\<close>
    for \<open>j \<in> J\<close>, so \<open>z \<cdot> A b\<^sub>n\<close> grows linearly, contradicting the bound.
  Hence the solver \<open>cd_solve_total\<close> returns exactly the minimal solutions.
\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma sum_Leqc:
  "finite I \<Longrightarrow> (\<Sum>i\<in>I. Leqc (p i) (c i)) = Leqc (\<Sum>i\<in>I. p i) (\<Sum>i\<in>I. c i :: rat)"
  by (induction I rule: finite_induct) (simp_all add: zero_le_constraint_def)

text \<open>A common denominator.\<close>

lemma common_denom:
  fixes C :: "'a \<Rightarrow> rat"
  shows "finite J \<Longrightarrow> \<exists>D::nat. 0 < D \<and> (\<forall>j\<in>J. C j * of_nat D \<in> \<int>)"
proof (induction J rule: finite_induct)
  case empty
  then show ?case by (intro exI[of _ 1]) simp
next
  case (insert x J)
  then obtain D where D: "0 < D" "\<forall>j\<in>J. C j * of_nat D \<in> \<int>" by blast
  obtain p d where pd: "quotient_of (C x) = (p, d)" by (cases "quotient_of (C x)")
  have d: "0 < d" "C x = of_int p / of_int d"
    using quotient_of_denom_pos[OF pd] quotient_of_div[OF pd] by simp_all
  have nd: "of_nat (nat d) = (of_int d :: rat)" using d(1) by simp
  show ?case
  proof (intro exI conjI ballI)
    show "0 < D * nat d" using D d by simp
  next
    fix j assume "j \<in> insert x J"
    then show "C j * of_nat (D * nat d) \<in> \<int>"
    proof
      assume j: "j = x"
      have cx: "C x * of_int d = of_int p" using d by simp
      have "C j * of_nat (D * nat d) = (C x * of_int d) * of_nat D"
        by (simp only: j of_nat_mult nd ac_simps)
      also have "\<dots> = of_int (p * int D)" using cx by simp
      finally show ?thesis by (metis Ints_of_int)
    next
      assume j: "j \<in> J"
      have "C j * of_nat (D * nat d) = (C j * of_nat D) * of_int d"
        by (simp only: of_nat_mult nd mult.assoc)
      then show ?thesis using D(2) j by (metis Ints_mult Ints_of_int)
    qed
  qed
qed

text \<open>A sequence in a finite set with a property that is antimonotone in \<open>k\<close>.\<close>

lemma finite_alive:
  fixes Q :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes "finite S" "\<And>k. \<exists>x\<in>S. Q x k" "\<And>x k k'. k \<le> k' \<Longrightarrow> Q x k' \<Longrightarrow> Q x k"
  shows "\<exists>x\<in>S. \<forall>k. Q x k"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>x\<in>S. \<exists>k. \<not> Q x k" by blast
  then obtain K where K: "\<And>x. x \<in> S \<Longrightarrow> \<not> Q x (K x)" by metis
  obtain x where x: "x \<in> S" "Q x (\<Sum>y\<in>S. K y)" using assms(2) by blast
  have "K x \<le> (\<Sum>y\<in>S. K y)" using assms(1) x(1) by (intro member_le_sum) simp_all
  then show False using assms(3) x K by blast
qed

lemma dot_bump:
  assumes "length v = q" "j < q"
  shows "dot r (bump v j) = dot r v + dot r (unitv q j)"
proof -
  have lb: "length (bump v j) = q" using assms(1) by simp
  have "dot r (bump v j) = (\<Sum>i<q. int (bump v j ! i) * dot r (unitv q i))"
    by (rule dot_units[OF lb])
  also have "\<dots> =
      (\<Sum>i<q. int (v ! i) * dot r (unitv q i) + (if i = j then dot r (unitv q i) else 0))"
    by (intro sum.cong refl) (auto simp: bump_def nth_list_update assms algebra_simps)
  also have "\<dots> = dot r v + dot r (unitv q j)"
    using assms by (simp add: sum.distrib dot_units[OF assms(1)])
  finally show ?thesis .
qed

lemma sum_list_sq_add:
  fixes f g :: "'a \<Rightarrow> int"
  shows "sum_list (map (\<lambda>r. (f r + g r) * (f r + g r)) xs) = sum_list (map (\<lambda>r. f r * f r) xs)
    + 2 * sum_list (map (\<lambda>r. f r * g r) xs) + sum_list (map (\<lambda>r. g r * g r) xs)"
  by (induction xs) (simp_all add: algebra_simps)

lemma bump_nth: "length v = q \<Longrightarrow> j < q \<Longrightarrow> i < q \<Longrightarrow> v ! i \<le> bump v j ! i"
  by (simp add: bump_def nth_list_update)

subsection \<open>Levels and branches\<close>

context hlds
begin

text \<open>The state after \<open>n\<close> levels.\<close>

primrec lvl :: "nat \<Rightarrow> nat list list \<times> nat list list" where
  "lvl 0 = ([], map (unitv q) [0..<q])"
| "lvl (Suc n) = cd_step q A (fst (lvl n)) (snd (lvl n))"

lemma lvl_inv: "cd_inv (Suc n) (fst (lvl n)) (snd (lvl n))"
proof (induction n)
  case 0
  then show ?case using cd_inv_init by simp
next
  case (Suc n)
  then show ?case
    using cd_step_inv[OF Suc.IH, of "fst (lvl (Suc n))" "snd (lvl (Suc n))"] by simp
qed

lemma lvl_loop: "snd (lvl (i + k)) = [] \<Longrightarrow> cd_loop q A k (fst (lvl i)) (snd (lvl i)) \<noteq> None"
proof (induction k arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "snd (lvl i)")
    case Nil
    then show ?thesis by simp
  next
    case (Cons v P)
    have "cd_loop q A k (fst (lvl (Suc i))) (snd (lvl (Suc i))) \<noteq> None"
      using Suc.IH[of "Suc i"] Suc.prems by simp
    then show ?thesis using Cons by (simp add: case_prod_beta)
  qed
qed

text \<open>\<open>w\<close> is a child of the node \<open>v\<close> of level \<open>n\<close>.\<close>

definition ch :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "ch n v w \<longleftrightarrow> v \<in> set (snd (lvl n)) \<and> \<not> dominated (fst (lvl n)) v \<and> \<not> is_sol q A v
    \<and> (\<exists>j<q. ip (img A v) (img A (unitv q j)) < 0 \<and> w = bump v j)"

lemma ch_parent: "w \<in> set (snd (lvl (Suc n))) \<Longrightarrow> \<exists>v. ch n v w"
  by (auto simp: ch_def cd_step_def Let_def succs_def)

lemma ch_mem: "ch n v w \<Longrightarrow> w \<in> set (snd (lvl (Suc n)))"
  by (auto simp: ch_def cd_step_def Let_def succs_def)

text \<open>Descendants at depth \<open>k\<close>.\<close>

fun dsc :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list set" where
  "dsc n v 0 = {v}"
| "dsc n v (Suc k) = {w. \<exists>u \<in> dsc n v k. ch (n + k) u w}"

lemma dsc_shift: "dsc n v (Suc k) = {x. \<exists>w. ch n v w \<and> x \<in> dsc (Suc n) w k}"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  have "dsc n v (Suc (Suc k)) = {x. \<exists>u \<in> dsc n v (Suc k). ch (n + Suc k) u x}"
    by (rule dsc.simps(2))
  also have "\<dots> = {x. \<exists>w. ch n v w \<and> (\<exists>u \<in> dsc (Suc n) w k. ch (Suc n + k) u x)}"
    unfolding Suc.IH by auto
  also have "\<dots> = {x. \<exists>w. ch n v w \<and> x \<in> dsc (Suc n) w (Suc k)}"
    by (simp only: dsc.simps(2) mem_Collect_eq)
  finally show ?case .
qed

lemma dsc_anc: "w \<in> set (snd (lvl (n + k))) \<Longrightarrow> \<exists>v \<in> set (snd (lvl n)). w \<in> dsc n v k"
proof (induction k arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then obtain u where u: "ch (n + k) u w" using ch_parent by (metis add_Suc_right)
  then have "u \<in> set (snd (lvl (n + k)))" by (simp add: ch_def)
  then obtain v where "v \<in> set (snd (lvl n))" "u \<in> dsc n v k" using Suc.IH by blast
  then show ?case using u by auto
qed

lemma dsc_antimono: "k \<le> k' \<Longrightarrow> dsc n v k' \<noteq> {} \<Longrightarrow> dsc n v k \<noteq> {}"
proof (induction k')
  case 0
  then show ?case by simp
next
  case (Suc k')
  show ?case
  proof (cases "k = Suc k'")
    case True
    then show ?thesis using Suc.prems by simp
  next
    case False
    then have "k \<le> k'" using Suc.prems by simp
    moreover have "dsc n v k' \<noteq> {}" using Suc.prems(2) by auto
    ultimately show ?thesis using Suc.IH by blast
  qed
qed

text \<open>König's lemma: a search that never stops has an infinite branch.\<close>

lemma inf_branch:
  assumes nt: "\<And>k. snd (lvl k) \<noteq> []"
  obtains b where "\<And>n. ch n (b n) (b (Suc n))"
proof -
  define P where "P n v \<longleftrightarrow> v \<in> set (snd (lvl n)) \<and> (\<forall>k. dsc n v k \<noteq> {})" for n v
  have root: "\<exists>v. P 0 v"
  proof -
    have "\<exists>v \<in> set (snd (lvl 0)). \<forall>k. dsc 0 v k \<noteq> {}"
    proof (rule finite_alive)
      fix k
      have w: "hd (snd (lvl (0 + k))) \<in> set (snd (lvl (0 + k)))"
        using nt[of "0 + k"] by (rule hd_in_set)
      show "\<exists>v \<in> set (snd (lvl 0)). dsc 0 v k \<noteq> {}"
        using dsc_anc[OF w] by (elim bexE) (intro bexI, auto)
    next
      show "finite (set (snd (lvl 0)))" by (rule finite_set)
    next
      fix v :: "nat list" and k k' :: nat assume "k \<le> k'" "dsc 0 v k' \<noteq> {}"
      then show "dsc 0 v k \<noteq> {}" by (rule dsc_antimono)
    qed
    then show ?thesis unfolding P_def by (elim bexE) (intro exI conjI)
  qed
  have step: "\<exists>w. P (Suc n) w \<and> ch n v w" if Pv: "P n v" for n v
  proof -
    have "\<exists>w \<in> {w. ch n v w}. \<forall>k. dsc (Suc n) w k \<noteq> {}"
    proof (rule finite_alive)
      have "{w. ch n v w} \<subseteq> set (snd (lvl (Suc n)))" using ch_mem by blast
      then show "finite {w. ch n v w}" by (rule finite_subset) (rule finite_set)
    next
      fix k
      have "dsc n v (Suc k) \<noteq> {}" using Pv unfolding P_def by blast
      then show "\<exists>w \<in> {w. ch n v w}. dsc (Suc n) w k \<noteq> {}" unfolding dsc_shift by blast
    next
      fix w :: "nat list" and k k' :: nat assume "k \<le> k'" "dsc (Suc n) w k' \<noteq> {}"
      then show "dsc (Suc n) w k \<noteq> {}" by (rule dsc_antimono)
    qed
    then obtain w where w: "ch n v w" "\<forall>k. dsc (Suc n) w k \<noteq> {}" by blast
    have "P (Suc n) w" unfolding P_def using ch_mem[OF w(1)] w(2) by (intro conjI)
    then show ?thesis using w(1) by (intro exI conjI)
  qed
  have "\<exists>f. \<forall>n. P n (f n) \<and> ch n (f n) (f (Suc n))"
    by (rule dependent_nat_choice[of P "\<lambda>n v w. ch n v w", OF root step])
  then obtain b where b: "\<And>n. P n (b n) \<and> ch n (b n) (b (Suc n))" by blast
  show thesis by (rule that) (rule conjunct2[OF b])
qed

subsection \<open>Gordan's alternative\<close>

lemma gordan:
  assumes J: "J \<subseteq> {..<q}"
  shows "(\<exists>y. is_sol q A y \<and> nonzero y \<and> (\<forall>i<q. i \<notin> J \<longrightarrow> y ! i = 0))
    \<or> (\<exists>z :: nat \<Rightarrow> rat. \<forall>j\<in>J. 1 \<le> (\<Sum>k<length A. z k * of_int (dot (A ! k) (unitv q j))))"
proof -
  define a where "a k j = (of_int (dot (A ! k) (unitv q j)) :: rat)" for k j
  define c where "c j = Leqc (\<Sum>k<length A. lp_monom (- a k j) k) (-1 :: rat)" for j
  have fin: "finite J" using J finite_subset by blast
  show ?thesis
  proof (cases "\<exists>v. \<forall>j\<in>J. v \<Turnstile>\<^sub>l\<^sub>e c j")
    case True
    then obtain v where v: "\<forall>j\<in>J. v \<Turnstile>\<^sub>l\<^sub>e c j" by blast
    have "1 \<le> (\<Sum>k<length A. v k * a k j)" if "j \<in> J" for j
    proof -
      have "(\<Sum>k<length A. - a k j * v k) \<le> -1"
        using v that by (simp add: c_def valuate_sum valuate_lp_monom)
      then show ?thesis by (simp add: sum_negf mult.commute)
    qed
    then show ?thesis unfolding a_def by blast
  next
    case False
    have rel: "lec_rel ` c ` J \<subseteq> {Leq_Rel}" by (auto simp: c_def)
    from False Farkas'_Lemma_indexed[OF rel fin] obtain C const where
      C: "\<forall>j\<in>J. 0 \<le> C j" and
      eq: "(\<Sum>j\<in>J. Leqc (C j *R lec_poly (c j)) (C j *R lec_const (c j))) = Leqc 0 const" and
      neg: "const < 0" by blast
    from eq have ep: "(\<Sum>j\<in>J. C j *R lec_poly (c j)) = 0"
      and ec: "(\<Sum>j\<in>J. C j *R lec_const (c j)) = const"
      by (simp_all add: sum_Leqc[OF fin])
    have ker: "(\<Sum>j\<in>J. C j * a k j) = 0" if k: "k < length A" for k
    proof -
      have "coeff (\<Sum>j\<in>J. C j *R lec_poly (c j)) k = 0" using ep by simp
      then have "(\<Sum>j\<in>J. C j * - a k j) = 0"
        using k by (simp add: coeff_sum c_def if_distrib cong: if_cong)
      then show ?thesis by (simp add: sum_negf)
    qed
    have "(\<Sum>j\<in>J. - C j) < 0" using ec neg by (simp add: c_def)
    then have "0 < (\<Sum>j\<in>J. C j)" by (simp add: sum_negf)
    have "\<exists>j\<in>J. 0 < C j"
    proof (rule ccontr)
      assume "\<not> (\<exists>j\<in>J. 0 < C j)"
      then have "(\<Sum>j\<in>J. C j) \<le> 0" by (intro sum_nonpos) (simp add: not_less)
      then show False using \<open>0 < (\<Sum>j\<in>J. C j)\<close> by simp
    qed
    then obtain j0 where j0: "j0 \<in> J" "0 < C j0" by blast
    obtain D where D: "0 < D" "\<forall>j\<in>J. C j * of_nat D \<in> \<int>"
      using common_denom[OF fin] by blast
    define y where "y = map (\<lambda>i. if i \<in> J then nat \<lfloor>C i * of_nat D\<rfloor> else 0) [0..<q]"
    have ly: "length y = q" by (simp add: y_def)
    have yJ: "of_nat (y ! i) = C i * of_nat D" if i: "i \<in> J" for i
    proof -
      obtain t where t: "C i * of_nat D = of_int t" using D(2) i Ints_cases by metis
      have "0 \<le> C i * of_nat D" using C i by simp
      then have "0 \<le> t" using t by simp
      moreover have "i < q" using i J by auto
      ultimately show ?thesis using i t by (simp add: y_def)
    qed
    have y0: "y ! i = 0" if "i < q" "i \<notin> J" for i
      using that by (simp add: y_def)
    have sol: "dot r y = 0" if r: "r \<in> set A" for r
    proof -
      obtain k where k: "k < length A" "r = A ! k" using r by (metis in_set_conv_nth)
      have "(of_int (dot r y) :: rat) = (\<Sum>i<q. of_nat (y ! i) * a k i)"
        unfolding dot_units[OF ly] using k by (simp add: a_def)
      also have "\<dots> = (\<Sum>i\<in>J. of_nat (y ! i) * a k i)"
        using J y0 by (intro sum.mono_neutral_right) auto
      also have "\<dots> = of_nat D * (\<Sum>i\<in>J. C i * a k i)"
        by (simp add: yJ sum_distrib_left ac_simps)
      also have "\<dots> = 0" using ker[OF k(1)] by simp
      finally show ?thesis by simp
    qed
    have "(0 :: rat) < of_nat (y ! j0)" unfolding yJ[OF j0(1)] using j0(2) D(1) by simp
    then have "y ! j0 \<noteq> 0" by (metis of_nat_0 less_irrefl)
    moreover have "j0 < length y" using j0(1) J ly by auto
    ultimately have "nonzero y" by (auto simp: nonzero_iff)
    then show ?thesis using ly sol y0 by (auto simp: is_sol_def)
  qed
qed

subsection \<open>No infinite branch\<close>

definition nrm :: "nat list \<Rightarrow> int" where
  "nrm v = sum_list (map (\<lambda>r. dot r v * dot r v) A)"

lemma nrm_nonneg: "0 \<le> nrm v"
  unfolding nrm_def by (induction A) simp_all

lemma nrm_bump:
  assumes "length v = q" "j < q"
  shows "nrm (bump v j) = nrm v + 2 * ip (img A v) (img A (unitv q j)) + nrm (unitv q j)"
  unfolding nrm_def ip_img dot_bump[OF assms] by (rule sum_list_sq_add)

lemma no_branch:
  assumes br: "\<And>n. ch n (b n) (b (Suc n))"
  shows False
proof -
  have bm: "b n \<in> set (snd (lvl n))" for n using br[of n] by (simp add: ch_def)
  have lb: "length (b n) = q" and sb: "sum_list (b n) = Suc n" for n
    using lvl_inv[of n] bm[of n] by (auto simp: cd_inv_def)
  have nd: "\<not> dominated (fst (lvl n)) (b n)" for n using br[of n] by (simp add: ch_def)
  have stp: "\<exists>j<q. ip (img A (b n)) (img A (unitv q j)) < 0 \<and> b (Suc n) = bump (b n) j" for n
    using br[of n] by (simp add: ch_def)
  have mono: "b n ! i \<le> b n' ! i" if "n \<le> n'" "i < q" for n n' i
  proof -
    have st: "b m ! i \<le> b (Suc m) ! i" for m
    proof -
      obtain j where j: "j < q" "b (Suc m) = bump (b m) j" using stp[of m] by blast
      show ?thesis unfolding j(2) by (rule bump_nth[OF lb[of m] j(1) that(2)])
    qed
    show ?thesis by (rule lift_Suc_mono_le[of "\<lambda>m. b m ! i", OF st that(1)])
  qed
  text \<open>The bound \<open>\<parallel>A b\<^sub>n\<parallel>\<^sup>2 \<le> (n + 1) C\<close>.\<close>
  define C where "C = (\<Sum>j<q. nrm (unitv q j))"
  have Cj: "nrm (unitv q j) \<le> C" if "j < q" for j
    unfolding C_def using that nrm_nonneg by (intro member_le_sum) auto
  have C0: "0 \<le> C" unfolding C_def using nrm_nonneg by (simp add: sum_nonneg)
  have nb: "nrm (b n) \<le> int (Suc n) * C" for n
  proof (induction n)
    case 0
    obtain j where "j < q" "b 0 = unitv q j" using bm[of 0] by auto
    then show ?case using Cj by simp
  next
    case (Suc n)
    obtain j where j: "j < q" "ip (img A (b n)) (img A (unitv q j)) < 0" "b (Suc n) = bump (b n) j"
      using stp by blast
    have "nrm (b (Suc n)) \<le> nrm (b n) + C"
      using nrm_bump[OF lb j(1)] j Cj[OF j(1)] by simp
    then show ?case using Suc.IH by (simp add: algebra_simps)
  qed
  text \<open>The coordinates that grow without bound.\<close>
  define J where "J = {i. i < q \<and> (\<forall>B. \<exists>n. B < b n ! i)}"
  have JS: "J \<subseteq> {..<q}" by (auto simp: J_def)
  have "\<forall>i \<in> {..<q} - J. \<exists>B. \<forall>n. b n ! i \<le> B"
  proof
    fix i assume "i \<in> {..<q} - J"
    then obtain B where "\<not> (\<exists>n. B < b n ! i)" by (auto simp: J_def)
    then show "\<exists>B. \<forall>n. b n ! i \<le> B" by (auto simp: not_less)
  qed
  then have "\<exists>Bd. \<forall>i \<in> {..<q} - J. \<forall>n. b n ! i \<le> Bd i" by (rule bchoice)
  then obtain Bd where Bd0: "\<forall>i \<in> {..<q} - J. \<forall>n. b n ! i \<le> Bd i" by blast
  have Bd: "b n ! i \<le> Bd i" if "i \<in> {..<q} - J" for i n using Bd0 that by blast
  from gordan[OF JS] show False
  proof (elim disjE exE conjE)
    text \<open>A solution supported on \<open>J\<close> lies below the branch: the branch is cut.\<close>
    fix y assume ys: "is_sol q A y" and nz: "nonzero y" and y0: "\<forall>i<q. i \<notin> J \<longrightarrow> y ! i = 0"
    have "\<forall>i\<in>J. \<exists>n. y ! i < b n ! i" unfolding J_def by blast
    then have "\<exists>Nf. \<forall>i\<in>J. y ! i < b (Nf i) ! i" by (rule bchoice)
    then obtain Nf where Nf0: "\<forall>i\<in>J. y ! i < b (Nf i) ! i" by blast
    have Nf: "y ! i < b (Nf i) ! i" if "i \<in> J" for i using Nf0 that by blast
    define n where "n = (\<Sum>i\<in>J. Nf i) + sum_list y"
    have fJ: "finite J" using JS finite_subset by blast
    have ly: "length y = q" using ys by (simp add: is_sol_def)
    have yb: "y \<le>\<^sub>v b n"
    proof (rule less_eqI)
      show "length y = length (b n)" using ly lb by simp
      show "\<forall>i<length y. y ! i \<le> b n ! i"
      proof (intro allI impI)
        fix i assume i: "i < length y"
        show "y ! i \<le> b n ! i"
        proof (cases "i \<in> J")
          case True
          have "Nf i \<le> n" unfolding n_def using fJ True by (simp add: member_le_sum trans_le_add1)
          then show ?thesis using Nf[OF True] mono[of "Nf i" n i] i ly by simp
        next
          case False
          then show ?thesis using y0 i ly by simp
        qed
      qed
    qed
    obtain m where m: "m \<in> Minimal_Solutions" "m \<le>\<^sub>v y"
      using minimal_below[of y] ys nz by (auto simp: Solutions_def)
    have "sum_list m \<le> sum_list y" using m(2) by (rule le_sum_list_mono)
    then have "sum_list m < Suc n" unfolding n_def by simp
    then have "m \<in> set (fst (lvl n))" using lvl_inv[of n] m(1) by (simp add: cd_inv_def)
    moreover have "m \<le>\<^sub>v b n" using m(2) yb by (rule order_vec.order_trans)
    ultimately show False using nd[of n] by (auto simp: dominated_iff)
  next
    text \<open>A direction \<open>z\<close> with \<open>z \<cdot> A e\<^sub>j \<ge> 1\<close> on \<open>J\<close>: \<open>z \<cdot> A b\<^sub>n\<close> grows too fast.\<close>
    fix z :: "nat \<Rightarrow> rat"
    assume z: "\<forall>j\<in>J. 1 \<le> (\<Sum>k<length A. z k * of_int (dot (A ! k) (unitv q j)))"
    define g where "g i = (\<Sum>k<length A. z k * of_int (dot (A ! k) (unitv q i)))" for i
    define h where "h i = (if i \<in> J then 0 else of_nat (Bd i) * (\<bar>g i\<bar> + 1))" for i
    define H where "H = (\<Sum>i<q. h i)"
    define Z2 where "Z2 = (\<Sum>k<length A. z k * z k)"
    define T where "T = (of_int C + 1 :: rat)"
    define R where "R = 2 * T * H + T * T * Z2"
    have bound: "of_nat (Suc n) \<le> R" for n
    proof -
      define x where "x k = (of_int (dot (A ! k) (b n)) :: rat)" for k
      define L where "L = (\<Sum>k<length A. z k * x k)"
      have L: "L = (\<Sum>i<q. of_nat (b n ! i) * g i)"
      proof -
        have "L = (\<Sum>k<length A. \<Sum>i<q. z k * (of_nat (b n ! i) * of_int (dot (A ! k) (unitv q i))))"
          unfolding L_def x_def dot_units[OF lb[of n]] by (simp add: sum_distrib_left)
        also have "\<dots> = (\<Sum>i<q. \<Sum>k<length A. z k * (of_nat (b n ! i) * of_int (dot (A ! k) (unitv q i))))"
          by (rule sum.swap)
        also have "\<dots> = (\<Sum>i<q. of_nat (b n ! i) * g i)"
          unfolding g_def by (simp add: sum_distrib_left ac_simps)
        finally show ?thesis .
      qed
      have hi: "of_nat (b n ! i) - h i \<le> of_nat (b n ! i) * g i" if i: "i < q" for i
      proof (cases "i \<in> J")
        case True
        then have "1 \<le> g i" using z by (simp add: g_def)
        then have "of_nat (b n ! i) * 1 \<le> of_nat (b n ! i) * g i" by (intro mult_left_mono) simp_all
        then show ?thesis using True by (simp add: h_def)
      next
        case False
        let ?x = "of_nat (b n ! i) :: rat"
        have "?x \<le> of_nat (Bd i)" using Bd[of i n] i False by simp
        then have a: "?x * (\<bar>g i\<bar> + 1) \<le> of_nat (Bd i) * (\<bar>g i\<bar> + 1)"
          by (intro mult_right_mono) simp_all
        have b: "?x * (- \<bar>g i\<bar>) \<le> ?x * g i" by (intro mult_left_mono) simp_all
        have "?x * (\<bar>g i\<bar> + 1) = ?x * \<bar>g i\<bar> + ?x" by (simp add: algebra_simps)
        then show ?thesis using a b False by (simp add: h_def)
      qed
      have "of_nat (Suc n) - H = (\<Sum>i<q. of_nat (b n ! i) - h i)"
        unfolding H_def sum_subtractf
        using sb[of n] lb[of n] by (simp add: sum_list_sum_nth atLeast0LessThan flip: of_nat_sum)
      also have "\<dots> \<le> L" unfolding L by (intro sum_mono hi) simp
      finally have Lb: "of_nat (Suc n) - H \<le> L" .
      have N: "(\<Sum>k<length A. x k * x k) \<le> of_nat (Suc n) * of_int C"
      proof -
        have "(\<Sum>k<length A. x k * x k) = of_int (nrm (b n))"
          by (simp add: nrm_def x_def sum_list_sum_nth atLeast0LessThan)
        also have "\<dots> \<le> of_int (int (Suc n) * C)" using nb[of n] by (simp only: of_int_le_iff)
        finally show ?thesis by simp
      qed
      have sq: "0 \<le> (\<Sum>k<length A. (x k - T * z k) * (x k - T * z k))"
        by (intro sum_nonneg) simp
      also have "\<dots> = (\<Sum>k<length A. x k * x k) - 2 * T * L + T * T * Z2"
        unfolding L_def Z2_def
        by (simp add: sum_subtractf sum.distrib sum_distrib_left algebra_simps)
      finally have "2 * T * L \<le> of_nat (Suc n) * of_int C + T * T * Z2" using N by simp
      moreover have "2 * T * (of_nat (Suc n) - H) \<le> 2 * T * L"
        using Lb C0 by (intro mult_left_mono) (simp_all add: T_def)
      ultimately have "2 * T * of_nat (Suc n) \<le> of_nat (Suc n) * of_int C + R"
        by (simp add: R_def algebra_simps)
      moreover have "2 * T * of_nat (Suc n) = of_nat (Suc n) * of_int C + of_nat (Suc n) * (of_int C + 2)"
        by (simp add: T_def algebra_simps)
      moreover have "of_nat (Suc n) \<le> of_nat (Suc n) * (of_int C + (2 :: rat))"
        using C0 by (simp add: mult_le_cancel_left1)
      ultimately show ?thesis by linarith
    qed
    have "R \<le> of_int \<lceil>R\<rceil>" by (rule le_of_int_ceiling)
    also have "\<dots> \<le> of_nat (nat \<lceil>R\<rceil>)" by simp
    finally have r: "R \<le> of_nat (nat \<lceil>R\<rceil>)" .
    have "1 + of_nat (nat \<lceil>R\<rceil>) \<le> R" using bound[of "nat \<lceil>R\<rceil>"] by simp
    then show False using r by linarith
  qed
qed

subsection \<open>Termination and correctness of the solver\<close>

text \<open>Proposition 3: the search stops.\<close>

theorem cd_terminates: "\<exists>f. cd_solve f q A \<noteq> None"
proof -
  have "\<exists>k. snd (lvl k) = []"
  proof (rule ccontr)
    assume "\<nexists>k. snd (lvl k) = []"
    then obtain b where "\<And>n. ch n (b n) (b (Suc n))" using inf_branch by blast
    then show False by (rule no_branch)
  qed
  then obtain k where "snd (lvl (0 + k)) = []" by auto
  from lvl_loop[OF this] show ?thesis unfolding cd_solve_def by auto
qed

theorem cd_solve_total_correct: "set (cd_solve_total q A) = Minimal_Solutions"
proof -
  obtain f R where "cd_solve f q A = Some R" using cd_terminates by blast
  moreover from this have "cd_solve_total q A = R"
    unfolding cd_solve_def cd_solve_total_def by (rule cd_loop_run)
  ultimately show ?thesis using cd_solve_correct by simp
qed

end

interpretation dioph_cdt: dioph_solver "\<lambda>n A. Some (cd_solve_total n A)"
proof unfold_locales
  fix n A B b
  assume "Some (cd_solve_total n A) = Some B" "b \<in> set B"
  then show "is_sol n A b"
    using hlds.cd_solve_total_correct hlds.Minimal_SolutionsD(1) by (fastforce simp: hlds.Solutions_def)
next
  fix n A B y
  assume B: "Some (cd_solve_total n A) = Some B" and y: "is_sol n A y"
  have "hlds.Minimal_Solutions n A \<subseteq> set B"
    using B hlds.cd_solve_total_correct[of n A] by simp
  then show "\<exists>ks. length ks = length B \<and> (\<forall>j < n. y ! j = lc ks B j)"
    using y hlds.Solutions_gen_by[where q = n and A = A and y = y and S = B]
    by (simp add: hlds.Solutions_def)
qed

end
