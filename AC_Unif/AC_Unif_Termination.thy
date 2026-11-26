(*
Author: Guilherme Borges Brandão
*)

theory AC_Unif_Termination
  imports AC_Unif_Completeness
begin

section ‹Termination of the AC-unification algorithm›

text ‹
  The lexicographic measure of PVS (∗‹Certified first-order AC-unification and applications›,
  Section 5 and Appendix A), adapted from Fages:
  ‹(|V⇩N⇩A⇩C(P)|, |V⇩>⇩1(P)|, |AS(P)|, size(P))›. Subterms are taken in flattened form: the
  arguments of an AC application are its arguments below nested applications of the same AC symbol.
›

subsection ‹Flattened subterms›

context ac_sig
begin

text ‹‹t› is an AC application (of some AC symbol).›

definition is_acapp :: "('f, 'v) term ⇒ bool" where
  "is_acapp t ⟷ (∃g. is_ac_app g t)"

text ‹The arguments of a term, flattened below AC applications.›

fun targs :: "('f, 'v) term ⇒ ('f, 'v) term list" where
  "targs (Var x) = []"
| "targs (Fun g ts) = (if ac g ∧ length ts = 2 then args_ac g (Fun g ts) else ts)"

text ‹The head of a term: its symbol, and whether it is an AC application.›

fun key :: "('f, 'v) term ⇒ ('f × bool) option" where
  "key (Var x) = None"
| "key (Fun g ts) = Some (g, ac g ∧ length ts = 2)"

declare targs.simps(2) [simp del]

lemma size_targs: "u ∈ set (targs t) ⟹ size u < size t"
proof (cases t)
  case (Fun g ts)
  assume u: "u ∈ set (targs t)"
  show ?thesis
  proof (cases "ac g ∧ length ts = 2")
    case True
    then have app: "is_ac_app g t" using Fun by simp
    have "u ∈ set (args_ac g t)" using u Fun True by (simp add: targs.simps(2))
    then show ?thesis by (rule size_args_ac_less[OF app])
  next
    case False
    have "targs (Fun g ts) = ts" using False by (auto simp: targs.simps(2))
    then have "u ∈ set ts" using u Fun by simp
    then show ?thesis using Fun size_arg_less by simp
  qed
qed simp

function fsub :: "('f, 'v) term ⇒ ('f, 'v) term set" where
  "fsub (Var x) = {Var x}"
| "fsub (Fun g ts) = insert (Fun g ts) (⋃u ∈ set (targs (Fun g ts)). fsub u)"
  by pat_completeness auto
termination
  by (relation "measure size") (auto dest: size_targs)

lemma fsub_self [simp]: "t ∈ fsub t"
  by (cases t) auto

lemma fsub_Fun_iff:
  "u ∈ fsub (Fun g ts) ⟷ u = Fun g ts ∨ (∃a ∈ set (targs (Fun g ts)). u ∈ fsub a)"
  by auto

lemma finite_fsub [simp]: "finite (fsub t)"
  by (induction t rule: fsub.induct) auto

lemma fsub_FunE:
  assumes "u ∈ fsub (Fun g ts)"
  obtains "u = Fun g ts" | a where "a ∈ set (targs (Fun g ts))" "u ∈ fsub a"
  using assms by auto

lemma fsub_size: "u ∈ fsub t ⟹ size u ≤ size t"
proof (induction t rule: fsub.induct)
  case (2 g ts)
  from "2.prems" show ?case
  proof (cases rule: fsub_FunE)
    case (2 a)
    then show ?thesis using "2.IH"[OF 2] size_targs[OF 2(1)] by simp
  qed simp
qed simp

lemma fsub_size_less: "u ∈ fsub t ⟹ u ≠ t ⟹ size u < size t"
proof (cases t)
  case (Fun g ts)
  assume "u ∈ fsub t" "u ≠ t"
  then obtain a where "a ∈ set (targs t)" "u ∈ fsub a" using Fun by (auto elim: fsub_FunE)
  then show ?thesis using fsub_size[of u a] size_targs[of a t] by simp
qed simp

lemma fsub_trans: "u ∈ fsub t ⟹ w ∈ fsub u ⟹ w ∈ fsub t"
proof (induction t rule: fsub.induct)
  case (2 g ts)
  from "2.prems"(1) show ?case
  proof (cases rule: fsub_FunE)
    case 1
    then show ?thesis using "2.prems"(2) by simp
  next
    case (2 a)
    then show ?thesis using "2.IH"[OF 2 "2.prems"(2)] by auto
  qed
qed simp

lemma targs_fsub:
  assumes "a ∈ set (targs t)"
  shows "a ∈ fsub t"
proof (cases t)
  case (Fun g ts)
  have "a ∈ fsub a" by simp
  then show ?thesis using assms Fun by (simp only: fsub.simps(2)) blast
qed (use assms in simp)

lemma vars_targs: "a ∈ set (targs t) ⟹ vars_term a ⊆ vars_term t"
proof (cases t)
  case (Fun g ts)
  assume a: "a ∈ set (targs t)"
  show ?thesis
  proof (cases "ac g ∧ length ts = 2")
    case True
    then have "a ∈ set (args_ac g t)" using a Fun by (simp add: targs.simps(2))
    then show ?thesis using vars_args_ac[of t g] by auto
  next
    case False
    then have "a ∈ set ts" using a Fun by (auto simp: targs.simps(2))
    then show ?thesis using Fun by auto
  qed
qed simp

lemma vars_fsub: "u ∈ fsub t ⟹ vars_term u ⊆ vars_term t"
proof (induction t rule: fsub.induct)
  case (2 g ts)
  from "2.prems" show ?case
  proof (cases rule: fsub_FunE)
    case (2 a)
    then show ?thesis using "2.IH"[OF 2] vars_targs[OF 2(1)] by blast
  qed simp
qed simp

lemma is_acapp_Fun: "is_acapp (Fun g ts) ⟷ ac g ∧ length ts = 2"
  by (auto simp: is_acapp_def)

lemma not_acapp_Var [simp]: "¬ is_acapp (Var x)"
  by (simp add: is_acapp_def)

lemma targs_acapp: "is_ac_app g t ⟹ targs t = args_ac g t"
  by (auto simp: is_ac_app_def targs.simps(2))

lemma targs_not_acapp: "¬ is_acapp (Fun g ts) ⟹ targs (Fun g ts) = ts"
  by (auto simp: is_acapp_Fun targs.simps(2))

lemma key_subst [simp]: "is_Fun w ⟹ key (w ⋅ θ) = key w"
  by (cases w) auto

lemma is_acapp_subst [simp]: "is_Fun w ⟹ is_acapp (w ⋅ θ) = is_acapp w"
  by (cases w) (auto simp: is_acapp_Fun)

lemma key_acapp: "is_ac_app g t ⟹ key t = Some (g, True)"
  by (auto simp: is_ac_app_def)

lemma key_eq_acapp: "key t = key s ⟹ is_ac_app g t ⟹ is_ac_app g s"
  by (cases t; cases s) (auto simp: numeral_2_eq_2 length_Suc_conv)

lemma args_ac_subst:
  "args_ac g (t ⋅ θ) = concat (map (λa. args_ac g (a ⋅ θ)) (args_ac g t))"
  by (induction g t rule: args_ac.induct) auto

lemma targs_subst_not_acapp:
  "is_Fun w ⟹ ¬ is_acapp w ⟹ targs (w ⋅ θ) = map (λa. a ⋅ θ) (targs w)"
  by (cases w) (auto simp: is_acapp_Fun targs.simps(2))

lemma targs_subst_acapp:
  "is_ac_app g w ⟹ targs (w ⋅ θ) = concat (map (λa. args_ac g (a ⋅ θ)) (targs w))"
proof -
  assume g: "is_ac_app g w"
  then have g': "is_ac_app g (w ⋅ θ)" by (auto simp: is_ac_app_def)
  have "targs (w ⋅ θ) = args_ac g (w ⋅ θ)" by (rule targs_acapp[OF g'])
  also have "… = concat (map (λa. args_ac g (a ⋅ θ)) (args_ac g w))" by (rule args_ac_subst)
  also have "… = concat (map (λa. args_ac g (a ⋅ θ)) (targs w))" by (simp only: targs_acapp[OF g])
  finally show ?thesis .
qed

lemma targs_no_app: "is_ac_app g t ⟹ a ∈ set (targs t) ⟹ ¬ is_ac_app g a"
  by (simp add: targs_acapp args_ac_no_app)

lemma fsub_subst_lift:
  assumes a: "a ∈ set (targs v)" "is_Fun a"
    and P: "(∃w ∈ fsub a. is_Fun w ∧ T = w ⋅ θ) ∨
      (∃x ∈ vars_term a. T ∈ fsub (θ x) ∧
        (T = θ x ⟶ a = Var x ∨ (∃w ∈ fsub a. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))))"
  shows "(∃w ∈ fsub v. is_Fun w ∧ T = w ⋅ θ) ∨
      (∃x ∈ vars_term v. T ∈ fsub (θ x) ∧
        (T = θ x ⟶ v = Var x ∨ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))))"
proof -
  have sub: "fsub a ⊆ fsub v" using fsub_trans[OF targs_fsub[OF a(1)]] by blast
  have vs: "vars_term a ⊆ vars_term v" by (rule vars_targs[OF a(1)])
  from P show ?thesis
  proof
    assume "∃w ∈ fsub a. is_Fun w ∧ T = w ⋅ θ"
    then show ?thesis using sub by blast
  next
    assume "∃x ∈ vars_term a. T ∈ fsub (θ x) ∧
        (T = θ x ⟶ a = Var x ∨ (∃w ∈ fsub a. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x))))"
    then obtain x where x: "x ∈ vars_term a" "T ∈ fsub (θ x)"
      "T = θ x ⟶ a = Var x ∨ (∃w ∈ fsub a. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))" by blast
    have "T = θ x ⟶ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))"
      using x(3) a(2) sub by blast
    then show ?thesis using x(1,2) vs by blast
  qed
qed

text ‹Flattened subterms of an instance (PVS Lemma 19).›

lemma fsub_subst:
  assumes "T ∈ fsub (v ⋅ θ)"
  shows "(∃w ∈ fsub v. is_Fun w ∧ T = w ⋅ θ) ∨
    (∃x ∈ vars_term v. T ∈ fsub (θ x) ∧
      (T = θ x ⟶ v = Var x ∨ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
         ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))))"
  using assms
proof (induction v rule: fsub.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 g ts)
  let ?v = "Fun g ts"
  have "T = ?v ⋅ θ ∨ (∃b ∈ set (targs (?v ⋅ θ)). T ∈ fsub b)"
    using "2.prems" by (simp only: eval_term.simps fsub_Fun_iff)
  then show ?case
  proof
    assume "T = ?v ⋅ θ"
    then show ?thesis by auto
  next
    assume "∃b ∈ set (targs (?v ⋅ θ)). T ∈ fsub b"
    then obtain b where b: "b ∈ set (targs (?v ⋅ θ))" "T ∈ fsub b" by blast
    show ?thesis
    proof (cases "is_ac_app g ?v")
      case True
      then obtain a where a: "a ∈ set (targs ?v)" "b ∈ set (args_ac g (a ⋅ θ))"
        using b(1) targs_subst_acapp[OF True, of θ] by auto
      have na: "¬ is_ac_app g a" by (rule targs_no_app[OF True a(1)])
      show ?thesis
      proof (cases a)
        case (Var x)
        have x: "x ∈ vars_term ?v" using a(1) Var vars_targs[OF a(1)] by auto
        show ?thesis
        proof (cases "is_ac_app g (θ x)")
          case True': True
          have "T ∈ fsub (θ x)" "T ≠ θ x"
          proof -
            have bx: "b ∈ set (targs (θ x))" using a(2) Var True' by (simp add: targs_acapp)
            show "T ∈ fsub (θ x)" using fsub_trans[OF targs_fsub[OF bx] b(2)] .
            show "T ≠ θ x" using fsub_size[OF b(2)] size_targs[OF bx] by auto
          qed
          then show ?thesis using x by blast
        next
          case False
          then have "b = θ x" using a(2) Var by simp
          then show ?thesis using x b(2) a(1) Var True False by (intro disjI2 bexI[of _ x]) auto
        qed
      next
        case (Fun h us)
        have "¬ is_ac_app g (a ⋅ θ)" using na Fun by (auto simp: is_ac_app_def)
        then have "b = a ⋅ θ" using a(2) by simp
        then show ?thesis
          using fsub_subst_lift[OF a(1) _ "2.IH"[OF a(1)]] b(2) Fun by simp
      qed
    next
      case False
      then have nac: "¬ is_acapp ?v" by (auto simp: is_acapp_def is_acapp_Fun)
      then obtain a where a: "a ∈ set (targs ?v)" "b = a ⋅ θ"
        using b(1) targs_subst_not_acapp[OF _ nac, of θ] by auto
      show ?thesis
      proof (cases a)
        case (Var x)
        have x: "x ∈ vars_term ?v" using a(1) Var vars_targs[OF a(1)] by auto
        have "¬ (∃g'. is_ac_app g' ?v ∧ is_ac_app g' (θ x))" using nac by (auto simp: is_acapp_def)
        then show ?thesis using x b(2) a Var by (intro disjI2 bexI[of _ x]) auto
      next
        case (Fun h us)
        show ?thesis
          using fsub_subst_lift[OF a(1) _ "2.IH"[OF a(1)]] b(2) a(2) Fun by simp
      qed
    qed
  qed
qed

text ‹A variable argument of a flattened subterm of an instance.›

lemma var_targs_subst:
  assumes "is_Fun w" "Var y ∈ set (targs (w ⋅ θ))"
  shows "∃x. Var x ∈ set (targs w) ∧
    (θ x = Var y ∨ (∃g. is_ac_app g w ∧ is_ac_app g (θ x) ∧ Var y ∈ set (args_ac g (θ x))))"
proof (cases "is_acapp w")
  case True
  then obtain g where g: "is_ac_app g w" by (auto simp: is_acapp_def)
  then obtain a where a: "a ∈ set (targs w)" "Var y ∈ set (args_ac g (a ⋅ θ))"
    using assms(2) targs_subst_acapp[OF g, of θ] by auto
  have na: "¬ is_ac_app g a" by (rule targs_no_app[OF g a(1)])
  show ?thesis
  proof (cases a)
    case (Var x)
    then show ?thesis using a g by (cases "is_ac_app g (θ x)") auto
  next
    case (Fun h us)
    then have "¬ is_ac_app g (a ⋅ θ)" using na by (auto simp: is_ac_app_def)
    then show ?thesis using a(2) Fun by simp
  qed
next
  case False
  then obtain a where a: "a ∈ set (targs w)" "Var y = a ⋅ θ"
    using assms targs_subst_not_acapp[OF assms(1) False, of θ] by auto
  obtain x where "a = Var x" using a(2) by (cases a) auto
  then show ?thesis using a by auto
qed

end

subsection ‹Properties of ‹inst››

definition eq_sides :: "('f, 'v) eqs ⇒ ('f, 'v) term set" where
  "eq_sides E = (⋃(a, b) ∈ set E. {a, b})"

lemma eq_sides_simps [simp]:
  "eq_sides [] = {}"
  "eq_sides ((a, b) # E) = insert a (insert b (eq_sides E))"
  "eq_sides (E @ F) = eq_sides E ∪ eq_sides F"
  by (auto simp: eq_sides_def)

lemma eq_sides_subst: "eq_sides (subst_eqs σ E) = (λu. u ⋅ σ) ` eq_sides E"
  by (induction E) auto

lemma vars_upd_subst_eqs:
  "vars_eqs (subst_eqs (Var(z := t)) E) ⊆ (vars_eqs E - {z}) ∪ vars_term t"
  by (induction E) (auto simp: vars_term_subst split: if_splits)

context ac_unif
begin

lemma inst_idem:
  "inst E = Some (R, θ) ⟹ w ∈ vars_term (θ y) ⟹ θ w = Var w"
proof (induction E arbitrary: R θ y w rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this "2.prems"(2)] show ?thesis .
  next
    case ts: False
    have step: "θ w = Var w"
      if r1: "inst (subst_eqs (Var(z := u)) E) = Some (R, θ')" and θ: "θ = Var(z := u) ∘⇩s θ'"
        and z: "z ∉ vars_term u" and w: "w ∈ vars_term (θ y)"
        and IH: "⋀y w. w ∈ vars_term (θ' y) ⟹ θ' w = Var w"
      for z u θ'
    proof -
      have iv: "⋀x. vars_term (θ' x) ⊆ vars_eqs (subst_eqs (Var(z := u)) E) ∪ {x}"
        using inst_vars[OF r1] by blast
      have zE: "z ∉ vars_eqs (subst_eqs (Var(z := u)) E)"
        using vars_upd_subst_eqs[of z u E] z by blast
      obtain v where v: "v ∈ vars_term ((Var(z := u)) y)" "w ∈ vars_term (θ' v)"
        using w by (auto simp: θ subst_compose vars_term_subst)
      have "v ≠ z" using v(1) z by (auto split: if_splits)
      then have "w ≠ z" using iv[of v] v(2) zE by blast
      then show ?thesis using IH[OF v(2)] by (simp add: θ subst_compose)
    qed
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and rec: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        and θ: "θ = Var(z := t) ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      show ?thesis by (rule step[OF rec θ z "2.prems"(2) "2.IH"(2)[OF ts Var z rec]])
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        obtain θ' where x: "x ∉ vars_term s" and rec: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ')"
          and θ: "θ = Var(x := s) ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        show ?thesis by (rule step[OF rec θ x "2.prems"(2) "2.IH"(3)[OF ts Fun Var x rec]])
      next
        case (Fun f ts')
        obtain R0 where rec: "inst E = Some (R0, θ)"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        show ?thesis by (rule "2.IH"(4)[OF ts ‹s = Fun g ss› Fun rec "2.prems"(2)])
      qed
    qed
  qed
qed

lemma inst_idem_term: "inst E = Some (R, θ) ⟹ x ∈ vars_term (u ⋅ θ) ⟹ θ x = Var x"
  by (auto simp: vars_term_subst dest: inst_idem)

text ‹Facts about one variable elimination step inside ‹inst›.›

lemma upd_compose_other: "y ≠ z ⟹ (Var(z := u) ∘⇩s θ') y = θ' y"
  by (simp add: subst_compose)

lemma upd_compose_self: "z ∉ vars_term u ⟹ u ⋅ (Var(z := u) ∘⇩s θ') = u ⋅ θ'"
  by (simp add: subst_upd_not_in)

text ‹Every binding is a variable left unbound, or a non-variable side of the problem, instantiated.›

lemma inst_img:
  "inst E = Some (R, θ) ⟹
    (∃w. θ y = Var w ∧ θ w = Var w) ∨ (∃a ∈ eq_sides E. is_Fun a ∧ θ y = a ⋅ θ)"
proof (induction E arbitrary: R θ y rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this, of y] show ?thesis by auto
  next
    case ts: False
    have step: "(∃w. θ y = Var w ∧ θ w = Var w) ∨ (∃a ∈ eq_sides ((t, s) # E). is_Fun a ∧ θ y = a ⋅ θ)"
      if r1: "inst (subst_eqs (Var(z := u)) E) = Some (R, θ')" and th: "θ = Var(z := u) ∘⇩s θ'"
        and z: "z ∉ vars_term u" and u: "u ∈ {t, s}" and zs: "Var z ∈ {t, s}"
        and IH: "⋀y. (∃w. θ' y = Var w ∧ θ' w = Var w) ∨
          (∃a ∈ eq_sides (subst_eqs (Var(z := u)) E). is_Fun a ∧ θ' y = a ⋅ θ')"
      for z u θ'
    proof -
      let ?σ = "Var(z := u)"
      have iv: "⋀x. vars_term (θ' x) ⊆ vars_eqs (subst_eqs ?σ E) ∪ {x}"
        using inst_vars[OF r1] by blast
      have zE: "z ∉ vars_eqs (subst_eqs ?σ E)" using vars_upd_subst_eqs[of z u E] z by blast
      have lift: "?thesis" if "θ y = θ' v" "v ≠ z" for v
      proof -
        from IH[of v] show ?thesis
        proof
          assume "∃w. θ' v = Var w ∧ θ' w = Var w"
          then obtain w where w: "θ' v = Var w" "θ' w = Var w" by blast
          have "w ≠ z" using iv[of v] w(1) zE that(2) by auto
          then show ?thesis using w that(1) by (simp add: th upd_compose_other)
        next
          assume "∃a ∈ eq_sides (subst_eqs ?σ E). is_Fun a ∧ θ' v = a ⋅ θ'"
          then obtain a0 where a0: "a0 ∈ eq_sides E" "is_Fun (a0 ⋅ ?σ)" "θ' v = a0 ⋅ ?σ ⋅ θ'"
            by (auto simp: eq_sides_subst)
          have "is_Fun a0 ∨ (a0 = Var z ∧ is_Fun u)" using a0(2) by (cases a0) (auto split: if_splits)
          then show ?thesis
          proof
            assume "is_Fun a0"
            then show ?thesis using a0 that(1) by (intro disjI2 bexI[of _ a0]) (auto simp: th)
          next
            assume "a0 = Var z ∧ is_Fun u"
            then show ?thesis using a0 that(1) u z by (intro disjI2 bexI[of _ u]) (auto simp: th subst_upd_not_in)
          qed
        qed
      qed
      show ?thesis
      proof (cases "y = z")
        case True
        have "θ z = u ⋅ θ'" by (simp add: th subst_compose)
        also have "… = u ⋅ θ" by (simp add: th subst_upd_not_in[OF z])
        finally have tz: "θ z = u ⋅ θ" .
        show ?thesis
        proof (cases u)
          case (Var v)
          then have "v ≠ z" using z by auto
          moreover have "θ y = θ' v" using True Var by (simp add: th subst_compose)
          ultimately show ?thesis by (rule lift[rotated])
        next
          case (Fun g us)
          then show ?thesis using tz True u by auto
        qed
      next
        case False
        then show ?thesis by (intro lift) (simp_all add: th upd_compose_other)
      qed
    qed
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and r1: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        and th: "θ = Var(z := t) ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      show ?thesis by (rule step[OF r1 th z _ _ "2.IH"(2)[OF ts Var z r1]]) (simp_all add: Var)
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        obtain θ' where x: "x ∉ vars_term s" and r1: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ')"
          and th: "θ = Var(x := s) ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        show ?thesis by (rule step[OF r1 th x _ _ "2.IH"(3)[OF ts Fun Var x r1]]) (simp_all add: Var)
      next
        case (Fun f ts')
        obtain R0 where r1: "inst E = Some (R0, θ)"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        from "2.IH"(4)[OF ts ‹s = Fun g ss› Fun r1, of y] show ?thesis by auto
      qed
    qed
  qed
qed

lemma fst_subst_upd:
  assumes "Var y ∈ fst ` set (subst_eqs (Var(z := u)) E)"
  shows "Var y ∈ fst ` set E ∨ u = Var y"
proof -
  obtain a b where ab: "(a, b) ∈ set E" "a ⋅ Var(z := u) = Var y"
    using assms by (auto simp: subst_eqs_def)
  show ?thesis
  proof (cases a)
    case (Var w)
    then show ?thesis using ab by (cases "w = z") force+
  qed (use ab in auto)
qed

text ‹A variable bound to a variable is bound to a variable left-hand side of the problem.›

lemma inst_var_img:
  "inst E = Some (R, θ) ⟹ θ v = Var y ⟹ v = y ∨ Var y ∈ fst ` set E"
proof (induction E arbitrary: R θ v rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this "2.prems"(2)] show ?thesis by auto
  next
    case ts: False
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and r1: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        and th: "θ = Var(z := t) ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      note IH = "2.IH"(2)[OF ts Var z r1]
      have fst: "Var y ∈ fst ` set (subst_eqs (Var(z := t)) E) ⟹ Var y ∈ fst ` set ((t, s) # E)"
        using fst_subst_upd[of y z t E] by auto
      show ?thesis
      proof (cases "v = z")
        case True
        then have "t ⋅ θ' = Var y" using "2.prems"(2) by (simp add: th subst_compose)
        then obtain x where x: "t = Var x" "θ' x = Var y" by (cases t) auto
        from IH[OF x(2)] show ?thesis using x(1) fst by auto
      next
        case False
        then have "θ' v = Var y" using "2.prems"(2) by (simp add: th subst_compose)
        from IH[OF this] show ?thesis using fst by auto
      qed
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        obtain θ' where x: "x ∉ vars_term s" and r1: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ')"
          and th: "θ = Var(x := s) ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        note IH = "2.IH"(3)[OF ts Fun Var x r1]
        have fst: "Var y ∈ fst ` set (subst_eqs (Var(x := s)) E) ⟹ Var y ∈ fst ` set ((t, s) # E)"
          using fst_subst_upd[of y x s E] Fun by auto
        have "v ≠ x"
        proof
          assume "v = x"
          then have "s ⋅ θ' = Var y" using "2.prems"(2) by (simp add: th subst_compose)
          then show False using Fun by simp
        qed
        then have "θ' v = Var y" using "2.prems"(2) by (simp add: th subst_compose)
        from IH[OF this] show ?thesis using fst by auto
      next
        case (Fun f ts')
        obtain R0 where r1: "inst E = Some (R0, θ)"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        from "2.IH"(4)[OF ts ‹s = Fun g ss› Fun r1 "2.prems"(2)] show ?thesis by auto
      qed
    qed
  qed
qed

text ‹Residual equations are instances of sides of the problem, and both sides are not variables.›

lemma inst_res:
  "inst E = Some (R, θ) ⟹ (a, b) ∈ set R ⟹
    is_Fun a ∧ is_Fun b ∧ a ∈ (λu. u ⋅ θ) ` eq_sides E ∧ b ∈ (λu. u ⋅ θ) ` eq_sides E"
proof (induction E arbitrary: R θ rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this "2.prems"(2)] show ?thesis by auto
  next
    case ts: False
    have step: "?thesis"
      if r1: "inst (subst_eqs (Var(z := u)) E) = Some (R, θ')" and th: "θ = Var(z := u) ∘⇩s θ'"
        and IH: "is_Fun a ∧ is_Fun b ∧ a ∈ (λu. u ⋅ θ') ` eq_sides (subst_eqs (Var(z := u)) E) ∧
          b ∈ (λu. u ⋅ θ') ` eq_sides (subst_eqs (Var(z := u)) E)"
      for z u θ'
      using IH by (auto simp: eq_sides_subst th image_image)
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and r1: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        and th: "θ = Var(z := t) ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      show ?thesis by (rule step[OF r1 th "2.IH"(2)[OF ts Var z r1 "2.prems"(2)]])
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        obtain θ' where x: "x ∉ vars_term s" and r1: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ')"
          and th: "θ = Var(x := s) ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        show ?thesis by (rule step[OF r1 th "2.IH"(3)[OF ts Fun Var x r1 "2.prems"(2)]])
      next
        case (Fun f ts')
        obtain R0 where r1: "inst E = Some (R0, θ)" and R: "R = (t ⋅ θ, s ⋅ θ) # R0"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        show ?thesis
        proof (cases "(a, b) = (t ⋅ θ, s ⋅ θ)")
          case True
          then show ?thesis using Fun ‹s = Fun g ss› by auto
        next
          case False
          then have "(a, b) ∈ set R0" using "2.prems"(2) R by auto
          from "2.IH"(4)[OF ts ‹s = Fun g ss› Fun r1 this] show ?thesis by auto
        qed
      qed
    qed
  qed
qed

text ‹
  An invariant of the equations of an AC step: no left-hand side is an application of ‹f›,
  and a right-hand side that is an application of ‹f› has a variable on the left that occurs
  as a side of no other equation. Then no residual equation has an application of ‹f› as a side.
›

definition cnt :: "('f, 'v) eqs ⇒ 'v ⇒ nat" where
  "cnt E x = length (filter (λ(a, b). a = Var x ∨ b = Var x) E)"

definition invF :: "'f ⇒ ('f, 'v) eqs ⇒ bool" where
  "invF f E ⟷ (∀(a, b) ∈ set E. ¬ is_ac_app f a ∧
     (is_ac_app f b ⟶ (∃x. a = Var x ∧ cnt E x = 1)))"

lemma invF_D:
  "invF f E ⟹ (a, b) ∈ set E ⟹ ¬ is_ac_app f a ∧ (is_ac_app f b ⟶ (∃x. a = Var x ∧ cnt E x = 1))"
  unfolding invF_def by (drule (1) bspec) simp

lemma cnt_Cons: "cnt ((a, b) # E) x = (if a = Var x ∨ b = Var x then Suc (cnt E x) else cnt E x)"
  by (simp add: cnt_def)

lemma cnt_pos: "(a, b) ∈ set E ⟹ a = Var x ∨ b = Var x ⟹ 0 < cnt E x"
  by (auto simp: cnt_def filter_empty_conv length_greater_0_conv)

lemma invF_tail: "invF f (e # E) ⟹ invF f E"
proof -
  assume h: "invF f (e # E)"
  obtain a0 b0 where e: "e = (a0, b0)" by fastforce
  show "invF f E" unfolding invF_def
  proof (intro ballI, clarify)
    fix a b
    assume ab: "(a, b) ∈ set E"
    have ab': "(a, b) ∈ set (e # E)" using ab by simp
    have "¬ is_ac_app f a" using invF_D[OF h ab'] by blast
    moreover have "∃x. a = Var x ∧ cnt E x = 1" if bapp: "is_ac_app f b"
    proof -
      obtain x where x: "a = Var x" "cnt (e # E) x = 1" using invF_D[OF h ab'] bapp by blast
      have "0 < cnt E x" using cnt_pos[OF ab] x(1) by simp
      then show ?thesis using x by (auto simp: e cnt_Cons split: if_splits)
    qed
    ultimately show "¬ is_ac_app f a ∧ (is_ac_app f b ⟶ (∃x. a = Var x ∧ cnt E x = 1))" by blast
  qed
qed

lemma cnt_subst:
  assumes "⋀a. (a ⋅ σ = Var x) ⟷ a = Var x"
  shows "cnt (subst_eqs σ E) x = cnt E x"
proof -
  have h: "((λ(a, b). a = Var x ∨ b = Var x) ∘ (λ(s, t). (s ⋅ σ, t ⋅ σ))) = (λ(a, b). a = Var x ∨ b = Var x)"
    by (rule ext) (simp only: comp_def case_prod_beta fst_conv snd_conv assms)
  show ?thesis by (simp only: cnt_def subst_eqs_def filter_map length_map h)
qed

lemma cnt_subst_upd:
  assumes "x ≠ z" "u ≠ Var x"
  shows "cnt (subst_eqs (Var(z := u)) E) x = cnt E x"
proof (rule cnt_subst)
  fix a :: "('f, 'a) term"
  show "(a ⋅ Var(z := u) = Var x) ⟷ a = Var x" using assms by (cases a) auto
qed

lemma not_app_upd:
  "¬ is_ac_app f a ⟹ ¬ is_ac_app f u ⟹ ¬ is_ac_app f (a ⋅ Var(z := u))"
  by (cases a) (auto simp: is_ac_app_def)

lemma app_upd:
  "is_ac_app f (b ⋅ Var(z := u)) ⟹ is_ac_app f b ∨ (b = Var z ∧ is_ac_app f u)"
  by (cases b) (auto simp: is_ac_app_def split: if_splits)

lemma invF_subst:
  assumes inv: "invF f ((t, s) # E)" and zu: "(Var z = s ∧ u = t) ∨ (Var z = t ∧ u = s ∧ is_Fun s)"
    and z: "z ∉ vars_term u"
  shows "invF f (subst_eqs (Var(z := u)) E)"
  unfolding invF_def
proof (intro ballI, clarify)
  let ?σ = "Var(z := u)"
  fix a' b'
  assume "(a', b') ∈ set (subst_eqs ?σ E)"
  then obtain a b where ab: "(a, b) ∈ set E" "a' = a ⋅ ?σ" "b' = b ⋅ ?σ"
    by (auto simp: subst_eqs_def)
  have na: "¬ is_ac_app f a" using inv ab(1) by (auto simp: invF_def)
  have zcnt: "0 < cnt ((t, s) # E) z" using zu by (auto simp: cnt_Cons)
  have u_ok: "¬ is_ac_app f u ∨ ¬ (∃b. (Var z, b) ∈ set E ∨ (b, Var z) ∈ set E)"
  proof (cases "is_ac_app f u")
    case True
    then have "u = s" "Var z = t" using zu inv by (auto simp: invF_def)
    then have "cnt ((t, s) # E) z = 1" using inv True by (auto simp: invF_def)
    then have "cnt E z = 0" by (simp add: cnt_Cons ‹Var z = t›[symmetric])
    then show ?thesis by (auto dest: cnt_pos)
  qed simp
  have "¬ is_ac_app f a'"
  proof
    assume "is_ac_app f a'"
    then have "a = Var z ∧ is_ac_app f u" using app_upd[of f a z u] na ab(2) by auto
    then show False using u_ok ab(1) by auto
  qed
  moreover have "∃x. a' = Var x ∧ cnt (subst_eqs ?σ E) x = 1" if b'app: "is_ac_app f b'"
  proof -
    have "is_ac_app f b"
    proof -
      have "is_ac_app f b ∨ (b = Var z ∧ is_ac_app f u)" using app_upd[of f b z u] b'app ab(3) by simp
      then show ?thesis using u_ok ab(1) by auto
    qed
    have ab': "(a, b) ∈ set ((t, s) # E)" using ab(1) by simp
    obtain x where x0: "a = Var x" "cnt ((t, s) # E) x = 1"
      using invF_D[OF inv ab'] ‹is_ac_app f b› by blast
    have "0 < cnt E x" using cnt_pos[OF ab(1)] x0(1) by simp
    then have tx: "t ≠ Var x" "s ≠ Var x" and x: "a = Var x" "cnt E x = 1"
      using x0 by (auto simp: cnt_Cons split: if_splits)
    have xz: "x ≠ z" using tx zu by auto
    have ux: "u ≠ Var x" using tx zu by auto
    have "a' = Var x" using ab(2) x(1) xz by simp
    moreover have "cnt (subst_eqs ?σ E) x = 1" using cnt_subst_upd[OF xz ux] x(2) by simp
    ultimately show ?thesis by blast
  qed
  ultimately show "¬ is_ac_app f a' ∧ (is_ac_app f b' ⟶ (∃x. a' = Var x ∧ cnt (subst_eqs ?σ E) x = 1))"
    by blast
qed

lemma inst_res_not_app:
  "inst E = Some (R, θ) ⟹ invF f E ⟹ (a, b) ∈ set R ⟹ ¬ is_ac_app f a ∧ ¬ is_ac_app f b"
proof (induction E arbitrary: R θ rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this invF_tail[OF "2.prems"(2)] "2.prems"(3)] show ?thesis .
  next
    case ts: False
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and r1: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      have "invF f (subst_eqs (Var(z := t)) E)" by (rule invF_subst[OF "2.prems"(2) _ z]) (simp add: Var)
      from "2.IH"(2)[OF ts Var z r1 this "2.prems"(3)] show ?thesis .
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x)
        obtain θ' where x: "x ∉ vars_term s" and r1: "inst (subst_eqs (Var(x := s)) E) = Some (R, θ')"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        have "invF f (subst_eqs (Var(x := s)) E)" by (rule invF_subst[OF "2.prems"(2) _ x]) (simp add: Var Fun)
        from "2.IH"(3)[OF ts Fun Var x r1 this "2.prems"(3)] show ?thesis .
      next
        case (Fun f' ts')
        obtain R0 where r1: "inst E = Some (R0, θ)" and R: "R = (t ⋅ θ, s ⋅ θ) # R0"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        show ?thesis
        proof (cases "(a, b) = (t ⋅ θ, s ⋅ θ)")
          case True
          have "¬ is_ac_app f t" using "2.prems"(2) by (simp add: invF_def)
          moreover have "¬ is_ac_app f s" using "2.prems"(2) Fun by (auto simp: invF_def)
          ultimately show ?thesis using True Fun ‹s = Fun g ss› not_app_subst by auto
        next
          case False
          then have "(a, b) ∈ set R0" using "2.prems"(3) R by auto
          from "2.IH"(4)[OF ts ‹s = Fun g ss› Fun r1 invF_tail[OF "2.prems"(2)] this] show ?thesis .
        qed
      qed
    qed
  qed
qed

subsection ‹The measure›

text ‹Flattened subterms of the sides of a problem.›

definition Sub :: "('f, 'v) eqs ⇒ ('f, 'v) term set" where
  "Sub P = (⋃t ∈ eq_sides P. fsub t)"

text ‹PVS Definition 11: variables occurring not only as arguments of AC applications.›

definition VNAC :: "('f, 'v) eqs ⇒ 'v set" where
  "VNAC P = {x. Var x ∈ eq_sides P} ∪
    {x. ∃t ∈ Sub P. is_Fun t ∧ ¬ is_acapp t ∧ Var x ∈ set (targs t)}"

text ‹PVS Definition 13: variables that are arguments of terms with different heads.›

definition V2 :: "('f, 'v) eqs ⇒ 'v set" where
  "V2 P = {x. ∃t ∈ Sub P. ∃s ∈ Sub P. is_Fun t ∧ is_Fun s ∧ key t ≠ key s ∧
    Var x ∈ set (targs t) ∧ Var x ∈ set (targs s)}"

text ‹PVS Definition 15: admissible subterms, the proper non-variable (flattened) subterms of the sides.›

definition AS :: "('f, 'v) eqs ⇒ ('f, 'v) term set" where
  "AS P = {u. ∃t ∈ eq_sides P. u ∈ fsub t ∧ u ≠ t ∧ is_Fun u}"

definition psize :: "('f, 'v) eqs ⇒ nat" where
  "psize P = sum_list (map (λ(a, b). size a + size b) P)"

definition tmeasure :: "('f, 'v) eqs ⇒ nat × nat × nat × nat" where
  "tmeasure P = (card (VNAC P), card (V2 P), card (AS P), psize P)"

lemma finite_eq_sides [simp]: "finite (eq_sides P)"
  by (induction P) (auto simp: eq_sides_def)

lemma finite_Sub [simp]: "finite (Sub P)"
  by (simp add: Sub_def)

lemma vars_eq_sides: "t ∈ eq_sides P ⟹ vars_term t ⊆ vars_eqs P"
  by (auto simp: eq_sides_def vars_eqs_def)

lemma vars_Sub: "u ∈ Sub P ⟹ vars_term u ⊆ vars_eqs P"
  using vars_fsub vars_eq_sides by (fastforce simp: Sub_def)

lemma Var_targs_vars: "Var x ∈ set (targs t) ⟹ x ∈ vars_term t"
  using vars_targs by fastforce

lemma VNAC_vars: "VNAC P ⊆ vars_eqs P"
proof
  fix x
  assume "x ∈ VNAC P"
  then consider "Var x ∈ eq_sides P" | t where "t ∈ Sub P" "Var x ∈ set (targs t)"
    by (auto simp: VNAC_def)
  then show "x ∈ vars_eqs P"
  proof cases
    case 1
    then show ?thesis using vars_eq_sides[OF 1] by simp
  next
    case 2
    then show ?thesis using vars_Sub[OF 2(1)] Var_targs_vars[OF 2(2)] by blast
  qed
qed

lemma V2_vars: "V2 P ⊆ vars_eqs P"
proof
  fix x
  assume "x ∈ V2 P"
  then obtain t where t: "t ∈ Sub P" "Var x ∈ set (targs t)" by (auto simp: V2_def)
  show "x ∈ vars_eqs P" using vars_Sub[OF t(1)] Var_targs_vars[OF t(2)] by blast
qed

lemma finite_vars_eqs [simp]: "finite (vars_eqs P)"
  by (induction P) (auto simp: vars_eqs_def)

lemma finite_VNAC [simp]: "finite (VNAC P)"
  by (rule finite_subset[OF VNAC_vars]) simp

lemma finite_V2 [simp]: "finite (V2 P)"
  by (rule finite_subset[OF V2_vars]) simp

lemma AS_Sub: "AS P ⊆ Sub P"
  by (auto simp: AS_def Sub_def)

lemma finite_AS [simp]: "finite (AS P)"
  by (rule finite_subset[OF AS_Sub]) simp

lemma Sub_mono: "eq_sides P ⊆ eq_sides P' ⟹ Sub P ⊆ Sub P'"
  by (auto simp: Sub_def)

lemma AS_fsub: "u ∈ AS P ⟹ w ∈ fsub u ⟹ is_Fun w ⟹ w ∈ AS P"
proof -
  assume "u ∈ AS P" "w ∈ fsub u" "is_Fun w"
  then obtain t where t: "t ∈ eq_sides P" "u ∈ fsub t" "u ≠ t" by (auto simp: AS_def)
  have "w ∈ fsub t" by (rule fsub_trans[OF t(2) ‹w ∈ fsub u›])
  moreover have "w ≠ t" using fsub_size[OF ‹w ∈ fsub u›] fsub_size_less[OF t(2,3)] by auto
  ultimately show ?thesis using t(1) ‹is_Fun w› by (auto simp: AS_def)
qed

subsection ‹The equations of an AC step›

text ‹The shape of the equations returned by ‹solve_ac›.›

definition shapeC :: "'f ⇒ ('f, nat) term ⇒ ('f, nat) term ⇒ nat ⇒ nat ⇒ ('f, nat) eqs ⇒ bool" where
  "shapeC f t s nv nv' C ⟷ distinct (map fst C) ∧ nv ≤ nv' ∧
    (∀(w, r) ∈ set C. w ∈ set (args_ac f t) ∪ set (args_ac f s) ∧
      ((∃z. r = Var z ∧ nv ≤ z ∧ z < nv') ∨
       (is_ac_app f r ∧ (∀a ∈ set (args_ac f r). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv'))) ∧
      (is_Fun w ⟶ is_Var r))"

lemma distinct_dio_ws: "distinct (dio_ws f t s)"
proof -
  have d: "distinct (map fst (dio_us f t s))" for t s
    by (simp add: dio_us_def grp_def comp_def)
  have mem: "x ∈# dio_L f t s" if "x ∈ fst ` set (dio_us f t s)" for x t s
    using that by (auto simp: dio_us_def grp_def)
  have "fst ` set (dio_us f t s) ∩ fst ` set (dio_us f s t) = {}"
  proof (rule equals0I)
    fix x
    assume "x ∈ fst ` set (dio_us f t s) ∩ fst ` set (dio_us f s t)"
    then have "x ∈# dio_L f t s" "x ∈# dio_L f s t" using mem by auto
    then show False by (simp add: dio_L_def in_diff_count)
  qed
  then show ?thesis using d[of t s] d[of s t] by (simp add: dio_ws_def)
qed

lemma length_new_vars: "length (new_vars nv D j) = col_sum D j"
  by (simp add: new_vars_def length_concat comp_def col_sum_def sum_list_nth
      interv_sum_list_conv_sum_set_nat atLeast0LessThan)

lemma set_new_vars: "a ∈ set (new_vars nv D j) ⟹ ∃z. a = Var z ∧ nv ≤ z ∧ z < nv + length D"
  by (auto simp: new_vars_def)

lemma mk_ac_new_vars:
  assumes "ac f" "0 < col_sum D j"
  shows "(∃z. mk_ac f (new_vars nv D j) = Var z ∧ nv ≤ z ∧ z < nv + length D) ∨
    (is_ac_app f (mk_ac f (new_vars nv D j)) ∧
     (∀a ∈ set (args_ac f (mk_ac f (new_vars nv D j))). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv + length D))"
proof (cases "col_sum D j = 1")
  case True
  then obtain a :: "('f, nat) term" where nv1: "new_vars nv D j = [a]" using length_new_vars[of nv D j]
    by (metis length_0_conv length_Suc_conv One_nat_def)
  then obtain z where "a = Var z" "nv ≤ z" "z < nv + length D" using set_new_vars[of a nv D j] by auto
  then show ?thesis unfolding nv1 by auto
next
  case False
  let ?xs = "new_vars nv D j :: ('f, nat) term list"
  have l: "length ?xs = col_sum D j" by (rule length_new_vars)
  have len: "length ?xs ≥ 2" using False assms(2) l by simp
  have ne: "?xs ≠ []" using len by auto
  have nap: "∀a ∈ set ?xs. ¬ is_ac_app f a"
  proof
    fix a
    assume "a ∈ set ?xs"
    then obtain z where "a = Var z" using set_new_vars by blast
    then show "¬ is_ac_app f a" by simp
  qed
  have "args_ac f (mk_ac f ?xs) = ?xs" by (rule args_ac_mk_ac[OF assms(1) ne nap])
  then show ?thesis using is_ac_app_mk_ac[OF assms(1) len] set_new_vars by auto
qed

lemma mk_ac_new_vars_single:
  assumes "col_sum D j = 1"
  shows "is_Var (mk_ac f (new_vars nv D j))"
proof -
  obtain a :: "('f, nat) term" where "new_vars nv D j = [a]" using length_new_vars[of nv D j] assms
    by (metis length_0_conv length_Suc_conv One_nat_def)
  then show ?thesis using set_new_vars[of a nv D j] by auto
qed

lemma sol_eq_shape:
  assumes "ac f" "valid_sub ws D" "j < length ws"
  shows "((∃z. mk_ac f (new_vars nv D j) = Var z ∧ nv ≤ z ∧ z < nv + length D) ∨
      (is_ac_app f (mk_ac f (new_vars nv D j)) ∧
       (∀a ∈ set (args_ac f (mk_ac f (new_vars nv D j))). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv + length D))) ∧
    (is_Fun (ws ! j) ⟶ is_Var (mk_ac f (new_vars nv D j)))"
proof
  have pos: "0 < col_sum D j" using assms(2,3) by (simp add: valid_sub_def)
  show "(∃z. mk_ac f (new_vars nv D j) = Var z ∧ nv ≤ z ∧ z < nv + length D) ∨
      (is_ac_app f (mk_ac f (new_vars nv D j)) ∧
       (∀a ∈ set (args_ac f (mk_ac f (new_vars nv D j))). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv + length D))"
    by (rule mk_ac_new_vars[OF assms(1) pos])
  show "is_Fun (ws ! j) ⟶ is_Var (mk_ac f (new_vars nv D j))"
    using assms(2,3) mk_ac_new_vars_single by (auto simp: valid_sub_def)
qed

lemma solve_ac_shape:
  assumes "ac f" "(C, nv') ∈ set (solve_ac f t s nv)"
  shows "shapeC f t s nv nv' C"
  using mem_solve_ac[OF assms(2)]
proof
  assume "dio_L f t s = {#} ∧ dio_L f s t = {#} ∧ C = [] ∧ nv' = nv"
  then show ?thesis by (simp add: shapeC_def)
next
  assume "∃D. D ∈ set (subseqs (dio_basis f t s)) ∧ valid_sub (dio_ws f t s) D ∧
      C = sol_eqs f nv (dio_ws f t s) D ∧ nv' = nv + length D"
  then obtain D where D: "valid_sub (dio_ws f t s) D" "C = sol_eqs f nv (dio_ws f t s) D"
    "nv' = nv + length D" by blast
  let ?ws = "dio_ws f t s"
  have "map fst C = ?ws" using D(2) by (simp add: sol_eqs_def comp_def map_nth)
  moreover have "∀(w, r) ∈ set C. w ∈ set (args_ac f t) ∪ set (args_ac f s) ∧
      ((∃z. r = Var z ∧ nv ≤ z ∧ z < nv') ∨
       (is_ac_app f r ∧ (∀a ∈ set (args_ac f r). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv'))) ∧
      (is_Fun w ⟶ is_Var r)"
  proof -
    have "?ws ! j ∈ set (args_ac f t) ∪ set (args_ac f s)" if "j < length ?ws" for j
      using that set_dio_ws[of f t s] nth_mem[OF that] by blast
    then show ?thesis using sol_eq_shape[OF assms(1) D(1)] D(3)
      unfolding D(2) set_sol_eqs by auto
  qed
  ultimately show ?thesis using distinct_dio_ws D(3) by (simp add: shapeC_def)
qed

text ‹A variable bound by ‹inst› occurs as a side of the problem.›

lemma inst_dom:
  "inst E = Some (R, θ) ⟹ θ x ≠ Var x ⟹ Var x ∈ eq_sides E"
proof (induction E arbitrary: R θ rule: inst.induct)
  case 1
  then show ?case by auto
next
  case (2 t s E)
  show ?case
  proof (cases "t = s")
    case True
    then have "inst E = Some (R, θ)" using "2.prems"(1) by simp
    from "2.IH"(1)[OF True this "2.prems"(2)] show ?thesis by auto
  next
    case ts: False
    have step: "Var x ∈ eq_sides ((t, s) # E)"
      if th: "θ = Var(z := u) ∘⇩s θ'" and zs: "Var z ∈ {t, s}" and us: "u ∈ {t, s}"
        and IH: "θ' x ≠ Var x ⟹ Var x ∈ eq_sides (subst_eqs (Var(z := u)) E)"
      for z u θ'
    proof (cases "x = z")
      case True
      then show ?thesis using zs by auto
    next
      case False
      then have "θ' x ≠ Var x" using "2.prems"(2) by (simp add: th subst_compose)
      then obtain a where a: "a ∈ eq_sides E" "a ⋅ Var(z := u) = Var x"
        using IH by (auto simp: eq_sides_subst)
      then have "a = Var x ∨ u = Var x" by (cases a) (auto split: if_splits)
      then show ?thesis using a(1) us by auto
    qed
    show ?thesis
    proof (cases s)
      case (Var z)
      obtain θ' where z: "z ∉ vars_term t" and r1: "inst (subst_eqs (Var(z := t)) E) = Some (R, θ')"
        and th: "θ = Var(z := t) ∘⇩s θ'"
        using "2.prems"(1) ts Var by (auto split: if_splits)
      show ?thesis by (rule step[OF th _ _ "2.IH"(2)[OF ts Var z r1]]) (simp_all add: Var)
    next
      case (Fun g ss)
      show ?thesis
      proof (cases t)
        case (Var x')
        obtain θ' where x: "x' ∉ vars_term s" and r1: "inst (subst_eqs (Var(x' := s)) E) = Some (R, θ')"
          and th: "θ = Var(x' := s) ∘⇩s θ'"
          using "2.prems"(1) ts Var Fun by (auto split: if_splits)
        show ?thesis by (rule step[OF th _ _ "2.IH"(3)[OF ts Fun Var x r1]]) (simp_all add: Var)
      next
        case (Fun f' ts')
        obtain R0 where r1: "inst E = Some (R0, θ)"
          using "2.prems"(1) ts ‹s = Fun g ss› Fun by auto
        from "2.IH"(4)[OF ts ‹s = Fun g ss› Fun r1 "2.prems"(2)] show ?thesis by auto
      qed
    qed
  qed
qed

end

subsection ‹One AC step›

text ‹
  The setting of one AC step: the AC pair ‹t ≈? s› of the symbol ‹f›, the equations ‹C› returned
  by ‹solve_ac›, and the result ‹(R, θ)› of ‹inst› on them.
›

locale ac_step = ac_unif ac dsolve
  for ac :: "'f ⇒ bool" and dsolve :: "nat ⇒ int list list ⇒ nat list list option" +
  fixes f :: 'f and t s :: "('f, nat) term" and nv nv' :: nat and C R :: "('f, nat) eqs"
    and θ :: "('f, nat) subst"
  assumes f: "ac f" and t: "is_ac_app f t" and s: "is_ac_app f s"
    and V: "vars_term t ∪ vars_term s ⊆ {..<nv}" and shape: "shapeC f t s nv nv' C"
    and inst: "inst C = Some (R, θ)"
begin

definition U0 :: "('f, nat) term set" where
  "U0 = {w. (∃r. (w, r) ∈ set C) ∧ is_Fun w}"

lemma lhs_args: "(w, r) ∈ set C ⟹ w ∈ set (args_ac f t) ∪ set (args_ac f s)"
  using shape by (auto simp: shapeC_def)

lemma lhs_targs: "(w, r) ∈ set C ⟹ w ∈ set (targs t) ∪ set (targs s)"
  using lhs_args t s by (simp add: targs_acapp)

lemma lhs_vars: "(w, r) ∈ set C ⟹ vars_term w ⊆ {..<nv}"
proof -
  assume "(w, r) ∈ set C"
  then have "vars_term w ⊆ vars_term t ∪ vars_term s"
    using lhs_args vars_args_ac[of t f] vars_args_ac[of s f] by blast
  then show ?thesis using V by blast
qed

lemma lhs_noapp: "(w, r) ∈ set C ⟹ ¬ is_ac_app f w"
  using lhs_args args_ac_no_app by blast

lemma rhs_form:
  "(w, r) ∈ set C ⟹ (∃z. r = Var z ∧ nv ≤ z ∧ z < nv') ∨
    (is_ac_app f r ∧ (∀a ∈ set (args_ac f r). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv'))"
  using shape by (auto simp: shapeC_def)

lemma fun_lhs: "(w, r) ∈ set C ⟹ is_Fun w ⟹ is_Var r"
  using shape by (auto simp: shapeC_def)

lemma nv_le: "nv ≤ nv'"
  using shape by (simp add: shapeC_def)

lemma rhs_vars: "(w, r) ∈ set C ⟹ x ∈ vars_term r ⟹ nv ≤ x ∧ x < nv'"
proof -
  assume wr: "(w, r) ∈ set C" and x: "x ∈ vars_term r"
  from rhs_form[OF wr] show ?thesis
  proof
    assume "is_ac_app f r ∧ (∀a ∈ set (args_ac f r). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv')"
    then show ?thesis using x vars_args_ac[of r f] by fastforce
  qed (use x in auto)
qed

lemma sides_C: "a ∈ eq_sides C ⟹ (∃r. (a, r) ∈ set C) ∨ (∃w. (w, a) ∈ set C)"
  by (auto simp: eq_sides_def)

lemma fst_Var: "Var y ∈ fst ` set C ⟹ y < nv"
  using lhs_vars by fastforce

lemma invF_C: "invF f C"
  unfolding invF_def
proof (intro ballI, clarify)
  fix w r
  assume wr: "(w, r) ∈ set C"
  have "∃x. w = Var x ∧ cnt C x = 1" if rapp: "is_ac_app f r"
  proof -
    obtain x where x: "w = Var x" using fun_lhs[OF wr] rapp by (cases w) auto
    have xnv: "x < nv" using lhs_vars[OF wr] x by simp
    have "cnt C x = 1"
    proof -
      have d: "distinct (map fst C)" using shape by (simp add: shapeC_def)
      have other: "¬ (a = Var x ∨ b = Var x)" if "(a, b) ∈ set C" "(a, b) ≠ (w, r)" for a b
      proof
        assume "a = Var x ∨ b = Var x"
        then show False
        proof
          assume "a = Var x"
          then have "a = w" using x by simp
          then show False using d that wr by (metis (no_types, lifting) eq_key_imp_eq_value prod.inject)
        next
          assume "b = Var x"
          then show False using rhs_vars[OF that(1), of x] xnv by simp
        qed
      qed
      have rx: "r ≠ Var x" using rapp by auto
      have "filter (λ(a, b). a = Var x ∨ b = Var x) C = [(w, r)]"
      proof -
        have "distinct C" using d by (simp add: distinct_map)
        then show ?thesis using wr other x
        proof (induction C)
          case (Cons e C')
          then show ?case by (cases e) (auto simp: filter_empty_conv)
        qed simp
      qed
      then show ?thesis by (simp add: cnt_def)
    qed
    then show ?thesis using x by blast
  qed
  then show "¬ is_ac_app f w ∧ (is_ac_app f r ⟶ (∃x. w = Var x ∧ cnt C x = 1))"
    using lhs_noapp[OF wr] by blast
qed

lemma img_var: "θ v = Var y ⟹ v = y ∨ y < nv"
  using inst_var_img[OF inst] fst_Var by blast

lemma img_var_arg: "θ v = Var y ⟹ v ≠ y ⟹ Var y ∈ set (targs t) ∪ set (targs s)"
proof -
  assume "θ v = Var y" "v ≠ y"
  then have "Var y ∈ fst ` set C" using inst_var_img[OF inst] by blast
  then show ?thesis using lhs_targs by force
qed

lemma dom_orig:
  assumes "θ x ≠ Var x" "x < nv"
  shows "Var x ∈ set (targs t) ∪ set (targs s)"
proof -
  have "Var x ∈ eq_sides C" by (rule inst_dom[OF inst assms(1)])
  then consider r where "(Var x, r) ∈ set C" | w where "(w, Var x) ∈ set C" using sides_C by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using lhs_targs by blast
  next
    case 2
    then show ?thesis using rhs_vars[OF 2, of x] assms(2) by simp
  qed
qed

lemma dom_vars: "θ x ≠ Var x ⟹ x ∈ vars_eqs C"
  using inst_vars[OF inst] by blast

lemma vars_C: "vars_eqs C ⊆ {..<nv'}"
proof
  fix x
  assume "x ∈ vars_eqs C"
  then obtain w r where wr: "(w, r) ∈ set C" "x ∈ vars_term w ∨ x ∈ vars_term r"
    by (auto simp: vars_eqs_def)
  then show "x ∈ {..<nv'}" using lhs_vars[OF wr(1)] rhs_vars[OF wr(1), of x] nv_le by auto
qed

lemma idem: "x ∈ vars_term (u ⋅ θ) ⟹ θ x = Var x"
  by (rule inst_idem_term[OF inst])

lemma U0_noapp: "u ∈ U0 ⟹ ¬ is_ac_app f (u ⋅ δ)"
proof -
  assume "u ∈ U0"
  then obtain r where ur: "(u, r) ∈ set C" "is_Fun u" by (auto simp: U0_def)
  show ?thesis by (rule not_app_subst[OF lhs_noapp[OF ur(1)] ur(2)])
qed

lemma U0_fsub: "u ∈ U0 ⟹ u ∈ set (targs t) ∪ set (targs s)"
  using lhs_targs by (auto simp: U0_def)

text ‹The images of variables (the characterization (T') of the bindings).›

lemma img_shape:
  "is_Fun (θ y) ⟹ (∃u ∈ U0. θ y = u ⋅ θ) ∨
    (is_ac_app f (θ y) ∧ (∀b ∈ set (args_ac f (θ y)). (∃w. b = Var w ∧ θ w = Var w) ∨ (∃u ∈ U0. b = u ⋅ θ)))"
proof (induction "size (θ y)" arbitrary: y rule: less_induct)
  case less
  obtain a where a: "a ∈ eq_sides C" "is_Fun a" "θ y = a ⋅ θ"
    using inst_img[OF inst, of y] less.prems by auto
  from sides_C[OF a(1)] show ?case
  proof
    assume "∃r. (a, r) ∈ set C"
    then show ?thesis using a by (auto simp: U0_def)
  next
    assume "∃w. (w, a) ∈ set C"
    then obtain w where wa: "(w, a) ∈ set C" by blast
    have app: "is_ac_app f a" and args: "∀b ∈ set (args_ac f a). ∃z. b = Var z"
      using rhs_form[OF wa] a(2) by auto
    have "is_ac_app f (θ y)" using app a(3) by (auto simp: is_ac_app_def)
    moreover have "(∃w. b = Var w ∧ θ w = Var w) ∨ (∃u ∈ U0. b = u ⋅ θ)"
      if b: "b ∈ set (args_ac f (θ y))" for b
    proof -
      have "b ∈ set (concat (map (λc. args_ac f (c ⋅ θ)) (args_ac f a)))"
        using b a(3) args_ac_subst[of f a θ] by simp
      then obtain c where c: "c ∈ set (args_ac f a)" "b ∈ set (args_ac f (c ⋅ θ))" by auto
      obtain z where z: "c = Var z" using args c(1) by blast
      have zv: "z ∈ vars_term a"
      proof -
        have "Var z ∈ set (args_ac f a)" using c(1) z by simp
        then have "z ∈ (⋃u ∈ set (args_ac f a). vars_term u)" by force
        then show ?thesis using vars_args_ac[of a f] by simp
      qed
      have lt: "size (θ z) < size (θ y)"
      proof -
        have "a ≠ Var z" using a(2) by auto
        then show ?thesis using size_subst_occurs[OF zv, of θ] a(3) by simp
      qed
      show ?thesis
      proof (cases "is_Fun (θ z)")
        case False
        then obtain w where w: "θ z = Var w" by (cases "θ z") auto
        then have "θ w = Var w" using idem[of w "Var z"] by simp
        then show ?thesis using c(2) z w by auto
      next
        case True
        from less.hyps[OF lt True] show ?thesis
        proof
          assume "∃u ∈ U0. θ z = u ⋅ θ"
          then obtain u where u: "u ∈ U0" "θ z = u ⋅ θ" by blast
          have "¬ is_ac_app f (u ⋅ θ)" by (rule U0_noapp[OF u(1)])
          then show ?thesis using c(2) z u by auto
        next
          assume "is_ac_app f (θ z) ∧ (∀b ∈ set (args_ac f (θ z)). (∃w. b = Var w ∧ θ w = Var w) ∨
            (∃u ∈ U0. b = u ⋅ θ))"
          then show ?thesis using c(2) z by auto
        qed
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma nonvar_img:
  assumes "a0 ∈ eq_sides C" "is_Fun (a0 ⋅ θ)" "¬ is_ac_app f (a0 ⋅ θ)"
  shows "a0 ⋅ θ ∈ (λu. u ⋅ θ) ` U0"
proof (cases a0)
  case (Var y)
  then have "is_Fun (θ y)" "¬ is_ac_app f (θ y)" using assms(2,3) by simp_all
  then show ?thesis using img_shape[of y] Var by auto
next
  case (Fun g ts)
  from sides_C[OF assms(1)] show ?thesis
  proof
    assume "∃r. (a0, r) ∈ set C"
    then have "a0 ∈ U0" using Fun by (auto simp: U0_def)
    then show ?thesis by (rule imageI)
  next
    assume "∃w. (w, a0) ∈ set C"
    then obtain w where wa: "(w, a0) ∈ set C" ..
    from rhs_form[OF wa] have "is_ac_app f a0" using Fun by auto
    then have "is_ac_app f (a0 ⋅ θ)" by (auto simp: is_ac_app_def)
    then show ?thesis using assms(3) by simp
  qed
qed

lemma res_shape: "(a, b) ∈ set R ⟹ a ∈ (λu. u ⋅ θ) ` U0 ∧ b ∈ (λu. u ⋅ θ) ` U0"
proof -
  assume ab: "(a, b) ∈ set R"
  note r = inst_res[OF inst ab]
  note na = inst_res_not_app[OF inst invF_C ab]
  obtain a0 where a0: "a0 ∈ eq_sides C" "a = a0 ⋅ θ" using r by blast
  obtain b0 where b0: "b0 ∈ eq_sides C" "b = b0 ⋅ θ" using r by blast
  show ?thesis using nonvar_img[OF a0(1)] nonvar_img[OF b0(1)] a0(2) b0(2) r na by auto
qed

lemma res_Fun: "u ∈ eq_sides R ⟹ is_Fun u"
  using inst_res[OF inst] by (auto simp: eq_sides_def)

text ‹A variable argument of the image of a variable that is an application of ‹f›.›

lemma rhs_trace:
  "is_ac_app f (θ y) ⟹ Var Y ∈ set (args_ac f (θ y)) ⟹
    ∃w r z. (w, r) ∈ set C ∧ is_ac_app f r ∧ Var z ∈ set (args_ac f r) ∧ θ z = Var Y"
proof (induction "size (θ y)" arbitrary: y rule: less_induct)
  case less
  obtain a where a: "a ∈ eq_sides C" "is_Fun a" "θ y = a ⋅ θ"
    using inst_img[OF inst, of y] less.prems(1) by auto
  from sides_C[OF a(1)] show ?case
  proof
    assume "∃r. (a, r) ∈ set C"
    then have "a ∈ U0" using a(2) by (auto simp: U0_def)
    then show ?thesis using U0_noapp less.prems(1) a(3) by metis
  next
    assume "∃w. (w, a) ∈ set C"
    then obtain w where wa: "(w, a) ∈ set C" by blast
    have app: "is_ac_app f a" and args: "∀b ∈ set (args_ac f a). ∃z. b = Var z"
      using rhs_form[OF wa] a(2) by auto
    have "Var Y ∈ set (concat (map (λc. args_ac f (c ⋅ θ)) (args_ac f a)))"
      using less.prems(2) a(3) args_ac_subst[of f a θ] by simp
    then obtain c where c: "c ∈ set (args_ac f a)" "Var Y ∈ set (args_ac f (c ⋅ θ))" by auto
    obtain z where z: "c = Var z" using args c(1) by blast
    show ?thesis
    proof (cases "is_ac_app f (θ z)")
      case False
      then have "θ z = Var Y" using c(2) z by simp
      then show ?thesis using wa app c(1) z by blast
    next
      case True
      have zv: "z ∈ vars_term a"
      proof -
        have "Var z ∈ set (args_ac f a)" using c(1) z by simp
        then have "z ∈ (⋃u ∈ set (args_ac f a). vars_term u)" by force
        then show ?thesis using vars_args_ac[of a f] by simp
      qed
      have "a ≠ Var z" using a(2) by auto
      then have lt: "size (θ z) < size (θ y)" using size_subst_occurs[OF zv, of θ] a(3) by simp
      show ?thesis by (rule less.hyps[OF lt True]) (use c(2) z in simp)
    qed
  qed
qed

lemma fsub_rhs:
  assumes "(w, r) ∈ set C" "T ∈ fsub r" "is_Fun T"
  shows "T = r ∧ is_ac_app f r"
proof -
  from rhs_form[OF assms(1)] show ?thesis
  proof
    assume "∃z. r = Var z ∧ nv ≤ z ∧ z < nv'"
    then show ?thesis using assms(2,3) by auto
  next
    assume r: "is_ac_app f r ∧ (∀a ∈ set (args_ac f r). ∃z. a = Var z ∧ nv ≤ z ∧ z < nv')"
    then obtain g ts where g: "r = Fun g ts" by (auto simp: is_ac_app_def)
    have "T = r"
    proof (rule ccontr)
      assume "T ≠ r"
      then obtain b where b: "b ∈ set (targs r)" "T ∈ fsub b" using assms(2) g by (auto elim: fsub_FunE)
      then obtain z where "b = Var z" using r targs_acapp by fastforce
      then show False using b(2) assms(3) by simp
    qed
    then show ?thesis using r by simp
  qed
qed

text ‹The flattened subterms after ‹solve_ac›, before instantiation (PVS ‹P⇩0⇧*›).›

definition SubS :: "('f, nat) eqs ⇒ ('f, nat) term set" where
  "SubS Q = Sub Q ∪ (⋃a ∈ eq_sides C. fsub a)"

definition traced :: "('f, nat) eqs ⇒ ('f, nat) term ⇒ bool" where
  "traced Q T ⟷ (∀Y. Var Y ∈ set (targs T) ⟶
    (∃t2 ∈ SubS Q. is_Fun t2 ∧ key t2 = key T ∧ (∃X. Var X ∈ set (targs t2) ∧ θ X = Var Y)))"

lemma rhs_side: "(w, r) ∈ set C ⟹ r ∈ eq_sides C"
  by (force simp: eq_sides_def)

lemma lhs_side: "(w, r) ∈ set C ⟹ w ∈ eq_sides C"
  by (force simp: eq_sides_def)

lemma C_SubS: "a ∈ eq_sides C ⟹ a ∈ SubS Q"
  unfolding SubS_def using fsub_self by blast

lemma U0_SubS: "u ∈ U0 ⟹ fsub u ⊆ SubS Q"
  by (auto simp: U0_def SubS_def eq_sides_def)

lemma trace_aux:
  "(∀v. is_Fun v ⟶ fsub v ⊆ SubS Q ⟶ size (v ⋅ θ) = n ⟶
      (∀T ∈ fsub (v ⋅ θ). is_Fun T ⟶ traced Q T)) ∧
   (∀y. size (θ y) = n ⟶ (∀T ∈ fsub (θ y). is_Fun T ⟶ traced Q T))"
proof (induction n rule: less_induct)
  case (less n)
  have IHy: "⋀y T. size (θ y) < n ⟹ T ∈ fsub (θ y) ⟹ is_Fun T ⟹ traced Q T"
    using less.IH by blast
  have IHv: "⋀v T. is_Fun v ⟹ fsub v ⊆ SubS Q ⟹ size (v ⋅ θ) < n ⟹ T ∈ fsub (v ⋅ θ) ⟹
      is_Fun T ⟹ traced Q T"
    using less.IH by blast
  have vpart: "traced Q T"
    if v: "is_Fun v" "fsub v ⊆ SubS Q" "size (v ⋅ θ) = n" and T: "T ∈ fsub (v ⋅ θ)" "is_Fun T" for v T
  proof -
    have lt: "size (θ x) < n" if "x ∈ vars_term v" for x
      using size_subst_occurs[OF that, of θ] v(1,3) by auto
    from fsub_subst[OF T(1)] show ?thesis
    proof
      assume "∃w ∈ fsub v. is_Fun w ∧ T = w ⋅ θ"
      then obtain w where w: "w ∈ fsub v" "is_Fun w" "T = w ⋅ θ" by blast
      show ?thesis unfolding traced_def
      proof (intro allI impI)
        fix Y
        assume "Var Y ∈ set (targs T)"
        then have "Var Y ∈ set (targs (w ⋅ θ))" using w(3) by simp
        from var_targs_subst[OF w(2) this] obtain X where X: "Var X ∈ set (targs w)" "θ X = Var Y ∨
            (∃g. is_ac_app g w ∧ is_ac_app g (θ X) ∧ Var Y ∈ set (args_ac g (θ X)))"
          by (elim exE conjE) (rule that)
        have wS: "w ∈ SubS Q" using w(1) v(2) by blast
        from X(2) show "∃t2 ∈ SubS Q. is_Fun t2 ∧ key t2 = key T ∧ (∃X. Var X ∈ set (targs t2) ∧ θ X = Var Y)"
        proof
          assume "θ X = Var Y"
          then show ?thesis using wS w X(1) by auto
        next
          assume "∃g. is_ac_app g w ∧ is_ac_app g (θ X) ∧ Var Y ∈ set (args_ac g (θ X))"
          then obtain g where g: "is_ac_app g w" "is_ac_app g (θ X)" "Var Y ∈ set (args_ac g (θ X))" by blast
          have Xv: "X ∈ vars_term v" using vars_fsub[OF w(1)] Var_targs_vars[OF X(1)] by blast
          have "traced Q (θ X)" by (rule IHy[OF lt[OF Xv] fsub_self]) (use g(2) in ‹auto simp: is_ac_app_def›)
          moreover have "Var Y ∈ set (targs (θ X))" using g(2,3) by (simp add: targs_acapp)
          ultimately obtain t2 X' where "t2 ∈ SubS Q" "is_Fun t2" "key t2 = key (θ X)"
            "Var X' ∈ set (targs t2)" "θ X' = Var Y" by (auto simp: traced_def)
          moreover have "key (θ X) = key T" using g(1,2) w(3) key_acapp[of g] by (auto simp: is_ac_app_def)
          ultimately show ?thesis by auto
        qed
      qed
    next
      assume "∃x ∈ vars_term v. T ∈ fsub (θ x) ∧
        (T = θ x ⟶ v = Var x ∨ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x))))"
      then obtain x where x: "x ∈ vars_term v" "T ∈ fsub (θ x)" by blast
      show ?thesis by (rule IHy[OF lt[OF x(1)] x(2) T(2)])
    qed
  qed
  have ypart: "traced Q T" if y: "size (θ y) = n" and T: "T ∈ fsub (θ y)" "is_Fun T" for y T
  proof -
    have fy: "is_Fun (θ y)" using T by (cases "θ y") auto
    from img_shape[OF fy] show ?thesis
    proof
      assume "∃u ∈ U0. θ y = u ⋅ θ"
      then obtain u where u: "u ∈ U0" "θ y = u ⋅ θ" by blast
      have "is_Fun u" using u(1) by (simp add: U0_def)
      then show ?thesis using vpart[OF _ U0_SubS[OF u(1)]] u(2) y T by auto
    next
      assume sh: "is_ac_app f (θ y) ∧ (∀b ∈ set (args_ac f (θ y)). (∃w. b = Var w ∧ θ w = Var w) ∨
          (∃u ∈ U0. b = u ⋅ θ))"
      then have sh1: "is_ac_app f (θ y)" and sh2: "⋀b. b ∈ set (args_ac f (θ y)) ⟹
          (∃w. b = Var w ∧ θ w = Var w) ∨ (∃u ∈ U0. b = u ⋅ θ)" by blast+
      show ?thesis
      proof (cases "T = θ y")
        case True
        show ?thesis unfolding traced_def
        proof (intro allI impI)
          fix Y
          assume "Var Y ∈ set (targs T)"
          then have "Var Y ∈ set (args_ac f (θ y))" using True targs_acapp[OF sh1] by simp
          then obtain w r z where wr: "(w, r) ∈ set C" "is_ac_app f r" "Var z ∈ set (args_ac f r)" "θ z = Var Y"
            using rhs_trace[OF sh1] by blast
          have "r ∈ SubS Q" using C_SubS[OF rhs_side[OF wr(1)]] .
          moreover have "key r = key T" using wr(2) sh1 True by (simp add: key_acapp)
          ultimately show "∃t2 ∈ SubS Q. is_Fun t2 ∧ key t2 = key T ∧ (∃X. Var X ∈ set (targs t2) ∧ θ X = Var Y)"
            using wr(2,3,4) by (intro bexI[of _ r]) (auto simp: targs_acapp is_ac_app_def)
        qed
      next
        case False
        obtain g ts where g: "θ y = Fun g ts" using fy by (cases "θ y") auto
        obtain b where b: "b ∈ set (targs (θ y))" "T ∈ fsub b"
          using T(1) False g by (auto elim: fsub_FunE)
        have "b ∈ set (args_ac f (θ y))" using b(1) targs_acapp[OF sh1] by simp
        from sh2[OF this] consider w where "b = Var w" | u where "u ∈ U0" "b = u ⋅ θ" by blast
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using b(2) T(2) by simp
        next
          case 2
          have lt: "size (u ⋅ θ) < n" using size_targs[OF b(1)] 2(2) y by simp
          have "is_Fun u" using 2(1) by (simp add: U0_def)
          then show ?thesis using IHv[OF _ U0_SubS[OF 2(1)] lt] b(2) 2(2) T(2) by simp
        qed
      qed
    qed
  qed
  show ?case using vpart ypart by blast
qed

lemma trace_v:
  "is_Fun v ⟹ fsub v ⊆ SubS Q ⟹ T ∈ fsub (v ⋅ θ) ⟹ is_Fun T ⟹ traced Q T"
  using trace_aux[of Q "size (v ⋅ θ)"] by blast

text ‹The renaming of variables done by the step (PVS ‹ψ›).›

definition psi :: "nat ⇒ nat" where
  "psi x = (case θ x of Var y ⇒ y | _ ⇒ x)"

lemma psi_Var: "θ x = Var y ⟹ psi x = y"
  by (simp add: psi_def)

lemma psi_Fun: "is_Fun (θ x) ⟹ psi x = x"
  by (cases "θ x") (auto simp: psi_def)

lemma Sub_Cons: "Sub ((a, b) # P) = fsub a ∪ fsub b ∪ Sub P"
  by (auto simp: Sub_def)

lemma lhs_fsub: "(w, r) ∈ set C ⟹ fsub w ⊆ fsub t ∪ fsub s"
  using lhs_targs fsub_trans[OF targs_fsub] by blast

lemma SubS_cases:
  assumes "T ∈ SubS Q"
  shows "T ∈ Sub ((t, s) # Q) ∨ (∃w r. (w, r) ∈ set C ∧ T ∈ fsub r)"
proof -
  have "T ∈ Sub Q ∨ (∃a ∈ eq_sides C. T ∈ fsub a)" using assms by (auto simp: SubS_def)
  then show ?thesis
  proof
    assume "∃a ∈ eq_sides C. T ∈ fsub a"
    then obtain a where a: "a ∈ eq_sides C" "T ∈ fsub a" by blast
    from sides_C[OF a(1)] show ?thesis
    proof
      assume "∃r. (a, r) ∈ set C"
      then show ?thesis using lhs_fsub a(2) by (auto simp: Sub_Cons)
    qed (use a(2) in blast)
  qed (simp add: Sub_Cons)
qed

lemma key_t: "key t = Some (f, True)"
  by (rule key_acapp[OF t])

lemma key_s: "key s = Some (f, True)"
  by (rule key_acapp[OF s])

lemma SubS_key:
  "T ∈ SubS Q ⟹ is_Fun T ⟹ key T ≠ Some (f, True) ⟹ T ∈ Sub ((t, s) # Q)"
  using SubS_cases fsub_rhs key_acapp by blast

lemma SubS_low:
  assumes "T ∈ SubS Q" "Var X ∈ set (targs T)" "X < nv"
  shows "T ∈ Sub ((t, s) # Q)"
proof -
  from SubS_cases[OF assms(1)] show ?thesis
  proof
    assume "∃w r. (w, r) ∈ set C ∧ T ∈ fsub r"
    then obtain w r where wr: "(w, r) ∈ set C" "T ∈ fsub r" by blast
    have Tf: "is_Fun T" using assms(2) by (cases T) auto
    have Tr: "T = r" using fsub_rhs[OF wr Tf] by auto
    have Xr: "X ∈ vars_term r" using Var_targs_vars[OF assms(2)] Tr by simp
    show ?thesis using rhs_vars[OF wr(1) Xr] assms(3) by simp
  qed
qed

context
  fixes Q :: "('f, nat) eqs"
  assumes QF: "∀a ∈ eq_sides Q. is_Fun a" and QV: "vars_eqs Q ⊆ {..<nv}"
begin

abbreviation "S0 ≡ (t, s) # Q"
abbreviation "S1 ≡ subst_eqs θ Q @ R"

lemma S0_vars: "vars_eqs S0 ⊆ {..<nv}"
  using V QV by auto

lemma S0_Sub_ts: "fsub t ⊆ Sub S0" "fsub s ⊆ Sub S0"
  by (auto simp: Sub_Cons)

lemma S1_sides: "a ∈ eq_sides S1 ⟹ (∃q ∈ eq_sides Q. a = q ⋅ θ) ∨ (∃u ∈ U0. a = u ⋅ θ)"
proof -
  assume "a ∈ eq_sides S1"
  then have "a ∈ (λq. q ⋅ θ) ` eq_sides Q ∨ a ∈ eq_sides R" by (simp add: eq_sides_subst)
  then show ?thesis
  proof
    assume "a ∈ eq_sides R"
    then obtain b where "(a, b) ∈ set R ∨ (b, a) ∈ set R" by (auto simp: eq_sides_def)
    then show ?thesis using res_shape by blast
  qed blast
qed

lemma S1_Fun:
  assumes "a ∈ eq_sides S1"
  shows "is_Fun a"
proof -
  from S1_sides[OF assms] obtain b where b: "b ∈ eq_sides Q ∨ b ∈ U0" "a = b ⋅ θ" by blast
  then have "is_Fun b" using QF by (auto simp: U0_def)
  then show ?thesis using b(2) by (cases b) auto
qed

lemma S1_trace: "T ∈ Sub S1 ⟹ is_Fun T ⟹ traced Q T"
proof -
  assume T: "T ∈ Sub S1" "is_Fun T"
  then obtain a where a: "a ∈ eq_sides S1" "T ∈ fsub a" by (auto simp: Sub_def)
  from S1_sides[OF a(1)] show ?thesis
  proof
    assume "∃q ∈ eq_sides Q. a = q ⋅ θ"
    then obtain q where q: "q ∈ eq_sides Q" "a = q ⋅ θ" by blast
    have "fsub q ⊆ SubS Q" using q(1) by (auto simp: SubS_def Sub_def)
    then show ?thesis using trace_v[of q] QF q a(2) T(2) by auto
  next
    assume "∃u ∈ U0. a = u ⋅ θ"
    then obtain u where u: "u ∈ U0" "a = u ⋅ θ" by blast
    then show ?thesis using trace_v[OF _ U0_SubS[OF u(1)]] a(2) T(2) by (auto simp: U0_def)
  qed
qed

lemma S1_fixed: "y ∈ vars_eqs S1 ⟹ θ y = Var y"
proof -
  assume "y ∈ vars_eqs S1"
  then obtain a where a: "a ∈ eq_sides S1" "y ∈ vars_term a"
    by (auto simp: vars_eqs_def eq_sides_def)
  from S1_sides[OF a(1)] obtain b where "a = b ⋅ θ" by blast
  then show ?thesis using idem a(2) by blast
qed

lemma S1_vars: "vars_eqs S1 ⊆ vars_eqs S0 ∪ {nv..<nv'}"
proof
  fix y
  assume y: "y ∈ vars_eqs S1"
  then obtain a where a: "a ∈ eq_sides S1" "y ∈ vars_term a"
    by (auto simp: vars_eqs_def eq_sides_def)
  from S1_sides[OF a(1)] obtain b where b: "b ∈ eq_sides Q ∨ b ∈ U0" "a = b ⋅ θ" by blast
  then obtain x where x: "x ∈ vars_term b" "y ∈ vars_term (θ x)" using a(2) by (auto simp: vars_term_subst)
  have xS0: "x ∈ vars_eqs S0"
    using b(1)
  proof
    assume "b ∈ eq_sides Q"
    then show ?thesis using vars_eq_sides[of b Q] x(1) by auto
  next
    assume "b ∈ U0"
    then have "b ∈ set (targs t) ∪ set (targs s)" by (rule U0_fsub)
    then have "x ∈ vars_term t ∪ vars_term s" using vars_targs x(1) by blast
    then show ?thesis by auto
  qed
  show "y ∈ vars_eqs S0 ∪ {nv..<nv'}"
  proof (cases "θ x = Var x")
    case True
    then show ?thesis using x(2) xS0 by simp
  next
    case False
    then have "vars_term (θ x) ⊆ vars_eqs C" using inst_vars[OF inst] dom_vars by blast
    then have "y ∈ vars_eqs C" using x(2) by blast
    then obtain w r where wr: "(w, r) ∈ set C" "y ∈ vars_term w ∨ y ∈ vars_term r"
      by (auto simp: vars_eqs_def)
    from wr(2) show ?thesis
    proof
      assume "y ∈ vars_term w"
      then have "y ∈ vars_term t ∪ vars_term s"
        using lhs_args[OF wr(1)] vars_args_ac[of t f] vars_args_ac[of s f] by blast
      then show ?thesis by auto
    qed (use rhs_vars[OF wr(1)] in auto)
  qed
qed

text ‹PVS Lemma 17, one step.›

lemma VNAC_step: "VNAC S1 ⊆ psi ` VNAC S0"
proof
  fix y
  assume "y ∈ VNAC S1"
  then consider "Var y ∈ eq_sides S1" | T where "T ∈ Sub S1" "is_Fun T" "¬ is_acapp T" "Var y ∈ set (targs T)"
    by (auto simp: VNAC_def)
  then show "y ∈ psi ` VNAC S0"
  proof cases
    case 1
    then show ?thesis using S1_Fun by fastforce
  next
    case 2
    obtain t2 X where t2: "t2 ∈ SubS Q" "is_Fun t2" "key t2 = key T" "Var X ∈ set (targs t2)" "θ X = Var y"
      using S1_trace[OF 2(1,2)] 2(4) by (auto simp: traced_def)
    have nac: "¬ is_acapp t2" using t2(2,3) 2(2,3) by (cases t2; cases T) (auto simp: is_acapp_Fun)
    have "key t2 ≠ Some (f, True)" using nac t2(2) by (cases t2) (auto simp: is_acapp_Fun)
    then have "t2 ∈ Sub S0" using SubS_key t2(1,2) by blast
    then have "X ∈ VNAC S0" using t2(2,4) nac by (auto simp: VNAC_def)
    then show ?thesis using psi_Var[OF t2(5)] by force
  qed
qed

text ‹Key facts for PVS Lemma 18.›

lemma V2_K:
  assumes "t2 ∈ SubS Q" "is_Fun t2" "key t2 ≠ Some (f, True)" "Var V ∈ set (targs t2)"
    "θ V = Var Y" "V ≠ Y"
  shows "Y ∈ psi ` V2 S0"
proof -
  have t2S: "t2 ∈ Sub S0" using SubS_key assms(1,2,3) by blast
  have "V ∈ vars_eqs S0" using vars_Sub[OF t2S] Var_targs_vars[OF assms(4)] by blast
  then have "V < nv" using S0_vars by blast
  moreover have "θ V ≠ Var V" using assms(5,6) by simp
  ultimately have "Var V ∈ set (targs t) ∪ set (targs s)" by (rule dom_orig[rotated])
  then obtain p where p: "p ∈ {t, s}" "Var V ∈ set (targs p)" by blast
  have pS: "p ∈ Sub S0" using p(1) S0_Sub_ts by auto
  have "key p = Some (f, True)" using p(1) key_t key_s by auto
  then have kk: "key t2 ≠ key p" using assms(3) by simp
  have pF: "is_Fun p" using p(1) t s by (auto simp: is_ac_app_def)
  have "V ∈ V2 S0" unfolding V2_def using t2S pS assms(2,4) pF p(2) kk by blast
  then show ?thesis using psi_Var[OF assms(5)] by force
qed

lemma V2_K':
  assumes "t2 ∈ SubS Q" "is_Fun t2" "key t2 ≠ Some (f, True)" "Var Y ∈ set (targs t2)"
    "θ Y = Var Y" "s2 ∈ SubS Q ∨ s2 ∈ Sub S0" "is_Fun s2" "key s2 ≠ key t2" "Var Y ∈ set (targs s2)"
  shows "Y ∈ psi ` V2 S0"
proof -
  have t2S: "t2 ∈ Sub S0" using SubS_key assms(1,2,3) by blast
  have "Y ∈ vars_eqs S0" using vars_Sub[OF t2S] Var_targs_vars[OF assms(4)] by blast
  then have "Y < nv" using S0_vars by blast
  then have s2S: "s2 ∈ Sub S0" using SubS_low[OF _ assms(9)] assms(6) by blast
  have "Y ∈ V2 S0" using t2S s2S assms(2,4,7,8,9) by (auto simp: V2_def)
  then show ?thesis using psi_Var[OF assms(5)] by force
qed

text ‹PVS Lemma 18, one step.›

lemma V2_step: "V2 S1 ⊆ psi ` V2 S0"
proof
  fix Y
  assume "Y ∈ V2 S1"
  then obtain T1 T2 where T: "T1 ∈ Sub S1" "T2 ∈ Sub S1" "is_Fun T1" "is_Fun T2" "key T1 ≠ key T2"
    "Var Y ∈ set (targs T1)" "Var Y ∈ set (targs T2)"
    by (auto simp: V2_def)
  obtain t2 X where t2: "t2 ∈ SubS Q" "is_Fun t2" "key t2 = key T1" "Var X ∈ set (targs t2)" "θ X = Var Y"
    using S1_trace[OF T(1,3)] T(6) by (auto simp: traced_def)
  obtain s2 W where s2: "s2 ∈ SubS Q" "is_Fun s2" "key s2 = key T2" "Var W ∈ set (targs s2)" "θ W = Var Y"
    using S1_trace[OF T(2,4)] T(7) by (auto simp: traced_def)
  have k: "key t2 ≠ key s2" using t2(3) s2(3) T(5) by simp
  have YY: "θ Y = Var Y"
  proof -
    have "Y ∈ vars_eqs S1" using vars_Sub[OF T(1)] Var_targs_vars[OF T(6)] by blast
    then show ?thesis by (rule S1_fixed)
  qed
  let ?fk = "Some (f, True)"
  have sym: "Y ∈ psi ` V2 S0"
    if a: "a2 ∈ SubS Q" "is_Fun a2" "Var A ∈ set (targs a2)" "θ A = Var Y"
      and b: "b2 ∈ SubS Q" "is_Fun b2" "Var B ∈ set (targs b2)" "θ B = Var Y"
      and kb: "key b2 ≠ ?fk" and kab: "key a2 ≠ key b2"
    for a2 A b2 B
  proof (cases "B = Y")
    case False
    then show ?thesis using V2_K[OF b(1,2) kb b(3,4)] by simp
  next
    case BY: True
    show ?thesis
    proof (cases "A = Y")
      case True
      then show ?thesis using V2_K'[OF b(1,2) kb _ YY[folded BY] disjI1[OF a(1)] a(2)] b(3) BY a(3) kab
        by auto
    next
      case False
      then have "Var Y ∈ set (targs t) ∪ set (targs s)" using img_var_arg a(4) by blast
      then obtain p where p: "p ∈ {t, s}" "Var Y ∈ set (targs p)" by blast
      have pS: "p ∈ Sub S0" using p(1) S0_Sub_ts fsub_self by blast
      have kp: "key p = ?fk" using p(1) key_t key_s by auto
      have pF: "is_Fun p" using p(1) t s by (auto simp: is_ac_app_def)
      have kpb: "key p ≠ key b2" using kp kb by simp
      have "Var Y ∈ set (targs b2)" using b(3) BY by simp
      then show ?thesis using V2_K'[OF b(1,2) kb _ YY disjI2[OF pS] pF kpb p(2)] by simp
    qed
  qed
  show "Y ∈ psi ` V2 S0"
  proof (cases "key s2 = ?fk")
    case False
    then show ?thesis using sym[OF t2(1,2,4,5) s2(1,2,4,5)] k by simp
  next
    case True
    then have "key t2 ≠ ?fk" using k by simp
    then show ?thesis using sym[OF s2(1,2,4,5) t2(1,2,4,5)] k by simp
  qed
qed

lemma U0_AS: "U0 ⊆ AS S0"
proof
  fix u
  assume u: "u ∈ U0"
  then obtain p where p: "p ∈ {t, s}" "u ∈ set (targs p)" using U0_fsub by blast
  have "u ∈ fsub p" by (rule targs_fsub[OF p(2)])
  moreover have "u ≠ p" using size_targs[OF p(2)] by auto
  moreover have "p ∈ eq_sides S0" using p(1) by auto
  ultimately show "u ∈ AS S0" using u by (auto simp: AS_def U0_def)
qed

lemma AS_S0_Sub: "u ∈ AS S0 ⟹ fsub u ⊆ Sub S0"
proof -
  assume "u ∈ AS S0"
  then obtain a where a: "a ∈ eq_sides S0" "u ∈ fsub a" by (auto simp: AS_def)
  then show ?thesis using fsub_trans[OF a(2)] by (auto simp: Sub_def)
qed

lemma AS_core:
  assumes NoV: "∀X ∈ V2 S0. is_Var (θ X)"
  shows "is_Fun v ⟹ v ∈ eq_sides S0 ∨ v ∈ AS S0 ⟹ T ∈ fsub (v ⋅ θ) ⟹ T ≠ v ⋅ θ ⟹
    is_Fun T ⟹ T ∈ (λu. u ⋅ θ) ` AS S0"
proof (induction "size (v ⋅ θ)" arbitrary: v T rule: less_induct)
  case less
  have properAS: "w ∈ AS S0" if "w ∈ fsub v" "w ≠ v" "is_Fun w" for w
    using less.prems(2)
  proof
    assume "v ∈ eq_sides S0"
    then show ?thesis using that by (auto simp: AS_def)
  next
    assume "v ∈ AS S0"
    then show ?thesis using AS_fsub that(1,3) by blast
  qed
  have vS: "fsub v ⊆ Sub S0"
    using less.prems(2) AS_S0_Sub by (auto simp: Sub_def)
  have vvars: "vars_term v ⊆ {..<nv}"
    using vars_Sub[of v S0] vS fsub_self S0_vars by blast
  have lt: "size (θ x) < size (v ⋅ θ)" if "x ∈ vars_term v" for x
    using size_subst_occurs[OF that, of θ] less.prems(1) by auto
  from fsub_subst[OF less.prems(3)] show ?case
  proof
    assume "∃w ∈ fsub v. is_Fun w ∧ T = w ⋅ θ"
    then obtain w where w: "w ∈ fsub v" "is_Fun w" "T = w ⋅ θ" by blast
    then have "w ≠ v" using less.prems(4) by blast
    then show ?thesis using properAS[OF w(1) _ w(2)] w(3) by blast
  next
    assume "∃x ∈ vars_term v. T ∈ fsub (θ x) ∧
        (T = θ x ⟶ v = Var x ∨ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x))))"
    then obtain x where x: "x ∈ vars_term v" "T ∈ fsub (θ x)"
      "T = θ x ⟶ v = Var x ∨ (∃w ∈ fsub v. is_Fun w ∧ Var x ∈ set (targs w) ∧
           ¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x)))" by blast
    have fx: "is_Fun (θ x)" using x(2) less.prems(5) by (cases "θ x") auto
    from img_shape[OF fx] show ?thesis
    proof
      assume "∃u ∈ U0. θ x = u ⋅ θ"
      then obtain u where u: "u ∈ U0" "θ x = u ⋅ θ" by blast
      have uAS: "u ∈ AS S0" using u(1) U0_AS by blast
      show ?thesis
      proof (cases "T = u ⋅ θ")
        case True
        then show ?thesis using uAS by blast
      next
        case False
        have uF: "is_Fun u" using u(1) by (simp add: U0_def)
        show ?thesis
          by (rule less.hyps[OF _ uF _ _ False less.prems(5)]) (use lt[OF x(1)] u(2) uAS x(2) in auto)
      qed
    next
      assume sh: "is_ac_app f (θ x) ∧ (∀b ∈ set (args_ac f (θ x)). (∃w. b = Var w ∧ θ w = Var w) ∨
          (∃u ∈ U0. b = u ⋅ θ))"
      then have sh1: "is_ac_app f (θ x)" and sh2: "⋀b. b ∈ set (args_ac f (θ x)) ⟹
          (∃w. b = Var w ∧ θ w = Var w) ∨ (∃u ∈ U0. b = u ⋅ θ)" by blast+
      show ?thesis
      proof (cases "T = θ x")
        case True
        have "v ≠ Var x" using less.prems(1) by auto
        then obtain w where w: "w ∈ fsub v" "is_Fun w" "Var x ∈ set (targs w)"
          "¬ (∃g. is_ac_app g w ∧ is_ac_app g (θ x))" using x(3) True by blast
        have "¬ is_ac_app f w" using w(4) sh1 by blast
        then have kw: "key w ≠ Some (f, True)" using w(2) f
          by (cases w) (auto simp: numeral_2_eq_2 length_Suc_conv)
        have xnv: "x < nv" using x(1) vvars by blast
        have "θ x ≠ Var x" using fx by auto
        then have "Var x ∈ set (targs t) ∪ set (targs s)" by (rule dom_orig[OF _ xnv])
        then obtain p where p: "p ∈ {t, s}" "Var x ∈ set (targs p)" by blast
        have pS: "p ∈ Sub S0" using p(1) S0_Sub_ts fsub_self by blast
        have pF: "is_Fun p" using p(1) t s by (auto simp: is_ac_app_def)
        have "key p = Some (f, True)" using p(1) key_t key_s by auto
        then have "key w ≠ key p" using kw by simp
        then have "x ∈ V2 S0" unfolding V2_def using w(1,2,3) vS pS pF p(2) by blast
        then have "is_Var (θ x)" using NoV by blast
        then show ?thesis using fx by simp
      next
        case False
        obtain g ts where g: "θ x = Fun g ts" using fx by (cases "θ x") auto
        obtain b where b: "b ∈ set (targs (θ x))" "T ∈ fsub b"
          using x(2) False g by (auto elim: fsub_FunE)
        have "b ∈ set (args_ac f (θ x))" using b(1) targs_acapp[OF sh1] by simp
        from sh2[OF this] consider w where "b = Var w" | u where "u ∈ U0" "b = u ⋅ θ" by blast
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using b(2) less.prems(5) by simp
        next
          case 2
          have uAS: "u ∈ AS S0" using 2(1) U0_AS by blast
          show ?thesis
          proof (cases "T = u ⋅ θ")
            case True
            then show ?thesis using uAS by blast
          next
            case False
            have uF: "is_Fun u" using 2(1) by (simp add: U0_def)
            have "size (u ⋅ θ) < size (v ⋅ θ)"
              using size_targs[OF b(1)] 2(2) lt[OF x(1)] by simp
            then show ?thesis
              by (rule less.hyps[OF _ uF _ _ False less.prems(5)]) (use uAS b(2) 2(2) in auto)
          qed
        qed
      qed
    qed
  qed
qed

text ‹PVS Lemmas 22 and 23, one step.›

lemma AS_step:
  assumes NoV: "∀X ∈ V2 S0. is_Var (θ X)"
  shows "AS S1 ⊆ (λu. u ⋅ θ) ` AS S0" "eq_sides R ⊆ (λu. u ⋅ θ) ` AS S0"
proof
  fix T
  assume "T ∈ AS S1"
  then obtain a where a: "a ∈ eq_sides S1" "T ∈ fsub a" "T ≠ a" "is_Fun T" by (auto simp: AS_def)
  from S1_sides[OF a(1)] obtain b where b: "b ∈ eq_sides Q ∨ b ∈ U0" "a = b ⋅ θ" by blast
  have bF: "is_Fun b" using b(1) QF by (auto simp: U0_def)
  have "b ∈ eq_sides S0 ∨ b ∈ AS S0" using b(1) U0_AS by auto
  then show "T ∈ (λu. u ⋅ θ) ` AS S0" using AS_core[OF NoV bF] a(2,3,4) b(2) by blast
next
  show "eq_sides R ⊆ (λu. u ⋅ θ) ` AS S0"
  proof
    fix a
    assume "a ∈ eq_sides R"
    then obtain b where "(a, b) ∈ set R ∨ (b, a) ∈ set R" by (auto simp: eq_sides_def)
    then have "a ∈ (λu. u ⋅ θ) ` U0" using res_shape by blast
    then show "a ∈ (λu. u ⋅ θ) ` AS S0" using U0_AS by blast
  qed
qed

end

lemma fixed_low: "x < nv ⟹ x ∉ vars_term t ∪ vars_term s ⟹ θ x = Var x"
proof (rule ccontr)
  assume x: "x < nv" "x ∉ vars_term t ∪ vars_term s" "θ x ≠ Var x"
  then obtain w r where wr: "(w, r) ∈ set C" "x ∈ vars_term w ∨ x ∈ vars_term r"
    using dom_vars[OF x(3)] by (auto simp: vars_eqs_def)
  show False
  proof (cases "x ∈ vars_term w")
    case True
    then show False using lhs_targs[OF wr(1)] vars_targs x(2) by blast
  next
    case False
    then show False using rhs_vars[OF wr(1), of x] wr(2) x(1) by auto
  qed
qed

end

subsection ‹One AC round›

context ac_unif
begin

lemma ac_pair_D: "ac_pair ac (t, s) ⟹ ∃f a b c d. t = Fun f [a, b] ∧ s = Fun f [c, d] ∧ ac f"
  by (cases "(ac, (t, s))" rule: ac_pair.cases) auto

lemma ac_pair_subst: "ac_pair ac e ⟹ ac_pair ac ((λ(a, b). (a ⋅ θ, b ⋅ θ)) e)"
  by (cases e) (auto dest!: ac_pair_D)

definition rinv :: "('f, nat) eqs ⇒ ('f, nat) eqs ⇒ nat ⇒ bool" where
  "rinv P R nv ⟷ (∀e ∈ set P. ac_pair ac e) ∧ (∀a ∈ eq_sides (P @ R). is_Fun a) ∧
     vars_eqs (P @ R) ⊆ {..<nv}"

lemma ac_round_meas:
  assumes "(Pn, σn, nvn) ∈ set (ac_round P R σ nv)" "rinv P R nv"
  shows "∃F. VNAC Pn ⊆ F ` VNAC (P @ R) ∧ V2 Pn ⊆ F ` V2 (P @ R) ∧
    (∀X < nv. X ∉ vars_eqs (P @ R) ⟶ F X = X) ∧
    (∀y ∈ vars_eqs Pn. y ∈ vars_eqs (P @ R) ∨ nv ≤ y) ∧ vars_eqs Pn ⊆ {..<nvn} ∧
    (V2 Pn = F ` V2 (P @ R) ⟶ (∃ρ. AS Pn ⊆ (λu. u ⋅ ρ) ` AS (P @ R) ∧
       eq_sides Pn ⊆ (λu. u ⋅ ρ) ` (AS (P @ R) ∪ eq_sides R)))"
  using assms
proof (induction P R σ nv rule: ac_round.induct)
  case (1 R σ nv)
  then have "Pn = R" "nvn = nv" by auto
  then show ?case using 1(2)
    by (intro exI[of _ id] conjI impI exI[of _ Var]) (auto simp: rinv_def)
next
  case (2 t s P R σ nv)
  note IH = 2(2)
  have inv: "rinv ((t, s) # P) R nv" by fact
  then obtain f a b c d where tsf: "t = Fun f [a, b]" "s = Fun f [c, d]" "ac f"
  proof -
    have "ac_pair ac (t, s)" using inv by (simp add: rinv_def)
    then show ?thesis using ac_pair_D that by blast
  qed
  obtain C nv' R' θ where Cm: "(C, nv') ∈ set (solve_ac f t s nv)" "inst C = Some (R', θ)"
      "(Pn, σn, nvn) ∈ set (ac_round (subst_eqs θ P) (subst_eqs θ R @ R') (σ ∘⇩s θ) nv')"
  proof -
    let ?g = "\<lambda>(C, nv'). case inst C of None \<Rightarrow> []
           | Some (R', \<theta>) \<Rightarrow> ac_round (subst_eqs \<theta> P) (subst_eqs \<theta> R @ R') (\<sigma> \<circ>\<^sub>s \<theta>) nv'"
    have "(Pn, \<sigma>n, nvn) \<in> set (concat (map ?g (solve_ac f t s nv)))" using 2(3) tsf(1) by simp
    then obtain x where x: "x \<in> set (solve_ac f t s nv)" "(Pn, \<sigma>n, nvn) \<in> set (?g x)"
      unfolding set_concat set_map by blast
    obtain C nv' where Cx: "x = (C, nv')" by fastforce
    show ?thesis
    proof (cases "inst C")
      case None
      then show ?thesis using x(2) Cx by simp
    next
      case (Some p)
      obtain R' \<theta> where "p = (R', \<theta>)" by fastforce
      then show ?thesis using that[of C nv'] x Cx Some by simp
    qed
  qed
  have QF: "∀a ∈ eq_sides (P @ R). is_Fun a" and QV: "vars_eqs (P @ R) ⊆ {..<nv}"
    using inv by (auto simp: rinv_def)
  have V: "vars_term t ∪ vars_term s ⊆ {..<nv}" using inv by (auto simp: rinv_def)
  interpret st: ac_step ac dsolve f t s nv nv' C R' θ
    by (intro ac_step.intro ac_unif_axioms ac_step_axioms.intro tsf(3) V solve_ac_shape[OF tsf(3) Cm(1)]
        Cm(2)) (simp_all add: tsf)
  have e0: "(t, s) # (P @ R) = ((t, s) # P) @ R" by simp
  have e1: "subst_eqs θ (P @ R) @ R' = subst_eqs θ P @ (subst_eqs θ R @ R')" by simp
  note VN = st.VNAC_step[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  note VT = st.V2_step[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  note S1F = st.S1_Fun[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  note S1V = st.S1_vars[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  note S1X = st.S1_fixed[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  note S0V = st.S0_vars[where Q = "P @ R", OF QF QV, unfolded e0]
  note ASs = st.AS_step[where Q = "P @ R", OF QF QV, unfolded e0 e1]
  have nvle: "nv ≤ nv'" by (rule st.nv_le)
  have inv1: "rinv (subst_eqs θ P) (subst_eqs θ R @ R') nv'"
    unfolding rinv_def
  proof (intro conjI ballI)
    fix e
    assume "e ∈ set (subst_eqs θ P)"
    then obtain a0 b0 where ab: "(a0, b0) \<in> set P" "e = (a0 \<cdot> \<theta>, b0 \<cdot> \<theta>)"
      by (auto simp: subst_eqs_def)
    have "ac_pair ac (a0, b0)" using inv ab(1) by (auto simp: rinv_def)
    from ac_pair_subst[OF this, of \<theta>] show "ac_pair ac e" using ab(2) by simp
  next
    fix a
    assume "a ∈ eq_sides (subst_eqs θ P @ subst_eqs θ R @ R')"
    then show "is_Fun a" using S1F by blast
  next
    show "vars_eqs (subst_eqs θ P @ subst_eqs θ R @ R') ⊆ {..<nv'}"
      by (rule order.trans[OF S1V]) (use S0V nvle in auto)
  qed
  obtain F' where F': "VNAC Pn ⊆ F' ` VNAC (subst_eqs θ P @ subst_eqs θ R @ R')"
      "V2 Pn ⊆ F' ` V2 (subst_eqs θ P @ subst_eqs θ R @ R')"
      "∀X < nv'. X ∉ vars_eqs (subst_eqs θ P @ subst_eqs θ R @ R') ⟶ F' X = X"
      "∀y ∈ vars_eqs Pn. y ∈ vars_eqs (subst_eqs θ P @ subst_eqs θ R @ R') ∨ nv' ≤ y"
      "vars_eqs Pn ⊆ {..<nvn}"
      "V2 Pn = F' ` V2 (subst_eqs θ P @ subst_eqs θ R @ R') ⟶ (∃ρ.
         AS Pn ⊆ (λu. u ⋅ ρ) ` AS (subst_eqs θ P @ subst_eqs θ R @ R') ∧
         eq_sides Pn ⊆ (λu. u ⋅ ρ) ` (AS (subst_eqs θ P @ subst_eqs θ R @ R') ∪
           eq_sides (subst_eqs θ R @ R')))"
    using IH[OF tsf(1) Cm(1) HOL.refl Cm(2) HOL.refl Cm(3) inv1] by blast
  let ?F = "F' ∘ st.psi"
  let ?S0 = "((t, s) # P) @ R"
  let ?S1 = "subst_eqs θ P @ subst_eqs θ R @ R'"
  have a: "VNAC Pn ⊆ ?F ` VNAC ?S0"
    using order.trans[OF F'(1) image_mono[OF VN, of F']] unfolding image_comp .
  have b: "V2 Pn ⊆ ?F ` V2 ?S0"
    using order.trans[OF F'(2) image_mono[OF VT, of F']] unfolding image_comp .
  have d: "∀X < nv. X ∉ vars_eqs ?S0 ⟶ ?F X = X"
  proof (intro allI impI)
    fix X
    assume X: "X < nv" "X ∉ vars_eqs ?S0"
    then have "θ X = Var X" using st.fixed_low[OF X(1)] by simp
    then have "st.psi X = X" by (rule st.psi_Var)
    moreover have "X ∉ vars_eqs ?S1"
    proof
      assume "X ∈ vars_eqs ?S1"
      then have "X ∈ vars_eqs ?S0 ∪ {nv..<nv'}" using S1V by blast
      then show False using X by auto
    qed
    ultimately show "?F X = X" using F'(3) X(1) nvle by simp
  qed
  have e: "∀y ∈ vars_eqs Pn. y ∈ vars_eqs ?S0 ∨ nv ≤ y"
  proof
    fix y
    assume yP: "y ∈ vars_eqs Pn"
    have "y ∈ vars_eqs ?S1 ∨ nv' ≤ y" by (rule bspec[OF F'(4) yP])
    then show "y ∈ vars_eqs ?S0 ∨ nv ≤ y" using S1V nvle by auto
  qed
  have c: "∃ρ. AS Pn ⊆ (λu. u ⋅ ρ) ` AS ?S0 ∧ eq_sides Pn ⊆ (λu. u ⋅ ρ) ` (AS ?S0 ∪ eq_sides R)"
    if eq: "V2 Pn = ?F ` V2 ?S0"
  proof -
    have NoV: "∀X ∈ V2 ?S0. is_Var (θ X)"
    proof (rule ccontr)
      assume "¬ (∀X ∈ V2 ?S0. is_Var (θ X))"
      then obtain X where X: "X ∈ V2 ?S0" "is_Fun (θ X)" by auto
      have psX: "st.psi X = X" by (rule st.psi_Fun[OF X(2)])
      have Xnv: "X < nv" using subsetD[OF S0V subsetD[OF V2_vars X(1)]] by simp
      have nS1: "X ∉ vars_eqs ?S1"
      proof
        assume "X ∈ vars_eqs ?S1"
        from S1X[OF this] X(2) show False by simp
      qed
      have FX: "F' X = X" using F'(3) Xnv nvle nS1 by simp
      have "?F X ∈ V2 Pn" unfolding eq using X(1) by (rule imageI)
      then have "X ∈ V2 Pn" using FX psX by simp
      then have XP: "X ∈ vars_eqs Pn" by (rule subsetD[OF V2_vars])
      have "X ∈ vars_eqs ?S1 ∨ nv' ≤ X" by (rule bspec[OF F'(4) XP])
      then show False using nS1 Xnv nvle by auto
    qed
    have "V2 Pn = F' ` V2 ?S1"
    proof
      show "F' ` V2 ?S1 ⊆ V2 Pn" using image_mono[OF VT, of F'] unfolding eq image_comp .
    qed (rule F'(2))
    then obtain ρ' where ρ': "AS Pn ⊆ (λu. u ⋅ ρ') ` AS ?S1"
        "eq_sides Pn ⊆ (λu. u ⋅ ρ') ` (AS ?S1 ∪ eq_sides (subst_eqs θ R @ R'))"
      using F'(6) by blast
    have AS1: "AS ?S1 ⊆ (λu. u ⋅ θ) ` AS ?S0" and R1: "eq_sides R' ⊆ (λu. u ⋅ θ) ` AS ?S0"
      by (rule ASs(1)[OF NoV], rule ASs(2)[OF NoV])
    have comp: "(λu. u ⋅ ρ') ` (λu. u ⋅ θ) ` A = (λu. u ⋅ (θ ∘⇩s ρ')) ` A" for A :: "('f, nat) term set"
      by (simp add: image_image)
    have A1: "AS Pn ⊆ (λu. u ⋅ (θ ∘⇩s ρ')) ` AS ?S0"
      using order.trans[OF ρ'(1) image_mono[OF AS1, of "λu. u ⋅ ρ'"]] unfolding comp .
    have AR: "AS ?S1 ∪ eq_sides (subst_eqs θ R @ R') ⊆ (λu. u ⋅ θ) ` (AS ?S0 ∪ eq_sides R)"
      using AS1 R1 by (auto simp: eq_sides_subst)
    have A2: "eq_sides Pn ⊆ (λu. u ⋅ (θ ∘⇩s ρ')) ` (AS ?S0 ∪ eq_sides R)"
      using order.trans[OF ρ'(2) image_mono[OF AR, of "λu. u ⋅ ρ'"]] unfolding comp .
    show ?thesis by (rule exI[of _ "θ ∘⇩s ρ'"]) (use A1 A2 in blast)
  qed
  show ?case
    by (rule exI[of _ ?F]) (use a b c d e F'(5) in auto)
qed

subsection \<open>The syntactic steps\<close>

definition mless :: "('f, nat) eqs \<Rightarrow> ('f, nat) eqs \<Rightarrow> bool" where
  "mless P' P \<longleftrightarrow> (tmeasure P', tmeasure P) \<in> less_than <*lex*> less_than <*lex*> less_than <*lex*> less_than"

lemma wf_mless: "wf {(P', P). mless P' P}"
proof -
  have "wf (inv_image (less_than <*lex*> less_than <*lex*> less_than <*lex*> less_than) tmeasure)"
    by (intro wf_inv_image wf_lex_prod wf_less_than)
  moreover have "{(P', P). mless P' P} = inv_image (less_than <*lex*> less_than <*lex*> less_than <*lex*> less_than) tmeasure"
    by (auto simp: mless_def inv_image_def)
  ultimately show ?thesis by simp
qed

lemma mless_VNAC: "card (VNAC P') < card (VNAC P) \<Longrightarrow> mless P' P"
  by (simp add: mless_def tmeasure_def)

lemma mless_le:
  assumes "VNAC P' \<subseteq> VNAC P" "V2 P' \<subseteq> V2 P" "AS P' \<subseteq> AS P" "psize P' < psize P"
  shows "mless P' P"
proof -
  have "card (VNAC P') \<le> card (VNAC P)" "card (V2 P') \<le> card (V2 P)" "card (AS P') \<le> card (AS P)"
    using assms(1-3) by (simp_all add: card_mono)
  then show ?thesis using assms(4) by (auto simp: mless_def tmeasure_def)
qed

lemma psize_append [simp]: "psize (P @ Q) = psize P + psize Q"
  by (simp add: psize_def)

lemma psize_remove1: "(a, b) \<in> set P \<Longrightarrow> psize P = size a + size b + psize (remove1 (a, b) P)"
proof (induction P)
  case (Cons e P)
  then show ?case by (cases "e = (a, b)") (auto simp: psize_def)
qed simp

lemma eq_sides_remove1: "eq_sides (remove1 e P) \<subseteq> eq_sides P"
  using set_remove1_subset[of e P] by (auto simp: eq_sides_def)

lemma vars_remove1: "vars_eqs (remove1 e P) \<subseteq> vars_eqs P"
  using set_remove1_subset[of e P] by (auto simp: vars_eqs_def)

lemma vars_in: "(a, b) \<in> set P \<Longrightarrow> vars_term a \<union> vars_term b \<subseteq> vars_eqs P"
  unfolding vars_eqs_def by blast

lemma side_in: "(a, b) \<in> set P \<Longrightarrow> a \<in> eq_sides P \<and> b \<in> eq_sides P"
  by (auto simp: eq_sides_def)

lemma VNAC_mono: "eq_sides P' \<subseteq> eq_sides P \<Longrightarrow> VNAC P' \<subseteq> VNAC P"
  using Sub_mono[of P' P] unfolding VNAC_def by blast

lemma V2_mono: "eq_sides P' \<subseteq> eq_sides P \<Longrightarrow> V2 P' \<subseteq> V2 P"
  using Sub_mono[of P' P] unfolding V2_def by blast

lemma AS_mono: "eq_sides P' \<subseteq> eq_sides P \<Longrightarrow> AS P' \<subseteq> AS P"
  unfolding AS_def by blast

text \<open>Deleting a trivial equation.\<close>

lemma mless_delete: "(a, b) \<in> set P \<Longrightarrow> mless (remove1 (a, b) P) P"
proof (rule mless_le)
  assume ab: "(a, b) \<in> set P"
  show "psize (remove1 (a, b) P) < psize P" using psize_remove1[OF ab] by (cases a; cases b) auto
qed (intro VNAC_mono V2_mono AS_mono eq_sides_remove1)+

text \<open>Decomposition.\<close>

lemma psize_zip: "length ts = length ss \<Longrightarrow> psize (zip ts ss) < size (Fun f ts) + size (Fun g ss)"
  by (induction ts ss rule: list_induct2) (auto simp: psize_def)

lemma mless_decomp:
  assumes in_P: "(Fun f ts, Fun f ss) \<in> set P" and len: "length ts = length ss"
    and nac: "\<not> ac_pair ac (Fun f ts, Fun f ss)"
  shows "mless (zip ts ss @ remove1 (Fun f ts, Fun f ss) P) P"
    and "vars_eqs (zip ts ss @ remove1 (Fun f ts, Fun f ss) P) \<subseteq> vars_eqs P"
proof -
  let ?t = "Fun f ts" and ?s = "Fun f ss"
  let ?P' = "zip ts ss @ remove1 (?t, ?s) P"
  have na: "\<not> (ac f \<and> length ts = 2)"
  proof
    assume "ac f \<and> length ts = 2"
    then obtain a b c d where "ts = [a, b]" "ss = [c, d]" "ac f" using len
      by (auto simp: numeral_2_eq_2 length_Suc_conv)
    then show False using nac by simp
  qed
  have tt: "targs ?t = ts" "targs ?s = ss" using na len by (auto simp: targs.simps(2))
  have nt: "\<not> is_acapp ?t" "\<not> is_acapp ?s" using na len by (auto simp: is_acapp_Fun)
  have sides: "eq_sides ?P' \<subseteq> set ts \<union> set ss \<union> eq_sides P"
    using eq_sides_remove1[of "(?t, ?s)" P] by (auto simp: eq_sides_def dest: set_zip_leftD set_zip_rightD)
  have tsP: "?t \<in> eq_sides P" "?s \<in> eq_sides P" using side_in[OF in_P] by auto
  have argsub: "fsub a \<subseteq> Sub P" if aT: "a \<in> set ts \<union> set ss" for a
  proof -
    obtain p where p: "p \<in> {?t, ?s}" "a \<in> set (targs p)"
    proof (cases "a \<in> set ts")
      case True
      then show ?thesis using that[of ?t] tt by simp
    next
      case False
      then show ?thesis using that[of ?s] tt aT by simp
    qed
    have afp: "a \<in> fsub p" by (rule targs_fsub[OF p(2)])
    have "fsub a \<subseteq> fsub p" by (rule subsetI) (rule fsub_trans[OF afp])
    moreover have "fsub p \<subseteq> Sub P" using p(1) tsP by (auto simp: Sub_def)
    ultimately show ?thesis by blast
  qed
  have SubP: "Sub ?P' \<subseteq> Sub P"
  proof
    fix u
    assume "u \<in> Sub ?P'"
    then obtain a where a: "a \<in> eq_sides ?P'" "u \<in> fsub a" by (auto simp: Sub_def)
    show "u \<in> Sub P"
    proof (cases "a \<in> eq_sides P")
      case True
      then show ?thesis using a(2) by (auto simp: Sub_def)
    next
      case False
      then show ?thesis using a sides argsub by blast
    qed
  qed
  have "VNAC ?P' \<subseteq> VNAC P"
  proof
    fix x
    assume "x \<in> VNAC ?P'"
    then consider "Var x \<in> eq_sides ?P'"
      | T where "T \<in> Sub ?P'" "is_Fun T" "\<not> is_acapp T" "Var x \<in> set (targs T)"
      unfolding VNAC_def by blast
    then show "x \<in> VNAC P"
    proof cases
      case 1
      then have "Var x \<in> eq_sides P \<or> Var x \<in> set ts \<or> Var x \<in> set ss" using sides by blast
      then show ?thesis
      proof (elim disjE)
        assume "Var x \<in> set ts"
        then show ?thesis using tsP(1) nt(1) tt(1) unfolding VNAC_def Sub_def by force
      next
        assume "Var x \<in> set ss"
        then show ?thesis using tsP(2) nt(2) tt(2) unfolding VNAC_def Sub_def by force
      qed (simp add: VNAC_def)
    next
      case 2
      then show ?thesis using SubP unfolding VNAC_def by blast
    qed
  qed
  moreover have "V2 ?P' \<subseteq> V2 P" using SubP unfolding V2_def by blast
  moreover have "AS ?P' \<subseteq> AS P"
  proof
    fix u
    assume "u \<in> AS ?P'"
    then obtain a where a: "a \<in> eq_sides ?P'" "u \<in> fsub a" "u \<noteq> a" "is_Fun u" by (auto simp: AS_def)
    show "u \<in> AS P"
    proof (cases "a \<in> eq_sides P")
      case True
      then show ?thesis using a by (auto simp: AS_def)
    next
      case False
      then have aT: "a \<in> set ts \<union> set ss" using a(1) sides by blast
      have "\<exists>p \<in> {?t, ?s}. a \<in> set (targs p)" using aT tt by auto
      then obtain p where p: "p \<in> {?t, ?s}" "a \<in> set (targs p)" by blast
      have "u \<in> fsub p" using fsub_trans[OF targs_fsub[OF p(2)] a(2)] .
      moreover have "u \<noteq> p" using fsub_size[OF a(2)] size_targs[OF p(2)] by auto
      ultimately show ?thesis using p(1) tsP a(4) by (auto simp: AS_def)
    qed
  qed
  moreover have "psize ?P' < psize P"
    using psize_zip[OF len, of f f] psize_remove1[OF in_P] by simp
  ultimately show "mless ?P' P" by (rule mless_le)
  show "vars_eqs ?P' \<subseteq> vars_eqs P"
  proof -
    have "vars_eqs (zip ts ss) \<subseteq> vars_term ?t \<union> vars_term ?s"
    proof
      fix x
      assume "x \<in> vars_eqs (zip ts ss)"
      then obtain a b where ab: "(a, b) \<in> set (zip ts ss)" "x \<in> vars_term a \<or> x \<in> vars_term b"
        by (auto simp: vars_eqs_def)
      then show "x \<in> vars_term ?t \<union> vars_term ?s"
        using set_zip_leftD[OF ab(1)] set_zip_rightD[OF ab(1)] by auto
    qed
    moreover have "vars_term ?t \<union> vars_term ?s \<subseteq> vars_eqs P" by (rule vars_in[OF in_P])
    ultimately show ?thesis using vars_remove1[of "(?t, ?s)" P] unfolding vars_eqs_simps(3) by blast
  qed
qed

text \<open>Variable elimination.\<close>

lemma VNAC_elim:
  assumes e: "e \<in> set P" "Var x \<in> eq_sides [e]" and u: "u \<in> eq_sides P" "x \<notin> vars_term u"
  shows "VNAC (subst_eqs (Var(x := u)) (remove1 e P)) \<subseteq> VNAC P - {x}"
proof -
  let ?\<sigma> = "Var(x := u)"
  let ?E = "remove1 e P"
  let ?P' = "subst_eqs ?\<sigma> ?E"
  have EP: "eq_sides ?E \<subseteq> eq_sides P" by (rule eq_sides_remove1)
  have xP: "Var x \<in> eq_sides P" using e by (auto simp: eq_sides_def)
  have sides: "eq_sides ?P' = (\<lambda>a. a \<cdot> ?\<sigma>) ` eq_sides ?E" by (rule eq_sides_subst)
  have xn: "x \<notin> vars_eqs ?P'" using vars_upd_subst_eqs[of x u ?E] u(2) by blast
  have uSub: "fsub u \<subseteq> Sub P" using u(1) by (auto simp: Sub_def)
  have varside: "y \<in> VNAC P" if "Var y = a \<cdot> ?\<sigma>" "a \<in> eq_sides P" for y a
  proof (cases a)
    case (Var z)
    show ?thesis
    proof (cases "z = x")
      case True
      then have "u = Var y" using that(1) Var by simp
      then show ?thesis using u(1) by (simp add: VNAC_def)
    next
      case False
      then show ?thesis using that Var by (simp add: VNAC_def)
    qed
  qed (use that in simp)
  have "VNAC ?P' \<subseteq> VNAC P"
  proof
    fix y
    assume "y \<in> VNAC ?P'"
    then consider "Var y \<in> eq_sides ?P'"
      | T where "T \<in> Sub ?P'" "is_Fun T" "\<not> is_acapp T" "Var y \<in> set (targs T)"
      unfolding VNAC_def by blast
    then show "y \<in> VNAC P"
    proof cases
      case 1
      then obtain a where "a \<in> eq_sides ?E" "Var y = a \<cdot> ?\<sigma>" using sides by auto
      then show ?thesis using varside EP by blast
    next
      case 2
      then obtain a where a: "a \<in> eq_sides ?E" "T \<in> fsub (a \<cdot> ?\<sigma>)" using sides by (auto simp: Sub_def)
      have aP: "a \<in> eq_sides P" using a(1) EP by blast
      from fsub_subst[OF a(2)] show ?thesis
      proof
        assume "\<exists>w \<in> fsub a. is_Fun w \<and> T = w \<cdot> ?\<sigma>"
        then obtain w where w: "w \<in> fsub a" "is_Fun w" "T = w \<cdot> ?\<sigma>" by blast
        have nw: "\<not> is_acapp w" using 2(3) w(2,3) by simp
        have "Var y \<in> set (map (\<lambda>b. b \<cdot> ?\<sigma>) (targs w))"
          using 2(4) unfolding w(3) targs_subst_not_acapp[OF w(2) nw] .
        then obtain b where b: "b \<in> set (targs w)" "Var y = b \<cdot> ?\<sigma>" by auto
        have wS: "w \<in> Sub P" using w(1) aP by (auto simp: Sub_def)
        show ?thesis
        proof (cases b)
          case (Var z)
          show ?thesis
          proof (cases "z = x")
            case True
            then show ?thesis using varside[of y b] b(2) u(1) Var by (simp add: VNAC_def)
          next
            case False
            then have "b = Var y" using b(2) Var by simp
            then show ?thesis using b(1) wS w(2) nw unfolding VNAC_def by blast
          qed
        qed (use b(2) in simp)
      next
        assume "\<exists>z \<in> vars_term a. T \<in> fsub (?\<sigma> z) \<and>
          (T = ?\<sigma> z \<longrightarrow> a = Var z \<or> (\<exists>w \<in> fsub a. is_Fun w \<and> Var z \<in> set (targs w) \<and>
             \<not> (\<exists>g. is_ac_app g w \<and> is_ac_app g (?\<sigma> z))))"
        then obtain z where z: "T \<in> fsub (?\<sigma> z)" by blast
        show ?thesis
        proof (cases "z = x")
          case True
          then have "T \<in> Sub P" using z uSub by auto
          then show ?thesis using 2(2-4) unfolding VNAC_def by blast
        next
          case False
          then show ?thesis using z 2(2) by simp
        qed
      qed
    qed
  qed
  moreover have "x \<notin> VNAC ?P'" using xn VNAC_vars[of ?P'] by blast
  ultimately show ?thesis by blast
qed

lemma mless_elim:
  assumes e: "e \<in> set P" "Var x \<in> eq_sides [e]" and u: "u \<in> eq_sides P" "x \<notin> vars_term u"
  shows "mless (subst_eqs (Var(x := u)) (remove1 e P)) P"
proof (rule mless_VNAC, rule psubset_card_mono)
  have "x \<in> VNAC P" using e by (auto simp: VNAC_def eq_sides_def)
  then show "VNAC (subst_eqs (Var(x := u)) (remove1 e P)) \<subset> VNAC P"
    using VNAC_elim[OF assms] by blast
qed simp

lemma vars_elim:
  assumes "e \<in> set P" "u \<in> eq_sides P"
  shows "vars_eqs (subst_eqs (Var(x := u)) (remove1 e P)) \<subseteq> vars_eqs P"
proof -
  have "vars_term u \<subseteq> vars_eqs P" using assms(2) by (rule vars_eq_sides)
  then show ?thesis using vars_upd_subst_eqs[of x u "remove1 e P"] vars_remove1[of e P] by blast
qed

subsection \<open>Termination\<close>

lemma ac_round_mless:
  assumes ne: "P \<noteq> []" and acp: "\<forall>e \<in> set P. ac_pair ac e" and V: "vars_eqs P \<subseteq> {..<nv}"
    and mem: "(Pn, \<sigma>n, nvn) \<in> set (ac_round P [] \<sigma> nv)"
  shows "mless Pn P" "vars_eqs Pn \<subseteq> {..<nvn}"
proof -
  have sF: "\<forall>a \<in> eq_sides P. is_Fun a"
  proof
    fix a
    assume "a \<in> eq_sides P"
    then obtain b where "(a, b) \<in> set P \<or> (b, a) \<in> set P" by (auto simp: eq_sides_def)
    then show "is_Fun a" using acp ac_pair_D by fastforce
  qed
  have inv: "rinv P [] nv" using acp sF V by (simp add: rinv_def)
  obtain F where F: "VNAC Pn \<subseteq> F ` VNAC P" "V2 Pn \<subseteq> F ` V2 P" "vars_eqs Pn \<subseteq> {..<nvn}"
      "V2 Pn = F ` V2 P \<longrightarrow> (\<exists>\<rho>. AS Pn \<subseteq> (\<lambda>u. u \<cdot> \<rho>) ` AS P \<and> eq_sides Pn \<subseteq> (\<lambda>u. u \<cdot> \<rho>) ` AS P)"
    using ac_round_meas[OF mem inv] unfolding append_Nil2 eq_sides_simps(1) Un_empty_right by blast
  show "vars_eqs Pn \<subseteq> {..<nvn}" by (rule F(3))
  have cV: "card (VNAC Pn) \<le> card (VNAC P)"
    using card_mono[OF finite_imageI[OF finite_VNAC] F(1)] card_image_le[OF finite_VNAC, of F P] by simp
  have cT: "card (V2 Pn) \<le> card (V2 P)"
    using card_mono[OF finite_imageI[OF finite_V2] F(2)] card_image_le[OF finite_V2, of F P] by simp
  show "mless Pn P"
  proof (cases "card (VNAC Pn) < card (VNAC P)")
    case True
    then show ?thesis by (rule mless_VNAC)
  next
    case False
    then have eq1: "card (VNAC Pn) = card (VNAC P)" using cV by simp
    show ?thesis
    proof (cases "card (V2 Pn) < card (V2 P)")
      case True
      then show ?thesis using eq1 by (simp add: mless_def tmeasure_def)
    next
      case False
      then have eq2: "card (V2 Pn) = card (V2 P)" using cT by simp
      have c1: "card (F ` V2 P) \<le> card (V2 Pn)" using card_image_le[OF finite_V2, of F P] eq2 by linarith
      have c2: "card (V2 Pn) \<le> card (F ` V2 P)" by (rule card_mono[OF finite_imageI[OF finite_V2] F(2)])
      have "V2 Pn = F ` V2 P"
        by (rule card_subset_eq[OF finite_imageI[OF finite_V2] F(2)]) (use c1 c2 in linarith)
      then obtain \<rho> where \<rho>: "AS Pn \<subseteq> (\<lambda>u. u \<cdot> \<rho>) ` AS P" "eq_sides Pn \<subseteq> (\<lambda>u. u \<cdot> \<rho>) ` AS P"
        using F(4) by blast
      have cI: "card ((\<lambda>u. u \<cdot> \<rho>) ` AS P) \<le> card (AS P)" by (rule card_image_le[OF finite_AS])
      have "card (AS Pn) < card (AS P) \<or> (card (AS Pn) = card (AS P) \<and> psize Pn < psize P)"
      proof (cases Pn)
        case Nil
        obtain e P' where P: "P = e # P'" using ne by (cases P) auto
        obtain a b where e: "e = (a, b)" by fastforce
        have "is_Fun a" using sF P e by simp
        then have pos: "0 < psize P" using P e by (cases a) (auto simp: psize_def)
        have A0: "AS Pn = {}" "psize Pn = 0" using Nil by (simp_all add: AS_def psize_def)
        show ?thesis using pos unfolding A0 card.empty by linarith
      next
        case (Cons e Pn')
        obtain a0 b0 where e: "e = (a0, b0)" by fastforce
        let ?M = "Max (size ` eq_sides Pn)"
        have ne2: "eq_sides Pn \<noteq> {}" using Cons e by simp
        have "?M \<in> size ` eq_sides Pn" by (rule Max_in) (simp_all add: ne2)
        then obtain m where m: "?M = size m" "m \<in> eq_sides Pn" by (rule imageE)
        have big: "size a \<le> size m" if "a \<in> eq_sides Pn" for a
          using Max_ge[of "size ` eq_sides Pn" "size a"] that m(1) by simp
        have mn: "m \<notin> AS Pn"
        proof
          assume "m \<in> AS Pn"
          then obtain a where a: "a \<in> eq_sides Pn" "m \<in> fsub a" "m \<noteq> a" by (auto simp: AS_def)
          have "size m < size a" by (rule fsub_size_less[OF a(2,3)])
          then show False using big[OF a(1)] by simp
        qed
        have mi: "m \<in> (\<lambda>u. u \<cdot> \<rho>) ` AS P" by (rule subsetD[OF \<rho>(2) m(2)])
        have "AS Pn \<noteq> (\<lambda>u. u \<cdot> \<rho>) ` AS P"
        proof
          assume "AS Pn = (\<lambda>u. u \<cdot> \<rho>) ` AS P"
          then show False using mn mi by simp
        qed
        then have "AS Pn \<subset> (\<lambda>u. u \<cdot> \<rho>) ` AS P" by (rule psubsetI[OF \<rho>(1)])
        then have "card (AS Pn) < card ((\<lambda>u. u \<cdot> \<rho>) ` AS P)"
          by (rule psubset_card_mono[OF finite_imageI[OF finite_AS]])
        then show ?thesis using cI by simp
      qed
      then show ?thesis using eq1 eq2 by (auto simp: mless_def tmeasure_def)
    qed
  qed
qed

lemma acunif_dom_all: "\<forall>\<sigma> nv. vars_eqs P \<subseteq> {..<nv} \<longrightarrow> acunif_dom (P, \<sigma>, nv)"
proof (rule wf_induct[OF wf_mless, of "\<lambda>P. \<forall>\<sigma> nv. vars_eqs P \<subseteq> {..<nv} \<longrightarrow> acunif_dom (P, \<sigma>, nv)"])
  fix P :: "('f, nat) eqs"
  assume IH: "\<forall>P'. (P', P) \<in> {(P', P). mless P' P} \<longrightarrow>
    (\<forall>\<sigma> nv. vars_eqs P' \<subseteq> {..<nv} \<longrightarrow> acunif_dom (P', \<sigma>, nv))"
  have IH': "acunif_dom (P', \<sigma>, nv)" if "mless P' P" "vars_eqs P' \<subseteq> {..<nv}" for P' \<sigma> nv
    using IH that by blast
  show "\<forall>\<sigma> nv. vars_eqs P \<subseteq> {..<nv} \<longrightarrow> acunif_dom (P, \<sigma>, nv)"
  proof (intro allI impI)
    fix \<sigma> nv
    assume V: "vars_eqs P \<subseteq> {..<nv}"
    show "acunif_dom (P, \<sigma>, nv)"
    proof (rule acunif.domintros)
      fix Pn \<sigma>n nvn
      assume ne: "P \<noteq> []" and fn: "find (\<lambda>e. \<not> ac_pair ac e) P = None"
        and mem: "(Pn, \<sigma>n, nvn) \<in> set (ac_round P [] \<sigma> nv)"
      have acp: "\<forall>e \<in> set P. ac_pair ac e" using fn by (auto simp: find_None_iff)
      show "acunif_dom (Pn, \<sigma>n, nvn)"
        by (rule IH'[OF ac_round_mless[OF ne acp V mem]])
    next
      fix b
      assume "find (\<lambda>e. \<not> ac_pair ac e) P = Some (b, b)"
      then have e: "(b, b) \<in> set P" by (auto simp: find_Some_iff)
      show "acunif_dom (remove1 (b, b) P, \<sigma>, nv)"
        by (rule IH'[OF mless_delete[OF e]]) (use vars_remove1[of "(b, b)" P] V in blast)
    next
      fix b x
      assume "find (\<lambda>e. \<not> ac_pair ac e) P = Some (Var x, b)" and xb: "x \<notin> vars_term b"
      then have e: "(Var x, b) \<in> set P" by (auto simp: find_Some_iff)
      have bP: "b \<in> eq_sides P" using side_in[OF e] by blast
      show "acunif_dom (subst_eqs (Var(x := b)) (remove1 (Var x, b) P), \<sigma> \<circ>\<^sub>s Var(x := b), nv)"
        by (rule IH'[OF mless_elim[OF e _ bP xb]]) (use vars_elim[OF e bP, of x] V in auto)
    next
      fix g ts x
      assume "find (\<lambda>e. \<not> ac_pair ac e) P = Some (Fun g ts, Var x)" and xb: "\<forall>t \<in> set ts. x \<notin> vars_term t"
      then have e: "(Fun g ts, Var x) \<in> set P" by (auto simp: find_Some_iff)
      have bP: "Fun g ts \<in> eq_sides P" using side_in[OF e] by blast
      have xb': "x \<notin> vars_term (Fun g ts)" using xb by simp
      show "acunif_dom (subst_eqs (Var(x := Fun g ts)) (remove1 (Fun g ts, Var x) P),
          \<sigma> \<circ>\<^sub>s Var(x := Fun g ts), nv)"
        by (rule IH'[OF mless_elim[OF e _ bP xb']]) (use vars_elim[OF e bP, of x] V in auto)
    next
      fix g ts ss
      assume "find (\<lambda>e. \<not> ac_pair ac e) P = Some (Fun g ts, Fun g ss)" and len: "length ts = length ss"
      then have e: "(Fun g ts, Fun g ss) \<in> set P" and nac: "\<not> ac_pair ac (Fun g ts, Fun g ss)"
        by (auto simp: find_Some_iff)
      show "acunif_dom (zip ts ss @ remove1 (Fun g ts, Fun g ss) P, \<sigma>, nv)"
        by (rule IH'[OF mless_decomp(1)[OF e len nac]]) (use mless_decomp(2)[OF e len nac] V in blast)
    qed
  qed
qed

theorem acunif_dom: "vars_eqs P \<subseteq> {..<nv} \<Longrightarrow> acunif_dom (P, \<sigma>, nv)"
  using acunif_dom_all by blast

theorem ac_unifiers_dom: "acunif_dom ([(s, t)], Var, nv0 s t)"
  by (rule acunif_dom) (use vars_below_nv0[of s t] in simp)

text \<open>Soundness and completeness of \<open>ac_unifiers\<close>, now unconditionally (PVS Corollary 5 and Lemma 10).\<close>

theorem ac_unifiers_sound:
  assumes "\<theta> \<in> set (ac_unifiers s t)"
  shows "s \<cdot> \<theta> \<approx> t \<cdot> \<theta>"
  by (rule ac_unifiers_sound_dom[OF ac_unifiers_dom assms])

theorem ac_unifiers_complete:
  fixes \<delta> :: "('f, nat) subst"
  assumes total: "\<And>n A. dsolve n A \<noteq> None" and u: "s \<cdot> \<delta> \<approx> t \<cdot> \<delta>"
  shows "\<exists>\<theta>\<in>set (ac_unifiers s t). \<exists>\<rho>. \<forall>x\<in>vars_term s \<union> vars_term t. \<delta> x \<approx> \<theta> x \<cdot> \<rho>"
  by (rule ac_unifiers_complete_dom[OF total ac_unifiers_dom u])

end

end
