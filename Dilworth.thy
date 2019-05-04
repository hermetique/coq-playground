theory Dilworth
  imports Main
begin

context order
begin

interpretation pred_on UNIV "(\<le>)" .

lemma chain_def:
  "chain X \<longleftrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. x \<le> y \<or> y \<le> x)"
  by (auto simp: chain_def)

lemma chain_singleton [simp]:
  "chain {x}"
  by (auto simp: chain_def)

definition anti_chain where
  "anti_chain X \<longleftrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. x \<le> y \<longrightarrow> x = y)"

theorem Dilworth_easy:
  assumes Cs: "\<forall>C \<in> Cs. chain C" and A_Cs: "A \<subseteq> \<Union>Cs" and ac_A: "anti_chain A"
  obtains f where "inj_on f A" "f ` A \<subseteq> Cs" "\<forall>a \<in> A. a \<in> f a"
proof -
  { fix a assume "a \<in> A" then have "\<exists>C \<in> Cs. a \<in> C" using A_Cs by auto }
  then obtain f where f: "\<And>a. a \<in> A \<Longrightarrow> f a \<in> Cs \<and> a \<in> f a" by metis
  show ?thesis
  proof (rule that[of f])
    { fix x y assume xy: "x \<in> A" "y \<in> A" and "f x = f y"
      then have "f y \<in> Cs" and xy': "x \<in> f y" "y \<in> f y" by (auto dest: f)
      then have "chain (f y)" using Cs by auto
      then have "x = y" using xy xy' ac_A unfolding chain_def anti_chain_def by auto
    }
    then show "inj_on f A" by (auto simp: inj_on_def)
  qed (auto dest: f)
qed

corollary Dilworth_easy_card:
  assumes fin: "finite Cs" and Cs: "\<forall>C \<in> Cs. chain C" and A_Cs: "A \<subseteq> \<Union>Cs" and ac_A: "anti_chain A"
  shows "finite A \<and> card A \<le> card Cs"
proof
  guess f using Dilworth_easy[OF Cs A_Cs ac_A] . note f = this
  show "finite A" using f(1,2) fin by (meson inj_on_finite)
  show "card A \<le> card Cs" using f(1,2) fin by (metis card_image card_mono)
qed

lemma find_min:
  assumes "finite X" "X \<noteq> {}"
  obtains m where "m \<in> X" "\<And>x. x \<in> X \<Longrightarrow> x \<le> m \<Longrightarrow> x = m"
  using assms
proof (induct arbitrary: thesis rule: finite_ne_induct)
  case (insert x X)
  guess m using insert(4) .
  then show ?case using insert(1,2,3)
    apply (intro insert(5)[of "if x \<le> m then x else m"])
    subgoal by simp
    subgoal by simp (metis (full_types) local.antisym local.dual_order.trans)
    done
qed simp_all

theorem Dilworth_hard:
  assumes "finite X"
  obtains Cs f where
    "finite Cs" "\<Union>Cs = X" "\<forall>C \<in> Cs. chain C"
    "inj_on f Cs" "\<forall>C \<in> Cs. f C \<in> C" "anti_chain (f ` Cs)"
  using assms
proof (induct X arbitrary: thesis rule: finite_psubset_induct)
  case (psubset X)
  then show ?case
  proof (cases "X = {}")
    case True
    then show ?thesis using psubset(3)[of "{}" undefined] by (simp add: anti_chain_def)
  next
    case False
    guess m using find_min[OF `finite X` `X \<noteq> {}`] . note m = this
    have "X - {m} \<subset> X" using m(1) by blast
    from psubset(2)[OF this] guess Cs0 f0 .
    note Cs0 = this(1-3) and f0 = this(4-6)
    define anti_chain0 where
      "\<And>f. anti_chain0 f \<longleftrightarrow> inj_on f Cs0 \<and> (\<forall>C \<in> Cs0. f C \<in> C) \<and> anti_chain (f ` Cs0)"
    have ac0_f0: "anti_chain0 f0" using f0 by (simp add: anti_chain0_def)
    { fix C assume C: "C \<in> Cs0"
      let ?C' = "{f C |f. anti_chain0 f}"
      have "?C' \<subseteq> C" using C Cs0(2) unfolding anti_chain0_def by blast
      then have fin_C': "finite ?C'" using Cs0(2) psubset(1) C
        by (metis (no_types, lifting) Cs0(1) finite_Diff infinite_super le_cSup_finite)
      moreover have "f0 C \<in> ?C'" using ac0_f0 by blast
      then have "?C' \<noteq> {}" by blast
      ultimately guess x by (rule find_min[of ?C']) note x = this
      have "x \<in> C" using x(1) C by (auto simp: anti_chain0_def)
      have "\<exists>x. x \<in> C \<and> (\<exists>f. anti_chain0 f \<and> f C = x) \<and> (\<forall>f D. D \<in> Cs0 \<longrightarrow> anti_chain0 f \<longrightarrow> f D \<le> x \<longrightarrow> f D = x)"
      proof (intro exI[of _ x] conjI allI impI, goal_cases)
        case 2 show ?case using x(1) by blast
      next
        case (3 f D)
        have "f C \<in> C" "f D \<in> D" using 3(1,2) C by (auto simp: anti_chain0_def)
        have "f C \<in> {f C |f. anti_chain0 f}" using 3(2) by blast
        from x(2)[OF this] have "x \<le> f C"
          using Cs0(3)[rule_format, OF C] `x \<in> C` `f C \<in> C` unfolding chain_def by auto
        then have "f D \<le> f C" using 3(3) by auto
        then have "C = D" using C 3(1,2) unfolding anti_chain0_def anti_chain_def inj_on_def by blast
        then show ?case using `f D \<le> x` `x \<le> f C` by simp
      qed fact
    }
    then obtain f1 where f1: "\<And>C. C \<in> Cs0 \<Longrightarrow> f1 C \<in> C \<and> (\<exists>f. anti_chain0 f \<and> f C = f1 C) \<and>
      (\<forall>f D. D \<in> Cs0 \<longrightarrow> anti_chain0 f \<longrightarrow> f D \<le> f1 C \<longrightarrow> f D = f1 C)" by metis
    have "anti_chain0 f1" unfolding anti_chain0_def anti_chain_def
    proof (intro conjI ballI impI inj_onI, goal_cases)
      case (1 C D)
      obtain f where f: "anti_chain0 f" "f C = f1 C" using f1[OF 1(1)] by blast
      have "f D \<in> D" "f1 D \<in> D" using f(1) `D \<in> Cs0` f1[of D] by (auto simp: anti_chain0_def)
      then have "f C \<le> f D" using f1[OF 1(1), THEN conjunct2, THEN conjunct2, rule_format, of D f]
        Cs0(3)[rule_format, of D, unfolded chain_def, rule_format, of "f1 D" "f D"]
        by (auto simp: 1(3) f `D \<in> Cs0`)
      then show "C = D" using f(1) `C \<in> Cs0` `D \<in> Cs0`
        unfolding anti_chain0_def anti_chain_def inj_on_def by blast
    next
      case (2 C) then show ?case using f1 by blast
    next
      case (3 x y)
      then obtain C D where C: "C \<in> Cs0" "x = f1 C" and D: "D \<in> Cs0" "y = f1 D" by blast
      obtain f where f: "anti_chain0 f" "f C = f1 C" using f1[OF C(1)] by blast
      note C(1) D(1) 3(3)[unfolded C(2) D(2)]
      have "f D \<in> D" "f1 D \<in> D" using f(1) `D \<in> Cs0` f1[of D] by (auto simp: anti_chain0_def)
      then have "f1 D \<le> f D" using f1[of D, THEN conjunct2, THEN conjunct2, rule_format, of D f]
        Cs0(3)[rule_format, of D, unfolded chain_def, rule_format, of "f1 D" "f D"] f(1) `D \<in> Cs0`
        by auto
      then have "f C \<le> f D" using `x \<le> y` by (simp add: C(2) D(2) f(2))
      then have "C = D" using f(1) `C \<in> Cs0` `D \<in> Cs0` `x \<le> y`
        unfolding anti_chain0_def anti_chain_def inj_on_def using C(2) D(2) f(2) by blast
      then show ?case by (simp add: C(2) D(2))
    qed
    have no_m: "\<not> m \<in> C" if "C \<in> Cs0" for C using that Cs0(2) by blast
    consider C where "C \<in> Cs0" "m \<le> f1 C" | "\<And>C. C \<in> Cs0 \<Longrightarrow> \<not> m \<le> f1 C" by blast
    then show ?thesis
    proof (cases)
      case 1
      (* TODO: hard case *)
      show ?thesis sorry
    next
      case 2
      let ?f2 = "\<lambda>C. if m \<in> C then m else f1 C"
      show ?thesis
      proof (rule psubset(3)[of "insert {m} Cs0" "?f2"], goal_cases)
        case 1 show ?case using Cs0(1) by simp
      next
        case 2 show ?case using Cs0(2) m(1) by auto
      next
        case 3 show ?case using Cs0(3) by auto
      next
        case 4
        have "inj_on f1 Cs0" using `anti_chain0 f1` by (simp add: anti_chain0_def)
        then have "inj_on ?f2 Cs0" by (auto simp: inj_on_def no_m)
        then show ?case using f1 by (auto simp: no_m)
      next
        case 5 show ?case using f1 by auto
      next
        case 6
        { fix C assume "C \<in> Cs0" "f1 C \<le> m"
          then have "f1 C = m" by (metis Cs0(2) DiffE UnionI f1 m(2))
        }
        moreover have "anti_chain (f1 ` Cs0)" using `anti_chain0 f1` by (simp add: anti_chain0_def)
        ultimately show ?case using 2 by (auto simp: anti_chain_def)
      qed
    qed
  qed
qed

theorem Dilworth_hard_card:
  assumes "finite X"
  obtains Cs A where
    "finite Cs" "\<Union>Cs = X" "\<forall>C \<in> Cs. chain C"
    "finite A" "A \<subseteq> X" "anti_chain A" "card A = card Cs"
proof -
  guess Cs f using Dilworth_hard[OF assms] . note Cs = this(1-3) and f = this(4-6)
  show ?thesis
  proof (rule that[of Cs "f ` Cs"], goal_cases)
    case 4 show ?case using Cs(1) by simp
  next
    case 5 show ?case using f(2) Cs(2) by blast
  next
    case 7 show ?case using Cs(1) f(1) by (intro card_image)
  qed fact+
qed

end

end