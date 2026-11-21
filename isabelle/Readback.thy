theory Readback
  imports Conservative Lambda
begin

section \<open>Readback into the \<open>\<lambda>\<close>-calculus and the extension theorem E1\<close>

text \<open>Adapted from the \<open>\<lambda>env\<close> development.  \<open>tm\<close>, \<open>en\<close>, \<open>pure\<close> are in
  \<open>Sorted\<close>; preservation of sortedness and \<open>sorted_not_clash\<close> are in
  \<open>Conservative\<close>.\<close>

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Id \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rb (Nm x) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Id \<rho> = \<rho>"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"
| "rbe (Nm x) \<rho> = \<rho>"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Id
  then show ?case by simp
next
  case (Nm x)
  then show ?case by (simp add: ext)
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

subsection \<open>Simulation\<close>

lemma sig0_rb:
  "sig0 M N \<Longrightarrow>
     (tm M \<longrightarrow> tm N \<and> (\<forall>\<rho>. rb N \<rho> = rb M \<rho>)) \<and>
     (en M \<longrightarrow> en N \<and> (\<forall>\<rho>. rbe N \<rho> = rbe M \<rho>))"
  by (induction rule: sig0.induct) (auto simp: fun_upd_def)

lemma beta0_not_en: "beta0 M N \<Longrightarrow> \<not> en M"
  by (induction rule: beta0.induct) auto

lemma beta0_rb:
  "beta0 M N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>)"
proof (induction rule: beta0.induct)
  case (Beta1 x M L N)
  have "rb (App (Comp (Lam x M) L) N) \<rho> \<rightarrow>\<^sub>h rb (Comp M (Extn N x L)) \<rho>" for \<rho>
    using hbeta[of "rb M ((\<lambda>y. lift (rbe L \<rho> y) 0)(x := DVar 0))" "rb N \<rho>"]
    by (simp add: beta_rb)
  then show ?case using Beta1 by simp
next
  case (Beta2 x M N)
  have "rb (App (Lam x M) N) \<rho> \<rightarrow>\<^sub>h rb (Comp M (Extn N x Id)) \<rho>" for \<rho>
    using hbeta[of "rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0))" "rb N \<rho>"]
    by (simp add: beta_rb)
  then show ?case using Beta2 by simp
next
  case (AppL M N L)
  then show ?case by (auto intro: happ)
next
  case (CompL M N L)
  then show ?case by auto
next
  case (VarR M N x)
  then show ?case using beta0_not_en by auto
qed

lemma wh_sorted_rb:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h N" "tm M"
  shows "tm N \<and> ((\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M \<or> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>))"
proof -
  from assms(1) have "M \<rightarrow>\<^sub>\<sigma> N \<or> M \<rightarrow>\<^sub>\<beta> N" by (simp add: wh_def)
  then show ?thesis
  proof
    assume s: "M \<rightarrow>\<^sub>\<sigma> N"
    then have "sig0 M N" using sorted_sig_iff assms(2) by blast
    then show ?thesis using sig0_rb assms(2) sig_tlength_decrease[OF s] by blast
  next
    assume b: "M \<rightarrow>\<^sub>\<beta> N"
    then have "beta0 M N" using sorted_beta_iff assms(2) by blast
    then show ?thesis using beta0_rb assms(2) by blast
  qed
qed

lemma wh_steps_sorted_rb:
  "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> hred\<^sup>*\<^sup>* (rb M \<rho>) (rb N \<rho>)"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step N P)
  then show ?case
    using wh_sorted_rb[of N P] by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed

subsection \<open>Normal forms\<close>

inductive hneu :: "dB \<Rightarrow> bool" where
  "hneu (DVar i)"
| "hneu s \<Longrightarrow> hneu (DApp s t)"

lemma hneu_normal: "hneu s \<Longrightarrow> normal hred s"
proof (induction rule: hneu.induct)
  case (1 i)
  then show ?case by (auto simp: normal_def elim: hred.cases)
next
  case (2 s t)
  then show ?case by (auto simp: normal_def elim: hred.cases hneu.cases)
qed

lemma DAbs_normal: "normal hred (DAbs s)"
  by (auto simp: normal_def elim: hred.cases)

lemma neu_not_en: "neu M \<Longrightarrow> \<not> en M"
  by (induction rule: neu.induct) auto

lemma neu_rb: "neu M \<Longrightarrow> tm M \<Longrightarrow> hneu (rb M DVar)"
proof (induction rule: neu.induct)
  case (NVar x)
  then show ?case by (simp add: hneu.intros)
next
  case (NApp M N)
  then show ?case by (simp add: hneu.intros)
next
  case (NComp M x)
  then show ?case using neu_not_en by simp
qed

theorem rb_WHNF: "tm M \<Longrightarrow> WHNF M \<Longrightarrow> normal hred (rb M DVar)"
proof -
  assume t: "tm M" and n: "WHNF M"
  from n consider "neu M" | "val M" | "clash M" by (auto simp: WHNF_iff_classes)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using t neu_rb hneu_normal by blast
  next
    case 2
    then show ?thesis using t by (cases rule: val.cases) (simp_all add: DAbs_normal)
  next
    case 3
    then show ?thesis using t sorted_not_clash by blast
  qed
qed

subsection \<open>E1\<close>

lemma SN_at_normal_reachable: "SN_at R a \<Longrightarrow> \<exists>b. R\<^sup>*\<^sup>* a b \<and> normal R b"
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof (cases "normal R a")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain b where "R a b" by (auto simp: normal_def)
    with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

lemma CFWHN_imp_lam_WHN:
  assumes t: "tm M" and c: "CFWHN M"
  shows "lam_WHN (rb M DVar)"
proof -
  obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N"
    using c by (auto simp: CFWHN_def)
  from wh_steps_sorted_rb[OF r t] have tN: "tm N" and h: "hred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
    by blast+
  show ?thesis
    unfolding lam_WHN_def using h rb_WHNF[OF tN n] by blast
qed

lemma hdist_imp_WHSN: "hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
  proof -
    fix M
    show "hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>w\<^sub>h N"
        from wh_sorted_rb[OF s \<open>tm M\<close>] have tN: "tm N"
          and c: "(\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M \<or> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>)"
          by blast+
        from c show "WHSN N"
        proof
          assume a: "(\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M"
          then have "hdist (rb N DVar) n" using less.prems(1) by simp
          then show "WHSN N" using less.hyps a tN by blast
        next
          assume "\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>"
          then obtain m where "n = Suc m" "hdist (rb N DVar) m"
            using hdist_step less.prems(1) by blast
          then show "WHSN N" using IHn tN by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma lam_WHN_imp_CFWHSN: "tm M \<Longrightarrow> lam_WHN (rb M DVar) \<Longrightarrow> CFWHSN M"
proof -
  assume t: "tm M" and w: "lam_WHN (rb M DVar)"
  then obtain n where "hdist (rb M DVar) n" using lam_WHN_hdist by blast
  then have "WHSN M" using t hdist_imp_WHSN by blast
  moreover have "\<not> clash N" if r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" for N
  proof -
    have "tm N" using wh_steps_sorted_rb[OF r t] by blast
    then show ?thesis using sorted_not_clash by blast
  qed
  ultimately show ?thesis by (auto simp: CFWHSN_def)
qed

theorem E1_sorted:
  assumes "tm M"
  shows "(lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN M) \<and> (CFWHN M \<longleftrightarrow> CFWHSN M)"
  using assms CFWHN_imp_lam_WHN lam_WHN_imp_CFWHSN CFWHSN_imp_CFWHN CFWHN_imp_CFWHSN by blast

theorem E1:
  assumes "pure M"
  shows "(lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN M) \<and> (CFWHN M \<longleftrightarrow> CFWHSN M)"
  using E1_sorted pure_tm assms by blast

theorem pure_characterization:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> lam_WHN (rb M DVar)"
  using main_characterization E1[OF assms] by blast

text \<open>Oracle check for the conservativity results.\<close>

ML \<open>
  val ths = [@{thm conservative_CFWHN}, @{thm conservative_Typ}, @{thm sorted_wh_iff},
             @{thm E1_sorted}, @{thm E1}, @{thm pure_characterization}];
  val oracles = Thm_Deps.all_oracles ths;
  val _ = if null oracles then writeln "No oracles."
          else error ("Oracles used: " ^ commas (map (#1 o #1) oracles));
\<close>

end
