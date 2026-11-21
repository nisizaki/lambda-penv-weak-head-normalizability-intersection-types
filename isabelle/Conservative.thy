theory Conservative
  imports Sorted Main_Results
begin

section \<open>Conservativity over \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> on sorted terms\<close>

text \<open>
  On sorted terms none of the new rules (AppConst, ConstComp, VarLam, VarClos,
  ArgV) applies, sortedness is preserved, and the reduction of
  \<open>\<lambda>penv\<^sub>w\<^sub>h\<close> coincides with that of \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close>.  Sorted terms never reach a clash.
\<close>

lemma envh_not_tm: "envh V \<Longrightarrow> \<not> tm V"
  by (cases V) auto

lemma sig0_imp_sig: "sig0 M N \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N"
  by (induction rule: sig0.induct) (auto intro: sig.intros)

lemma sig_sorted_imp_sig0: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> tm M \<or> en M \<Longrightarrow> sig0 M N"
  by (induction rule: sig.induct) (auto intro: sig0.intros)

lemma sorted_sig_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<longleftrightarrow> sig0 M N"
  using sig0_imp_sig sig_sorted_imp_sig0 by blast

lemma beta0_imp_beta_c: "beta0 M N \<Longrightarrow> M \<rightarrow>\<^sub>c N"
  by (induction rule: beta0.induct) (auto intro: beta_c.intros)

lemma beta_c_sorted_imp_beta0: "M \<rightarrow>\<^sub>c N \<Longrightarrow> tm M \<or> en M \<Longrightarrow> beta0 M N"
  by (induction rule: beta_c.induct) (auto intro: beta0.intros)

lemma beta_h_sorted_imp_beta0: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> tm M \<or> en M \<Longrightarrow> beta0 M N"
proof (induction rule: beta_h.induct)
  case (C M N) then show ?case using beta_c_sorted_imp_beta0 by blast
next
  case (AppL M N L) then show ?case by (auto intro: beta0.intros)
next
  case (VarR M N x) then show ?case by (auto intro: beta0.intros)
next
  case (ArgV V M N) then show ?case using envh_not_tm by auto
qed

lemma sorted_beta_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N \<longleftrightarrow> beta0 M N"
  using beta_h_sorted_imp_beta0 beta0_imp_beta_c beta_c_imp_beta_h by blast

lemma sorted_wh_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N \<longleftrightarrow> wh0 M N"
  by (simp add: wh_def wh0_def sorted_sig_iff sorted_beta_iff)

lemma sig0_sorted: "sig0 M N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
  by (induction rule: sig0.induct) auto

lemma beta0_sorted: "beta0 M N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
  by (induction rule: beta0.induct) auto

lemma wh_sorted: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
proof -
  assume h: "M \<rightarrow>\<^sub>w\<^sub>h N"
  show ?thesis
  proof (intro conjI impI)
    assume "tm M"
    then have "wh0 M N" using h sorted_wh_iff by blast
    then show "tm N" using sig0_sorted beta0_sorted \<open>tm M\<close> unfolding wh0_def by blast
  next
    assume "en M"
    then have "wh0 M N" using h sorted_wh_iff by blast
    then show "en N" using sig0_sorted beta0_sorted \<open>en M\<close> unfolding wh0_def by blast
  qed
qed

lemma wh_steps_sorted: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N"
  by (induction rule: rtranclp_induct) (auto dest: wh_sorted)

lemma sorted_not_clash': "clash M \<Longrightarrow> \<not> (tm M \<or> en M)"
  by (induction rule: clash.induct) (auto dest: envh_not_tm)

lemma sorted_not_clash: "tm M \<Longrightarrow> \<not> clash M"
  using sorted_not_clash' by blast

theorem sorted_wh_steps_iff: "tm M \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<longleftrightarrow> wh0\<^sup>*\<^sup>* M N"
proof
  assume tm: "tm M" and r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N"
  from r show "wh0\<^sup>*\<^sup>* M N"
  proof (induction rule: rtranclp_induct)
    case base then show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step b c)
    have tb: "tm b" by (rule wh_steps_sorted[OF step.hyps(1) tm])
    have "wh0 b c" by (rule iffD1[OF sorted_wh_iff[OF disjI1[OF tb]] step.hyps(2)])
    show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH \<open>wh0 b c\<close>])
  qed
next
  assume tm: "tm M" and r: "wh0\<^sup>*\<^sup>* M N"
  from r show "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N"
  proof (induction rule: rtranclp_induct)
    case base then show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step b c)
    have tb: "tm b" by (rule wh_steps_sorted[OF step.IH tm])
    have "b \<rightarrow>\<^sub>w\<^sub>h c" by (rule iffD2[OF sorted_wh_iff[OF disjI1[OF tb]] step.hyps(2)])
    show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH \<open>b \<rightarrow>\<^sub>w\<^sub>h c\<close>])
  qed
qed

theorem conservative_CFWHN: "tm M \<Longrightarrow> CFWHN M \<longleftrightarrow> CFWHN0 M"
proof -
  assume tm: "tm M"
  have nf: "\<And>N. tm N \<Longrightarrow> normal wh N \<longleftrightarrow> normal wh0 N"
  proof -
    fix N assume tN: "tm N"
    show "normal wh N \<longleftrightarrow> normal wh0 N"
    proof
      assume h: "normal wh N"
      show "normal wh0 N"
        unfolding normal_def
      proof (rule notI)
        assume "\<exists>b. wh0 N b"
        then obtain b where "wh0 N b" by blast
        then have "wh N b" using sorted_wh_iff tN by blast
        with h show False unfolding normal_def by blast
      qed
    next
      assume h: "normal wh0 N"
      show "normal wh N"
        unfolding normal_def
      proof (rule notI)
        assume "\<exists>b. wh N b"
        then obtain b where "wh N b" by blast
        then have "wh0 N b" using sorted_wh_iff tN by blast
        with h show False unfolding normal_def by blast
      qed
    qed
  qed
  show ?thesis
  proof
    assume "CFWHN M"
    then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" unfolding CFWHN_def by blast
    have "tm N" using wh_steps_sorted r tm by blast
    then have "normal wh0 N" using nf n by blast
    with r have "wh0\<^sup>*\<^sup>* M N" using tm sorted_wh_steps_iff by blast
    then show "CFWHN0 M" unfolding CFWHN0_def using \<open>normal wh0 N\<close> by blast
  next
    assume "CFWHN0 M"
    then obtain N where r: "wh0\<^sup>*\<^sup>* M N" and n: "normal wh0 N" unfolding CFWHN0_def by blast
    have r': "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" using r tm sorted_wh_steps_iff by blast
    have tN: "tm N" using wh_steps_sorted r' tm by blast
    have "WHNF N" using nf[OF tN] n by blast
    moreover have "\<not> clash N" using sorted_not_clash tN by blast
    ultimately show "CFWHN M" unfolding CFWHN_def using r' by blast
  qed
qed

theorem conservative_Typ: "tm M \<Longrightarrow> Typ M \<longleftrightarrow> CFWHN0 M"
  using conservative_CFWHN main_characterization by blast

end
