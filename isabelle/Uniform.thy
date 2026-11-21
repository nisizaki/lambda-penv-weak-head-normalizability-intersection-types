theory Uniform
  imports Sig_Confluence WHNF_Classes
begin

section \<open>Uniform normalization (no typing involved)\<close>

text \<open>
  Head \<open>\<beta>\<close> is deterministic (\<open>beta_h_det\<close>, in \<open>Reduction\<close>), \<open>\<sigma>\<close> terminates and
  is confluent, and a \<open>\<sigma>\<close>-step commutes with the \<open>\<beta>\<close>-step
  (\<open>beta_c_sig_commute\<close>, \<open>beta_h_sig_commute\<close>).  Hence every
  \<open>\<rightarrow>\<^sub>w\<^sub>h\<close>-path follows one deterministic chain of \<open>\<sigma>\<close>-normal forms.
\<close>

lemma sig_nf: "\<exists>N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N"
proof -
  have "SN_at sig M" by (rule sig_SN)
  then show ?thesis
  proof (induction rule: SN_at_induct)
    case (step a)
    show ?case
    proof (cases "sig_normal a")
      case True then show ?thesis by blast
    next
      case False
      then obtain b where "a \<rightarrow>\<^sub>\<sigma> b" by (auto simp: normal_def)
      with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
qed

subsection \<open>Congruences for \<open>\<sigma>\<^sup>*\<close>\<close>

lemma ss_lift:
  assumes "\<And>P Q. P \<rightarrow>\<^sub>\<sigma> Q \<Longrightarrow> f P \<rightarrow>\<^sub>\<sigma> f Q"
  shows "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (f M) (f N)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl assms)

lemma ss_AppL: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (App M L) (App N L)"
  by (rule ss_lift[of "\<lambda>P. App P L"]) (rule sig.AppL)
lemma ss_AppR: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (App L M) (App L N)"
  by (rule ss_lift[of "\<lambda>P. App L P"]) (rule sig.AppR)
lemma ss_CompR: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp L M) (Comp L N)"
  by (rule ss_lift[of "\<lambda>P. Comp L P"]) (rule sig.CompR)
lemma ss_CompL: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp M L) (Comp N L)"
  by (rule ss_lift[of "\<lambda>P. Comp P L"]) (rule sig.CompL)

lemma ss1: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> sig\<^sup>*\<^sup>* M N" by (rule r_into_rtranclp)

lemma ss2: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> N \<rightarrow>\<^sub>\<sigma> P \<Longrightarrow> sig\<^sup>*\<^sup>* M P"
  by (meson converse_rtranclp_into_rtranclp ss1)

subsection \<open>Inversion of \<open>\<sigma>\<close>\<close>

lemma sig_Nm_no [simp]: "\<not> Nm x \<rightarrow>\<^sub>\<sigma> P" by (auto elim: sig.cases)
lemma sig_Var_no [simp]: "\<not> Var x \<rightarrow>\<^sub>\<sigma> P" by (auto elim: sig.cases)
lemma sig_Id_no [simp]: "\<not> Id \<rightarrow>\<^sub>\<sigma> P" by (auto elim: sig.cases)

lemma Lam_sig_inv: "Lam x B \<rightarrow>\<^sub>\<sigma> P \<Longrightarrow> \<exists>B'. P = Lam x B' \<and> B \<rightarrow>\<^sub>\<sigma> B'"
  by (auto elim: sig.cases)

lemma Clo_sig_inv:
  assumes "Comp (Lam x B) K \<rightarrow>\<^sub>\<sigma> P"
  shows "(\<exists>B'. P = Comp (Lam x B') K \<and> B \<rightarrow>\<^sub>\<sigma> B') \<or> (\<exists>K'. P = Comp (Lam x B) K' \<and> K \<rightarrow>\<^sub>\<sigma> K') \<or>
     (K = Id \<and> P = Lam x B)"
  using assms
proof (cases rule: sig.cases)
  case (CompL B0)
  then show ?thesis using Lam_sig_inv by blast
next
  case (CompR K')
  then show ?thesis by blast
next
  case IdR
  then show ?thesis by blast
qed

lemma Extn_sig_inv:
  "Extn M x L \<rightarrow>\<^sub>\<sigma> P \<Longrightarrow> \<exists>M' L'. P = Extn M' x L'"
  by (auto elim: sig.cases)

lemma envh_sig: "envh V \<Longrightarrow> V \<rightarrow>\<^sub>\<sigma> V' \<Longrightarrow> envh V'"
  by (cases V) (auto dest: Extn_sig_inv)

lemma sig_App_cases:
  assumes "App M N \<rightarrow>\<^sub>\<sigma> X"
  obtains (AppConst) y where "N = Nm y" "X = Comp (Var y) M"
  | (AppL) M' where "M \<rightarrow>\<^sub>\<sigma> M'" "X = App M' N"
  | (AppR) N' where "N \<rightarrow>\<^sub>\<sigma> N'" "X = App M N'"
  using assms by (cases rule: sig.cases) auto

lemma sig_Comp_cases:
  assumes "Comp A B \<rightarrow>\<^sub>\<sigma> X"
  obtains (Ass) L M where "A = Comp L M" "X = Comp L (Comp M B)"
  | (IdL) "A = Id" "X = B"
  | (IdR) "B = Id" "X = A"
  | (DExtn) L x M where "A = Extn L x M" "X = Extn (Comp L B) x (Comp M B)"
  | (VarRef) x M N where "A = Var x" "B = Extn M x N" "X = M"
  | (VarSkip) x y M N where "x \<noteq> y" "A = Var y" "B = Extn M x N" "X = Comp (Var y) N"
  | (DApp) M1 M2 where "A = App M1 M2" "X = App (Comp M1 B) (Comp M2 B)"
  | (ConstComp) x where "A = Nm x" "X = Nm x"
  | (CompL) A' where "A \<rightarrow>\<^sub>\<sigma> A'" "X = Comp A' B"
  | (CompR) B' where "B \<rightarrow>\<^sub>\<sigma> B'" "X = Comp A B'"
  using assms by (cases rule: sig.cases) auto

subsection \<open>Commutation of a \<open>\<sigma>\<close>-step with the \<open>\<beta>\<close>-step\<close>

definition comm_c :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "comm_c M1 M2 \<longleftrightarrow> (\<exists>M1' M3. sig\<^sup>*\<^sup>* M1 M1' \<and> M1' \<rightarrow>\<^sub>c M3 \<and> sig\<^sup>*\<^sup>* M2 M3)"

definition comm :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "comm M1 M2 \<longleftrightarrow> (\<exists>M1' M3. sig\<^sup>*\<^sup>* M1 M1' \<and> M1' \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M2 M3)"

lemma comm_cI: "sig\<^sup>*\<^sup>* M1 M1' \<Longrightarrow> M1' \<rightarrow>\<^sub>c M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm_c M1 M2"
  unfolding comm_c_def by blast

lemma comm_c_direct: "M1 \<rightarrow>\<^sub>c M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm_c M1 M2"
  by (rule comm_cI[OF rtranclp.rtrancl_refl])

lemma commI: "sig\<^sup>*\<^sup>* M1 M1' \<Longrightarrow> M1' \<rightarrow>\<^sub>\<beta> M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm M1 M2"
  unfolding comm_def by blast

lemma comm_direct: "M1 \<rightarrow>\<^sub>\<beta> M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm M1 M2"
  by (rule commI[OF rtranclp.rtrancl_refl])

lemma comm_c_comm: "comm_c M1 M2 \<Longrightarrow> comm M1 M2"
  unfolding comm_c_def comm_def by (blast intro: beta_h.C)

text \<open>Pushing an environment through \<open>P \<circ> (\<lceil>x\<rceil>/y \<cdot> K)\<close>.\<close>

lemma push_name_env:
  "sig\<^sup>*\<^sup>* (Comp (Comp P (Extn (Nm x) y K)) L) (Comp P (Extn (Nm x) y (Comp K L)))"
proof -
  have 1: "Comp (Comp P (Extn (Nm x) y K)) L \<rightarrow>\<^sub>\<sigma> Comp P (Comp (Extn (Nm x) y K) L)"
    by (rule sig.Ass)
  have 2: "Comp P (Comp (Extn (Nm x) y K) L) \<rightarrow>\<^sub>\<sigma> Comp P (Extn (Comp (Nm x) L) y (Comp K L))"
    by (rule sig.CompR[OF sig.DExtn])
  have 3: "Comp P (Extn (Comp (Nm x) L) y (Comp K L)) \<rightarrow>\<^sub>\<sigma> Comp P (Extn (Nm x) y (Comp K L))"
    by (rule sig.CompR[OF sig.ExtnL[OF sig.ConstComp]])
  from 1 2 3 show ?thesis by (meson converse_rtranclp_into_rtranclp ss1)
qed

lemma push_name_env_id:
  "sig\<^sup>*\<^sup>* (Comp (Comp P (Extn (Nm x) y Id)) L) (Comp P (Extn (Nm x) y L))"
proof -
  have "sig\<^sup>*\<^sup>* (Comp (Comp P (Extn (Nm x) y Id)) L) (Comp P (Extn (Nm x) y (Comp Id L)))"
    by (rule push_name_env)
  moreover have "Comp P (Extn (Nm x) y (Comp Id L)) \<rightarrow>\<^sub>\<sigma> Comp P (Extn (Nm x) y L)"
    by (rule sig.CompR[OF sig.ExtnR[OF sig.IdL]])
  ultimately show ?thesis by (meson rtranclp.rtrancl_into_rtrancl)
qed

lemma beta_c_sig_commute: "M \<rightarrow>\<^sub>c M2 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> M1 \<Longrightarrow> comm_c M1 M2"
proof (induction arbitrary: M1 rule: beta_c.induct)
  case (Beta1 x B K N)
  from Beta1.prems show ?case
  proof (cases rule: sig_App_cases)
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>c Comp B (Extn (Nm y) x K)" using AppConst by (simp add: beta_c.VarClos)
    then show ?thesis using AppConst by (auto intro: comm_c_direct)
  next
    case (AppL P)
    from Clo_sig_inv[OF AppL(1)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam x B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using AppL
        by (auto intro!: comm_c_direct beta_c.Beta1 ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam x B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using AppL
        by (auto intro!: comm_c_direct beta_c.Beta1 ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam x B"
      then show ?thesis using AppL
        by (auto intro!: comm_c_direct beta_c.Beta2)
    qed
  next
    case (AppR N')
    then show ?thesis by (auto intro!: comm_c_direct beta_c.Beta1 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (Beta2 x B N)
  from Beta2.prems show ?case
  proof (cases rule: sig_App_cases)
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>c Comp B (Extn (Nm y) x Id)" using AppConst by (simp add: beta_c.VarLam)
    then show ?thesis using AppConst by (auto intro: comm_c_direct)
  next
    case (AppL P)
    then obtain B' where "P = Lam x B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using AppL by (auto intro!: comm_c_direct beta_c.Beta2 ss1 sig.CompL)
  next
    case (AppR N')
    then show ?thesis by (auto intro!: comm_c_direct beta_c.Beta2 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (VarClos x y B K)
  from VarClos.prems show ?case
  proof (cases rule: sig_Comp_cases)
    case (CompR P)
    from Clo_sig_inv[OF CompR(1)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam y B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using CompR
        by (auto intro!: comm_c_direct beta_c.VarClos ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam y B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using CompR
        by (auto intro!: comm_c_direct beta_c.VarClos ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam y B"
      then show ?thesis using CompR
        by (auto intro!: comm_c_direct beta_c.VarLam)
    qed
  qed auto
next
  case (VarLam x y B)
  from VarLam.prems show ?case
  proof (cases rule: sig_Comp_cases)
    case (CompR P)
    then obtain B' where "P = Lam y B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using CompR by (auto intro!: comm_c_direct beta_c.VarLam ss1 sig.CompL)
  qed auto
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: sig_App_cases)
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>c Comp (Var y) M'" using AppConst AppL.hyps by (simp add: beta_c.VarR)
    moreover have "App M' L \<rightarrow>\<^sub>\<sigma> Comp (Var y) M'" using AppConst by (simp add: sig.AppConst)
    ultimately show ?thesis by (auto intro: comm_c_direct ss1)
  next
    case (AppL M1a)
    from AppL.IH[OF AppL(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>c M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_c_def)
    show ?thesis
      using AppL(2) ss_AppL[OF a(1)] beta_c.AppL[OF a(2)] ss_AppL[OF a(3)]
      by (auto intro: comm_cI)
  next
    case (AppR L')
    then show ?thesis using AppL.hyps by (auto intro!: comm_c_direct beta_c.AppL ss1 sig.AppR)
  qed
next
  case (CompL M M' L)
  note hyp = CompL.hyps and IH = CompL.IH
  from CompL.prems show ?case
  proof (cases rule: sig_Comp_cases)
    case (Ass Ma Mb)
    from hyp have "Comp Ma Mb \<rightarrow>\<^sub>c M'" using Ass by simp
    then show ?thesis
    proof (cases rule: beta_c_Comp_cases)
      case (VarClos x y P K)
      have s: "M1 \<rightarrow>\<^sub>\<sigma> Comp (Var x) (Comp (Lam y P) (Comp K L))"
        using Ass VarClos by (auto intro: sig.CompR sig.Ass)
      have b: "Comp (Var x) (Comp (Lam y P) (Comp K L)) \<rightarrow>\<^sub>c Comp P (Extn (Nm x) y (Comp K L))"
        by (rule beta_c.VarClos)
      show ?thesis using ss1[OF s] b push_name_env[of P x y K L] VarClos
        by (auto intro: comm_cI)
    next
      case (VarLam x y P)
      have b: "M1 \<rightarrow>\<^sub>c Comp P (Extn (Nm x) y L)"
        using Ass VarLam by (auto intro: beta_c.VarClos)
      show ?thesis using b push_name_env_id[of P x y L] VarLam
        by (auto intro: comm_c_direct)
    next
      case (CompL Ma')
      then show ?thesis using Ass
        by (auto intro!: comm_c_direct beta_c.CompL ss1 sig.Ass)
    next
      case (VarR x Mb')
      then show ?thesis using Ass
        by (auto intro!: comm_c_direct beta_c.VarR beta_c.CompL ss1 sig.Ass)
    qed
  next
    case IdL
    then show ?thesis using hyp by simp
  next
    case IdR
    have "sig\<^sup>*\<^sup>* (Comp M' Id) M'" by (rule ss1[OF sig.IdR])
    then show ?thesis using IdR hyp by (auto intro: comm_c_direct)
  next
    case (DExtn L0 x0 M0)
    then show ?thesis using hyp by simp
  next
    case (VarRef x0 M0 N0)
    then show ?thesis using hyp by simp
  next
    case (VarSkip x0 y0 M0 N0)
    then show ?thesis using hyp by simp
  next
    case (ConstComp x0)
    then show ?thesis using hyp by simp
  next
    case (DApp P Q)
    from hyp have "App P Q \<rightarrow>\<^sub>c M'" using DApp by simp
    then show ?thesis
    proof (cases rule: beta_c_App_cases)
      case (Beta1 x B K)
      have s1: "sig\<^sup>*\<^sup>* M1 (App (Comp (Lam x B) (Comp K L)) (Comp Q L))"
        using DApp Beta1 by (auto intro!: ss1 sig.AppL sig.Ass)
      have b: "App (Comp (Lam x B) (Comp K L)) (Comp Q L) \<rightarrow>\<^sub>c Comp B (Extn (Comp Q L) x (Comp K L))"
        by (rule beta_c.Beta1)
      have s2: "sig\<^sup>*\<^sup>* (Comp (Comp B (Extn Q x K)) L) (Comp B (Extn (Comp Q L) x (Comp K L)))"
      proof -
        have "Comp (Comp B (Extn Q x K)) L \<rightarrow>\<^sub>\<sigma> Comp B (Comp (Extn Q x K) L)" by (rule sig.Ass)
        moreover have "Comp B (Comp (Extn Q x K) L) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x (Comp K L))"
          by (rule sig.CompR[OF sig.DExtn])
        ultimately show ?thesis by (rule ss2)
      qed
      show ?thesis using s1 b s2 Beta1 DApp by (auto intro: comm_cI)
    next
      case (Beta2 x B)
      have b: "M1 \<rightarrow>\<^sub>c Comp B (Extn (Comp Q L) x L)"
        using DApp Beta2 by (auto intro: beta_c.Beta1)
      have s2: "sig\<^sup>*\<^sup>* (Comp (Comp B (Extn Q x Id)) L) (Comp B (Extn (Comp Q L) x L))"
      proof -
        have 1: "Comp (Comp B (Extn Q x Id)) L \<rightarrow>\<^sub>\<sigma> Comp B (Comp (Extn Q x Id) L)" by (rule sig.Ass)
        have 2: "Comp B (Comp (Extn Q x Id) L) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x (Comp Id L))"
          by (rule sig.CompR[OF sig.DExtn])
        have 3: "Comp B (Extn (Comp Q L) x (Comp Id L)) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x L)"
          by (rule sig.CompR[OF sig.ExtnR[OF sig.IdL]])
        from 1 2 3 show ?thesis by (meson converse_rtranclp_into_rtranclp ss1)
      qed
      show ?thesis using b s2 Beta2 DApp by (auto intro: comm_c_direct)
    next
      case (AppL P')
      then show ?thesis using DApp
        by (auto intro!: comm_c_direct beta_c.AppL beta_c.CompL ss1 sig.DApp)
    qed
  next
    case (CompL M1a)
    from IH[OF CompL(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>c M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_c_def)
    show ?thesis
      using CompL(2) ss_CompL[OF a(1)] beta_c.CompL[OF a(2)] ss_CompL[OF a(3)]
      by (auto intro: comm_cI)
  next
    case (CompR L')
    then show ?thesis using hyp by (auto intro!: comm_c_direct beta_c.CompL ss1 sig.CompR)
  qed
next
  case (VarR M M' x)
  note hyp = VarR.hyps and IH = VarR.IH
  from VarR.prems show ?case
  proof (cases rule: sig_Comp_cases)
    case (CompR M1a)
    from IH[OF CompR(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>c M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_c_def)
    show ?thesis
      using CompR(2) ss_CompR[OF a(1)] beta_c.VarR[OF a(2)] ss_CompR[OF a(3)]
      by (auto intro: comm_cI)
  next
    case (IdR) then show ?thesis using hyp by simp
  next
    case (VarRef x0 M0 N0) then show ?thesis using hyp by simp
  next
    case (VarSkip x0 y0 M0 N0) then show ?thesis using hyp by simp
  qed auto
qed

lemma beta_h_sig_commute: "M \<rightarrow>\<^sub>\<beta> M2 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> M1 \<Longrightarrow> comm M1 M2"
proof (induction arbitrary: M1 rule: beta_h.induct)
  case (C M N)
  then show ?case using beta_c_sig_commute comm_c_comm by blast
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: sig_App_cases)
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>\<beta> Comp (Var y) M'" using AppConst AppL.hyps by (simp add: beta_h.VarR)
    moreover have "App M' L \<rightarrow>\<^sub>\<sigma> Comp (Var y) M'" using AppConst by (simp add: sig.AppConst)
    ultimately show ?thesis by (auto intro: comm_direct ss1)
  next
    case (AppL M1a)
    from AppL.IH[OF AppL(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using AppL(2) ss_AppL[OF a(1)] beta_h.AppL[OF a(2)] ss_AppL[OF a(3)]
      by (auto intro: commI)
  next
    case (AppR L')
    then show ?thesis using AppL.hyps by (auto intro!: comm_direct beta_h.AppL ss1 sig.AppR)
  qed
next
  case (VarR M M' x)
  note hyp = VarR.hyps and IH = VarR.IH
  from VarR.prems show ?case
  proof (cases rule: sig_Comp_cases)
    case (CompR M1a)
    from IH[OF CompR(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using CompR(2) ss_CompR[OF a(1)] beta_h.VarR[OF a(2)] ss_CompR[OF a(3)]
      by (auto intro: commI)
  next
    case (IdR) then show ?thesis using hyp by simp
  next
    case (VarRef x0 M0 N0) then show ?thesis using hyp by simp
  next
    case (VarSkip x0 y0 M0 N0) then show ?thesis using hyp by simp
  qed auto
next
  case (ArgV V M M')
  note hyp = ArgV.hyps and IH = ArgV.IH
  from ArgV.prems show ?case
  proof (cases rule: sig_App_cases)
    case (AppConst y)
    then show ?thesis using hyp by simp
  next
    case (AppL V')
    have "envh V'" using envh_sig[OF hyp(1) AppL(1)] .
    then have "M1 \<rightarrow>\<^sub>\<beta> App V' M'" using AppL hyp by (simp add: beta_h.ArgV)
    moreover have "sig\<^sup>*\<^sup>* (App V M') (App V' M')" using AppL by (auto intro: ss1 sig.AppL)
    ultimately show ?thesis by (auto intro: comm_direct)
  next
    case (AppR M1a)
    from IH[OF AppR(1)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using AppR(2) ss_AppR[OF a(1)] beta_h.ArgV[OF hyp(1) a(2)] ss_AppR[OF a(3)]
      by (auto intro: commI)
  qed
qed

subsection \<open>\<open>\<sigma>\<close>-normal forms\<close>

lemma sig_steps_tlength: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> tlength N \<le> tlength M"
  by (induction rule: rtranclp_induct) (auto dest: sig_tlength_decrease)

definition snf :: "trm \<Rightarrow> trm" where
  "snf M = (SOME N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N)"

lemma snf_spec: "sig\<^sup>*\<^sup>* M (snf M) \<and> sig_normal (snf M)"
  unfolding snf_def using sig_nf by (rule someI_ex)

lemma snf_unique: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig_normal N \<Longrightarrow> snf M = N"
proof -
  assume r: "sig\<^sup>*\<^sup>* M N" and n: "sig_normal N"
  obtain P where p1: "sig\<^sup>*\<^sup>* (snf M) P" and p2: "sig\<^sup>*\<^sup>* N P"
    using sig_confluent[OF snf_spec[THEN conjunct1] r] by blast
  have "P = snf M" using normal_rtranclp[OF snf_spec[THEN conjunct2] p1] .
  moreover have "P = N" using normal_rtranclp[OF n p2] .
  ultimately show ?thesis by simp
qed

lemma snf_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> snf M' = snf M"
proof -
  assume r: "sig\<^sup>*\<^sup>* M M'"
  have "sig\<^sup>*\<^sup>* M (snf M')" using r snf_spec[of M'] by (meson rtranclp_trans)
  then have "snf M = snf M'" using snf_unique snf_spec by blast
  then show ?thesis by simp
qed

lemma snf_beta:
  "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> \<exists>M3. snf M \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M' M3"
proof (induction "tlength M" arbitrary: M M' rule: less_induct)
  case less
  show ?case
  proof (cases "sig_normal M")
    case True
    then have "snf M = M" using snf_unique by blast
    then show ?thesis using less.prems by auto
  next
    case False
    then obtain M1 where s: "M \<rightarrow>\<^sub>\<sigma> M1" by (auto simp: normal_def)
    from beta_h_sig_commute[OF less.prems s] obtain M1' M3' where
      a: "sig\<^sup>*\<^sup>* M1 M1'" "M1' \<rightarrow>\<^sub>\<beta> M3'" "sig\<^sup>*\<^sup>* M' M3'"
      by (auto simp: comm_def)
    have lt: "tlength M1' < tlength M"
      using sig_tlength_decrease[OF s] sig_steps_tlength[OF a(1)] by simp
    from less.hyps[OF lt a(2)] obtain M3 where b: "snf M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M3' M3"
      by blast
    have "snf M1' = snf M"
      using snf_steps[OF converse_rtranclp_into_rtranclp[OF s a(1)]] .
    then show ?thesis using b a(3) by (metis rtranclp_trans)
  qed
qed

subsection \<open>The deterministic chain\<close>

inductive cd :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> bool" where
  cd0: "normal beta_h (snf M) \<Longrightarrow> cd M 0 (snf M)"
| cdS: "snf M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> cd N n E \<Longrightarrow> cd M (Suc n) E"

lemma cd_snf: "cd A n E \<Longrightarrow> snf A = snf B \<Longrightarrow> cd B n E"
proof (cases rule: cd.cases)
  assume "cd A n E" "snf A = snf B"
  {
    assume "normal beta_h (snf A)" "n = 0" "E = snf A"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cd0)
  }
  {
    fix N m assume "n = Suc m" "snf A \<rightarrow>\<^sub>\<beta> N" "cd N m E"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cdS)
  }
qed

lemma cd_det: "cd M n E \<Longrightarrow> cd M n' E' \<Longrightarrow> n = n' \<and> E = E'"
proof (induction arbitrary: n' E' rule: cd.induct)
  case (cd0 M)
  from cd0.prems show ?case
    by (cases rule: cd.cases) (use cd0.hyps in \<open>auto simp: normal_def\<close>)
next
  case (cdS M N n E)
  note h = cdS.hyps(1) and IH = cdS.IH
  from cdS.prems show ?case
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using h by (auto simp: normal_def)
  next
    case (cdS N' m)
    then have "N' = N" using beta_h_det h by blast
    then show ?thesis using IH cdS by blast
  qed
qed

lemma cd_back_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_fwd_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_back_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M (Suc n) E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M' n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  have "cd M3 n E" using cd_snf[OF c] snf_steps[OF m3(2)] by simp
  then show ?thesis by (rule cdS[OF m3(1)])
qed

lemma cd_fwd_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M n E \<Longrightarrow> \<exists>m. n = Suc m \<and> cd M' m E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  from c show ?thesis
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using m3(1) by (auto simp: normal_def)
  next
    case (cdS N m)
    then have "N = M3" using beta_h_det m3(1) by blast
    then have "cd M3 m E" using cdS by simp
    then have "cd M' m E" using cd_snf snf_steps[OF m3(2)] by metis
    then show ?thesis using cdS by blast
  qed
qed

lemma WHNF_cd: "WHNF N \<Longrightarrow> cd N 0 N"
proof -
  assume n: "WHNF N"
  have sn: "snf N = N" using snf_unique[OF rtranclp.rtrancl_refl WHNF_imp_sig_normal[OF n]] .
  have "normal beta_h N" using n by (auto simp: normal_def wh_def)
  then show ?thesis using cd0[of N] sn by simp
qed

lemma steps_cd: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> WHNF N \<Longrightarrow> \<exists>k. cd M k N"
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case using WHNF_cd by blast
next
  case (step M M')
  then obtain k where c: "cd M' k N" by blast
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: wh_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_back_sig c by blast
  next
    case 2 then show ?thesis using cd_back_beta c by blast
  qed
qed

lemma cd_WHSN: "cd M n E \<Longrightarrow> WHSN M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. cd M n E \<Longrightarrow> WHSN M"
  proof -
    fix M
    show "cd M n E \<Longrightarrow> WHSN M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>w\<^sub>h N"
        then consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>\<beta> N" by (auto simp: wh_def)
        then show "WHSN N"
        proof cases
          case 1
          have "cd N n E" using cd_fwd_sig[OF 1 less.prems] .
          moreover have "tlength N < tlength M" using sig_tlength_decrease[OF 1] .
          ultimately show ?thesis using less.hyps by blast
        next
          case 2
          then obtain m where "n = Suc m" "cd N m E" using cd_fwd_beta less.prems by blast
          then show ?thesis using IHn by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma cd_reach_end: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N' \<Longrightarrow> cd M n E \<Longrightarrow> WHNF N' \<Longrightarrow> N' = E"
proof (induction arbitrary: n rule: converse_rtranclp_induct)
  case base
  then show ?case using WHNF_cd cd_det by blast
next
  case (step M M')
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: wh_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_fwd_sig step.prems step.IH by blast
  next
    case 2 then show ?thesis using cd_fwd_beta step.prems step.IH by blast
  qed
qed

theorem CFWHN_imp_CFWHSN: "CFWHN M \<Longrightarrow> CFWHSN M"
proof -
  assume "CFWHN M"
  then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" and c: "\<not> clash N"
    by (auto simp: CFWHN_def)
  from steps_cd[OF r n] obtain k where cdM: "cd M k N" by blast
  have "WHSN M" by (rule cd_WHSN[OF cdM])
  moreover have "\<not> clash N'" if "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N'" "WHNF N'" for N'
    using cd_reach_end[OF that(1) cdM that(2)] c by simp
  ultimately show "CFWHSN M" by (auto simp: CFWHSN_def)
qed

theorem WHNF_unique: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N1 \<Longrightarrow> WHNF N1 \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N2 \<Longrightarrow> WHNF N2 \<Longrightarrow> N1 = N2"
proof -
  assume r1: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N1" and n1: "WHNF N1" and r2: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N2" and n2: "WHNF N2"
  from steps_cd[OF r1 n1] obtain k where "cd M k N1" by blast
  then show ?thesis using cd_reach_end[OF r2 _ n2] by metis
qed


theorem CFWHSN_imp_CFWHN: "CFWHSN M \<Longrightarrow> CFWHN M"
proof -
  assume h: "CFWHSN M"
  then have sn: "WHSN M" by (simp add: CFWHSN_def)
  have "\<exists>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<and> WHNF N"
    using sn
  proof (induction rule: SN_at_induct)
    case (step a)
    show ?case
    proof (cases "WHNF a")
      case True then show ?thesis by blast
    next
      case False
      then obtain b where "a \<rightarrow>\<^sub>w\<^sub>h b" by (auto simp: normal_def)
      with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
  then show ?thesis using h by (auto simp: CFWHSN_def CFWHN_def)
qed

subsection \<open>Forward closure (used by soundness)\<close>

lemma CFWHN_fwd: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> CFWHN M \<Longrightarrow> CFWHN M'"
proof -
  assume s: "M \<rightarrow>\<^sub>w\<^sub>h M'" and c: "CFWHN M"
  have h: "CFWHSN M" by (rule CFWHN_imp_CFWHSN[OF c])
  have "WHSN M'" using h s by (auto simp: CFWHSN_def intro: SN_at_step)
  moreover have "\<not> clash N" if "M' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" "WHNF N" for N
    using h s that by (auto simp: CFWHSN_def intro: converse_rtranclp_into_rtranclp)
  ultimately have "CFWHSN M'" by (simp add: CFWHSN_def)
  then show ?thesis by (rule CFWHSN_imp_CFWHN)
qed

lemma Nm_WHNF: "WHNF (Nm x)"
  by (auto simp: normal_def wh_def)

lemma Nm_fwd: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x \<Longrightarrow> M' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x"
proof -
  assume s: "M \<rightarrow>\<^sub>w\<^sub>h M'" and r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x"
  have cd: "\<exists>k. cd M k (Nm x)" by (rule steps_cd[OF r Nm_WHNF])
  then have "WHSN M" using cd_WHSN by blast
  then have "WHSN M'" using s by (rule SN_at_step)
  then have "\<exists>N. M' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<and> WHNF N"
  proof (induction rule: SN_at_induct)
    case (step a)
    show ?case
    proof (cases "WHNF a")
      case True then show ?thesis by blast
    next
      case False
      then obtain b where "a \<rightarrow>\<^sub>w\<^sub>h b" by (auto simp: normal_def)
      with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
  then obtain N where r': "M' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" by blast
  have "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" using s r' by (rule converse_rtranclp_into_rtranclp)
  then have "N = Nm x" using WHNF_unique[OF _ n r Nm_WHNF] by blast
  then show ?thesis using r' by simp
qed

end
