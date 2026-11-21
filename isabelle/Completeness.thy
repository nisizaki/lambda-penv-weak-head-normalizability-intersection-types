theory Completeness
  imports Typing WHNF_Classes
begin

section \<open>Completeness: \<open>CFWHN M \<Longrightarrow> Typ M\<close>\<close>

subsection \<open>Replacing a subterm by one with at least the same typings\<close>

definition at_least :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "at_least M N \<longleftrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A)"

lemma rep_AppL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App N L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> App M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppL: "at_least M N \<Longrightarrow> at_least (App M L) (App N L)"
  unfolding at_least_def by (blast intro: rep_AppL_aux)

lemma rep_AppR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App L N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> App L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppR: "at_least M N \<Longrightarrow> at_least (App L M) (App L N)"
  unfolding at_least_def by (blast intro: rep_AppR_aux)

lemma rep_Lam_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Lam x N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Lam x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_Lam: "at_least M N \<Longrightarrow> at_least (Lam x M) (Lam x N)"
  unfolding at_least_def by (blast intro: rep_Lam_aux)

lemma rep_CompL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp N L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Comp M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompL: "at_least M N \<Longrightarrow> at_least (Comp M L) (Comp N L)"
  unfolding at_least_def by (blast intro: rep_CompL_aux)

lemma rep_CompR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp L N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Comp L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompR: "at_least M N \<Longrightarrow> at_least (Comp L M) (Comp L N)"
  unfolding at_least_def by (blast intro: rep_CompR_aux)

lemma rep_ExtnL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Extn N x L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Extn M x L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnL: "at_least M N \<Longrightarrow> at_least (Extn M x L) (Extn N x L)"
  unfolding at_least_def by (blast intro: rep_ExtnL_aux)

lemma rep_ExtnR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Extn L x N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Extn L x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnR: "at_least M N \<Longrightarrow> at_least (Extn L x M) (Extn L x N)"
  unfolding at_least_def by (blast intro: rep_ExtnR_aux)

subsection \<open>Root rules\<close>

lemma exp_Ass: "at_least (Comp (Comp L M) N) (Comp L (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp L (Comp M N) : A"
  then obtain D where 1: "C \<turnstile> Comp M N : D" and 2: "D \<turnstile> L : A"
    using gen_Comp by blast
  from 1 obtain D' where 3: "C \<turnstile> N : D'" and 4: "D' \<turnstile> M : D"
    using gen_Comp by blast
  from 4 2 have "D' \<turnstile> Comp L M : A" by (rule TComp)
  with 3 show "C \<turnstile> Comp (Comp L M) N : A" by (rule TComp)
qed

lemma exp_IdL: "at_least (Comp Id M) M"
  unfolding at_least_def by (blast intro: TComp TId)

lemma exp_IdR: "at_least (Comp M Id) M"
  unfolding at_least_def by (blast intro: TComp TId)

lemma exp_VarRef: "at_least (Comp (Var x) (Extn M x N)) M"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> M : A"
  then have "C \<turnstile> Extn M x N : Env ((x, A) # []) False"
    by (rule TExtn[OF _ typ_env_om])
  moreover have "Env [(x, A)] False \<turnstile> Var x : A"
    by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Extn M x N) : A"
    by (rule TComp)
qed

lemma exp_VarSkip: "x \<noteq> y \<Longrightarrow> at_least (Comp (Var y) (Extn M x N)) (Comp (Var y) N)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume xy: "x \<noteq> y" and "C \<turnstile> Comp (Var y) N : A"
  then obtain D where 1: "C \<turnstile> N : D" and 2: "D \<turnstile> Var y : A"
    using gen_Comp by blast
  from gen_Var[OF 2 refl] show "C \<turnstile> Comp (Var y) (Extn M x N) : A"
  proof
    assume "Om \<preceq> A"
    then show ?thesis by (blast intro: TSub TOm)
  next
    assume "\<exists>m ob B. D \<preceq> Env m ob \<and> map_of m y = Some B \<and> B \<preceq> A"
    then obtain m ob B where d: "D \<preceq> Env m ob" and l: "map_of m y = Some B" and b: "B \<preceq> A"
      by blast
    have "C \<turnstile> N : Env m ob" using 1 d by (rule TSub)
    then have "C \<turnstile> Extn M x N : Env ((x, Om) # m) ob" by (rule TExtn[OF TOm])
    moreover have "Env ((x, Om) # m) ob \<turnstile> Var y : A"
    proof -
      have "map_of ((x, Om) # m) y = Some B" using l xy by simp
      then have "Env ((x, Om) # m) ob \<turnstile> Var y : B" by (rule TVar[OF s_refl])
      then show ?thesis using b by (rule TSub)
    qed
    ultimately show ?thesis by (rule TComp)
  qed
qed

lemma exp_DExtn: "at_least (Comp (Extn L x M) N) (Extn (Comp L N) x (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Extn (Comp L N) x (Comp M N) : A"
  then obtain B m ob where 1: "C \<turnstile> Comp L N : B" and 2: "C \<turnstile> Comp M N : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> A"
    using gen_Extn by blast
  from 1 obtain D1 where a: "C \<turnstile> N : D1" "D1 \<turnstile> L : B" using gen_Comp by blast
  from 2 obtain D2 where b: "C \<turnstile> N : D2" "D2 \<turnstile> M : Env m ob" using gen_Comp by blast
  have "C \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "Inter D1 D2 \<turnstile> Extn L x M : Env ((x, B) # m) ob"
  proof (rule TExtn)
    show "Inter D1 D2 \<turnstile> L : B" by (rule narrowing[OF a(2) s_il])
    show "Inter D1 D2 \<turnstile> M : Env m ob" by (rule narrowing[OF b(2) s_ir])
  qed
  ultimately have "C \<turnstile> Comp (Extn L x M) N : Env ((x, B) # m) ob" by (rule TComp)
  from this s show "C \<turnstile> Comp (Extn L x M) N : A" by (rule TSub)
qed

lemma exp_DApp_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App (Comp M1 N) (Comp M2 N) \<Longrightarrow> C \<turnstile> Comp (App M1 M2) N : A"
proof (induction rule: hasty.induct)
  case (TApp C P A B Q)
  then have p: "C \<turnstile> Comp M1 N : Arr A B" and q: "C \<turnstile> Comp M2 N : A" by auto
  from p obtain D1 where a: "C \<turnstile> N : D1" "D1 \<turnstile> M1 : Arr A B" using gen_Comp by blast
  from q obtain D2 where b: "C \<turnstile> N : D2" "D2 \<turnstile> M2 : A" using gen_Comp by blast
  have "C \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "Inter D1 D2 \<turnstile> App M1 M2 : B"
  proof (rule hasty.TApp)
    show "Inter D1 D2 \<turnstile> M1 : Arr A B" by (rule narrowing[OF a(2) s_il])
    show "Inter D1 D2 \<turnstile> M2 : A" by (rule narrowing[OF b(2) s_ir])
  qed
  ultimately show ?case by (rule TComp)
qed (auto intro: hasty.intros)

lemma exp_DApp: "at_least (Comp (App M1 M2) N) (App (Comp M1 N) (Comp M2 N))"
  unfolding at_least_def using exp_DApp_aux by blast

lemma exp_Beta1: "at_least (App (Comp (Lam x M) L) N) (Comp M (Extn N x L))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn N x L) : A"
  then obtain D where 1: "C \<turnstile> Extn N x L : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> N : B" and l: "C \<turnstile> L : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have "Env ((x, B) # m) ob \<turnstile> M : A" using 2 s by (rule narrowing)
  then have "Env m ob \<turnstile> Lam x M : Arr B A" by (rule TLam[OF s_refl])
  with l have "C \<turnstile> Comp (Lam x M) L : Arr B A" by (rule TComp)
  with n show "C \<turnstile> App (Comp (Lam x M) L) N : A" by (blast intro: TApp)
qed

lemma exp_Beta2: "at_least (App (Lam x M) N) (Comp M (Extn N x Id))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn N x Id) : A"
  then obtain D where 1: "C \<turnstile> Extn N x Id : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> N : B" and l: "C \<turnstile> Id : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have c: "C \<preceq> Env m ob" using gen_Id[OF l refl] .
  have "Env ((x, B) # m) ob \<turnstile> M : A" using 2 s by (rule narrowing)
  then have "C \<turnstile> Lam x M : Arr B A" by (rule TLam[OF c])
  with n show "C \<turnstile> App (Lam x M) N : A" by (blast intro: TApp)
qed

lemma env_cons_sub:
  "B1 \<preceq> B2 \<Longrightarrow> Env ((y, B1) # m) ob \<preceq> Env ((y, B2) # m) ob"
proof (rule s_env)
  assume "B1 \<preceq> B2"
  then show "\<forall>z A'. map_of ((y, B2) # m) z = Some A' \<longrightarrow>
      (\<exists>A. map_of ((y, B1) # m) z = Some A \<and> A \<preceq> A')"
    by (auto intro: s_refl)
qed simp

lemma exp_AppConst: "at_least (App M (Nm x)) (Comp (Var x) M)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp (Var x) M : A"
  then obtain D where 1: "C \<turnstile> M : D" and 2: "D \<turnstile> Var x : A"
    using gen_Comp by blast
  from gen_Var[OF 2 refl] show "C \<turnstile> App M (Nm x) : A"
  proof
    assume "Om \<preceq> A"
    then show ?thesis by (blast intro: TSub TOm)
  next
    assume "\<exists>m ob B. D \<preceq> Env m ob \<and> map_of m x = Some B \<and> B \<preceq> A"
    then obtain m ob B where d: "D \<preceq> Env m ob" and l: "map_of m x = Some B" and b: "B \<preceq> A"
      by blast
    have "Env m ob \<preceq> Arr (QN x) B" by (rule s_envarr[OF l])
    moreover have "Arr (QN x) B \<preceq> Arr (QN x) A" by (rule s_arr[OF s_refl b])
    ultimately have "D \<preceq> Arr (QN x) A" using d by (blast intro: s_trans)
    with 1 have "C \<turnstile> M : Arr (QN x) A" by (rule TSub)
    then show ?thesis using TNm by (rule TApp)
  qed
qed

lemma exp_ConstComp: "at_least (Comp (Nm x) L) (Nm x)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Nm x : A"
  then have "QN x \<preceq> A" using gen_Nm by blast
  then have "Om \<turnstile> Nm x : A" by (rule TSub[OF TNm])
  moreover have "C \<turnstile> L : Om" by (rule TOm)
  ultimately show "C \<turnstile> Comp (Nm x) L : A" by (blast intro: TComp)
qed

lemma exp_VarLam: "at_least (Comp (Var x) (Lam y M)) (Comp M (Extn (Nm x) y Id))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn (Nm x) y Id) : A"
  then obtain D where 1: "C \<turnstile> Extn (Nm x) y Id : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> Nm x : B" and l: "C \<turnstile> Id : Env m ob"
    and s: "Env ((y, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have q: "QN x \<preceq> B" using gen_Nm[OF n refl] .
  have c: "C \<preceq> Env m ob" using gen_Id[OF l refl] .
  have "Env ((y, QN x) # m) ob \<preceq> D" using env_cons_sub[OF q] s by (rule s_trans)
  with 2 have "Env ((y, QN x) # m) ob \<turnstile> M : A" by (rule narrowing)
  then have "C \<turnstile> Lam y M : Arr (QN x) A" by (rule TLam[OF c])
  then have "C \<turnstile> Lam y M : Env [(x, A)] False" using s_arrenv by (rule TSub)
  moreover have "Env [(x, A)] False \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Lam y M) : A" by (rule TComp)
qed

lemma exp_VarClos:
  "at_least (Comp (Var x) (Comp (Lam y M) L)) (Comp M (Extn (Nm x) y L))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn (Nm x) y L) : A"
  then obtain D where 1: "C \<turnstile> Extn (Nm x) y L : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> Nm x : B" and l: "C \<turnstile> L : Env m ob"
    and s: "Env ((y, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have q: "QN x \<preceq> B" using gen_Nm[OF n refl] .
  have "Env ((y, QN x) # m) ob \<preceq> D" using env_cons_sub[OF q] s by (rule s_trans)
  with 2 have "Env ((y, QN x) # m) ob \<turnstile> M : A" by (rule narrowing)
  then have "Env m ob \<turnstile> Lam y M : Arr (QN x) A" by (rule TLam[OF s_refl])
  with l have "C \<turnstile> Comp (Lam y M) L : Arr (QN x) A" by (rule TComp)
  then have "C \<turnstile> Comp (Lam y M) L : Env [(x, A)] False" using s_arrenv by (rule TSub)
  moreover have "Env [(x, A)] False \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Comp (Lam y M) L) : A" by (rule TComp)
qed

subsection \<open>Subject expansion\<close>

lemma sig_expansion: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> at_least M N"
proof (induction rule: sig.induct)
  case (Ass L M N) show ?case by (rule exp_Ass)
next
  case (IdL M) show ?case by (rule exp_IdL)
next
  case (IdR M) show ?case by (rule exp_IdR)
next
  case (DExtn L x M N) show ?case by (rule exp_DExtn)
next
  case (VarRef x M N) show ?case by (rule exp_VarRef)
next
  case (VarSkip x y M N) then show ?case by (rule exp_VarSkip)
next
  case (DApp M1 M2 N) show ?case by (rule exp_DApp)
next
  case (AppConst M x) show ?case by (rule exp_AppConst)
next
  case (ConstComp x L) show ?case by (rule exp_ConstComp)
next
  case (AppL M N L) then show ?case by (blast intro: rep_AppL)
next
  case (AppR M N L) then show ?case by (blast intro: rep_AppR)
next
  case (Lam M N x) then show ?case by (blast intro: rep_Lam)
next
  case (CompL M N L) then show ?case by (blast intro: rep_CompL)
next
  case (CompR M N L) then show ?case by (blast intro: rep_CompR)
next
  case (ExtnL M N x L) then show ?case by (blast intro: rep_ExtnL)
next
  case (ExtnR M N L x) then show ?case by (blast intro: rep_ExtnR)
qed

lemma beta_c_expansion: "M \<rightarrow>\<^sub>c N \<Longrightarrow> at_least M N"
proof (induction rule: beta_c.induct)
  case (Beta1 x M L N) show ?case by (rule exp_Beta1)
next
  case (Beta2 x M N) show ?case by (rule exp_Beta2)
next
  case (VarClos x y M L) show ?case by (rule exp_VarClos)
next
  case (VarLam x y M) show ?case by (rule exp_VarLam)
next
  case (AppL M N L) then show ?case by (blast intro: rep_AppL)
next
  case (CompL M N L) then show ?case by (blast intro: rep_CompL)
next
  case (VarR M N x) then show ?case by (blast intro: rep_CompR)
qed

lemma beta_expansion: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> at_least M N"
proof (induction rule: beta_h.induct)
  case (C M N) then show ?case by (rule beta_c_expansion)
next
  case (AppL M N L) then show ?case by (blast intro: rep_AppL)
next
  case (VarR M N x) then show ?case by (blast intro: rep_CompR)
next
  case (ArgV V M N) then show ?case by (blast intro: rep_AppR)
qed

theorem subject_expansion: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> C \<turnstile> N : A \<Longrightarrow> C \<turnstile> M : A"
  using sig_expansion beta_expansion by (auto simp: wh_def at_least_def)

lemma subject_expansion_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> C \<turnstile> N : A \<Longrightarrow> C \<turnstile> M : A"
  by (induction rule: converse_rtranclp_induct) (auto intro: subject_expansion)

subsection \<open>Clash-free weak-head normal forms are typable\<close>

lemma neu_typable:
  "neu M \<Longrightarrow> qfree A \<Longrightarrow> \<exists>m. (\<forall>p \<in> set m. qfree (snd p)) \<and> Env m True \<turnstile> M : A"
proof (induction arbitrary: A rule: neu.induct)
  case (NVar x)
  have "Env [(x, A)] True \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  then show ?case using NVar by (auto intro: exI[of _ "[(x, A)]"])
next
  case (NApp M N)
  from NApp have "qfree (Arr Om A)" by simp
  then obtain m where q: "\<forall>p \<in> set m. qfree (snd p)" and "Env m True \<turnstile> M : Arr Om A"
    using NApp.IH by blast
  then have "Env m True \<turnstile> App M N : A" by (blast intro: TApp TOm)
  then show ?case using q by blast
next
  case (NComp M x)
  from NComp have "qfree (Env [(x, A)] True)" by simp
  then obtain m where q: "\<forall>p \<in> set m. qfree (snd p)" and "Env m True \<turnstile> M : Env [(x, A)] True"
    using NComp.IH by blast
  moreover have "Env [(x, A)] True \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  ultimately have "Env m True \<turnstile> Comp (Var x) M : A" by (blast intro: TComp)
  then show ?case using q by blast
qed

lemma lam_typable: "C \<preceq> Env m ob \<Longrightarrow> C \<turnstile> Lam x M : Arr Om Om"
  by (rule TLam) (auto intro: TOm)

lemma val_Typ: "val M \<Longrightarrow> Typ M"
proof (induction rule: val.induct)
  case (VLam M x)
  have "Env [] True \<turnstile> Lam x M : Arr Om Om" by (rule lam_typable[OF s_refl])
  then show ?case by (force simp: Typ_def)
next
  case (VClo M L x)
  have "Env [] True \<turnstile> L : Env [] False" by (rule typ_env_om)
  moreover have "Env [] False \<turnstile> Lam x M : Arr Om Om" by (rule lam_typable[OF s_refl])
  ultimately have "Env [] True \<turnstile> Comp (Lam x M) L : Arr Om Om" by (rule TComp)
  then show ?case by (force simp: Typ_def)
next
  case VId
  have "Env [] True \<turnstile> Id : Env [] True" by (rule TId)
  then show ?case by (force simp: Typ_def)
next
  case (VExtn M L x)
  have "Env [] True \<turnstile> Extn M x L : Env ((x, Om) # []) False"
    by (rule TExtn[OF TOm typ_env_om])
  then show ?case by (force simp: Typ_def)
next
  case (VNm x)
  have "Env [] True \<turnstile> Nm x : QN x" by (rule TNm)
  then show ?case by (force simp: Typ_def)
qed

lemma neu_Typ: "neu M \<Longrightarrow> Typ M"
proof -
  assume "neu M"
  then obtain m where "\<forall>p \<in> set m. qfree (snd p)" "Env m True \<turnstile> M : TV 0"
    using neu_typable[of M "TV 0"] by auto
  then show "Typ M" by (force simp: Typ_def)
qed

lemma cf_WHNF_Typ: "WHNF M \<Longrightarrow> \<not> clash M \<Longrightarrow> Typ M"
  using WHNF_iff_classes val_Typ neu_Typ by blast

theorem completeness: "CFWHN M \<Longrightarrow> Typ M"
proof -
  assume "CFWHN M"
  then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" and c: "\<not> clash N"
    by (auto simp: CFWHN_def)
  from cf_WHNF_Typ[OF n c] obtain m ob A where t: "Env m ob \<turnstile> N : A" and e: "ess A"
    and q: "\<forall>p \<in> set m. qfree (snd p)"
    by (auto simp: Typ_def)
  have "Env m ob \<turnstile> M : A" by (rule subject_expansion_steps[OF r t])
  with e q show "Typ M" by (auto simp: Typ_def)
qed

end
