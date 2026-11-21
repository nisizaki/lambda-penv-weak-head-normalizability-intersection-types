theory WHNF_Classes
  imports Reduction
begin

section \<open>Weak-head normal forms: neutral, value, clash\<close>

text \<open>
  Arguments \<open>N\<close>, bodies and environments below are \<open>\<sigma>\<close>-normal; an argument
  is never a quoted name (otherwise \<open>AppConst\<close> applies).
\<close>

inductive neu :: "trm \<Rightarrow> bool" where
  NVar: "neu (Var x)"
| NApp: "neu M \<Longrightarrow> sig_normal N \<Longrightarrow> (\<forall>y. N \<noteq> Nm y) \<Longrightarrow> neu (App M N)"
| NComp: "neu M \<Longrightarrow> neu (Comp (Var x) M)"

inductive val :: "trm \<Rightarrow> bool" where
  VLam: "sig_normal M \<Longrightarrow> val (Lam x M)"
| VClo: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> L \<noteq> Id \<Longrightarrow> val (Comp (Lam x M) L)"
| VId: "val Id"
| VExtn: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> val (Extn M x L)"
| VNm: "val (Nm x)"

inductive clash :: "trm \<Rightarrow> bool" where
  CNmApp: "sig_normal N \<Longrightarrow> (\<forall>y. N \<noteq> Nm y) \<Longrightarrow> clash (App (Nm x) N)"
| CEnv: "envh V \<Longrightarrow> sig_normal V \<Longrightarrow> WHNF W \<Longrightarrow> (\<forall>y. W \<noteq> Nm y) \<Longrightarrow> clash (App V W)"
| CApp: "clash M \<Longrightarrow> sig_normal N \<Longrightarrow> (\<forall>y. N \<noteq> Nm y) \<Longrightarrow> clash (App M N)"
| CVarNm: "clash (Comp (Var x) (Nm y))"
| CComp: "clash M \<Longrightarrow> clash (Comp (Var x) M)"

subsection \<open>WHNF of each constructor\<close>

lemma WHNF_Var: "WHNF (Var x)"
  by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)

lemma WHNF_Id: "WHNF Id"
  by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)

lemma WHNF_Nm: "WHNF (Nm x)"
  by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)

lemma WHNF_Lam_iff: "WHNF (Lam x M) \<longleftrightarrow> sig_normal M"
proof
  assume "WHNF (Lam x M)"
  then show "sig_normal M"
    by (auto simp: normal_def wh_def intro: sig.Lam)
next
  assume "sig_normal M"
  then show "WHNF (Lam x M)"
    by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)
qed

lemma WHNF_Extn_iff: "WHNF (Extn M x L) \<longleftrightarrow> sig_normal M \<and> sig_normal L"
proof
  assume "WHNF (Extn M x L)"
  then show "sig_normal M \<and> sig_normal L"
    by (auto simp: normal_def wh_def intro: sig.ExtnL sig.ExtnR)
next
  assume "sig_normal M \<and> sig_normal L"
  then show "WHNF (Extn M x L)"
    by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)
qed

lemma wh_CompL_nf:
  assumes "WHNF (Comp M N)" shows "WHNF M"
proof (rule normalI)
  fix M'
  show "\<not> M \<rightarrow>\<^sub>w\<^sub>h M'"
  proof
    assume "M \<rightarrow>\<^sub>w\<^sub>h M'"
    then consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: wh_def)
    then show False
    proof cases
      case 1
      then have "Comp M N \<rightarrow>\<^sub>\<sigma> Comp M' N" by (rule sig.CompL)
      then show False using assms by (auto simp: normal_def wh_def)
    next
      case 2
      then show False
      proof (cases rule: beta_h.cases)
        case (C)
        then have "Comp M N \<rightarrow>\<^sub>\<beta> Comp M' N"
          by (blast intro: beta_c.CompL beta_h.C)
        then show False using assms by (auto simp: normal_def wh_def)
      next
        case (AppL P N' L)
        then have "Comp M N \<rightarrow>\<^sub>\<sigma> App (Comp P N) (Comp L N)"
          by (simp add: sig.DApp)
        then show False using assms by (auto simp: normal_def wh_def)
      next
        case (VarR P N' x)
        then have "Comp M N \<rightarrow>\<^sub>\<sigma> Comp (Var x) (Comp P N)" using sig.Ass by simp
        then show False using assms by (auto simp: normal_def wh_def)
      next
        case (ArgV V P N')
        then have "Comp M N \<rightarrow>\<^sub>\<sigma> App (Comp V N) (Comp P N)"
          by (simp add: sig.DApp)
        then show False using assms by (auto simp: normal_def wh_def)
      qed
    qed
  qed
qed

lemma WHNF_App_iff:
  "WHNF (App M N) \<longleftrightarrow>
     WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)
     \<and> (\<forall>y. N \<noteq> Nm y) \<and> (envh M \<longrightarrow> WHNF N)"
proof
  assume nf: "WHNF (App M N)"
  have "WHNF M"
    using nf by (auto simp: normal_def dest: wh_AppL)
  moreover have "sig_normal N"
    using nf by (auto simp: normal_def wh_def intro: sig.AppR)
  moreover have "M \<noteq> Lam x P" for x P
    using nf by (auto simp: normal_def wh_def intro: beta_h.C beta_c.Beta2)
  moreover have "M \<noteq> Comp (Lam x P) L" for x P L
    using nf by (auto simp: normal_def wh_def intro: beta_h.C beta_c.Beta1)
  moreover have "N \<noteq> Nm y" for y
    using nf by (auto simp: normal_def wh_def intro: sig.AppConst)
  moreover have "WHNF N" if "envh M"
  proof (rule normalI)
    fix N' show "\<not> N \<rightarrow>\<^sub>w\<^sub>h N'"
      using nf that wh_ArgV by (auto simp: normal_def)
  qed
  ultimately show "WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)
     \<and> (\<forall>y. N \<noteq> Nm y) \<and> (envh M \<longrightarrow> WHNF N)"
    by blast
next
  assume a: "WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)
     \<and> (\<forall>y. N \<noteq> Nm y) \<and> (envh M \<longrightarrow> WHNF N)"
  show "WHNF (App M N)"
  proof (rule normalI)
    fix Q
    show "\<not> App M N \<rightarrow>\<^sub>w\<^sub>h Q"
    proof
      assume "App M N \<rightarrow>\<^sub>w\<^sub>h Q"
      then consider "App M N \<rightarrow>\<^sub>\<sigma> Q" | "App M N \<rightarrow>\<^sub>\<beta> Q"
        by (auto simp: wh_def)
      then show False
      proof cases
        case 1
        then show False
          using a by (cases rule: sig.cases) (auto simp: normal_def wh_def)
      next
        case 2
        then show False
        proof (cases rule: beta_h_App_cases)
          case C
          then show False
          proof (cases rule: beta_c_App_cases)
            case (Beta1 x P K) then show False using a by blast
          next
            case (Beta2 x P) then show False using a by blast
          next
            case (AppL M') then show False
              using a beta_c_imp_beta_h by (auto simp: normal_def wh_def)
          qed
        next
          case (AppL M') then show False using a by (auto simp: normal_def wh_def)
        next
          case (ArgV L') then show False using a by (auto simp: normal_def wh_def)
        qed
      qed
    qed
  qed
qed

text \<open>No root redex at a composition.\<close>

definition comp_root_ok :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "comp_root_ok M N \<longleftrightarrow>
     (\<forall>L K. M \<noteq> Comp L K) \<and> M \<noteq> Id \<and> N \<noteq> Id \<and> (\<forall>L x K. M \<noteq> Extn L x K) \<and>
     (\<forall>M1 M2. M \<noteq> App M1 M2) \<and> (\<forall>x L y K. \<not> (M = Var x \<and> N = Extn L y K)) \<and>
     (\<forall>x. M \<noteq> Nm x) \<and>
     (\<forall>x y P. \<not> (M = Var x \<and> N = Lam y P)) \<and>
     (\<forall>x y P K. \<not> (M = Var x \<and> N = Comp (Lam y P) K))"

lemma WHNF_Comp_iff:
  "WHNF (Comp M N) \<longleftrightarrow>
     WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
proof
  assume nf: "WHNF (Comp M N)"
  have "WHNF M"
    using nf by (rule wh_CompL_nf)
  moreover have "sig_normal N"
    using nf by (auto simp: normal_def wh_def intro: sig.CompR)
  moreover have "comp_root_ok M N"
  proof -
    have r: "\<not> Comp M N \<rightarrow>\<^sub>\<sigma> Q" for Q
      using nf by (auto simp: normal_def wh_def)
    have rb: "\<not> Comp M N \<rightarrow>\<^sub>c Q" for Q
      using nf by (auto simp: normal_def wh_def intro: beta_h.C)
    show ?thesis
      unfolding comp_root_ok_def
    proof (intro conjI allI notI)
      fix L K assume "M = Comp L K" then show False using r[of "Comp L (Comp K N)"] sig.Ass by blast
    next
      assume "M = Id" then show False using r[of N] sig.IdL by blast
    next
      assume "N = Id" then show False using r[of M] sig.IdR by blast
    next
      fix L x K assume "M = Extn L x K"
      then show False using r[of "Extn (Comp L N) x (Comp K N)"] sig.DExtn by blast
    next
      fix M1 M2 assume "M = App M1 M2"
      then show False using r[of "App (Comp M1 N) (Comp M2 N)"] sig.DApp by blast
    next
      fix x L y K assume e: "M = Var x \<and> N = Extn L y K"
      show False
      proof (cases "y = x")
        case True
        then show False using e r[of L] sig.VarRef by blast
      next
        case False
        then show False using e r[of "Comp (Var x) K"] sig.VarSkip by blast
      qed
    next
      fix x assume "M = Nm x" then show False using r[of "Nm x"] sig.ConstComp by blast
    next
      fix x y P assume "M = Var x \<and> N = Lam y P"
      then show False using rb[of "Comp P (Extn (Nm x) y Id)"] beta_c.VarLam by blast
    next
      fix x y P K assume "M = Var x \<and> N = Comp (Lam y P) K"
      then show False using rb[of "Comp P (Extn (Nm x) y K)"] beta_c.VarClos by blast
    qed
  qed
  moreover have "WHNF N" if "M = Var x" for x
    using nf that by (auto simp: normal_def dest: wh_VarR)
  ultimately show "WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
    by blast
next
  assume a: "WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
  show "WHNF (Comp M N)"
  proof (rule normalI)
    fix Q
    show "\<not> Comp M N \<rightarrow>\<^sub>w\<^sub>h Q"
    proof
      assume "Comp M N \<rightarrow>\<^sub>w\<^sub>h Q"
      then consider "Comp M N \<rightarrow>\<^sub>\<sigma> Q" | "Comp M N \<rightarrow>\<^sub>\<beta> Q"
        by (auto simp: wh_def)
      then show False
      proof cases
        case 1
        then show False
          using a by (cases rule: sig.cases) (auto simp: normal_def wh_def comp_root_ok_def)
      next
        case 2
        then show False
        proof (cases rule: beta_h_Comp_cases)
          case C
          then show False
          proof (cases rule: beta_c_Comp_cases)
            case (VarClos x y P K) then show False using a by (auto simp: comp_root_ok_def)
          next
            case (VarLam x y P) then show False using a by (auto simp: comp_root_ok_def)
          next
            case (CompL M') then show False
              using a beta_c_imp_beta_h beta_h_imp_wh normalD by metis
          next
            case (VarR x L') then show False
              using a beta_c_imp_beta_h beta_h_imp_wh normalD by metis
          qed
        next
          case (VarR x L') then show False using a by (auto simp: normal_def wh_def)
        qed
      qed
    qed
  qed
qed

subsection \<open>Classification theorem\<close>

lemma neu_not_Id: "neu M \<Longrightarrow> M \<noteq> Id"
  by (auto elim: neu.cases)
lemma neu_not_Extn: "neu M \<Longrightarrow> M \<noteq> Extn L x K"
  by (auto elim: neu.cases)
lemma neu_not_Lam: "neu M \<Longrightarrow> M \<noteq> Lam x P"
  by (auto elim: neu.cases)
lemma neu_not_Clo: "neu M \<Longrightarrow> M \<noteq> Comp (Lam x P) L"
  by (auto elim: neu.cases)
lemma neu_not_Nm: "neu M \<Longrightarrow> M \<noteq> Nm x"
  by (auto elim: neu.cases)
lemma neu_not_envh: "neu M \<Longrightarrow> \<not> envh M"
  by (cases M) (auto dest: neu_not_Id neu_not_Extn)

lemma clash_not_Id: "clash M \<Longrightarrow> M \<noteq> Id"
  by (auto elim: clash.cases)
lemma clash_not_Extn: "clash M \<Longrightarrow> M \<noteq> Extn L x K"
  by (auto elim: clash.cases)
lemma clash_not_Lam: "clash M \<Longrightarrow> M \<noteq> Lam x P"
  by (auto elim: clash.cases)
lemma clash_not_Clo: "clash M \<Longrightarrow> M \<noteq> Comp (Lam x P) L"
  by (auto elim: clash.cases)
lemma clash_not_Nm: "clash M \<Longrightarrow> M \<noteq> Nm x"
  by (auto elim: clash.cases)
lemma clash_not_envh: "clash M \<Longrightarrow> \<not> envh M"
  by (cases M) (auto dest: clash_not_Id clash_not_Extn)

lemma sn_Nm: "sig_normal (Nm x)"
  by (rule WHNF_imp_sig_normal[OF WHNF_Nm])

lemma sn_Extn: "sig_normal (Extn M x L) \<Longrightarrow> sig_normal M \<and> sig_normal L"
  by (auto simp: normal_def intro: sig.ExtnL sig.ExtnR)

lemma envh_WHNF: "envh V \<Longrightarrow> sig_normal V \<Longrightarrow> WHNF V"
  by (cases V) (auto simp: WHNF_Id WHNF_Extn_iff dest: sn_Extn)

lemma val_Clo_WHNF:
  assumes "sig_normal P" "sig_normal L" "L \<noteq> Id"
  shows "WHNF (Comp (Lam x P) L)"
  using assms by (simp add: WHNF_Comp_iff WHNF_Lam_iff comp_root_ok_def)

lemma neu_WHNF: "neu M \<Longrightarrow> WHNF M"
proof (induction rule: neu.induct)
  case (NVar x)
  then show ?case by (rule WHNF_Var)
next
  case (NApp M N)
  then show ?case
    by (auto simp: WHNF_App_iff dest: neu_not_Lam neu_not_Clo neu_not_envh)
next
  case (NComp M x)
  then show ?case
    by (auto simp: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_imp_sig_normal
        dest: neu_not_Id neu_not_Extn neu_not_Nm neu_not_Lam neu_not_Clo)
qed

lemma val_WHNF: "val M \<Longrightarrow> WHNF M"
  by (induction rule: val.induct)
     (auto simp: WHNF_Lam_iff WHNF_Extn_iff WHNF_Id WHNF_Nm intro: val_Clo_WHNF)

lemma clash_WHNF: "clash M \<Longrightarrow> WHNF M"
proof (induction rule: clash.induct)
  case (CNmApp N x)
  then show ?case by (simp add: WHNF_App_iff WHNF_Nm)
next
  case (CEnv V W)
  then show ?case by (simp add: WHNF_App_iff envh_WHNF WHNF_imp_sig_normal)
  \<comment> \<open>envh V excludes Lam and closures\<close>
  (cases V; simp)
next
  case (CApp M N)
  then show ?case
    by (auto simp: WHNF_App_iff dest: clash_not_Lam clash_not_Clo clash_not_envh)
next
  case (CVarNm x y)
  then show ?case
    by (simp add: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_Nm sn_Nm)
next
  case (CComp M x)
  then show ?case
    by (auto simp: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_imp_sig_normal
        dest: clash_not_Id clash_not_Extn clash_not_Nm clash_not_Lam clash_not_Clo)
qed

lemma WHNF_cases: "WHNF M \<Longrightarrow> neu M \<or> val M \<or> clash M"
proof (induction M)
  case (Var x)
  then show ?case by (auto intro: neu.intros)
next
  case (Lam x M)
  then show ?case by (auto simp: WHNF_Lam_iff intro: val.intros)
next
  case (App M N)
  then have hM: "WHNF M" and hN: "sig_normal N"
    and nL: "\<And>x P. M \<noteq> Lam x P" and nC: "\<And>x P L. M \<noteq> Comp (Lam x P) L"
    and nN: "\<And>y. N \<noteq> Nm y" and hE: "envh M \<Longrightarrow> WHNF N"
    by (auto simp: WHNF_App_iff)
  from App.IH(1)[OF hM] consider "neu M" | "val M" | "clash M" by blast
  then show ?case
  proof cases
    case 1 then show ?thesis using hN nN by (auto intro: neu.intros)
  next
    case 2 then show ?thesis
    proof (cases rule: val.cases)
      case (VLam P x) then show ?thesis using nL by blast
    next
      case (VClo P L x) then show ?thesis using nC by blast
    next
      case VId
      then have e: "envh M" by simp
      have "clash (App M N)"
        by (rule clash.CEnv[OF e WHNF_imp_sig_normal[OF hM] hE[OF e] allI[OF nN]])
      then show ?thesis by blast
    next
      case (VExtn P L x)
      then have e: "envh M" by simp
      have "clash (App M N)"
        by (rule clash.CEnv[OF e WHNF_imp_sig_normal[OF hM] hE[OF e] allI[OF nN]])
      then show ?thesis by blast
    next
      case (VNm x) then show ?thesis using hN nN by (auto intro: clash.intros)
    qed
  next
    case 3 then show ?thesis using hN nN by (auto intro: clash.intros)
  qed
next
  case Id
  then show ?case by (auto intro: val.intros)
next
  case (Extn M x L)
  then show ?case by (auto simp: WHNF_Extn_iff intro: val.intros)
next
  case (Comp M N)
  then have hM: "WHNF M" and hN: "sig_normal N" and ok: "comp_root_ok M N"
    and hV: "\<And>x. M = Var x \<Longrightarrow> WHNF N"
    by (auto simp: WHNF_Comp_iff)
  show ?case
  proof (cases M)
    case (Var x)
    then have nN: "WHNF N" using hV by blast
    have nId: "N \<noteq> Id" and nE: "\<And>L y K. N \<noteq> Extn L y K"
      and nL: "\<And>y P. N \<noteq> Lam y P" and nC: "\<And>y P K. N \<noteq> Comp (Lam y P) K"
      using ok Var by (auto simp: comp_root_ok_def)
    from Comp.IH(2)[OF nN] consider "neu N" | "val N" | "clash N" by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis using Var by (auto intro: neu.intros)
    next
      case 2 then show ?thesis
      proof (cases rule: val.cases)
        case (VLam P y) then show ?thesis using nL by blast
      next
        case (VClo P L y) then show ?thesis using nC by blast
      next
        case VId then show ?thesis using nId by blast
      next
        case (VExtn P L y) then show ?thesis using nE by blast
      next
        case (VNm y) then show ?thesis using Var by (auto intro: clash.intros)
      qed
    next
      case 3 then show ?thesis using Var by (auto intro: clash.intros)
    qed
  next
    case (Lam x P)
    then show ?thesis
      using hM hN ok by (auto simp: WHNF_Lam_iff comp_root_ok_def intro: val.intros)
  qed (use ok in \<open>auto simp: comp_root_ok_def\<close>)
next
  case (Nm x)
  then show ?case by (auto intro: val.intros)
qed

theorem WHNF_iff_classes: "WHNF M \<longleftrightarrow> neu M \<or> val M \<or> clash M"
  using WHNF_cases neu_WHNF val_WHNF clash_WHNF by blast

definition CFWHN :: "trm \<Rightarrow> bool" where
  "CFWHN M \<longleftrightarrow> (\<exists>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<and> WHNF N \<and> \<not> clash N)"

definition CFWHSN :: "trm \<Rightarrow> bool" where
  "CFWHSN M \<longleftrightarrow> WHSN M \<and> (\<forall>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<longrightarrow> WHNF N \<longrightarrow> \<not> clash N)"

lemma val_not_clash: "val M \<Longrightarrow> \<not> clash M"
  by (induction rule: val.induct) (auto elim: clash.cases)

lemma neu_not_clash: "neu M \<Longrightarrow> \<not> clash M"
proof (induction rule: neu.induct)
  case (NVar x)
  then show ?case by (auto elim: clash.cases)
next
  case (NApp M N)
  show ?case
  proof
    assume "clash (App M N)"
    then show False
      using NApp neu_not_Nm neu_not_envh by (cases rule: clash.cases) auto
  qed
next
  case (NComp M x)
  show ?case
  proof
    assume "clash (Comp (Var x) M)"
    then show False
      using NComp neu_not_Nm by (cases rule: clash.cases) auto
  qed
qed

end
