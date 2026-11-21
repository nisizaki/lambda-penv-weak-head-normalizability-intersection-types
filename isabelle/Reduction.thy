theory Reduction
  imports Syntax ARS
begin

section \<open>Weak-head reduction of \<open>\<lambda>penv\<close>: full \<open>\<sigma>\<close> plus head \<open>\<beta>\<close>\<close>

text \<open>
  \<open>\<sigma>\<close> is the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> \<open>\<sigma>\<close> plus \<open>AppConst\<close> and \<open>ConstComp\<close>, closed under
  all congruences.  Head \<open>\<beta>\<close> has four root rules (\<open>Beta1\<close>, \<open>Beta2\<close>, and
  \<open>VarClos\<close>, \<open>VarLam\<close>, which are \<open>\<sigma>\<close>-rules in \<open>\<lambda>penv\<close>; decision D1).
  \<open>beta_c\<close> closes them under the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> head contexts
  \<open>C ::= [] | C N | C\<circ>L | x\<circ>C\<close>; \<open>beta\<close> additionally evaluates the
  argument of an environment head (\<open>ArgV\<close>, decision D2), but not below a
  pending composition (decision D3):
  \<open>E ::= C | E N | x\<circ>E | V E\<close>.
\<close>

inductive sig :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<sigma>" 50) where
  Ass: "Comp (Comp L M) N \<rightarrow>\<^sub>\<sigma> Comp L (Comp M N)"
| IdL: "Comp Id M \<rightarrow>\<^sub>\<sigma> M"
| IdR: "Comp M Id \<rightarrow>\<^sub>\<sigma> M"
| DExtn: "Comp (Extn L x M) N \<rightarrow>\<^sub>\<sigma> Extn (Comp L N) x (Comp M N)"
| VarRef: "Comp (Var x) (Extn M x N) \<rightarrow>\<^sub>\<sigma> M"
| VarSkip: "x \<noteq> y \<Longrightarrow> Comp (Var y) (Extn M x N) \<rightarrow>\<^sub>\<sigma> Comp (Var y) N"
| DApp: "Comp (App M1 M2) N \<rightarrow>\<^sub>\<sigma> App (Comp M1 N) (Comp M2 N)"
| AppConst: "App M (Nm x) \<rightarrow>\<^sub>\<sigma> Comp (Var x) M"
| ConstComp: "Comp (Nm x) L \<rightarrow>\<^sub>\<sigma> Nm x"
| AppL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<sigma> App N L"
| AppR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App L M \<rightarrow>\<^sub>\<sigma> App L N"
| Lam: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Lam x M \<rightarrow>\<^sub>\<sigma> Lam x N"
| CompL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>\<sigma> Comp N L"
| CompR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp L M \<rightarrow>\<^sub>\<sigma> Comp L N"
| ExtnL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn M x L \<rightarrow>\<^sub>\<sigma> Extn N x L"
| ExtnR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn L x M \<rightarrow>\<^sub>\<sigma> Extn L x N"

inductive beta_c :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>c" 50) where
  Beta1: "App (Comp (Lam x M) L) N \<rightarrow>\<^sub>c Comp M (Extn N x L)"
| Beta2: "App (Lam x M) N \<rightarrow>\<^sub>c Comp M (Extn N x Id)"
| VarClos: "Comp (Var x) (Comp (Lam y M) L) \<rightarrow>\<^sub>c Comp M (Extn (Nm x) y L)"
| VarLam: "Comp (Var x) (Lam y M) \<rightarrow>\<^sub>c Comp M (Extn (Nm x) y Id)"
| AppL: "M \<rightarrow>\<^sub>c N \<Longrightarrow> App M L \<rightarrow>\<^sub>c App N L"
| CompL: "M \<rightarrow>\<^sub>c N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>c Comp N L"
| VarR: "M \<rightarrow>\<^sub>c N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>c Comp (Var x) N"

inductive beta_h :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>" 50) where
  C: "M \<rightarrow>\<^sub>c N \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N"
| AppL: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<beta> App N L"
| VarR: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>\<beta> Comp (Var x) N"
| ArgV: "envh V \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> App V M \<rightarrow>\<^sub>\<beta> App V N"

definition wh :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>w\<^sub>h" 50) where
  "M \<rightarrow>\<^sub>w\<^sub>h N \<longleftrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<or> M \<rightarrow>\<^sub>\<beta> N"

abbreviation wh_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>w\<^sub>h\<^sup>*" 50) where
  "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<equiv> wh\<^sup>*\<^sup>* M N"

abbreviation WHNF :: "trm \<Rightarrow> bool" where "WHNF M \<equiv> normal wh M"
abbreviation WHSN :: "trm \<Rightarrow> bool" where "WHSN M \<equiv> SN_at wh M"
abbreviation sig_normal :: "trm \<Rightarrow> bool" where "sig_normal M \<equiv> normal sig M"

lemma sig_imp_wh: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N" by (simp add: wh_def)
lemma beta_h_imp_wh: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N" by (simp add: wh_def)
lemma beta_c_imp_beta_h: "M \<rightarrow>\<^sub>c N \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N" by (rule beta_h.C)

lemma wh_AppL: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> App M L \<rightarrow>\<^sub>w\<^sub>h App N L"
  by (auto simp: wh_def intro: sig.AppL beta_h.AppL)
lemma wh_VarR: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h Comp (Var x) N"
  by (auto simp: wh_def intro: sig.CompR beta_h.VarR)
lemma wh_ArgV: "envh V \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> App V M \<rightarrow>\<^sub>w\<^sub>h App V N"
  by (auto simp: wh_def intro: sig.AppR beta_h.ArgV)


subsection \<open>Basic facts on head \<open>\<beta>\<close>\<close>

lemma beta_c_no [simp]:
  "\<not> Var x \<rightarrow>\<^sub>c N" "\<not> Id \<rightarrow>\<^sub>c N" "\<not> Lam x M \<rightarrow>\<^sub>c N" "\<not> Extn M x L \<rightarrow>\<^sub>c N"
  "\<not> Nm x \<rightarrow>\<^sub>c N" "\<not> Comp (Lam x M) L \<rightarrow>\<^sub>c N"
  by (auto elim: beta_c.cases)

lemma beta_h_no [simp]:
  "\<not> Var x \<rightarrow>\<^sub>\<beta> N" "\<not> Id \<rightarrow>\<^sub>\<beta> N" "\<not> Lam x M \<rightarrow>\<^sub>\<beta> N" "\<not> Extn M x L \<rightarrow>\<^sub>\<beta> N"
  "\<not> Nm x \<rightarrow>\<^sub>\<beta> N" "\<not> Comp (Lam x M) L \<rightarrow>\<^sub>\<beta> N"
  by (auto elim: beta_h.cases)

lemma envh_no_beta: "envh V \<Longrightarrow> \<not> V \<rightarrow>\<^sub>\<beta> N"
  by (cases V) auto

lemma envh_no_beta_c: "envh V \<Longrightarrow> \<not> V \<rightarrow>\<^sub>c N"
  by (cases V) auto

lemma beta_c_App_cases:
  assumes "App M L \<rightarrow>\<^sub>c X"
  obtains (Beta1) x P K where "M = Comp (Lam x P) K" "X = Comp P (Extn L x K)"
  | (Beta2) x P where "M = Lam x P" "X = Comp P (Extn L x Id)"
  | (AppL) M' where "M \<rightarrow>\<^sub>c M'" "X = App M' L"
  using assms by (cases rule: beta_c.cases) auto

lemma beta_c_Comp_cases:
  assumes "Comp M L \<rightarrow>\<^sub>c X"
  obtains (VarClos) x y P K where "M = Var x" "L = Comp (Lam y P) K" "X = Comp P (Extn (Nm x) y K)"
  | (VarLam) x y P where "M = Var x" "L = Lam y P" "X = Comp P (Extn (Nm x) y Id)"
  | (CompL) M' where "M \<rightarrow>\<^sub>c M'" "X = Comp M' L"
  | (VarR) x L' where "M = Var x" "L \<rightarrow>\<^sub>c L'" "X = Comp M L'"
  using assms by (cases rule: beta_c.cases) auto

lemma beta_h_App_cases:
  assumes "App M L \<rightarrow>\<^sub>\<beta> X"
  obtains (C) "App M L \<rightarrow>\<^sub>c X"
  | (AppL) M' where "M \<rightarrow>\<^sub>\<beta> M'" "X = App M' L"
  | (ArgV) L' where "envh M" "L \<rightarrow>\<^sub>\<beta> L'" "X = App M L'"
  using assms by (cases rule: beta_h.cases) auto

lemma beta_h_Comp_cases:
  assumes "Comp M L \<rightarrow>\<^sub>\<beta> X"
  obtains (C) "Comp M L \<rightarrow>\<^sub>c X"
  | (VarR) x L' where "M = Var x" "L \<rightarrow>\<^sub>\<beta> L'" "X = Comp M L'"
  using assms by (cases rule: beta_h.cases) auto

lemma beta_c_det: "M \<rightarrow>\<^sub>c N1 \<Longrightarrow> M \<rightarrow>\<^sub>c N2 \<Longrightarrow> N1 = N2"
proof (induction arbitrary: N2 rule: beta_c.induct)
  case (Beta1 x M L N) from Beta1.prems show ?case by (cases rule: beta_c_App_cases) auto
next
  case (Beta2 x M N) from Beta2.prems show ?case by (cases rule: beta_c_App_cases) auto
next
  case (VarClos x y M L) from VarClos.prems show ?case by (cases rule: beta_c_Comp_cases) auto
next
  case (VarLam x y M) from VarLam.prems show ?case by (cases rule: beta_c_Comp_cases) auto
next
  case (AppL M N L)
  from AppL.prems show ?case
  proof (cases rule: beta_c_App_cases)
    case (Beta1 x P K) then show ?thesis using AppL.hyps by simp
  next
    case (Beta2 x P) then show ?thesis using AppL.hyps by simp
  next
    case (AppL M') then show ?thesis using AppL.IH by simp
  qed
next
  case (CompL M N L)
  from CompL.prems show ?case
  proof (cases rule: beta_c_Comp_cases)
    case (VarClos x y P K) then show ?thesis using CompL.hyps by simp
  next
    case (VarLam x y P) then show ?thesis using CompL.hyps by simp
  next
    case (CompL M') then show ?thesis using CompL.IH by simp
  next
    case (VarR x L') then show ?thesis using CompL.hyps by simp
  qed
next
  case (VarR M N x)
  from VarR.prems show ?case
  proof (cases rule: beta_c_Comp_cases)
    case (VarClos x' y P K) then show ?thesis using VarR.hyps by simp
  next
    case (VarLam x' y P) then show ?thesis using VarR.hyps by simp
  next
    case (CompL M') then show ?thesis by simp
  next
    case (VarR x' L') then show ?thesis using VarR.IH by simp
  qed
qed

lemma beta_h_imp_c_or: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> M \<rightarrow>\<^sub>c N' \<Longrightarrow> N = N'"
proof (induction arbitrary: N' rule: beta_h.induct)
  case (C M N) then show ?case using beta_c_det by blast
next
  case (AppL M N L)
  from AppL.prems show ?case
  proof (cases rule: beta_c_App_cases)
    case (Beta1 x P K) then show ?thesis using AppL.hyps by simp
  next
    case (Beta2 x P) then show ?thesis using AppL.hyps by simp
  next
    case (AppL M') then show ?thesis using AppL.IH by simp
  qed
next
  case (VarR M N x)
  from VarR.prems show ?case
  proof (cases rule: beta_c_Comp_cases)
    case (VarClos x' y P K) then show ?thesis using VarR.hyps by simp
  next
    case (VarLam x' y P) then show ?thesis using VarR.hyps by simp
  next
    case (CompL M') then show ?thesis by simp
  next
    case (VarR x' L') then show ?thesis using VarR.IH by simp
  qed
next
  case (ArgV V M N)
  from ArgV.prems show ?case
  proof (cases rule: beta_c_App_cases)
    case (Beta1 x P K) then show ?thesis using ArgV.hyps by simp
  next
    case (Beta2 x P) then show ?thesis using ArgV.hyps by simp
  next
    case (AppL M') then show ?thesis using ArgV.hyps envh_no_beta_c by blast
  qed
qed

lemma beta_h_det: "M \<rightarrow>\<^sub>\<beta> N1 \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N2 \<Longrightarrow> N1 = N2"
proof (induction arbitrary: N2 rule: beta_h.induct)
  case (C M N)
  then show ?case using beta_h_imp_c_or by metis
next
  case (AppL M N L)
  from AppL.prems show ?case
  proof (cases rule: beta_h_App_cases)
    case C then show ?thesis using beta_h_imp_c_or beta_h.AppL[OF AppL.hyps] by metis
  next
    case (AppL M') then show ?thesis using AppL.IH by simp
  next
    case (ArgV L') then show ?thesis using AppL.hyps envh_no_beta by blast
  qed
next
  case (VarR M N x)
  from VarR.prems show ?case
  proof (cases rule: beta_h_Comp_cases)
    case C then show ?thesis using beta_h_imp_c_or beta_h.VarR[OF VarR.hyps] by metis
  next
    case (VarR x' L') then show ?thesis using VarR.IH by simp
  qed
next
  case (ArgV V M N)
  from ArgV.prems show ?case
  proof (cases rule: beta_h_App_cases)
    case C then show ?thesis using beta_h_imp_c_or beta_h.ArgV[OF ArgV.hyps] by metis
  next
    case (AppL M') then show ?thesis using ArgV.hyps envh_no_beta by blast
  next
    case (ArgV L') then show ?thesis using ArgV.IH by simp
  qed
qed

lemma WHNF_imp_sig_normal: "WHNF M \<Longrightarrow> sig_normal M"
  by (auto simp: normal_def wh_def)

subsection \<open>\<open>\<sigma>\<close> terminates (measure \<^verbatim>\<open>tlength\<close>)\<close>

lemma sig_tlength_decrease: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> tlength N < tlength M"
proof (induction rule: sig.induct)
  case (Ass L M N)
  have eq: "(tlength M + 1) * (tlength N + 1) = tlength M * (tlength N + 1) + tlength N + 1"
    by (simp add: algebra_simps)
  have "tlength M * (tlength N + 1) + 1 < (tlength M + 1) * (tlength N + 1)"
    using eq tlength_pos[of N] by linarith
  then have "tlength L * (tlength M * (tlength N + 1) + 1)
      < tlength L * ((tlength M + 1) * (tlength N + 1))"
    using tlength_pos[of L] by (rule mult_strict_left_mono)
  then show ?case
    by (simp only: tlength.simps mult.assoc)
next
  case (DExtn L x M N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (DApp M1 M2 N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (CompL M N L)
  have "tlength N * (tlength L + 1) < tlength M * (tlength L + 1)"
    using CompL.IH by (rule mult_strict_right_mono) simp
  then show ?case
    by (simp only: tlength.simps)
next
  case (CompR M N L)
  have "tlength L * (tlength N + 1) < tlength L * (tlength M + 1)"
    using CompR.IH tlength_pos[of L] by (intro mult_strict_left_mono) simp_all
  then show ?case
    by (simp only: tlength.simps)
qed simp_all

theorem sig_SN: "SN_at sig M"
proof (induction "tlength M" arbitrary: M rule: less_induct)
  case less
  show ?case
    by (rule SN_atI) (auto intro: less dest: sig_tlength_decrease)
qed

end
