theory Examples
  imports Main_Results
begin

section \<open>Examples\<close>

text \<open>
  Variables are natural numbers: \<open>x = 0\<close>, \<open>y = 1\<close>, and so on.
  Examples of reductions and typings.
\<close>

subsection \<open>Helpers\<close>

text \<open>A term that weakly reduces to a non-clashing weak-head normal form is typable.\<close>

lemma ex_Typ_of_nf:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" "WHNF N" "\<not> clash N"
  shows "Typ M"
proof -
  have "CFWHN M"
    unfolding CFWHN_def using assms by blast
  then show ?thesis
    by (rule iffD2[OF main_characterization[of M]])
qed

lemma ex_envh_Id: "envh Id"
  by simp

subsection \<open>1. \<open>x\<circ>(\<lambda>y.y)\<close>, a function used as an environment\<close>

lemma ex1_step1: "Comp (Var 0) (Lam 1 (Var 1)) \<rightarrow>\<^sub>w\<^sub>h Comp (Var 1) (Extn (Nm 0) 1 Id)"
  by (rule beta_h_imp_wh[OF beta_h.C[OF beta_c.VarLam]])

lemma ex1_step2: "Comp (Var 1) (Extn (Nm 0) 1 Id) \<rightarrow>\<^sub>w\<^sub>h Nm 0"
  by (rule sig_imp_wh[OF sig.VarRef])

lemma ex1_red: "Comp (Var 0) (Lam 1 (Var 1)) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm 0"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex1_step1)
  apply (rule r_into_rtranclp)
  apply (rule ex1_step2)
  done

lemma ex1_Typ: "Typ (Comp (Var 0) (Lam 1 (Var 1)))"
  by (rule ex_Typ_of_nf[OF ex1_red WHNF_Nm val_not_clash[OF val.VNm]])

subsection \<open>2. \<open>(id/0\<cdot>id)\<circ>\<lceil>0\<rceil>\<close>, an environment used as a function\<close>

lemma ex2_step1: "App (Extn Id 0 Id) (Nm 0) \<rightarrow>\<^sub>w\<^sub>h Comp (Var 0) (Extn Id 0 Id)"
  by (rule sig_imp_wh[OF sig.AppConst])

lemma ex2_step2: "Comp (Var 0) (Extn Id 0 Id) \<rightarrow>\<^sub>w\<^sub>h Id"
  by (rule sig_imp_wh[OF sig.VarRef])

lemma ex2_red: "App (Extn Id 0 Id) (Nm 0) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Id"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex2_step1)
  apply (rule r_into_rtranclp)
  apply (rule ex2_step2)
  done

lemma ex2_Typ: "Typ (App (Extn Id 0 Id) (Nm 0))"
  by (rule ex_Typ_of_nf[OF ex2_red WHNF_Id val_not_clash[OF val.VId]])

subsection \<open>3. \<open>id 1\<close>, a clash\<close>

lemma ex3_clash: "clash (App Id (Var 1))"
proof (rule clash.CEnv)
  show "envh Id" by (rule ex_envh_Id)
  show "sig_normal Id" by (rule WHNF_imp_sig_normal[OF WHNF_Id])
  show "WHNF (Var 1)" by (rule WHNF_Var)
  show "\<forall>y. Var 1 \<noteq> Nm y" by simp
qed

lemma ex3_WHNF: "WHNF (App Id (Var 1))"
  by (rule clash_WHNF[OF ex3_clash])

lemma ex3_not_Typ: "\<not> Typ (App Id (Var 1))"
  by (rule clash_not_Typ[OF ex3_WHNF ex3_clash])

subsection \<open>4. \<open>\<lceil>0\<rceil> 1\<close> and \<open>0\<circ>\<lceil>1\<rceil>\<close>, clashes\<close>

lemma ex4a_clash: "clash (App (Nm 0) (Var 1))"
  by (rule clash.CNmApp[OF WHNF_imp_sig_normal[OF WHNF_Var]]) simp

lemma ex4a_WHNF: "WHNF (App (Nm 0) (Var 1))"
  by (rule clash_WHNF[OF ex4a_clash])

lemma ex4a_not_Typ: "\<not> Typ (App (Nm 0) (Var 1))"
  by (rule clash_not_Typ[OF ex4a_WHNF ex4a_clash])

lemma ex4b_clash: "clash (Comp (Var 0) (Nm 1))"
  by (rule clash.CVarNm)

lemma ex4b_WHNF: "WHNF (Comp (Var 0) (Nm 1))"
  by (rule clash_WHNF[OF ex4b_clash])

lemma ex4b_not_Typ: "\<not> Typ (Comp (Var 0) (Nm 1))"
  by (rule clash_not_Typ[OF ex4b_WHNF ex4b_clash])

subsection \<open>5. \<open>id((\<lambda>2.\<lceil>0\<rceil>) 1)\<close>, using ArgV\<close>

lemma ex5_step1:
  "App Id (App (Lam 2 (Nm 0)) (Var 1)) \<rightarrow>\<^sub>w\<^sub>h App Id (Comp (Nm 0) (Extn (Var 1) 2 Id))"
  by (rule beta_h_imp_wh[OF beta_h.ArgV[OF ex_envh_Id beta_h.C[OF beta_c.Beta2]]])

lemma ex5_step2:
  "App Id (Comp (Nm 0) (Extn (Var 1) 2 Id)) \<rightarrow>\<^sub>w\<^sub>h App Id (Nm 0)"
  by (rule sig_imp_wh[OF sig.AppR[OF sig.ConstComp]])

lemma ex5_step3: "App Id (Nm 0) \<rightarrow>\<^sub>w\<^sub>h Comp (Var 0) Id"
  by (rule sig_imp_wh[OF sig.AppConst])

lemma ex5_step4: "Comp (Var 0) Id \<rightarrow>\<^sub>w\<^sub>h Var 0"
  by (rule sig_imp_wh[OF sig.IdR])

lemma ex5_red: "App Id (App (Lam 2 (Nm 0)) (Var 1)) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Var 0"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step1)
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step2)
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step3)
  apply (rule r_into_rtranclp)
  apply (rule ex5_step4)
  done

lemma ex5_Typ: "Typ (App Id (App (Lam 2 (Nm 0)) (Var 1)))"
  by (rule ex_Typ_of_nf[OF ex5_red WHNF_Var neu_not_clash[OF neu.NVar]])

end
