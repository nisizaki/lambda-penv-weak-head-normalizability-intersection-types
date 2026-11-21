theory Soundness
  imports Completeness Uniform
begin

section \<open>Soundness: \<open>Typ M \<Longrightarrow> CFWHN M\<close>\<close>

text \<open>Adapted from the \<open>\<lambda>env\<close> development.  The interpretation of
  \<open>Env m ob\<close> contains both lookup (\<open>x \<circ> e\<close>) and application to names
  (\<open>e N\<close> for \<open>N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* \<lceil>x\<rceil>\<close>); \<open>I (QN x) = {M. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x}\<close>.
  Forward closure comes from \<open>Uniform\<close> (\<open>CFWHN_fwd\<close>, \<open>Nm_fwd\<close>).\<close>

subsection \<open>Auxiliary reduction lemmas\<close>

lemma CFWHN_back: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> CFWHN M' \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def by (meson converse_rtranclp_into_rtranclp)

lemma CFWHN_back_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> CFWHN M' \<Longrightarrow> CFWHN M"
  by (induction rule: converse_rtranclp_induct) (auto intro: CFWHN_back)

lemma sig_steps_wh: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl sig_imp_wh)

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

lemma steps_lift:
  assumes "\<And>P Q. R P Q \<Longrightarrow> R' (f P) (f Q)"
  shows "R\<^sup>*\<^sup>* M N \<Longrightarrow> R'\<^sup>*\<^sup>* (f M) (f N)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl assms)

lemma wh_steps_AppL: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M' N"
  by (rule steps_lift[of wh wh "\<lambda>P. App P N"]) (auto intro: wh_AppL)

lemma sig_steps_AppR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M N'"
  by (rule steps_lift[of sig wh "\<lambda>P. App M P"]) (auto intro: sig_imp_wh sig.AppR)

lemma sig_steps_Lam: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Lam x M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Lam x M'"
  by (rule steps_lift[of sig wh "\<lambda>P. Lam x P"]) (auto intro: sig_imp_wh sig.Lam)

lemma sig_steps_CompL: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Comp M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp M' N"
  by (rule steps_lift[of sig wh "\<lambda>P. Comp P N"]) (auto intro: sig_imp_wh sig.CompL)

lemma sig_steps_CompR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> Comp M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp M N'"
  by (rule steps_lift[of sig wh "\<lambda>P. Comp M P"]) (auto intro: sig_imp_wh sig.CompR)

lemma sig_steps_ExtnL: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M' x N"
  by (rule steps_lift[of sig wh "\<lambda>P. Extn P x N"]) (auto intro: sig_imp_wh sig.ExtnL)

lemma sig_steps_ExtnR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M x N'"
  by (rule steps_lift[of sig wh "\<lambda>P. Extn M x P"]) (auto intro: sig_imp_wh sig.ExtnR)

lemma wh_steps_VarR: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var x) M'"
  by (rule steps_lift[of wh wh "\<lambda>P. Comp (Var x) P"]) (auto intro: wh_VarR)

lemma val_WHNF: "val M \<Longrightarrow> WHNF M"
  using WHNF_iff_classes by blast

lemma neu_WHNF: "neu M \<Longrightarrow> WHNF M"
  using WHNF_iff_classes by blast

lemma val_CFWHN: "val M \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def using val_WHNF val_not_clash by blast

lemma neu_CFWHN: "neu M \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def using neu_WHNF neu_not_clash by blast

lemma CFWHN_Lam: "CFWHN (Lam x M)"
proof -
  obtain M' where s: "sig\<^sup>*\<^sup>* M M'" and n: "sig_normal M'" using sig_nf by blast
  have "val (Lam x M')" using n by (rule VLam)
  then show ?thesis using CFWHN_back_steps[OF sig_steps_Lam[OF s]] val_CFWHN by blast
qed

lemma CFWHN_Extn: "CFWHN (Extn M x N)"
proof -
  obtain M' where s1: "sig\<^sup>*\<^sup>* M M'" and n1: "sig_normal M'" using sig_nf by blast
  obtain N' where s2: "sig\<^sup>*\<^sup>* N N'" and n2: "sig_normal N'" using sig_nf by blast
  have r: "Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M' x N'"
    using sig_steps_ExtnL[OF s1] sig_steps_ExtnR[OF s2] by (rule rtranclp_trans)
  have "val (Extn M' x N')" using n1 n2 by (rule VExtn)
  then show ?thesis using CFWHN_back_steps[OF r] val_CFWHN by blast
qed

lemma CFWHN_Clo: "CFWHN (Comp (Lam x M) e)"
proof -
  obtain M' where s1: "sig\<^sup>*\<^sup>* M M'" and n1: "sig_normal M'" using sig_nf by blast
  obtain e' where s2: "sig\<^sup>*\<^sup>* e e'" and n2: "sig_normal e'" using sig_nf by blast
  have r: "Comp (Lam x M) e \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Lam x M') e'"
  proof -
    have "sig\<^sup>*\<^sup>* (Lam x M) (Lam x M')"
      by (rule steps_lift[of sig sig "\<lambda>P. Lam x P", OF sig.Lam s1])
    then have "Comp (Lam x M) e \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Lam x M') e" by (rule sig_steps_CompL)
    then show ?thesis using sig_steps_CompR[OF s2] by (rule rtranclp_trans)
  qed
  show ?thesis
  proof (cases "e' = Id")
    case True
    have "Comp (Lam x M') e' \<rightarrow>\<^sub>w\<^sub>h Lam x M'" using True by (simp add: sig_imp_wh sig.IdR)
    moreover have "CFWHN (Lam x M')" using n1 VLam val_CFWHN by blast
    ultimately show ?thesis using CFWHN_back_steps[OF r] CFWHN_back by blast
  next
    case False
    have "val (Comp (Lam x M') e')" using n1 n2 False by (rule VClo)
    then show ?thesis using CFWHN_back_steps[OF r] val_CFWHN by blast
  qed
qed


text \<open>Weak neutral terms: arguments need not be \<open>\<sigma>\<close>-normal.\<close>

inductive wneu :: "trm \<Rightarrow> bool" where
  wneu_Var: "wneu (Var x)"
| wneu_App: "wneu M \<Longrightarrow> wneu (App M N)"
| wneu_Comp: "wneu M \<Longrightarrow> wneu (Comp (Var x) M)"

lemma wh_steps_ArgV:
  assumes "envh V" "N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N'"
  shows "App V N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App V N'"
  using assms(2)
  by (induction rule: rtranclp_induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl wh_ArgV[OF assms(1)])

lemma Nm_CFWHN: "CFWHN (Nm x)"
  using val_CFWHN VNm by blast

lemma wneu_reduces: "wneu M \<Longrightarrow> \<exists>M'. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<and> neu M'"
proof (induction rule: wneu.induct)
  case (wneu_Var x)
  then show ?case by (blast intro: neu.intros)
next
  case (wneu_App M N)
  then obtain M' where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M'" and n: "neu M'" by blast
  obtain N' where s: "sig\<^sup>*\<^sup>* N N'" and nn: "sig_normal N'" using sig_nf by blast
  have rr: "App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M' N'"
    using wh_steps_AppL[OF r] sig_steps_AppR[OF s] by (rule rtranclp_trans)
  show ?case
  proof (cases "\<exists>y. N' = Nm y")
    case True
    then obtain y where y: "N' = Nm y" by blast
    have "App M' (Nm y) \<rightarrow>\<^sub>w\<^sub>h Comp (Var y) M'" by (rule sig_imp_wh[OF sig.AppConst])
    with rr y have "App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var y) M'" by (blast intro: rtranclp.rtrancl_into_rtrancl)
    moreover have "neu (Comp (Var y) M')" using n by (rule NComp)
    ultimately show ?thesis by blast
  next
    case False
    then have "\<forall>y. N' \<noteq> Nm y" by blast
    then have "neu (App M' N')" by (rule NApp[OF n nn])
    with rr show ?thesis by blast
  qed
next
  case (wneu_Comp M x)
  then obtain M' where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M'" and n: "neu M'" by blast
  have "Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var x) M'" by (rule wh_steps_VarR[OF r])
  moreover have "neu (Comp (Var x) M')" using n by (rule NComp)
  ultimately show ?case by blast
qed

lemma wneu_CFWHN: "wneu M \<Longrightarrow> CFWHN M"
  using wneu_reduces neu_CFWHN CFWHN_back_steps by blast

subsection \<open>Interpretation of types\<close>

fun I :: "ty \<Rightarrow> trm set" where
  "I (TV n) = {M. CFWHN M}"
| "I Om = UNIV"
| "I (Arr A B) = {M. CFWHN M \<and> (\<forall>N \<in> I A. App M N \<in> I B)}"
| "I (Inter A B) = I A \<inter> I B"
| "I (QN x) = {M. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x}"
| "I (Env m ob) =
     {e. ((m \<noteq> [] \<or> ob) \<longrightarrow> CFWHN e) \<and>
         (\<forall>x S. map_of (map (\<lambda>(y, A). (y, I A)) m) x = Some S \<longrightarrow>
            Comp (Var x) e \<in> S \<and> (\<forall>N. N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x \<longrightarrow> App e N \<in> S))}"

lemma I_Env:
  "e \<in> I (Env m ob) \<longleftrightarrow>
     ((m \<noteq> [] \<or> ob) \<longrightarrow> CFWHN e) \<and>
     (\<forall>x A. map_of m x = Some A \<longrightarrow>
        Comp (Var x) e \<in> I A \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A))"
  by (simp add: map_of_map_dep) blast

declare I.simps(6) [simp del]

lemma I_QN: "N \<in> I (QN x) \<longleftrightarrow> N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Nm x"
  by simp

lemma I_back: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFWHN_back by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using CFWHN_back wh_AppL by simp blast
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case using QN.prems by (simp add: I_QN)
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A \<and> (\<forall>N \<in> I (QN x). App M N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M' \<in> I A" and a: "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M' N \<in> I A"
      using Env.prems(2) l by (simp_all add: I_Env)
    have "Comp (Var x) M \<in> I A" by (rule Env.IH[OF xa sn wh_VarR[OF Env.prems(1)] c])
    moreover have "App M N \<in> I A" if "N \<in> I (QN x)" for N
      by (rule Env.IH[OF xa sn wh_AppL[OF Env.prems(1)] a[OF that]])
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems CFWHN_back by (simp add: I_Env)
qed

lemma I_back_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
  by (induction rule: converse_rtranclp_induct) (auto intro: I_back)

lemma I_fwd: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> M \<in> I A \<Longrightarrow> M' \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFWHN_fwd by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using CFWHN_fwd wh_AppL by simp blast
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case using Nm_fwd by simp
next
  case (Env m ob)
  have "Comp (Var x) M' \<in> I A \<and> (\<forall>N \<in> I (QN x). App M' N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M \<in> I A" and a: "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M N \<in> I A"
      using Env.prems(2) l by (simp_all add: I_Env)
    have "Comp (Var x) M' \<in> I A" by (rule Env.IH[OF xa sn wh_VarR[OF Env.prems(1)] c])
    moreover have "App M' N \<in> I A" if "N \<in> I (QN x)" for N
      by (rule Env.IH[OF xa sn wh_AppL[OF Env.prems(1)] a[OF that]])
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems CFWHN_fwd by (simp add: I_Env)
qed

lemma I_ess: "ess A \<Longrightarrow> M \<in> I A \<Longrightarrow> CFWHN M"
proof (induction A arbitrary: M)
  case (TV n) then show ?case by simp
next
  case Om then show ?case by simp
next
  case (Arr A B) then show ?case by simp
next
  case (Inter A B)
  then show ?case by (cases "ess A") simp_all
next
  case (QN x)
  then show ?case using CFWHN_back_steps Nm_CFWHN by simp
next
  case (Env m ob)
  then show ?case by (simp add: I_Env)
qed

lemma wneu_I: "qfree A \<Longrightarrow> wneu M \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M)
  case (TV n) then show ?case using wneu_CFWHN by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using wneu_CFWHN wneu_App by simp
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A \<and> (\<forall>N \<in> I (QN x). App M N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have q: "qfree A" using Env.prems(1) xa by force
    have w: "wneu (Comp (Var x) M)" using Env.prems(2) by (rule wneu_Comp)
    have "Comp (Var x) M \<in> I A" by (rule Env.IH[OF xa sn q w])
    moreover have "App M N \<in> I A" for N
      by (rule Env.IH[OF xa sn q wneu_App[OF Env.prems(2)]])
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems wneu_CFWHN by (simp add: I_Env)
qed

lemma Var_I: "qfree A \<Longrightarrow> Var x \<in> I A"
  by (rule wneu_I) (auto intro: wneu_Var)

subsection \<open>Monotonicity\<close>

lemma I_mono: "A \<preceq> B \<Longrightarrow> I A \<subseteq> I B"
proof (induction rule: sub.induct)
  case (s_arr A' A B B')
  then show ?case by auto
next
  case (s_env m' m ob' ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have cf: "CFWHN e" if "m' \<noteq> [] \<or> ob'"
    proof -
      have "m \<noteq> [] \<or> ob"
      proof (cases "m' = []")
        case True then show ?thesis using that s_env.hyps by auto
      next
        case False
        then obtain p ps where "m' = p # ps" by (cases m') auto
        then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
        then obtain A where "map_of m (fst p) = Some A" using s_env.IH by blast
        then show ?thesis by auto
      qed
      then show ?thesis using e by (simp add: I_Env)
    qed
    moreover have "Comp (Var x) e \<in> I A' \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A')"
      if l: "map_of m' x = Some A'" for x A'
    proof -
      obtain A where "map_of m x = Some A" and "I A \<subseteq> I A'"
        using s_env.IH l by blast
      then show ?thesis using e by (auto simp: I_Env)
    qed
    ultimately show "e \<in> I (Env m' ob')" by (simp add: I_Env)
  qed
next
  case (s_emeet m1 o1 m2 o2)
  show ?case
  proof
    fix e
    assume "e \<in> I (Inter (Env m1 o1) (Env m2 o2))"
    then have e1: "e \<in> I (Env m1 o1)" and e2: "e \<in> I (Env m2 o2)" by simp_all
    have cf: "CFWHN e" if "emeet m1 m2 \<noteq> [] \<or> o1 \<or> o2"
      using that e1 e2 by (auto simp: I_Env emeet_def)
    moreover have "Comp (Var x) e \<in> I A \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A)"
      if l: "map_of (emeet m1 m2) x = Some A" for x A
    proof (cases "map_of m1 x")
      case None
      then have "map_of m2 x = Some A" using l by (simp add: map_of_emeet)
      then show ?thesis using e2 by (simp add: I_Env)
    next
      case (Some A1)
      show ?thesis
      proof (cases "map_of m2 x")
        case None
        then have "A = A1" using l Some by (simp add: map_of_emeet)
        then show ?thesis using e1 Some by (simp add: I_Env)
      next
        case (Some A2)
        then have "A = Inter A1 A2" using l \<open>map_of m1 x = Some A1\<close> by (simp add: map_of_emeet)
        then show ?thesis using e1 e2 Some \<open>map_of m1 x = Some A1\<close> by (auto simp: I_Env)
      qed
    qed
    ultimately show "e \<in> I (Env (emeet m1 m2) (o1 \<or> o2))" by (simp add: I_Env)
  qed
next
  case s_omenv
  then show ?case by (auto simp: I_Env)
next
  case (s_envarr m x A ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have "CFWHN e" using e s_envarr by (auto simp: I_Env)
    moreover have "App e N \<in> I A" if "N \<in> I (QN x)" for N
      using e s_envarr that by (auto simp: I_Env)
    ultimately show "e \<in> I (Arr (QN x) A)" by simp
  qed
next
  case (s_arrenv x A)
  show ?case
  proof
    fix M
    assume "M \<in> I (Arr (QN x) A)"
    then have cf: "CFWHN M" and ap: "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M N \<in> I A" by simp_all
    have "App M (Nm x) \<in> I A" by (rule ap) simp
    then have "Comp (Var x) M \<in> I A" using I_fwd[OF sig_imp_wh[OF sig.AppConst]] by blast
    then show "M \<in> I (Env [(x, A)] False)" using cf ap by (simp add: I_Env)
  qed
qed auto

subsection \<open>Realizers\<close>

lemma Id_I:
  assumes q: "\<forall>p \<in> set m. qfree (snd p)"
  shows "Id \<in> I (Env m ob)"
proof -
  have "CFWHN Id" using val_CFWHN VId by blast
  moreover have "Comp (Var x) Id \<in> I A \<and> (\<forall>N \<in> I (QN x). App Id N \<in> I A)"
    if l: "map_of m x = Some A" for x A
  proof -
    have qa: "qfree A" using q map_of_SomeD[OF l] by force
    have c: "Comp (Var x) Id \<in> I A"
      using I_back[OF sig_imp_wh[OF sig.IdR] Var_I[OF qa]] .
    have "App Id N \<in> I A" if n: "N \<in> I (QN x)" for N
    proof -
      have "App Id N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App Id (Nm x)" using n by (simp add: wh_steps_ArgV)
      moreover have "App Id (Nm x) \<in> I A"
        using I_back[OF sig_imp_wh[OF sig.AppConst] c] .
      ultimately show ?thesis by (rule I_back_steps)
    qed
    with c show ?thesis by blast
  qed
  ultimately show ?thesis by (simp add: I_Env)
qed

lemma Extn_I:
  assumes n: "N \<in> I A" and e: "e \<in> I (Env m ob)"
  shows "Extn N x e \<in> I (Env ((x, A) # m) ob)"
proof -
  have "Comp (Var y) (Extn N x e) \<in> I B \<and> (\<forall>N' \<in> I (QN y). App (Extn N x e) N' \<in> I B)"
    if l: "map_of ((x, A) # m) y = Some B" for y B
  proof -
    have c: "Comp (Var y) (Extn N x e) \<in> I B"
    proof (cases "y = x")
      case True
      then have "B = A" using l by simp
      then show ?thesis using True I_back[OF sig_imp_wh[OF sig.VarRef] n] by simp
    next
      case False
      then have "map_of m y = Some B" using l by simp
      then have "Comp (Var y) e \<in> I B" using e by (simp add: I_Env)
      moreover have "Comp (Var y) (Extn N x e) \<rightarrow>\<^sub>w\<^sub>h Comp (Var y) e"
        using False by (simp add: sig_imp_wh sig.VarSkip)
      ultimately show ?thesis using I_back by blast
    qed
    have "App (Extn N x e) N' \<in> I B" if n': "N' \<in> I (QN y)" for N'
    proof -
      have "App (Extn N x e) N' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App (Extn N x e) (Nm y)" using n' by (simp add: wh_steps_ArgV)
      moreover have "App (Extn N x e) (Nm y) \<in> I B"
        using I_back[OF sig_imp_wh[OF sig.AppConst] c] .
      ultimately show ?thesis by (rule I_back_steps)
    qed
    with c show ?thesis by blast
  qed
  then show ?thesis using CFWHN_Extn by (simp add: I_Env)
qed

subsection \<open>Basic lemma\<close>

definition env_app :: "trm \<Rightarrow> trm \<Rightarrow> trm" where
  "env_app M e = (if e = Id then M else Comp M e)"

lemma basic:
  "C \<turnstile> M : A \<Longrightarrow> e \<in> I C \<Longrightarrow> env_app M e \<in> I A"
proof (induction arbitrary: e rule: hasty.induct)
  case (TVar C m ob x A)
  have em: "e \<in> I (Env m ob)" using I_mono[OF TVar.hyps(1)] TVar.prems by blast
  then have c: "Comp (Var x) e \<in> I A" using TVar.hyps(2) by (simp add: I_Env)
  show ?case
  proof (cases "e = Id")
    case True
    then have "Comp (Var x) Id \<in> I A" using c by simp
    then show ?thesis using True I_fwd[OF sig_imp_wh[OF sig.IdR]] by (simp add: env_app_def)
  next
    case False then show ?thesis using c by (simp add: env_app_def)
  qed
next
  case (TLam C m ob x A M B)
  have em: "e \<in> I (Env m ob)" using I_mono[OF TLam.hyps(1)] TLam.prems by blast
  have app: "App (env_app (Lam x M) e) N \<in> I B" if n: "N \<in> I A" for N
  proof (cases "e = Id")
    case True
    have "Extn N x Id \<in> I (Env ((x, A) # m) ob)" using True em by (blast intro: Extn_I[OF n])
    then have "Comp M (Extn N x Id) \<in> I B" using TLam.IH by (force simp: env_app_def)
    then show ?thesis using True I_back[OF beta_h_imp_wh[OF beta_c_imp_beta_h[OF beta_c.Beta2]]] by (simp add: env_app_def)
  next
    case False
    have "Extn N x e \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I[OF n em])
    then have "Comp M (Extn N x e) \<in> I B" using TLam.IH by (force simp: env_app_def)
    then show ?thesis using False I_back[OF beta_h_imp_wh[OF beta_c_imp_beta_h[OF beta_c.Beta1]]] by (simp add: env_app_def)
  qed
  have "CFWHN (env_app (Lam x M) e)"
    by (simp add: env_app_def CFWHN_Lam CFWHN_Clo)
  with app show ?case by simp
next
  case (TApp C M A B N)
  have m: "env_app M e \<in> I (Arr A B)" and n: "env_app N e \<in> I A"
    using TApp.IH TApp.prems by blast+
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using m n by (simp add: env_app_def)
  next
    case False
    have "App (Comp M e) (Comp N e) \<in> I B" using m n False by (simp add: env_app_def)
    then show ?thesis using False I_back[OF sig_imp_wh[OF sig.DApp]] by (simp add: env_app_def)
  qed
next
  case (TId C)
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using TId.prems by (simp add: env_app_def)
  next
    case False
    then show ?thesis using TId.prems I_back[OF sig_imp_wh[OF sig.IdL]] by (simp add: env_app_def)
  qed
next
  case (TExtn C M A N m ob x)
  have m: "env_app M e \<in> I A" and n: "env_app N e \<in> I (Env m ob)"
    using TExtn.IH TExtn.prems by blast+
  have r: "Extn (env_app M e) x (env_app N e) \<in> I (Env ((x, A) # m) ob)"
    by (rule Extn_I[OF m n])
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using r by (simp add: env_app_def)
  next
    case False
    then show ?thesis using r I_back[OF sig_imp_wh[OF sig.DExtn]] by (simp add: env_app_def)
  qed
next
  case (TComp C N D M A)
  show ?case
  proof (cases "e = Id")
    case True
    have n: "N \<in> I D" using TComp.IH(1)[OF TComp.prems] True by (simp add: env_app_def)
    have "env_app M N \<in> I A" using TComp.IH(2)[OF n] .
    then show ?thesis
      using True I_back[OF sig_imp_wh[OF sig.IdR]] by (cases "N = Id") (simp_all add: env_app_def)
  next
    case False
    have n: "Comp N e \<in> I D" using TComp.IH(1)[OF TComp.prems] False by (simp add: env_app_def)
    have "env_app M (Comp N e) \<in> I A" using TComp.IH(2)[OF n] .
    then have "Comp M (Comp N e) \<in> I A" by (simp add: env_app_def)
    then show ?thesis using False I_back[OF sig_imp_wh[OF sig.Ass]] by (simp add: env_app_def)
  qed
next
  case (TNm C x)
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis by (simp add: env_app_def)
  next
    case False
    have "Nm x \<in> I (QN x)" by simp
    then have "Comp (Nm x) e \<in> I (QN x)"
      by (rule I_back[OF sig_imp_wh[OF sig.ConstComp]])
    then show ?thesis using False by (simp add: env_app_def)
  qed
next
  case (TOm C M)
  then show ?case by simp
next
  case (TInter C M A B)
  then show ?case by simp
next
  case (TSub C M A B)
  then show ?case using I_mono by blast
qed


theorem soundness: "Typ M \<Longrightarrow> CFWHN M"
proof -
  assume "Typ M"
  then obtain m ob A where t: "Env m ob \<turnstile> M : A" and e: "ess A"
    and q: "\<forall>p \<in> set m. qfree (snd p)" by (auto simp: Typ_def)
  have "env_app M Id \<in> I A" by (rule basic[OF t Id_I[OF q]])
  then have "M \<in> I A" by (simp add: env_app_def)
  then show "CFWHN M" by (rule I_ess[OF e])
qed

end
