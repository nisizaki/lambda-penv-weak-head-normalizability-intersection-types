theory ARS
  imports Main
begin

section \<open>Abstract rewriting (minimal)\<close>

definition normal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "normal R a \<longleftrightarrow> (\<nexists>b. R a b)"

lemma normalI: "(\<And>b. \<not> R a b) \<Longrightarrow> normal R a"
  by (auto simp: normal_def)

lemma normalD: "normal R a \<Longrightarrow> \<not> R a b"
  by (auto simp: normal_def)

lemma normal_rtranclp: "normal R a \<Longrightarrow> R\<^sup>*\<^sup>* a b \<Longrightarrow> b = a"
  by (erule converse_rtranclpE) (auto simp: normal_def)

definition SN_at :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "SN_at R a \<longleftrightarrow> Wellfounded.accp (\<lambda>b a. R a b) a"

lemma SN_atI: "(\<And>b. R a b \<Longrightarrow> SN_at R b) \<Longrightarrow> SN_at R a"
  unfolding SN_at_def by (rule accp.accI) blast

lemma SN_at_step: "SN_at R a \<Longrightarrow> R a b \<Longrightarrow> SN_at R b"
  unfolding SN_at_def by (rule accp_downward)

lemma SN_at_induct [consumes 1, case_names step]:
  assumes "SN_at R a"
    and step: "\<And>a. SN_at R a \<Longrightarrow> (\<And>b. R a b \<Longrightarrow> P b) \<Longrightarrow> P a"
  shows "P a"
proof -
  have "Wellfounded.accp (\<lambda>b a. R a b) a"
    using assms(1) by (simp add: SN_at_def)
  then show ?thesis
  proof (rule accp_induct)
    fix x
    assume acc: "Wellfounded.accp (\<lambda>b a. R a b) x" and IH: "\<forall>y. R x y \<longrightarrow> P y"
    show "P x"
    proof (rule step)
      show "SN_at R x"
        using acc by (simp add: SN_at_def)
      show "P b" if "R x b" for b
        using IH that by blast
    qed
  qed
qed

lemma SN_at_rtranclp:
  assumes "SN_at R a" and "R\<^sup>*\<^sup>* a b"
  shows "SN_at R b"
  using assms(2,1) by (induction rule: rtranclp_induct) (auto intro: SN_at_step)

lemma SN_at_normal: "normal R a \<Longrightarrow> SN_at R a"
  by (rule SN_atI) (auto simp: normal_def)

lemma SN_at_imp_no_infinite:
  assumes "SN_at R a"
  shows "\<not> (\<exists>f. f 0 = a \<and> (\<forall>i. R (f i) (f (Suc i))))"
  using assms
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof
    assume "\<exists>f. f 0 = a \<and> (\<forall>i. R (f i) (f (Suc i)))"
    then obtain f where f0: "f 0 = a" and steps: "\<forall>i. R (f i) (f (Suc i))" by blast
    have "R a (f (Suc 0))" using f0 steps by (metis)
    moreover have "\<exists>g. g 0 = f (Suc 0) \<and> (\<forall>i. R (g i) (g (Suc i)))"
    proof
      let ?g = "\<lambda>i. f (Suc i)"
      show "?g 0 = f (Suc 0) \<and> (\<forall>i. R (?g i) (?g (Suc i)))"
        using steps by simp
    qed
    ultimately show False using step.IH[of "f (Suc 0)"] by blast
  qed
qed

end
