theory Lambda
  imports ARS
begin

section \<open>Pure \<open>\<lambda>\<close>-calculus (de Bruijn) and weak-head reduction\<close>

text \<open>
  Definitions of \<open>lift\<close> and \<open>subst\<close> follow the Isabelle distribution
  (\<^verbatim>\<open>HOL/Proofs/Lambda/Lambda.thy\<close>), with constructors renamed.
\<close>

datatype dB =
    DVar nat
  | DApp dB dB
  | DAbs dB

primrec lift :: "dB \<Rightarrow> nat \<Rightarrow> dB" where
  "lift (DVar i) k = (if i < k then DVar i else DVar (i + 1))"
| "lift (DApp s t) k = DApp (lift s k) (lift t k)"
| "lift (DAbs s) k = DAbs (lift s (k + 1))"

primrec subst :: "dB \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB" ("_[_'/_]" [300, 0, 0] 300) where
  subst_Var: "(DVar i)[s/k] = (if k < i then DVar (i - 1) else if i = k then s else DVar i)"
| subst_App: "(DApp t u)[s/k] = DApp (t[s/k]) (u[s/k])"
| subst_Abs: "(DAbs t)[s/k] = DAbs (t[lift s 0 / k + 1])"

declare subst_Var [simp del]

lemma subst_eq [simp]: "(DVar k)[u/k] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j \<Longrightarrow> (DVar j)[u/i] = DVar (j - 1)"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i \<Longrightarrow> (DVar j)[u/i] = DVar j"
  by (simp add: subst_Var)

lemma lift_lift:
  "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst_lt:
  "i < j + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
  by (induct t arbitrary: i j s) (auto simp: lift_lift subst_Var)

lemma subst_lift [simp]: "(lift t k)[s/k] = t"
  by (induct t arbitrary: k s) simp_all

subsection \<open>Weak-head reduction\<close>

inductive hred :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>h" 50) where
  hbeta: "DApp (DAbs s) t \<rightarrow>\<^sub>h s[t/0]"
| happ: "s \<rightarrow>\<^sub>h s' \<Longrightarrow> DApp s t \<rightarrow>\<^sub>h DApp s' t"

lemma DAbs_no_step: "DAbs s \<rightarrow>\<^sub>h t \<Longrightarrow> False"
  by (auto elim: hred.cases)

lemma hred_det: "s \<rightarrow>\<^sub>h t \<Longrightarrow> s \<rightarrow>\<^sub>h u \<Longrightarrow> t = u"
proof (induction arbitrary: u rule: hred.induct)
  case (hbeta s t)
  from hbeta.prems show ?case
  proof (cases rule: hred.cases)
    case hbeta
    then show ?thesis by simp
  next
    case happ
    then obtain s1' where "DAbs s \<rightarrow>\<^sub>h s1'" by blast
    then show ?thesis by (rule DAbs_no_step[THEN FalseE])
  qed
next
  case (happ s s' t)
  note h1 = happ.hyps(1) and IH = happ.IH
  from happ.prems show ?case
  proof (cases rule: hred.cases)
    case hbeta
    then obtain s0 where "s = DAbs s0" by blast
    with h1 have "DAbs s0 \<rightarrow>\<^sub>h s'" by simp
    then show ?thesis by (rule DAbs_no_step[THEN FalseE])
  next
    case happ
    then obtain s1' where u: "u = DApp s1' t" and st: "s \<rightarrow>\<^sub>h s1'" by blast
    from IH[OF st] u show ?thesis by simp
  qed
qed

definition lam_WHN :: "dB \<Rightarrow> bool" where
  "lam_WHN t \<longleftrightarrow> (\<exists>u. hred\<^sup>*\<^sup>* t u \<and> normal hred u)"

text \<open>Number of steps to the normal form (unique by determinism).\<close>

inductive hdist :: "dB \<Rightarrow> nat \<Rightarrow> bool" where
  hd0: "normal hred t \<Longrightarrow> hdist t 0"
| hdS: "t \<rightarrow>\<^sub>h u \<Longrightarrow> hdist u n \<Longrightarrow> hdist t (Suc n)"

lemma lam_WHN_hdist: "lam_WHN t \<Longrightarrow> \<exists>n. hdist t n"
proof -
  assume "lam_WHN t"
  then obtain u where r: "hred\<^sup>*\<^sup>* t u" and nf: "normal hred u"
    by (auto simp: lam_WHN_def)
  from r show ?thesis
  proof (induction rule: converse_rtranclp_induct)
    case base
    then show ?case using nf hd0 by blast
  next
    case (step y z)
    then show ?case using hdS by blast
  qed
qed

lemma hdist_step:
  assumes "hdist t n" "t \<rightarrow>\<^sub>h u"
  shows "\<exists>m. n = Suc m \<and> hdist u m"
  using assms(1)
proof (cases rule: hdist.cases)
  case hd0
  then show ?thesis using assms(2) by (auto simp: normal_def)
next
  case (hdS u' m)
  then show ?thesis using assms(2) hred_det by blast
qed

end
