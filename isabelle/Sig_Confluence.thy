theory Sig_Confluence
  imports Reduction
begin

section \<open>Confluence of \<open>\<sigma>\<close>-reduction\<close>

subsection \<open>Newman's lemma\<close>

lemma newman:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes loc: "\<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow> \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
    and sn: "SN_at R a"
  shows "\<forall>b c. R\<^sup>*\<^sup>* a b \<longrightarrow> R\<^sup>*\<^sup>* a c \<longrightarrow> (\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d)"
  using sn
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof (intro allI impI)
    fix b c
    assume ab: "R\<^sup>*\<^sup>* a b" and ac: "R\<^sup>*\<^sup>* a c"
    show "\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
    proof (rule converse_rtranclpE[OF ab])
      assume "a = b"
      then show ?thesis using ac by auto
    next
      fix b1
      assume ab1: "R a b1" and b1b: "R\<^sup>*\<^sup>* b1 b"
      show ?thesis
      proof (rule converse_rtranclpE[OF ac])
        assume "a = c"
        then show ?thesis using ab by auto
      next
        fix c1
        assume ac1: "R a c1" and c1c: "R\<^sup>*\<^sup>* c1 c"
        from loc[OF ab1 ac1] obtain d0 where d1: "R\<^sup>*\<^sup>* b1 d0" and d2: "R\<^sup>*\<^sup>* c1 d0"
          by blast
        from step.IH[OF ab1] b1b d1 obtain e where e1: "R\<^sup>*\<^sup>* b e" and e2: "R\<^sup>*\<^sup>* d0 e"
          by blast
        have c1e: "R\<^sup>*\<^sup>* c1 e" using d2 e2 by (rule rtranclp_trans)
        from step.IH[OF ac1] c1c c1e obtain f where f1: "R\<^sup>*\<^sup>* c f" and f2: "R\<^sup>*\<^sup>* e f"
          by blast
        have "R\<^sup>*\<^sup>* b f" using e1 f2 by (rule rtranclp_trans)
        with f1 show ?thesis by blast
      qed
    qed
  qed
qed

subsection \<open>Congruences and joinability\<close>

abbreviation sst :: "trm \<Rightarrow> trm \<Rightarrow> bool" where "sst \<equiv> sig\<^sup>*\<^sup>*"

definition jn :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "jn A B \<longleftrightarrow> (\<exists>P. sst A P \<and> sst B P)"

lemma jn_refl: "jn A A" by (auto simp: jn_def)
lemma jn_sym: "jn A B \<Longrightarrow> jn B A" by (auto simp: jn_def)
lemma jn_stepL: "sig A A' \<Longrightarrow> jn A' B \<Longrightarrow> jn A B"
  by (auto simp: jn_def intro: converse_rtranclp_into_rtranclp)
lemma jn_stepR: "sig B B' \<Longrightarrow> jn A B' \<Longrightarrow> jn A B"
  by (auto simp: jn_def intro: converse_rtranclp_into_rtranclp)

lemma sc_AppL: "sst M M' \<Longrightarrow> sst (App M L) (App M' L)"
  by (induction rule: rtranclp.induct) (auto intro: sig.AppL rtranclp.rtrancl_into_rtrancl)
lemma sc_AppR: "sst M M' \<Longrightarrow> sst (App L M) (App L M')"
  by (induction rule: rtranclp.induct) (auto intro: sig.AppR rtranclp.rtrancl_into_rtrancl)
lemma sc_Lam: "sst M M' \<Longrightarrow> sst (Lam x M) (Lam x M')"
  by (induction rule: rtranclp.induct) (auto intro: sig.Lam rtranclp.rtrancl_into_rtrancl)
lemma sc_CompL: "sst M M' \<Longrightarrow> sst (Comp M L) (Comp M' L)"
  by (induction rule: rtranclp.induct) (auto intro: sig.CompL rtranclp.rtrancl_into_rtrancl)
lemma sc_CompR: "sst M M' \<Longrightarrow> sst (Comp L M) (Comp L M')"
  by (induction rule: rtranclp.induct) (auto intro: sig.CompR rtranclp.rtrancl_into_rtrancl)
lemma sc_ExtnL: "sst M M' \<Longrightarrow> sst (Extn M x L) (Extn M' x L)"
  by (induction rule: rtranclp.induct) (auto intro: sig.ExtnL rtranclp.rtrancl_into_rtrancl)
lemma sc_ExtnR: "sst M M' \<Longrightarrow> sst (Extn L x M) (Extn L x M')"
  by (induction rule: rtranclp.induct) (auto intro: sig.ExtnR rtranclp.rtrancl_into_rtrancl)

lemma jn_AppL: "jn A B \<Longrightarrow> jn (App A L) (App B L)"
  by (auto simp: jn_def dest: sc_AppL)
lemma jn_AppR: "jn A B \<Longrightarrow> jn (App L A) (App L B)"
  by (auto simp: jn_def dest: sc_AppR)
lemma jn_Lam: "jn A B \<Longrightarrow> jn (Lam x A) (Lam x B)"
  by (auto simp: jn_def dest: sc_Lam)
lemma jn_CompL: "jn A B \<Longrightarrow> jn (Comp A L) (Comp B L)"
  by (auto simp: jn_def dest: sc_CompL)
lemma jn_CompR: "jn A B \<Longrightarrow> jn (Comp L A) (Comp L B)"
  by (auto simp: jn_def dest: sc_CompR)
lemma jn_ExtnL: "jn A B \<Longrightarrow> jn (Extn A x L) (Extn B x L)"
  by (auto simp: jn_def dest: sc_ExtnL)
lemma jn_ExtnR: "jn A B \<Longrightarrow> jn (Extn L x A) (Extn L x B)"
  by (auto simp: jn_def dest: sc_ExtnR)

subsection \<open>Inversion lemmas\<close>

lemma sig_Var_no [simp]: "\<not> sig (Var x) Y"
  by (auto elim: sig.cases)
lemma sig_Id_no [simp]: "\<not> sig Id Y"
  by (auto elim: sig.cases)

lemma sig_Nm_no [simp]: "\<not> sig (Nm x) Y"
  by (auto elim: sig.cases)

lemma inv_App:
  assumes "sig (App A B) X"
  obtains (c_L) A' where "sig A A'" "X = App A' B"
  | (c_R) B' where "sig B B'" "X = App A B'"
  | (c_AC) x where "B = Nm x" "X = Comp (Var x) A"
  using assms by (cases rule: sig.cases) fastforce+

lemma inv_Lam:
  assumes "sig (Lam x A) X"
  obtains A' where "sig A A'" "X = Lam x A'"
  using assms by (cases rule: sig.cases) fastforce+

lemma inv_Extn:
  assumes "sig (Extn A x B) X"
  obtains (c_L) A' where "sig A A'" "X = Extn A' x B"
  | (c_R) B' where "sig B B'" "X = Extn A x B'"
  using assms by (cases rule: sig.cases) fastforce+

lemma inv_Comp:
  assumes "sig (Comp A B) X"
  obtains (c_Ass) L M where "A = Comp L M" "X = Comp L (Comp M B)"
  | (c_IdL) "A = Id" "X = B"
  | (c_IdR) "B = Id" "X = A"
  | (c_DExtn) L x M where "A = Extn L x M" "X = Extn (Comp L B) x (Comp M B)"
  | (c_VarRef) x M N where "A = Var x" "B = Extn M x N" "X = M"
  | (c_VarSkip) x y M N where "x \<noteq> y" "A = Var y" "B = Extn M x N" "X = Comp (Var y) N"
  | (c_DApp) M1 M2 where "A = App M1 M2" "X = App (Comp M1 B) (Comp M2 B)"
  | (c_CC) x where "A = Nm x" "X = Nm x"
  | (c_L) A' where "sig A A'" "X = Comp A' B"
  | (c_R) B' where "sig B B'" "X = Comp A B'"
  using assms by (cases rule: sig.cases) fastforce+

inductive rt :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Ass: "rt (Comp (Comp L M) N) (Comp L (Comp M N))"
| IdL: "rt (Comp Id M) M"
| IdR: "rt (Comp M Id) M"
| DExtn: "rt (Comp (Extn L x M) N) (Extn (Comp L N) x (Comp M N))"
| VarRef: "rt (Comp (Var x) (Extn M x N)) M"
| VarSkip: "x \<noteq> y \<Longrightarrow> rt (Comp (Var y) (Extn M x N)) (Comp (Var y) N)"
| DApp: "rt (Comp (App M1 M2) N) (App (Comp M1 N) (Comp M2 N))"
| ConstComp: "rt (Comp (Nm x) L) (Nm x)"

lemma inv_Comp_rt:
  assumes "sig (Comp A B) X"
  obtains (root) "rt (Comp A B) X"
  | (c_L) A' where "sig A A'" "X = Comp A' B"
  | (c_R) B' where "sig B B'" "X = Comp A B'"
  using assms by (cases rule: inv_Comp) (auto intro: rt.intros)

subsection \<open>Root steps against arbitrary steps\<close>

lemmas jn_tac = jn_stepL jn_stepR jn_refl sig.intros

lemma r_Ass: "sig (Comp (Comp L M) N) X \<Longrightarrow> jn (Comp L (Comp M N)) X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_IdL: "sig (Comp Id M) X \<Longrightarrow> jn M X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_IdR: "sig (Comp M Id) X \<Longrightarrow> jn M X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_DExtn: "sig (Comp (Extn L x M) N) X \<Longrightarrow> jn (Extn (Comp L N) x (Comp M N)) X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_VarRef: "sig (Comp (Var x) (Extn M x N)) X \<Longrightarrow> jn M X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_VarSkip: "x \<noteq> y \<Longrightarrow> sig (Comp (Var y) (Extn M x N)) X \<Longrightarrow> jn (Comp (Var y) N) X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_DApp: "sig (Comp (App M1 M2) N) X \<Longrightarrow> jn (App (Comp M1 N) (Comp M2 N)) X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma r_ConstComp: "sig (Comp (Nm x) L) X \<Longrightarrow> jn (Nm x) X"
  by (erule inv_Comp; (clarsimp)?; ((erule inv_Comp | erule inv_Extn | erule inv_App))?; (clarsimp)?; blast intro: jn_tac)

lemma root_join: "rt A B \<Longrightarrow> sig A X \<Longrightarrow> jn B X"
  by (induction rule: rt.induct)
     (blast intro: r_Ass r_IdL r_IdR r_DExtn r_VarRef r_VarSkip r_DApp r_ConstComp)+

subsection \<open>Local confluence and confluence\<close>

lemma lc:
  assumes "sig M N1"
  shows "\<forall>N2. sig M N2 \<longrightarrow> jn N1 N2"
  using assms
proof (induction rule: sig.induct)
  case (Ass L M N)
  then show ?case using r_Ass by blast
next
  case (IdL M)
  then show ?case using r_IdL by blast
next
  case (IdR M)
  then show ?case using r_IdR by blast
next
  case (DExtn L x M N)
  then show ?case using r_DExtn by blast
next
  case (VarRef x M N)
  then show ?case using r_VarRef by blast
next
  case (VarSkip x y M N)
  then show ?case using r_VarSkip VarSkip.hyps by blast
next
  case (DApp M1 M2 N)
  then show ?case using r_DApp by blast
next
  case (AppConst M x)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (App M (Nm x)) X"
    show "jn (Comp (Var x) M) X"
    proof (rule inv_App[OF h])
      fix A' assume c1: "sig M A'" and c2: "X = App A' (Nm x)"
      show ?thesis using c1 c2 by (blast intro: jn_tac)
    qed (simp_all add: jn_refl)
  qed
next
  case (ConstComp x L)
  then show ?case using r_ConstComp by blast
next
  case (AppL M N L)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (App M L) X"
    show "jn (App N L) X"
    proof (rule inv_App[OF h])
      fix A' assume c1: "sig M A'" and c2: "X = App A' L"
      from AppL.IH c1 have "jn N A'" by blast
      then have "jn (App N L) (App A' L)" by (rule jn_AppL)
      then show ?thesis by (simp add: c2)
    next
      fix B' assume c1: "sig L B'" and c2: "X = App M B'"
      show ?thesis using AppL.hyps c1 c2 by (blast intro: jn_tac)
    next
      fix x assume c1: "L = Nm x" and c2: "X = Comp (Var x) M"
      show ?thesis using AppL.hyps c1 c2 by (blast intro: jn_tac)
    qed
  qed
next
  case (AppR M N L)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (App L M) X"
    show "jn (App L N) X"
    proof (rule inv_App[OF h])
      fix A' assume c1: "sig L A'" and c2: "X = App A' M"
      show ?thesis using AppR.hyps c1 c2 by (blast intro: jn_tac)
    next
      fix B' assume c1: "sig M B'" and c2: "X = App L B'"
      from AppR.IH c1 have "jn N B'" by blast
      then have "jn (App L N) (App L B')" by (rule jn_AppR)
      then show ?thesis by (simp add: c2)
    next
      fix x assume "M = Nm x"
      with AppR.hyps show ?thesis by simp
    qed
  qed
next
  case (Lam M N x)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (Lam x M) X"
    from h obtain A' where a: "sig M A'" "X = Lam x A'" by (rule inv_Lam)
    with Lam.IH have "jn N A'" by blast
    then have "jn (Lam x N) (Lam x A')" by (rule jn_Lam)
    then show "jn (Lam x N) X" by (simp add: a(2))
  qed
next
  case (CompL M N L)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (Comp M L) X"
    show "jn (Comp N L) X"
    proof (rule inv_Comp_rt[OF h])
      assume root: "rt (Comp M L) X"
      have "sig (Comp M L) (Comp N L)" by (rule sig.CompL[OF CompL.hyps])
      then have "jn X (Comp N L)" by (rule root_join[OF root])
      then show ?thesis by (rule jn_sym)
    next
      fix A' assume c1: "sig M A'" and c2: "X = Comp A' L"
      from CompL.IH c1 have "jn N A'" by blast
      then have "jn (Comp N L) (Comp A' L)" by (rule jn_CompL)
      then show ?thesis by (simp add: c2)
    next
      fix B' assume c1: "sig L B'" and c2: "X = Comp M B'"
      show ?thesis using CompL.hyps c1 c2 by (blast intro: jn_tac)
    qed
  qed
next
  case (CompR M N L)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (Comp L M) X"
    show "jn (Comp L N) X"
    proof (rule inv_Comp_rt[OF h])
      assume root: "rt (Comp L M) X"
      have "sig (Comp L M) (Comp L N)" by (rule sig.CompR[OF CompR.hyps])
      then have "jn X (Comp L N)" by (rule root_join[OF root])
      then show ?thesis by (rule jn_sym)
    next
      fix A' assume c1: "sig L A'" and c2: "X = Comp A' M"
      show ?thesis using CompR.hyps c1 c2 by (blast intro: jn_tac)
    next
      fix B' assume c1: "sig M B'" and c2: "X = Comp L B'"
      from CompR.IH c1 have "jn N B'" by blast
      then have "jn (Comp L N) (Comp L B')" by (rule jn_CompR)
      then show ?thesis by (simp add: c2)
    qed
  qed
next
  case (ExtnL M N x L)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (Extn M x L) X"
    show "jn (Extn N x L) X"
    proof (rule inv_Extn[OF h])
      fix A' assume c1: "sig M A'" and c2: "X = Extn A' x L"
      from ExtnL.IH c1 have "jn N A'" by blast
      then have "jn (Extn N x L) (Extn A' x L)" by (rule jn_ExtnL)
      then show ?thesis by (simp add: c2)
    next
      fix B' assume c1: "sig L B'" and c2: "X = Extn M x B'"
      show ?thesis using ExtnL.hyps c1 c2 by (blast intro: jn_tac)
    qed
  qed
next
  case (ExtnR M N L x)
  show ?case
  proof (intro allI impI)
    fix X assume h: "sig (Extn L x M) X"
    show "jn (Extn L x N) X"
    proof (rule inv_Extn[OF h])
      fix A' assume c1: "sig L A'" and c2: "X = Extn A' x M"
      show ?thesis using ExtnR.hyps c1 c2 by (blast intro: jn_tac)
    next
      fix B' assume c1: "sig M B'" and c2: "X = Extn L x B'"
      from ExtnR.IH c1 have "jn N B'" by blast
      then have "jn (Extn L x N) (Extn L x B')" by (rule jn_ExtnR)
      then show ?thesis by (simp add: c2)
    qed
  qed
qed

lemma sig_local_confluent:
  "M \<rightarrow>\<^sub>\<sigma> N1 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N2 \<Longrightarrow> \<exists>P. sig\<^sup>*\<^sup>* N1 P \<and> sig\<^sup>*\<^sup>* N2 P"
  using lc[of M N1] by (auto simp: jn_def)

theorem sig_confluent:
  "sig\<^sup>*\<^sup>* M N1 \<Longrightarrow> sig\<^sup>*\<^sup>* M N2 \<Longrightarrow> \<exists>P. sig\<^sup>*\<^sup>* N1 P \<and> sig\<^sup>*\<^sup>* N2 P"
proof -
  assume h1: "sig\<^sup>*\<^sup>* M N1" and h2: "sig\<^sup>*\<^sup>* M N2"
  have loc: "\<And>a b c. sig a b \<Longrightarrow> sig a c \<Longrightarrow> \<exists>d. sig\<^sup>*\<^sup>* b d \<and> sig\<^sup>*\<^sup>* c d"
    by (rule sig_local_confluent)
  have key: "\<forall>b c. sig\<^sup>*\<^sup>* M b \<longrightarrow> sig\<^sup>*\<^sup>* M c \<longrightarrow> (\<exists>d. sig\<^sup>*\<^sup>* b d \<and> sig\<^sup>*\<^sup>* c d)"
    by (rule newman[OF loc sig_SN])
  from key[rule_format, OF h1 h2] show ?thesis .
qed

end
