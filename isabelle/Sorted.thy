theory Sorted
  imports Reduction
begin

section \<open>Sorted terms and the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> fragment of the reduction\<close>

text \<open>
  \<open>tm\<close>: term-sorted, \<open>en\<close>: environment-sorted (as in \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close>).  Quoted names
  are neither; hence sorted terms are exactly the sorted \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> terms.
\<close>

fun tm :: "trm \<Rightarrow> bool" and en :: "trm \<Rightarrow> bool" where
  "tm (Var x) = True"
| "tm (Lam x M) = tm M"
| "tm (App M N) = (tm M \<and> tm N)"
| "tm (Comp M L) = (tm M \<and> en L)"
| "tm Id = False"
| "tm (Extn M x L) = False"
| "tm (Nm x) = False"
| "en (Var x) = False"
| "en (Lam x M) = False"
| "en (App M N) = False"
| "en (Comp L1 L2) = (en L1 \<and> en L2)"
| "en Id = True"
| "en (Extn M x L) = (tm M \<and> en L)"
| "en (Nm x) = False"

fun pure :: "trm \<Rightarrow> bool" where
  "pure (Var x) = True"
| "pure (Lam x M) = pure M"
| "pure (App M N) = (pure M \<and> pure N)"
| "pure _ = False"

lemma pure_tm: "pure M \<Longrightarrow> tm M"
  by (induction M) auto

subsection \<open>The reduction of \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> (copied verbatim from the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> development)\<close>

inductive sig0 :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Ass: "sig0 (Comp (Comp L M) N) (Comp L (Comp M N))"
| IdL: "sig0 (Comp Id M) M"
| IdR: "sig0 (Comp M Id) M"
| DExtn: "sig0 (Comp (Extn L x M) N) (Extn (Comp L N) x (Comp M N))"
| VarRef: "sig0 (Comp (Var x) (Extn M x N)) M"
| VarSkip: "x \<noteq> y \<Longrightarrow> sig0 (Comp (Var y) (Extn M x N)) (Comp (Var y) N)"
| DApp: "sig0 (Comp (App M1 M2) N) (App (Comp M1 N) (Comp M2 N))"
| AppL: "sig0 M N \<Longrightarrow> sig0 (App M L) (App N L)"
| AppR: "sig0 M N \<Longrightarrow> sig0 (App L M) (App L N)"
| Lam: "sig0 M N \<Longrightarrow> sig0 (Lam x M) (Lam x N)"
| CompL: "sig0 M N \<Longrightarrow> sig0 (Comp M L) (Comp N L)"
| CompR: "sig0 M N \<Longrightarrow> sig0 (Comp L M) (Comp L N)"
| ExtnL: "sig0 M N \<Longrightarrow> sig0 (Extn M x L) (Extn N x L)"
| ExtnR: "sig0 M N \<Longrightarrow> sig0 (Extn L x M) (Extn L x N)"

inductive beta0 :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta1: "beta0 (App (Comp (Lam x M) L) N) (Comp M (Extn N x L))"
| Beta2: "beta0 (App (Lam x M) N) (Comp M (Extn N x Id))"
| AppL: "beta0 M N \<Longrightarrow> beta0 (App M L) (App N L)"
| CompL: "beta0 M N \<Longrightarrow> beta0 (Comp M L) (Comp N L)"
| VarR: "beta0 M N \<Longrightarrow> beta0 (Comp (Var x) M) (Comp (Var x) N)"

definition wh0 :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "wh0 M N \<longleftrightarrow> sig0 M N \<or> beta0 M N"

definition CFWHN0 :: "trm \<Rightarrow> bool" where
  "CFWHN0 M \<longleftrightarrow> (\<exists>N. wh0\<^sup>*\<^sup>* M N \<and> normal wh0 N)"

end
