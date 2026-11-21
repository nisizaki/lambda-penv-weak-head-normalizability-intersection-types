theory Typing
  imports Syntax
begin

section \<open>Intersection types with \<open>\<omega>\<close> and environment types\<close>

text \<open>
  \<open>Env m ob\<close>: \<open>m\<close> is an association list (first binding wins), \<open>ob = True\<close> is the
  open tail (essential), \<open>ob = False\<close> is the top tail (\<open>Env [] False\<close> plays the
  role of \<open>\<omega>\<close> as an environment).
\<close>

datatype ty =
    TV nat
  | Om
  | Arr ty ty
  | Inter ty ty
  | Env "(var \<times> ty) list" bool
  | QN var   \<comment> \<open>name type \<open>Q x\<close>: the type of the quoted name \<open>\<lceil>x\<rceil>\<close>\<close>

definition emeet :: "(var \<times> ty) list \<Rightarrow> (var \<times> ty) list \<Rightarrow> (var \<times> ty) list" where
  "emeet m1 m2 =
     map (\<lambda>(x, A). (x, case map_of m2 x of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)) m1 @ m2"

lemma map_of_map_dep:
  "map_of (map (\<lambda>(x, A). (x, f x A)) m) y = map_option (f y) (map_of m y)"
  by (induction m) auto

lemma map_of_emeet:
  "map_of (emeet m1 m2) y =
     (case map_of m1 y of
        Some A \<Rightarrow> Some (case map_of m2 y of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)
      | None \<Rightarrow> map_of m2 y)"
  by (auto simp: emeet_def map_of_map_dep map_add_def split: option.split)

subsection \<open>Subtyping \<open>\<le>\<^sub>0\<close>\<close>

inductive sub :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "\<preceq>" 50) where
  s_refl: "A \<preceq> A"
| s_trans: "A \<preceq> B \<Longrightarrow> B \<preceq> C \<Longrightarrow> A \<preceq> C"
| s_top: "A \<preceq> Om"
| s_il: "Inter A B \<preceq> A"
| s_ir: "Inter A B \<preceq> B"
| s_glb: "C \<preceq> A \<Longrightarrow> C \<preceq> B \<Longrightarrow> C \<preceq> Inter A B"
| s_arr: "A' \<preceq> A \<Longrightarrow> B \<preceq> B' \<Longrightarrow> Arr A B \<preceq> Arr A' B'"
| s_env: "(\<forall>x A'. map_of m' x = Some A' \<longrightarrow> (\<exists>A. map_of m x = Some A \<and> A \<preceq> A')) \<Longrightarrow>
          (ob' \<longrightarrow> ob) \<Longrightarrow> Env m ob \<preceq> Env m' ob'"
| s_emeet: "Inter (Env m1 o1) (Env m2 o2) \<preceq> Env (emeet m1 m2) (o1 \<or> o2)"
| s_omenv: "Om \<preceq> Env [] False"
| s_envarr: "map_of m x = Some A \<Longrightarrow> Env m ob \<preceq> Arr (QN x) A"
| s_arrenv: "Arr (QN x) A \<preceq> Env [(x, A)] False"

fun ess :: "ty \<Rightarrow> bool" where
  "ess (TV n) = True"
| "ess Om = False"
| "ess (Arr A B) = True"
| "ess (Inter A B) = (ess A \<or> ess B)"
| "ess (Env m ob) = (m \<noteq> [] \<or> ob)"
| "ess (QN x) = True"

lemma ess_down: "A \<preceq> B \<Longrightarrow> ess B \<Longrightarrow> ess A"
proof (induction rule: sub.induct)
  case (s_env m' m ob' ob)
  show ?case
  proof (cases "m' = []")
    case True
    then show ?thesis using s_env by auto
  next
    case False
    then obtain p ps where "m' = p # ps" by (cases m') auto
    then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
    then obtain x A' where "map_of m' x = Some A'" by blast
    with s_env.IH obtain A where "map_of m x = Some A" by blast
    then show ?thesis by auto
  qed
next
  case (s_emeet m1 o1 m2 o2)
  then show ?case by (auto simp: emeet_def)
qed auto

lemma sub_env_ext_meet1:
  "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Env ((x, B1) # m1) o1"
proof (rule s_env)
  show "\<forall>y A'. map_of ((x, B1) # m1) y = Some A' \<longrightarrow>
         (\<exists>A. map_of ((x, Inter B1 B2) # emeet m1 m2) y = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_il s_refl split: option.split)
qed simp

lemma sub_env_ext_meet2:
  "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Env ((x, B2) # m2) o2"
proof (rule s_env)
  show "\<forall>y A'. map_of ((x, B2) # m2) y = Some A' \<longrightarrow>
         (\<exists>A. map_of ((x, Inter B1 B2) # emeet m1 m2) y = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_ir s_refl split: option.split)
qed simp

subsection \<open>Typing (contexts are arbitrary types)\<close>

inductive hasty :: "ty \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51, 51, 51] 50) where
  TVar: "C \<preceq> Env m ob \<Longrightarrow> map_of m x = Some A \<Longrightarrow> C \<turnstile> Var x : A"
| TLam: "C \<preceq> Env m ob \<Longrightarrow> Env ((x, A) # m) ob \<turnstile> M : B \<Longrightarrow> C \<turnstile> Lam x M : Arr A B"
| TApp: "C \<turnstile> M : Arr A B \<Longrightarrow> C \<turnstile> N : A \<Longrightarrow> C \<turnstile> App M N : B"
| TId: "C \<turnstile> Id : C"
| TExtn: "C \<turnstile> M : A \<Longrightarrow> C \<turnstile> N : Env m ob \<Longrightarrow> C \<turnstile> Extn M x N : Env ((x, A) # m) ob"
| TComp: "C \<turnstile> N : D \<Longrightarrow> D \<turnstile> M : A \<Longrightarrow> C \<turnstile> Comp M N : A"
| TOm: "C \<turnstile> M : Om"
| TInter: "C \<turnstile> M : A \<Longrightarrow> C \<turnstile> M : B \<Longrightarrow> C \<turnstile> M : Inter A B"
| TSub: "C \<turnstile> M : A \<Longrightarrow> A \<preceq> B \<Longrightarrow> C \<turnstile> M : B"
| TNm: "C \<turnstile> Nm x : QN x"

text \<open>Types without name types (decision D4: free variables are not names).\<close>

fun qfree :: "ty \<Rightarrow> bool" where
  "qfree (TV n) = True"
| "qfree Om = True"
| "qfree (Arr A B) = (qfree A \<and> qfree B)"
| "qfree (Inter A B) = (qfree A \<and> qfree B)"
| "qfree (Env m ob) = (\<forall>p \<in> set m. qfree (snd p))"
| "qfree (QN x) = False"

definition Typ :: "trm \<Rightarrow> bool" where
  "Typ M \<longleftrightarrow> (\<exists>m ob A. Env m ob \<turnstile> M : A \<and> ess A \<and> (\<forall>p \<in> set m. qfree (snd p)))"

subsection \<open>Narrowing of contexts\<close>

lemma narrowing: "C \<turnstile> M : A \<Longrightarrow> C' \<preceq> C \<Longrightarrow> C' \<turnstile> M : A"
proof (induction arbitrary: C' rule: hasty.induct)
  case (TVar C m ob x A)
  then show ?case by (blast intro: hasty.TVar s_trans)
next
  case (TLam C m ob x A M B)
  then show ?case by (blast intro: hasty.TLam s_trans)
next
  case (TApp C M A B N)
  then show ?case by (blast intro: hasty.TApp)
next
  case (TId C)
  then show ?case by (blast intro: hasty.TId hasty.TSub)
next
  case (TExtn C M A N m ob x)
  then show ?case by (blast intro: hasty.TExtn)
next
  case (TComp C N D M A)
  then show ?case by (blast intro: hasty.TComp)
next
  case (TOm C M)
  show ?case by (rule hasty.TOm)
next
  case (TInter C M A B)
  then show ?case by (blast intro: hasty.TInter)
next
  case (TSub C M A B)
  then show ?case by (blast intro: hasty.TSub)
next
  case (TNm C x)
  show ?case by (rule hasty.TNm)
qed

lemma typ_env_om: "C \<turnstile> M : Env [] False"
  by (rule TSub[OF TOm s_omenv])

subsection \<open>Generation lemmas\<close>

lemma gen_Id: "C \<turnstile> P : A \<Longrightarrow> P = Id \<Longrightarrow> C \<preceq> A"
  by (induction rule: hasty.induct) (auto intro: s_refl s_trans s_top s_glb)

lemma gen_Comp:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp M L \<Longrightarrow> \<exists>D. C \<turnstile> L : D \<and> D \<turnstile> M : A"
proof (induction rule: hasty.induct)
  case (TComp C N D M' A)
  then show ?case by blast
next
  case (TOm C P)
  then show ?case by (blast intro: hasty.TOm)
next
  case (TInter C P A B)
  then obtain D1 D2 where 1: "C \<turnstile> L : D1" "D1 \<turnstile> M : A" and 2: "C \<turnstile> L : D2" "D2 \<turnstile> M : B"
    by blast
  have "C \<turnstile> L : Inter D1 D2" using 1 2 by (blast intro: hasty.TInter)
  moreover have "Inter D1 D2 \<turnstile> M : Inter A B"
    using 1 2 by (blast intro: hasty.TInter narrowing s_il s_ir)
  ultimately show ?case by blast
next
  case (TSub C P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma gen_Extn:
  "C \<turnstile> P : D \<Longrightarrow> P = Extn N x L \<Longrightarrow>
     \<exists>B m ob. C \<turnstile> N : B \<and> C \<turnstile> L : Env m ob \<and> Env ((x, B) # m) ob \<preceq> D"
proof (induction rule: hasty.induct)
  case (TExtn C M A N' m ob x')
  then show ?case by (blast intro: s_refl)
next
  case (TOm C P)
  have "Env [(x, Om)] False \<preceq> Om" by (rule s_top)
  then show ?case using hasty.TOm typ_env_om by blast
next
  case (TInter C P A B)
  then obtain B1 m1 o1 B2 m2 o2 where
    1: "C \<turnstile> N : B1" "C \<turnstile> L : Env m1 o1" "Env ((x, B1) # m1) o1 \<preceq> A" and
    2: "C \<turnstile> N : B2" "C \<turnstile> L : Env m2 o2" "Env ((x, B2) # m2) o2 \<preceq> B"
    by blast
  have "C \<turnstile> N : Inter B1 B2" using 1 2 by (blast intro: hasty.TInter)
  moreover have "C \<turnstile> L : Env (emeet m1 m2) (o1 \<or> o2)"
    using 1 2 by (blast intro: hasty.TInter hasty.TSub s_emeet)
  moreover have "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Inter A B"
    using 1 2 by (blast intro: s_glb s_trans sub_env_ext_meet1 sub_env_ext_meet2)
  ultimately show ?case by blast
next
  case (TSub C P A B)
  then show ?case by (blast intro: s_trans)
qed auto

lemma gen_Nm: "C \<turnstile> P : A \<Longrightarrow> P = Nm x \<Longrightarrow> QN x \<preceq> A"
  by (induction rule: hasty.induct) (auto intro: s_refl s_trans s_top s_glb)

lemma gen_Var:
  "D \<turnstile> P : A \<Longrightarrow> P = Var y \<Longrightarrow>
     Om \<preceq> A \<or> (\<exists>m ob B. D \<preceq> Env m ob \<and> map_of m y = Some B \<and> B \<preceq> A)"
proof (induction rule: hasty.induct)
  case (TVar C m ob x A)
  then show ?case by (blast intro: s_refl)
next
  case (TOm C P)
  then show ?case by (blast intro: s_refl)
next
  case (TInter C P A B)
  from TInter.IH TInter.prems consider
      (oo) "Om \<preceq> A" "Om \<preceq> B"
    | (oe) "Om \<preceq> A" "\<exists>m ob B'. C \<preceq> Env m ob \<and> map_of m y = Some B' \<and> B' \<preceq> B"
    | (eo) "\<exists>m ob B'. C \<preceq> Env m ob \<and> map_of m y = Some B' \<and> B' \<preceq> A" "Om \<preceq> B"
    | (ee) "\<exists>m ob B'. C \<preceq> Env m ob \<and> map_of m y = Some B' \<and> B' \<preceq> A"
           "\<exists>m ob B'. C \<preceq> Env m ob \<and> map_of m y = Some B' \<and> B' \<preceq> B"
    by blast
  then show ?case
  proof cases
    case oo
    then show ?thesis by (blast intro: s_glb)
  next
    case oe
    then obtain m ob B' where "C \<preceq> Env m ob" "map_of m y = Some B'" "B' \<preceq> B" by blast
    moreover have "B' \<preceq> A" using oe(1) by (blast intro: s_trans s_top)
    ultimately show ?thesis by (blast intro: s_glb)
  next
    case eo
    then obtain m ob B' where "C \<preceq> Env m ob" "map_of m y = Some B'" "B' \<preceq> A" by blast
    moreover have "B' \<preceq> B" using eo(2) by (blast intro: s_trans s_top)
    ultimately show ?thesis by (blast intro: s_glb)
  next
    case ee
    then obtain m1 o1 B1 m2 o2 B2 where
      1: "C \<preceq> Env m1 o1" "map_of m1 y = Some B1" "B1 \<preceq> A" and
      2: "C \<preceq> Env m2 o2" "map_of m2 y = Some B2" "B2 \<preceq> B"
      by blast
    have "C \<preceq> Env (emeet m1 m2) (o1 \<or> o2)"
      using 1 2 by (blast intro: s_glb s_trans s_emeet)
    moreover have "map_of (emeet m1 m2) y = Some (Inter B1 B2)"
      using 1 2 by (simp add: map_of_emeet)
    moreover have "Inter B1 B2 \<preceq> Inter A B"
      using 1 2 by (blast intro: s_glb s_trans s_il s_ir)
    ultimately show ?thesis by blast
  qed
next
  case (TSub C P A B)
  then show ?case by (blast intro: s_trans)
qed auto

end
