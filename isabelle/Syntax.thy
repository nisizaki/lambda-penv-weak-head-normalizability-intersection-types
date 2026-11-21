theory Syntax
  imports Main
begin

section \<open>Syntax of \<open>\<lambda>penv\<^sub>w\<^sub>h\<close>: \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> with quoted names\<close>

text \<open>
  Term variables are natural numbers.  There is no \<open>\<alpha>\<close>-equivalence:
  equality of terms is syntactic identity of the first-order datatype.
\<close>

type_synonym var = nat

datatype (plugins del: "quickcheck") trm =
    Var var
  | Lam var trm
  | App trm trm
  | Id
  | Extn trm var trm
  | Comp trm trm
  | Nm var   \<comment> \<open>quoted name \<open>\<lceil>x\<rceil>\<close> (\<open>Const (CName x)\<close> in \<open>\<lambda>penv\<close>)\<close>

fun tlength :: "trm \<Rightarrow> nat" where
  "tlength (Var x) = 1"
| "tlength (App M N) = tlength M + tlength N + 1"
| "tlength (Lam x M) = tlength M * 2"
| "tlength (Comp M N) = tlength M * (tlength N + 1)"
| "tlength Id = 1"
| "tlength (Extn M x N) = tlength M + tlength N + 1"
| "tlength (Nm x) = 1"

lemma tlength_pos [simp]: "0 < tlength M"
  by (induction M) simp_all

fun names :: "trm \<Rightarrow> var set" where
  "names (Var x) = {x}"
| "names (Lam x M) = insert x (names M)"
| "names (App M N) = names M \<union> names N"
| "names Id = {}"
| "names (Extn M x N) = insert x (names M \<union> names N)"
| "names (Comp M N) = names M \<union> names N"
| "names (Nm x) = {x}"

text \<open>Environment heads: terms that, applied to a quoted name, look it up.\<close>

fun envh :: "trm \<Rightarrow> bool" where
  "envh Id = True"
| "envh (Extn M x L) = True"
| "envh _ = False"

lemma names_finite [simp]: "finite (names M)"
  by (induction M) auto

end
