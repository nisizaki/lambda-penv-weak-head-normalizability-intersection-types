theory Main_Results
  imports Soundness
begin

section \<open>Main results\<close>

theorem main_characterization: "Typ M \<longleftrightarrow> CFWHN M"
  using soundness completeness by blast

theorem main_characterization_SN: "Typ M \<longleftrightarrow> CFWHSN M"
  using main_characterization CFWHN_imp_CFWHSN CFWHSN_imp_CFWHN by blast

corollary clash_not_Typ: "WHNF M \<Longrightarrow> clash M \<Longrightarrow> \<not> Typ M"
proof
  assume nf: "WHNF M" and cl: "clash M" and "Typ M"
  then have "CFWHN M" using main_characterization by blast
  then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and "\<not> clash N" unfolding CFWHN_def by blast
  moreover have "N = M" using normal_rtranclp[OF nf r] .
  ultimately show False using cl by simp
qed

text \<open>Oracle check: the main theorems depend on no oracle (in particular no \<open>sorry\<close>).\<close>

thm_oracles main_characterization main_characterization_SN

ML \<open>
  val ths = [@{thm main_characterization}, @{thm main_characterization_SN}, @{thm clash_not_Typ}];
  val oracles = Thm_Deps.all_oracles ths;
  val _ = if null oracles then writeln "No oracles."
          else if Config.get @{context} quick_and_dirty
          then warning ("Oracles used (quick_and_dirty): " ^ commas (map (#1 o #1) oracles))
          else error ("Oracles used: " ^ commas (map (#1 o #1) oracles));
\<close>

end
