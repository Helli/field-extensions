section \<open>Missing Preliminaries\<close>
theory Missing
  imports
    "HOL-Algebra.Ring_Divisibility"
    "VectorSpace_by_HoldenLee/Missing_VectorSpace"
begin

subsection \<open>Vector Spaces\<close>

lemma (in module) lin_indpt_empty: "lin_indpt {}"
  by (simp add: lin_dep_def)

lemma (in vectorspace) dim_greater_0:
  assumes fin_dim
  assumes "carrier V \<noteq> {\<zero>\<^bsub>V\<^esub>}"
  shows "dim > 0"
proof (rule ccontr, simp)
  assume "dim = 0"
  with \<open>fin_dim\<close> have "\<exists>A. finite A \<and> card A = 0 \<and> A \<subseteq> carrier V \<and> gen_set A"
    using assms basis_def dim_basis finite_basis_exists by auto
  then have "gen_set {}"
    by force
  then obtain v where "v \<in> carrier V" "v \<in> span {}" "v \<noteq> \<zero>\<^bsub>V\<^esub>"
    using assms(2) by blast
  then have "\<exists>a. lincomb a {} = v \<and> a\<in> ({}\<rightarrow>carrier K)"
    unfolding span_def by auto
  then show False unfolding lincomb_def
    using M.finsum_empty \<open>v \<noteq> \<zero>\<^bsub>V\<^esub>\<close> by blast
qed

text\<open>The next two lemmas formalise
  \<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LA_info_no_dates.pdf#chapter.5\<close>\<close>

lemma (in vectorspace) corollary_5_14:
  assumes fin_dim
  assumes "S \<subseteq> carrier V" and "lin_indpt S"
  shows "\<exists>B. S \<subseteq> B \<and> basis B"
proof -
  from \<open>fin_dim\<close> have "finite M \<and> card M \<le> dim" if "M \<subseteq> carrier V" "lin_indpt M" for M
    using that by (simp add: li_le_dim)
  note useful = maximal_exists[OF this]
  have "\<exists>B. finite B \<and> maximal B (\<lambda>M. S \<subseteq> M \<and> M \<subseteq> carrier V \<and> lin_indpt M)"
    by (rule useful) (use assms in auto)
  then show ?thesis
    by (smt dual_order.trans max_li_is_basis maximal_def)
qed

lemma (in subspace) corollary_5_16:
  assumes "vectorspace.fin_dim K V"
  shows "vectorspace.fin_dim K (V\<lparr>carrier := W\<rparr>)"
    and "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) \<le> vectorspace.dim K V"
    and "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) = vectorspace.dim K V \<Longrightarrow> W = carrier V"
proof -
  have subspace: "vectorspace K (V\<lparr>carrier := W\<rparr>)"
    by (simp add: subspace_axioms vectorspace.subspace_is_vs vs)
  {
    fix S
    assume "S \<subseteq> W" "module.lin_indpt K (V\<lparr>carrier := W\<rparr>) S"
    then have "S \<subseteq> carrier V" "module.lin_indpt K V S"
      apply (meson dual_order.trans module.submoduleE(1) submod vectorspace.axioms(1) vs)
      using \<open>S \<subseteq> W\<close> \<open>\<not> module.lin_dep K (V\<lparr>carrier := W\<rparr>) S\<close> module.span_li_not_depend(2) submod vectorspace_def vs by blast
    then have "finite S \<and> card S \<le> vectorspace.dim K V"
      using assms vectorspace.fin_dim_li_fin vectorspace.li_le_dim(2) vs by blast
  }  note useful = this
  have empty_lin_indpt_in_W: "module.lin_indpt K (V\<lparr>carrier := W\<rparr>) {}"
    by (simp add: module.lin_indpt_empty module.submodule_is_module submod vectorspace.axioms(1) vs)
  then obtain B where B: "finite B \<and> maximal B (\<lambda>B. B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier := W\<rparr>) B)"
    using maximal_exists[OF useful, of _ "{}"] by fastforce
  then have B_lin_indpt: "B \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier := W\<rparr>) B"
    by (simp add: maximal_def)
  from subspace B have B_spans_W: "module.span K (V\<lparr>carrier := W\<rparr>) B = W"
    by (simp add: vectorspace.max_li_is_gen)
  then show "vectorspace.fin_dim K (V\<lparr>carrier := W\<rparr>)"
    using B B_lin_indpt subspace vectorspace.fin_dim_def by fastforce
  show "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) \<le> vectorspace.dim K V"
    by (metis (no_types) B_lin_indpt B_spans_W dual_order.trans module.carrier_vs_is_self subspace
        useful vectorspace.gen_ge_dim vectorspace_def vs)
  from B B_lin_indpt B_spans_W assms show "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) = vectorspace.dim K V \<Longrightarrow> W = carrier V"
    by (smt module.carrier_vs_is_self module.span_li_not_depend(1,2) module.submoduleE(1)
        partial_object.surjective partial_object.update_convs(1) submod subset_trans subspace
        vectorspace.axioms(1) vectorspace.basis_def vectorspace.dim_li_is_basis vectorspace.gen_ge_dim vs)
qed


end
