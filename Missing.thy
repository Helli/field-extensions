theory Missing
  imports "VectorSpace_by_HoldenLee/Missing_VectorSpace"
begin

subsection \<open>Vector Spaces\<close>

lemma (in module) lin_indpt_empty: "lin_indpt {}"
  by (simp add: finite_lin_indpt2)

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
  have "\<exists>B. finite B \<and> maximal B (\<lambda>M. M \<subseteq> W \<and> module.lin_indpt K (V\<lparr>carrier := W\<rparr>) M)"
    apply (rule maximal_exists[OF useful]) apply auto[2] using empty_lin_indpt_in_W by blast
  show fin_dim: "vectorspace.fin_dim K (V\<lparr>carrier := W\<rparr>)"
  proof -
    obtain CC :: "'c set" where
      f1: "finite CC \<and> maximal CC (\<lambda>C. C \<subseteq> W \<and> \<not> module.lin_dep K (V\<lparr>carrier := W\<rparr>) C)"
    using \<open>\<exists>B. finite B \<and> maximal B (\<lambda>M. M \<subseteq> W \<and> \<not> module.lin_dep K (V\<lparr>carrier := W\<rparr>) M)\<close> by blast
    then have f2: "\<forall>p pa. ((vectorspace.fin_dim (pa::\<lparr>carrier :: 'a set, mult :: _ \<Rightarrow> _ \<Rightarrow> _, one :: _, zero :: _, add :: _ \<Rightarrow> _ \<Rightarrow> _, \<dots> :: 'b\<rparr>) (p::(_, 'c, 'd) module_scheme) \<or> module.span pa p CC \<noteq> carrier p) \<or> \<not> CC \<subseteq> carrier p) \<or> \<not> vectorspace pa p"
      using vectorspace.fin_dim_def by blast
    have f3: "CC \<subseteq> W \<and> \<not> module.lin_dep K (V\<lparr>carrier := W\<rparr>) CC"
      using f1 by (simp add: maximal_def)
    have "vectorspace K (V\<lparr>carrier := W\<rparr>)"
      using subspace_axioms subspace_def vectorspace.subspace_is_vs by blast
    then have "module.span K (V\<lparr>carrier := W\<rparr>) CC = W"
      using f1 by (simp add: vectorspace.max_li_is_gen)
    then show ?thesis
      using f3 f2 by (metis (no_types) module.carrier_vs_is_self subspace_axioms subspace_def vectorspace.subspace_is_vs vectorspace_def)
  qed
  then show "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) \<le> vectorspace.dim K V"
    by (metis module.carrier_vs_is_self subspace_axioms subspace_def useful vectorspace.basis_def
        vectorspace.dim_basis vectorspace.finite_basis_exists vectorspace.subspace_is_vs
        vectorspace_def)
  with fin_dim assms show "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) = vectorspace.dim K V \<Longrightarrow> W = carrier V"
    by (smt module.carrier_vs_is_self module.span_li_not_depend module.submoduleE(1)
        monoid.surjective partial_object.update_convs(1) submod subset_trans subspace_axioms
        vectorspace.axioms(1) vectorspace.basis_def vectorspace.dim_basis
        vectorspace.dim_li_is_basis vectorspace.finite_basis_exists vectorspace.subspace_is_vs vs)
qed


end
