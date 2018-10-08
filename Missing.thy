(* Author: Fabian Hellauer, 2018 *)
section \<open>Missing Preliminaries\<close>
theory Missing
  imports
    "HOL-Algebra.Ring_Divisibility"
    "HOL-Algebra.Subrings"
    "VectorSpace_by_HoldenLee/Missing_VectorSpace"
begin


subsection \<open>Subrings\<close>

lemma (in ring) subring_ring_hom_ring: "subring S R \<Longrightarrow> ring_hom_ring (R\<lparr>carrier:=S\<rparr>) R id"
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def
  by (auto simp: subring_is_ring ring_axioms intro!: ring_hom_memI) (use subringE(1) in blast)

lemma (in cring) subring_cring: "subring S R \<Longrightarrow> cring (R\<lparr>carrier:=S\<rparr>)"
  using cring.subcringI' is_cring ring_axioms ring.subcring_iff subringE(1) by blast

lemma (in subring) cring_ring_hom_cring:
  "cring R \<Longrightarrow> ring_hom_cring (R\<lparr>carrier:=H\<rparr>) R id"
  by (simp add: RingHom.ring_hom_cringI cring.subring_cring cring.axioms(1) ring.subring_ring_hom_ring subring_axioms)


subsection \<open>Ring Divisibility\<close>

lemma (in cring) in_PIdl_impl_divided: \<comment> \<open>proof extracted from @{thm[source] to_contain_is_to_divide}\<close>
  "a \<in> carrier R \<Longrightarrow> b \<in> PIdl a \<Longrightarrow> a divides b"
  unfolding factor_def cgenideal_def using m_comm by blast


subsection \<open>Linear Combinations\<close>

lemma (in module) lincomb_restrict_simp[simp, intro]:
  assumes U: "U \<subseteq> carrier M"
      and a: "a : U \<rightarrow> carrier R" (* needed? *)
  shows "lincomb (restrict a U) U = lincomb a U"
  by (meson U a lincomb_cong restrict_apply')

lemma (in module) lin_indpt_empty: "lin_indpt {}"
  by (simp add: lin_dep_def)


subsection \<open>Vector Spaces\<close>

subsubsection \<open>Subspaces\<close>

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

subsubsection \<open>Direct Sum of Vector Spaces\<close>

lemma (in linear_map) emb_image_dim:
  assumes "inj_on T (carrier V)"
  assumes V.fin_dim \<comment> \<open>needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.dim = vectorspace.dim K (vs imT)"
  using assms inj_imp_dim_ker0 rank_nullity by linarith

lemma (in linear_map) iso_preserves_dim:
  assumes "bij_betw T (carrier V) (carrier W)" \<comment> \<open>a module-isomorphism\<close>
  assumes V.fin_dim \<comment> \<open>needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "W.fin_dim" "V.dim = W.dim"
  using assms apply (simp add: bij_betw_def rank_nullity_main(2))
  using assms by (simp add: bij_betw_def dim_eq) \<comment> \<open>uses Missing\_VectorSpace (*rm*)\<close>

lemma (in mod_hom) mod_hom_the_inv:
  assumes bij: "bij_betw f (carrier M) (carrier N)"
  shows "mod_hom R N M (the_inv_into (carrier M) f)" (is "mod_hom R N M ?inv_f")
proof (unfold_locales; auto simp: module_hom_def)
  fix n1 n2 assume ns_carrier: "n1 \<in> carrier N" "n2 \<in> carrier N"
  then have ms_carrier: "?inv_f n1 \<in> carrier M" "?inv_f n2 \<in> carrier M"
    by (metis bij bij_betw_def order_refl the_inv_into_into)+
  from bij have "f (?inv_f (n1 \<oplus>\<^bsub>N\<^esub> n2)) = n1 \<oplus>\<^bsub>N\<^esub> n2"
    by (simp add: bij_betw_def f_the_inv_into_f ns_carrier)
  also from bij have "... = f(?inv_f n1) \<oplus>\<^bsub>N\<^esub> f(?inv_f n2)"
    by (simp add: bij_betw_def f_the_inv_into_f ns_carrier)
  also from bij[unfolded bij_betw_def] f_add have "\<dots> = f(?inv_f n1 \<oplus>\<^bsub>M\<^esub> ?inv_f n2)"
    by (simp add: ns_carrier the_inv_into_into)
  finally show "?inv_f (n1 \<oplus>\<^bsub>N\<^esub> n2) = ?inv_f n1 \<oplus>\<^bsub>M\<^esub> ?inv_f n2"
    using bij[unfolded bij_betw_def, THEN conjunct1, unfolded inj_on_def] ms_carrier
    by (simp add: bij[unfolded bij_betw_def] ns_carrier the_inv_into_into)
next
  fix r n assume "r \<in> carrier R" "n \<in> carrier N"
  then have "?inv_f n \<in> carrier M"
    by (simp add: bij[unfolded bij_betw_def] the_inv_into_into)
  have "?inv_f (r \<odot>\<^bsub>N\<^esub> n) = ?inv_f (r \<odot>\<^bsub>N\<^esub> f(?inv_f n))"
    by (simp add: bij[unfolded bij_betw_def] \<open>n \<in> carrier N\<close> f_the_inv_into_f)
  also have "... = ?inv_f (f (r \<odot>\<^bsub>M\<^esub> ?inv_f n))"
    by (simp add: \<open>r \<in> carrier R\<close> \<open>?inv_f n \<in> carrier M\<close>)
  finally show "?inv_f (r \<odot>\<^bsub>N\<^esub> n) = r \<odot>\<^bsub>M\<^esub> ?inv_f n"
    by (metis M.smult_closed bij[unfolded bij_betw_def] \<open>r \<in> carrier R\<close> \<open>?inv_f n \<in> carrier M\<close> the_inv_into_f_f)
qed (metis bij bij_betw_def order_refl the_inv_into_into)

corollary (in linear_map) linear_map_the_inv:
  "bij_betw T (carrier V) (carrier W) \<Longrightarrow> linear_map K W V (the_inv_into (carrier V) T)"
  by (meson linear_map_axioms linear_map_def mod_hom_the_inv)

lemma (in linear_map) iso_imports_dim:
  assumes "bij_betw T (carrier V) (carrier W)"
  assumes W.fin_dim \<comment> \<open>needed because otherwise \<^term>\<open>dim\<close> is not defined\<close>
  shows "V.fin_dim" "V.dim = W.dim"
  by (simp_all add: linear_map.iso_preserves_dim[OF linear_map_the_inv] assms bij_betw_the_inv_into)

lemma (in vectorspace) zero_not_in_basis:
  "basis B \<Longrightarrow> \<zero>\<^bsub>V\<^esub> \<notin> B"
  by (simp add: basis_def vs_zero_lin_dep)

lemma direct_sum_dim:
  assumes "vectorspace K V" "vectorspace.fin_dim K V"
  assumes "vectorspace K W" "vectorspace.fin_dim K W"
  shows "vectorspace.fin_dim K (direct_sum V W)"
    and "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
proof -
  interpret ds: vectorspace K \<open>direct_sum V W\<close>
    by (simp add: assms(1) assms(3) direct_sum_is_vs)

  txt \<open>embeddings into @{term "direct_sum V W"}:\<close>
  have lin1: "linear_map K V (direct_sum V W) (inj1 V W)"
    and lin2: "linear_map K W (direct_sum V W) (inj2 V W)"
    by (simp_all add: assms(1-4) inj1_linear inj2_linear)
  have inj1: "inj_on (inj1 V W) (carrier V)"
    and inj2: "inj_on (inj2 V W) (carrier W)"
    by (simp_all add: inj1_def inj2_def inj_on_def)

  from assms obtain Bv Bw where
    Bv: "finite Bv" "Bv \<subseteq> carrier V" "module.gen_set K V Bv" and
    Bw: "finite Bw" "Bw \<subseteq> carrier W" "module.gen_set K W Bw"
    by (meson vectorspace.fin_dim_def)
  let ?Bv = "inj1 V W ` Bv" and ?Bw = "inj2 V W ` Bw"
  let ?Bds = "?Bv \<union> ?Bw"
  from Bv(1) Bw(1) have "finite ?Bds"
    by simp_all
  moreover
    from Bv(2) Bw(2) have "?Bds \<subseteq> carrier (direct_sum V W)"
    unfolding direct_sum_def by (auto simp: inj1_def inj2_def)
      (meson assms vectorspace.span_closed vectorspace.span_zero)+
  moreover have "module.gen_set K (direct_sum V W) ?Bds"
    apply auto using calculation(2) ds.span_closed apply blast
  proof goal_cases
    case (1 a b)
    then have in_carrier: "a \<in> carrier V" "b \<in> carrier W"
      by (simp_all add: direct_sum_def)
    then obtain f A g B where lincomb1: "module.lincomb V f A = a" "finite A" "A\<subseteq>Bv" "f \<in> A\<rightarrow>carrier K"
      and lincomb2: "module.lincomb W g B = b" "finite B" "B\<subseteq>Bw" "g \<in> B\<rightarrow>carrier K"
      by (metis Bv Bw assms(1,3) module.finite_in_span subsetI vectorspace_def)
    have f: "f = f\<circ>fst \<circ> inj1 V W" and g: "g = g\<circ>snd \<circ> inj2 V W"
      unfolding inj1_def inj2_def by fastforce+
    note im_lincomb =
      linear_map.lincomb_linear_image[OF lin1 inj1, where a="f\<circ>fst" and A=A]
      linear_map.lincomb_linear_image[OF lin2 inj2, where a="g\<circ>snd" and A=B]
    let ?A = "inj1 V W ` A" and ?B = "inj2 V W ` B"
    have
      "ds.lincomb (f\<circ>fst) ?A = inj1 V W (module.lincomb V (f\<circ>fst \<circ> inj1 V W) A)"
      "ds.lincomb (g\<circ>snd) ?B = inj2 V W (module.lincomb W (g\<circ>snd \<circ> inj2 V W) B)"
      apply (auto intro!: im_lincomb)
      using Bv(2) lincomb1(3) apply blast
      apply (simp add: ds.coeff_in_ring2 inj1_def lincomb1(4))
      apply (simp add: lincomb1(2))
      using Bw(2) lincomb2(3) apply blast
      apply (simp add: ds.coeff_in_ring2 inj2_def lincomb2(4))
      by (simp add: lincomb2(2))
    moreover have "?A \<subseteq> ?Bv" "?B \<subseteq> ?Bw"
      by (simp_all add: image_mono lincomb1(3) lincomb2(3))
    moreover have "finite ?A" "finite ?B"
      by (simp_all add: lincomb1(2) lincomb2(2))
    moreover have "f\<circ>fst \<in> ?A \<rightarrow> carrier K" "g\<circ>snd \<in> ?B \<rightarrow> carrier K"
      unfolding inj1_def inj2_def using lincomb1(4) lincomb2(4)by auto
    ultimately have "inj1 V W a \<in> ds.span ?Bv" "inj2 V W b \<in> ds.span ?Bw"
      by (auto simp flip: f g simp: ds.span_def lincomb1(1) lincomb2(1)) metis+
    then have "inj1 V W a \<in> ds.span ?Bds" "inj2 V W b \<in> ds.span ?Bds"
      by (meson contra_subsetD ds.span_is_monotone le_sup_iff order_refl)+
    then have "inj1 V W a \<oplus>\<^bsub>direct_sum V W\<^esub> inj2 V W b \<in> ds.span ?Bds"
      using ds.span_add1[OF \<open>?Bds \<subseteq> carrier (direct_sum V W)\<close>] by simp
    then show ?case unfolding inj1_def inj2_def
      unfolding direct_sum_def using assms(1,3)[unfolded vectorspace_def] in_carrier
      by (simp add: module_def abelian_group_def abelian_monoid.l_zero abelian_monoid.r_zero)
  qed
  ultimately show "ds.fin_dim" unfolding ds.fin_dim_def
    by meson

txt \<open>I had planned to adapt the proof above to also show that @{term ?Bds} is minimal, but it turned
  out too tiresome. Instead, I use @{thm[source] linear_map.rank_nullity[OF _ this]}:\<close>
  note inj1 inj2
  moreover have emb1: "inj1 V W ` carrier V = carrier V \<times> {\<zero>\<^bsub>W\<^esub>}"
    and emb2: "inj2 V W ` carrier W = {\<zero>\<^bsub>V\<^esub>} \<times> carrier W"
    unfolding inj1_def inj2_def by blast+
  ultimately
  have "vectorspace.dim K V = vectorspace.dim K (ds.vs (mod_hom.im V (inj1 V W)))"
    and "vectorspace.dim K W = vectorspace.dim K (ds.vs (mod_hom.im W (inj2 V W)))"
    by (simp_all add: lin1 lin2 assms(2,4) linear_map.emb_image_dim)
  then have propagate_dims: "vectorspace.dim K V = vectorspace.dim K (ds.vs (carrier V \<times> {\<zero>\<^bsub>W\<^esub>}))"
    "vectorspace.dim K W = vectorspace.dim K (ds.vs ({\<zero>\<^bsub>V\<^esub>} \<times> carrier W))" apply auto
    apply (metis emb1 lin1 linear_map_def mod_hom.im_def)
    apply (metis emb2 lin2 linear_map_def mod_hom.im_def)
    done

  have "ds.dim = vectorspace.dim K (ds.vs (carrier V \<times> {\<zero>\<^bsub>W\<^esub>})) + vectorspace.dim K (ds.vs ({\<zero>\<^bsub>V\<^esub>} \<times> carrier W))"
  proof -
    let ?T = "\<lambda>(v,w). (v,\<zero>\<^bsub>W\<^esub>)"
    interpret T: linear_map K \<open>direct_sum V W\<close> \<open>direct_sum V W\<close> ?T
      apply unfold_locales unfolding module_hom_def apply auto
      unfolding direct_sum_def apply auto
      using Module.module_def abelian_groupE(2) assms(3) vectorspace.axioms(1) apply blast
      apply (metis Module.module_def abelian_group_def abelian_monoid.r_zero
          abelian_monoid.zero_closed assms(3) vectorspace.axioms(1))
      by (metis (no_types, hide_lams) Module.module_def abelian_group.r_neg1 abelian_group_def
          abelian_monoid.r_zero abelian_monoid.zero_closed assms(3) module.smult_closed
          module.smult_r_distr vectorspace_def)
    have mod_hom_T: "mod_hom K (direct_sum V W) (direct_sum V W) ?T" by intro_locales
    have ker_is_V: "T.ker = {\<zero>\<^bsub>V\<^esub>} \<times> carrier W" unfolding T.ker_def
      unfolding mod_hom.ker_def[OF mod_hom_T] direct_sum_def apply auto
      using Module.module_def abelian_groupE(2) assms(1) vectorspace.axioms(1) by blast
    have "T.im = carrier V \<times> {\<zero>\<^bsub>W\<^esub>}" unfolding T.im_def mod_hom.im_def[OF mod_hom_T]
      unfolding direct_sum_def apply auto
    proof -
      fix a :: 'c
      assume a1: "a \<in> carrier V"
      have f2: "(fst \<zero>\<^bsub>direct_sum V W\<^esub>, \<zero>\<^bsub>W\<^esub>) = \<zero>\<^bsub>direct_sum V W\<^esub>"
        by (metis (no_types) T.f0_is_0 split_def)
      have "carrier V \<times> carrier W = carrier (direct_sum V W)"
        by (simp add: direct_sum_def)
      then have "\<zero>\<^bsub>W\<^esub> \<in> carrier W"
        using f2 by (metis (no_types) ds.M.zero_closed mem_Sigma_iff)
      then show "(a, \<zero>\<^bsub>W\<^esub>) \<in> (\<lambda>(c, e). (c, \<zero>\<^bsub>W\<^esub>)) ` (carrier V \<times> carrier W)"
        using a1 by auto
    qed
    with \<open>ds.fin_dim\<close> ker_is_V show ?thesis
      using T.rank_nullity by simp
  qed
  with propagate_dims show "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
    by simp
qed (* to-do: use \<^sub> in part 1*)

subsubsection \<open>Zero Vector Space\<close>

lemma (in module) submodule_zsm: "submodule {\<zero>\<^bsub>M\<^esub>} R M"
  using M.r_neg submoduleI by fastforce

lemma (in module) module_zsm: "module R (md {\<zero>\<^bsub>M\<^esub>})"
  by (simp add: submodule_is_module submodule_zsm)

lemma (in vectorspace) vectorspace_zss: "vectorspace K (vs {\<zero>\<^bsub>V\<^esub>})"
  using module_zsm vectorspace_axioms vectorspace_def by blast

lemma (in subspace) dim0_zss:
  "vectorspace.fin_dim K V \<Longrightarrow> vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = 0 \<Longrightarrow> W = {\<zero>\<^bsub>V\<^esub>}"
proof -
  have vs: "vectorspace K (V\<lparr>carrier:=W\<rparr>)"
    by (simp add: subspace_axioms vectorspace.subspace_is_vs vs)
  assume "vectorspace.fin_dim K V" "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = 0"
  with vs have "vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) {}"
    by (simp add: corollary_5_16(1) module.finite_lin_indpt2 vectorspace.dim_li_is_basis vectorspace_def)
  then show ?thesis
    using vectorspace.basis_def vectorspace.span_empty vs by fastforce
qed

lemma (in vectorspace) basis_zss: "vectorspace.basis K (vs {\<zero>\<^bsub>V\<^esub>}) {}"
  by (simp add: LinearCombinations.module.finite_lin_indpt2 span_empty module_zsm
      span_li_not_depend(1) submodule_zsm vectorspace.basis_def vectorspace_zss)

corollary (in vectorspace) zss_dim:
  "vectorspace.fin_dim K (vs {\<zero>\<^bsub>V\<^esub>})" "vectorspace.dim K (vs {\<zero>\<^bsub>V\<^esub>}) = 0"
  using basis_zss vectorspace.basis_def vectorspace.fin_dim_def vectorspace_zss apply fastforce
  using basis_zss vectorspace.dim_basis vectorspace_zss by fastforce

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

lemma (in vectorspace) dim_0_trivial:
  "fin_dim \<Longrightarrow> dim = 0 \<Longrightarrow> carrier V = {\<zero>\<^bsub>V\<^esub>}"
  using dim_greater_0 by linarith

subsubsection \<open>The Field Itself as Vector Space\<close>

abbreviation "vs_of K \<equiv> \<comment> \<open>\<^term>\<open>K\<close>, viewed as a module (i.e. \<^term>\<open>monoid.mult K\<close> as \<^const>\<open>smult\<close>)\<close>
  \<lparr>carrier = carrier K, monoid.mult = undefined, one = undefined, zero = \<zero>\<^bsub>K\<^esub>, add = (\<oplus>\<^bsub>K\<^esub>),
  smult = (\<otimes>\<^bsub>K\<^esub>)\<rparr>"

sublocale field \<subseteq> self_vs: vectorspace R \<open>vs_of R\<close>
  rewrites "carrier (vs_of R) = carrier R"
   apply (rule vs_criteria) apply auto
       apply (simp add: local.field_axioms)
      apply (fact add.m_comm)
     apply (fact add.m_assoc)
    apply (fact m_assoc)
   apply (fact l_distr)
  by (simp add: r_distr)

lemma (in field) self_vs_size:
  shows self_vs_fin_dim: "self_vs.fin_dim"
    and self_vs_dim: "self_vs.dim = 1"
proof -
  let ?A = "{\<one>}"
  have A_generates_R: "finite ?A \<and> ?A \<subseteq> carrier R \<and> self_vs.gen_set ?A"
  proof auto
    show "x \<in> self_vs.span {\<one>}" if "x \<in> carrier R" for x
      unfolding self_vs.span_def apply auto apply (rule exI[of _ "\<lambda>_. x"]) \<comment> \<open>coefficient \<^term>\<open>x\<close>\<close>
      by (rule exI[of _ ?A]) (auto simp: that self_vs.lincomb_def)
  qed (metis empty_subsetI insert_subset one_closed self_vs.span_closed)
  then show self_vs.fin_dim "self_vs.dim = 1"
    using self_vs.fin_dim_def apply force
    using A_generates_R self_vs.dim1I by auto
qed

subsubsection \<open>Finite-Dimensional Vector Spaces\<close>

text \<open>The following corresponds to theorem 11.7 of \<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LADS_no_dates.pdf#section.0.11\<close>\<close>
lemma (in vectorspace) decompose_step:
  assumes fin_dim
  assumes "dim > 0"
  shows "\<exists>h V'. linear_map K V (direct_sum (vs_of K) (vs V')) h
    \<and> bij_betw h (carrier V) (carrier K \<times> V')
    \<and> subspace K V' V
    \<and> vectorspace.dim K (vs V') = dim - 1"
proof - \<comment> \<open>Possibly easier if the map definition is swapped as in Kemper's proof.\<close>
  from assms obtain B where B: "basis B" "card B > 0"
    using dim_basis finite_basis_exists by auto
  then obtain b where "b \<in> B"
    by fastforce
  let ?B = "B - {b}"
  have liB: "lin_indpt ?B" and BiV: "?B \<subseteq> carrier V" "finite ?B"
    apply (meson B(1) Diff_subset basis_def supset_ld_is_ld)
    using B(1) basis_def apply blast using B
    using card_infinite neq0_conv by blast
  let ?V = "vs (span ?B)"
  note goal_3 = span_is_subspace[OF BiV(1)]
  then interpret vs_span_B: vectorspace K ?V
    rewrites "carrier (vs (span ?B)) = span ?B"
    using subspace_is_vs by blast simp
  from liB have liB': "vs_span_B.lin_indpt ?B"
    by (simp add: BiV in_own_span span_is_subspace span_li_not_depend(2))
  then have new_basis: "vs_span_B.basis ?B"
    by (simp add: BiV(1) in_own_span span_is_submodule span_li_not_depend(1) vs_span_B.basis_def)
  moreover have "card ?B = dim - 1"
    using B(1) BiV(2) \<open>b \<in> B\<close> dim_basis by auto
  ultimately have "vs_span_B.fin_dim" and goal_4: "vs_span_B.dim = dim - 1"
    unfolding vs_span_B.fin_dim_def apply -
    apply (metis BiV(2) new_basis vs_span_B.basis_def)
    using BiV(2) vs_span_B.dim_basis by presburger
  define coeffs where "coeffs = the_inv_into (B \<rightarrow>\<^sub>E carrier K) (\<lambda>a. lincomb a B)"
  have coeffs_unique: "\<exists>!c. c \<in> B \<rightarrow>\<^sub>E carrier K \<and> lincomb c B = v" if "v \<in> carrier V" for v
    using basis_criterion by (metis (full_types) B basis_def card_ge_0_finite that)
  have okese: "coeffs v \<in> B \<rightarrow>\<^sub>E carrier K" "v = lincomb (coeffs v) B" if "v \<in> carrier V" for v
    using that theI'[OF coeffs_unique] by (simp_all add: coeffs_def the_inv_into_def)
  have c_sum: "coeffs (v1\<oplus>\<^bsub>V\<^esub>v2) \<in> B \<rightarrow>\<^sub>E carrier K"
    "v1\<oplus>\<^bsub>V\<^esub>v2 = lincomb (coeffs (v1\<oplus>\<^bsub>V\<^esub>v2)) B" if "v1 \<in> carrier V" "v2 \<in> carrier V" for v1 v2
    apply (simp add: okese(1) that(1) that(2))
    apply (simp add: okese(2) that(1) that(2))
    done
  have c_sum': "lincomb (\<lambda>v. coeffs v1 v \<oplus>\<^bsub>K\<^esub> coeffs v2 v) B = lincomb (coeffs (v1\<oplus>\<^bsub>V\<^esub>v2)) B" if "v1 \<in> carrier V" "v2 \<in> carrier V" for v1 v2
  proof -
    note b = okese(2)[OF that(1)] okese(2)[OF that(2)]
    note a = okese(1)[OF that(1)] okese(1)[OF that(2)]
    then have "coeffs v1 \<in> B \<rightarrow> carrier K" "coeffs v2 \<in> B \<rightarrow> carrier K"
      by blast+
    note lincomb_sum[OF _ _ this, folded b]
    then show ?thesis
      using B(1) B(2) basis_def c_sum(2) that(1) that(2) by force
  qed
  let ?T = "\<lambda>v. (coeffs v b, lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs v bv) (B - {b}))"
  have goal_1: "linear_map K V (direct_sum (vs_of K) ?V) ?T"
    unfolding linear_map_def apply auto
    apply (simp add: vectorspace_axioms)
    unfolding mod_hom_def module_hom_def mod_hom_axioms_def apply auto
    using direct_sum_is_vs self_vs.vectorspace_axioms vs_span_B.vectorspace_axioms apply blast
    apply (simp add: module.module_axioms)
    apply (simp add: direct_sum_is_module self_vs.module_axioms vs_span_B.module_axioms)
    unfolding direct_sum_def apply auto
    using \<open>b \<in> B\<close> okese(1) apply fastforce
    using vs_span_B.lincomb_closed apply (smt BiV DiffE finite_span PiE_mem Pi_I coeff_in_ring
        insertCI mem_Collect_eq module_axioms okese(1))
  proof -
    fix m1 m2
    assume mcV: "m1 \<in> carrier V" "m2 \<in> carrier V"
    then have B_to_K_map: "(\<lambda>bv. coeffs m1 bv \<oplus>\<^bsub>K\<^esub> coeffs m2 bv) \<in> B \<rightarrow> carrier K"
      by (smt PiE_mem Pi_I R.add.m_closed okese(1))
    let ?restricted = "\<lambda>bv\<in>B. coeffs m1 bv \<oplus>\<^bsub>K\<^esub> coeffs m2 bv"
    have "lincomb (coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2)) B = lincomb ?restricted B"
      using mcV B(1) basis_def c_sum' B_to_K_map by auto
    moreover have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow>\<^sub>E carrier K"
      "?restricted \<in> B \<rightarrow>\<^sub>E carrier K"
       apply (simp add: mcV c_sum(1))
      by (simp add: B_to_K_map)
    ultimately
      have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) = ?restricted"
      using basis_criterion
      by (metis (no_types, lifting) mcV B(1) B(2) M.add.m_closed basis_def c_sum(2)
          card_ge_0_finite)
    then have distr: "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) b = coeffs m1 b \<oplus>\<^bsub>K\<^esub> coeffs m2 b" if "b \<in> B" for b
      by (simp add: that)
    then show "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) b = coeffs m1 b \<oplus>\<^bsub>K\<^esub> coeffs m2 b"
      by (simp add: \<open>b \<in> B\<close>)
    have [simp]: "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else xyz bv) (B-{b})
      = lincomb xyz (B-{b})" if "xyz \<in> B \<rightarrow> carrier K" for xyz
      using that
      by (smt BiV(1) Diff_not_in Pi_split_insert_domain \<open>b \<in> B\<close> insert_Diff lincomb_cong)
    have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow> carrier K"
      "coeffs m1 \<in> B \<rightarrow> carrier K"
      "coeffs m2 \<in> B \<rightarrow> carrier K"
      using \<open>coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow>\<^sub>E carrier K\<close> apply auto[1]
      using mcV okese(1) by fastforce+
    with distr show "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) bv) (B-{b})
      = lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m1 bv) (B-{b})
      \<oplus>\<^bsub>V\<^esub> lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m2 bv) (B-{b})" apply simp
      by (smt BiV DiffE Pi_split_insert_domain \<open>b \<in> B\<close> insert_Diff lincomb_cong lincomb_sum)
    fix r m
    assume rK: "r \<in> carrier K" and mV: "m \<in> carrier V"
    have sane: "(\<lambda>bv. r \<otimes>\<^bsub>K\<^esub> coeffs m bv) \<in> B \<rightarrow> carrier K"
      using mV okese(1) rK by fastforce
    let ?restricted = "\<lambda>bv\<in>B. r \<otimes>\<^bsub>K\<^esub> coeffs m bv"
    have "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) B = lincomb ?restricted B"
      by (metis B(1) PiE_restrict basis_def lincomb_distrib lincomb_restrict_simp mV okese rK
          restrict_PiE sane smult_closed)
    moreover have "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow>\<^sub>E carrier K" "?restricted \<in> B \<rightarrow>\<^sub>E carrier K"
       apply (simp add: mV okese(1) rK)
      by (simp add: sane)
    ultimately have "coeffs (r \<odot>\<^bsub>V\<^esub> m) = ?restricted"
      by (metis coeffs_unique mV okese(2) rK smult_closed)
    then have scale: "coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b" if "b \<in> B" for b
      by (simp add: that)
    then show "coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b"
      using \<open>b \<in> B\<close> by blast
    have "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow> carrier K"
      "coeffs m \<in> B \<rightarrow> carrier K"
      using \<open>coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow>\<^sub>E carrier K\<close> apply auto[1]
      using mV okese(1) by fastforce
    with scale \<open>r \<in> carrier K\<close> show "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs (r \<odot>\<^bsub>V\<^esub> m) bv) (B-{b}) =
    r \<odot>\<^bsub>V\<^esub> lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m bv) (B-{b})"
    proof simp
      assume a1: "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow> carrier K"
      assume a2: "r \<in> carrier K"
      assume a3: "coeffs m \<in> B \<rightarrow> carrier K"
      assume a4: "\<And>b. b \<in> B \<Longrightarrow> coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b"
      have f5: "\<forall>C Ca f fa. (C \<noteq> Ca \<or> \<not> C \<subseteq> carrier V \<or> (\<exists>c. c \<in> C \<and> f c \<noteq> fa c) \<or> fa \<notin> Ca \<rightarrow> carrier K) \<or> lincomb f C = lincomb fa Ca"
        by (metis (no_types) lincomb_cong)
      obtain cc :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c set \<Rightarrow> 'c" where
        "\<forall>x0 x1 x3. (\<exists>v4. v4 \<in> x3 \<and> x1 v4 \<noteq> x0 v4) = (cc x0 x1 x3 \<in> x3 \<and> x1 (cc x0 x1 x3) \<noteq> x0 (cc x0 x1 x3))"
        by moura
      then have f6: "\<forall>C Ca f fa. (C \<noteq> Ca \<or> \<not> C \<subseteq> carrier V \<or> cc fa f C \<in> C \<and> f (cc fa f C) \<noteq> fa (cc fa f C) \<or> fa \<notin> Ca \<rightarrow> carrier K) \<or> lincomb f C = lincomb fa Ca"
        using f5 by presburger
      have f7: "insert b (B - {b}) = B"
        using \<open>b \<in> B\<close> by blast
      have f8: "\<forall>f c C fa. (f \<in> Pi (insert (c::'c) C) fa) = (f \<in> Pi C fa \<and> (f c::'a) \<in> fa c)"
        by blast
      then have f9: "cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) \<in> B - {b} \<and> r \<otimes>\<^bsub>K\<^esub> coeffs m (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<noteq> coeffs (r \<odot>\<^bsub>V\<^esub> m) (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<or> lincomb (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) = lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b})"
        using f7 f6 a1 by (metis (no_types) \<open>B - {b} \<subseteq> carrier V\<close>)
      have "coeffs m \<in> B - {b} \<rightarrow> carrier K \<and> coeffs m b \<in> carrier K"
        using f8 f7 a3 by (metis (no_types))
      then show "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b}) = r \<odot>\<^bsub>V\<^esub> lincomb (coeffs m) (B - {b})"
        using f9 a4 a2 \<open>B - {b} \<subseteq> carrier V\<close> lincomb_distrib by fastforce
    qed
  qed
  then interpret linmap: linear_map K V \<open>direct_sum (vs_of K) ?V\<close> ?T .
  {
    fix v
    assume "v \<in> carrier V"
    let ?c = "coeffs v"
    have a: "?c \<in> B \<rightarrow>\<^sub>E carrier K" "v = lincomb ?c B"
      using okese by (simp add: \<open>v \<in> carrier V\<close>)+
    have c0s: "v = \<zero>\<^bsub>V\<^esub> \<Longrightarrow> coeffs v \<in> B \<rightarrow> {\<zero>\<^bsub>K\<^esub>}"
      by (metis (no_types, lifting) B(1) B(2) Diff_cancel Diff_eq_empty_iff PiE_mem Pi_I a(1) a(2) basis_def card_ge_0_finite not_lindepD)
    have "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else ?c bv) ?B = \<zero>\<^bsub>V\<^esub> \<longleftrightarrow> ?c \<in> ?B\<rightarrow>{\<zero>\<^bsub>K\<^esub>}"
      apply standard
      using not_lindepD
       apply (smt BiV(2) Diff_cancel Diff_eq_empty_iff Diff_iff PiE_mem Pi_I a(1) liB lin_dep_crit singletonI)
      by (smt BiV(1) Diff_not_in Pi_cong lincomb_zero)
    then have "?T v = \<zero>\<^bsub>direct_sum (vs_of K) (vs (span ?B))\<^esub> \<longrightarrow> v = \<zero>\<^bsub>V\<^esub>"
      unfolding direct_sum_def by auto (smt B(1) Pi_split_insert_domain \<open>b \<in> B\<close> a(2) insertCI
          insert_Diff lincomb_zero vectorspace.basis_def vectorspace_axioms)
  }
  then have "linmap.kerT = {\<zero>\<^bsub>V\<^esub>}"
    unfolding linmap.ker_def by auto
  then have goal_2a: "inj_on ?T (carrier V)"
    by (simp add: linmap.Ke0_imp_inj)
  from self_vs_size \<open>vs_span_B.fin_dim\<close> have "linmap.W.dim = 1 + vs_span_B.dim"
    by (simp add: direct_sum_dim(2) self_vs.vectorspace_axioms vs_span_B.vectorspace_axioms)
  also from goal_4 have "\<dots> = dim" using \<open>dim > 0\<close> by force
  also have "\<dots> = vectorspace.dim K (linmap.W.vs linmap.im)"
    using assms(1) linmap.emb_image_dim goal_2a by blast
  finally have "carrier (direct_sum (vs_of K) ?V) = linmap.imT"
    using subspace.corollary_5_16(3)[OF linmap.imT_is_subspace] \<open>vs_span_B.fin_dim\<close>
      direct_sum_dim(1) self_vs.vectorspace_axioms self_vs_fin_dim vs_span_B.vectorspace_axioms by auto
  note goal_2b = this[unfolded linmap.im_def direct_sum_def, simplified]
  from goal_1 goal_2a goal_2b goal_3 goal_4 show ?thesis
    unfolding bij_betw_def by blast
qed


subsection \<open>Linear Maps\<close>

lemma (in subring) module_wrt_subring:
  "module R M \<Longrightarrow> module (R\<lparr>carrier:=H\<rparr>) M"
  unfolding module_def module_axioms_def by (simp add: cring.subring_cring subring_axioms)

lemma (in subfield) vectorspace_wrt_subfield:
  "vectorspace R V \<Longrightarrow> vectorspace (R\<lparr>carrier:=K\<rparr>) V" unfolding vectorspace_def
  by (auto simp: module_wrt_subring ring.subfield_iff(2) cring.axioms(1) module.axioms(1) subfield_axioms)

lemma (in subring) hom_wrt_subring:
  "h \<in> module_hom R M N \<Longrightarrow> h \<in> module_hom (R\<lparr>carrier:=H\<rparr>) M N"
  by (simp add: LinearCombinations.module_hom_def)

lemma (in subfield) linear_wrt_subfield:
  "linear_map R M N T \<Longrightarrow> linear_map (R\<lparr>carrier:=K\<rparr>) M N T" unfolding linear_map_def
  by (auto simp: vectorspace_wrt_subfield hom_wrt_subring mod_hom_axioms_def mod_hom_def module_wrt_subring)


subsection \<open>Fields\<close>

context field begin \<comment> \<open>"Let @{term R} be a field."\<close>

lemma has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

lemma inv_nonzero: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<noteq> \<zero>"
  using Units_inv_Units field_Units by simp

end

lemma (in subfield) finsum_simp:
  assumes \<open>ring R\<close>
  assumes "v ` A \<subseteq> K"
  shows "(\<Oplus>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub>i \<in> A. v i) = (\<Oplus>\<^bsub>R\<^esub>i \<in> A. v i)"
  unfolding finsum_def apply auto using assms
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case
    by (simp add: finprod_def)
next
  case empty
  have "\<zero> \<in> K"
    by (metis monoid.select_convs(2) subgroup_axioms subgroup_def)
  then show ?case
      by (simp add: finprod_def)
next
  case (insert x F)
  have a: "v \<in> F \<rightarrow> K"
    using insert.prems(2) by auto
  moreover have "K \<subseteq> carrier R"
    by (simp add: subset)
  ultimately have b: "v \<in> F \<rightarrow> carrier R"
    by fast
  have d: "v x \<in> K"
    using insert.prems(2) by auto
  then have e: "v x \<in> carrier R"
    using \<open>K \<subseteq> carrier R\<close> by blast
  have "abelian_monoid (R\<lparr>carrier := K\<rparr>)" using assms(1)
    using abelian_group_def ring.subring_iff ring_def subring_axioms subset by auto
  then have f: "comm_monoid \<lparr>carrier = K, monoid.mult = (\<oplus>), one = \<zero>, \<dots> = undefined::'b\<rparr>"
    by (simp add: abelian_monoid_def)
  note comm_monoid.finprod_insert[of "add_monoid R", simplified, OF _ insert.hyps b e, simplified]
  then have "finprod (add_monoid R) v (insert x F) = v x \<oplus> finprod (add_monoid R) v F"
    using abelian_group.a_comm_group assms(1) comm_group_def ring_def by blast
  with comm_monoid.finprod_insert[of "add_monoid (R\<lparr>carrier := K\<rparr>)", simplified, OF f insert.hyps a d, simplified]
  show ?case
    by (simp add: a image_subset_iff_funcset insert.IH insert.prems(1))
qed


subsection \<open>Univariate Polynomials\<close>

lemma (in UP_ring) lcoeff_Unit_nonzero:
  "carrier R \<noteq> {\<zero>} \<Longrightarrow> lcoeff p \<in> Units R \<Longrightarrow> p \<noteq> \<zero>\<^bsub>P\<^esub>"
  by (metis R.Units_r_inv_ex R.l_null R.one_zeroD coeff_zero)

lemma (in UP_cring) Unit_scale_zero:
  "c \<in> Units R \<Longrightarrow> r \<in> carrier P \<Longrightarrow> c \<odot>\<^bsub>P\<^esub> r = \<zero>\<^bsub>P\<^esub> \<Longrightarrow> r = \<zero>\<^bsub>P\<^esub>"
  by (metis R.Units_closed R.Units_l_inv_ex UP_smult_one smult_assoc_simp smult_r_null)

abbreviation (in UP) degree where "degree \<equiv> deg R" \<comment> \<open>Why is \<^term>\<open>R\<close> not part of the definition?\<close>

lemma (in UP_cring) Unit_scale_deg[simp]:
  "c \<in> Units R \<Longrightarrow> r \<in> carrier P \<Longrightarrow> degree (c \<odot>\<^bsub>P\<^esub> r) = degree r"
  by (metis R.Units_closed R.Units_l_inv_ex deg_smult_decr le_antisym smult_assoc_simp smult_closed smult_one)

lemma (in UP_cring) weak_long_div_theorem: \<comment> \<open>barely weaker. Useful to prove \<^term>\<open>euclidean_domain P degree\<close>.\<close>
  assumes g_in_P [simp]: "g \<in> carrier P" and f_in_P [simp]: "f \<in> carrier P"
  and lcoeff_g: "lcoeff g \<in> Units R" and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  shows "\<exists>q r. q \<in> carrier P \<and> r \<in> carrier P \<and> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (r = \<zero>\<^bsub>P\<^esub> \<or> degree r < degree g)"
proof -
  from long_div_theorem[OF g_in_P f_in_P] obtain q r and k::nat where qrk: "q \<in> carrier P"
    "r \<in> carrier P" "lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r" "r = \<zero>\<^bsub>P\<^esub> \<or> degree r < degree g"
    using R_not_trivial lcoeff_Unit_nonzero lcoeff_g by auto
  from lcoeff_g have inv: "lcoeff g [^] k \<in> Units R"
    by (induction k) simp_all
  let ?inv = "inv (lcoeff g [^] k)"
  have inv_ok: "?inv \<in> Units R" "?inv \<in> carrier R"
    using inv by simp_all
  from inv have "f = ?inv \<otimes> lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f"
    by simp
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> (lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f)"
    by (simp add: inv smult_assoc_simp)
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r)"
    by (simp add: qrk)
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r"
    by (simp add: UP_smult_assoc2 UP_smult_r_distr inv_ok qrk(1-2))
  also have "\<dots> = g \<otimes>\<^bsub>P\<^esub> (?inv \<odot>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r"
    using UP_m_comm inv_ok qrk(1) smult_assoc2 by auto
  finally have "f = g \<otimes>\<^bsub>P\<^esub> (?inv \<odot>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r" .
  moreover have "?inv \<odot>\<^bsub>P\<^esub> q \<in> carrier P" "?inv \<odot>\<^bsub>P\<^esub> r \<in> carrier P"
    by (simp_all add: inv_ok qrk(1-2))
  moreover have "?inv \<odot>\<^bsub>P\<^esub> r = \<zero>\<^bsub>P\<^esub> \<or> degree (?inv \<odot>\<^bsub>P\<^esub> r) < degree (?inv \<odot>\<^bsub>P\<^esub> g)"
    using Unit_scale_deg inv_ok(1) qrk(2,4) by auto
  ultimately show ?thesis using inv_ok(1) by auto
qed


subsection \<open>Generalisations\<close>

lemma (in comm_monoid) finprod_singleton':
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and x_in_G: "x \<in> carrier G"
  shows "(\<Otimes>j\<in>A. if i=j then x else \<one>) = x"
  using i_in_A finprod_insert [of "A-{i}" i "\<lambda>j. if i=j then x else \<one>"]
    fin_A x_in_G finprod_one [of "A-{i}"]
    finprod_cong [of "A-{i}" "A-{i}" "\<lambda>j. if i=j then x else \<one>" "\<lambda>_. \<one>"]
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)
thm \<comment> \<open>recover @{thm comm_monoid.finprod_singleton} from this\<close>
  comm_monoid.finprod_singleton[of _ i _ f for i f]
  comm_monoid.finprod_singleton'[of _ i _ \<open>f i\<close> for f i]
lemmas (in abelian_monoid) finsum_singleton' = add.finprod_singleton'
  \<comment> \<open>compare @{thm finsum_singleton}\<close>

end
