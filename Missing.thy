(* Author: Fabian Hellauer, 2018 *)
section \<open>Missing Preliminaries\<close>
theory Missing
  imports
    "HOL-Algebra.Ring_Divisibility"
    "HOL-Algebra.Subrings"
    "VectorSpace_by_HoldenLee/Missing_VectorSpace"
begin

subsection \<open>Function Sets\<close>

lemma funcset_compose': "f ` A = B \<Longrightarrow> g \<circ> f \<in> A \<rightarrow> C \<Longrightarrow> g \<in> B \<rightarrow> C"
  by auto

lemma singleton_PiE_bij:
  "bij_betw (\<lambda>m. m a) ({a} \<rightarrow>\<^sub>E B) B"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>m. m a) ({a} \<rightarrow>\<^sub>E B)"
    by standard fastforce
next
  {
    fix b
    assume "b\<in>B"
    then have "(\<lambda>_\<in>{a}. b) \<in> {a} \<rightarrow>\<^sub>E B"
      by simp
    moreover have "b = (\<lambda>m. m a) (\<lambda>_\<in>{a}. b)"
      by simp
    ultimately have "b \<in> (\<lambda>m. m a) ` ({a} \<rightarrow>\<^sub>E B)"
      by blast
  }
  then show "(\<lambda>m. m a) ` ({a} \<rightarrow>\<^sub>E B) = B"
    by blast
qed


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


subsection \<open>Finite Products / Finite Sums\<close>

lemma (in monoid) finprod_eqI[intro]: "(\<And>i. f i = g i) \<Longrightarrow> (\<Otimes>i\<in>A. f i) = (\<Otimes>i\<in>A. g i)"
  by presburger
lemmas (in abelian_monoid) finsum_eqI[intro] = add.finprod_eqI[folded finsum_def]

lemma (in comm_monoid) finprod_singleton': \<comment> \<open>a variation of @{thm finprod_singleton}\<close>
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and x_in_G: "x \<in> carrier G"
  shows "(\<Otimes>j\<in>A. if i=j then x else \<one>) = x"
  using i_in_A finprod_insert [of "A-{i}" i "\<lambda>j. if i=j then x else \<one>"]
    fin_A x_in_G finprod_one [of "A-{i}"]
    finprod_cong [of "A-{i}" "A-{i}" "\<lambda>j. if i=j then x else \<one>" "\<lambda>_. \<one>"]
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

lemmas (in abelian_monoid) finsum_singleton' = add.finprod_singleton'
  \<comment> \<open>compare @{thm finsum_singleton}\<close>


subsection \<open>Linear Combinations\<close>

lemma (in module) lincomb_restrict_simp[simp, intro]:
  assumes U: "U \<subseteq> carrier M"
      and a: "a : U \<rightarrow> carrier R"
  shows "lincomb (restrict a U) U = lincomb a U"
  by (meson U a lincomb_cong restrict_apply')

lemma (in module) lin_indpt_empty: "lin_indpt {}"
  by (simp add: lin_dep_def)


subsection \<open>Vector Spaces\<close>

subsubsection \<open>Subspaces\<close>

lemma (in vectorspace) lin_indpt_extends_to_basis:
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

text \<open>Corollary 10.16 of \<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LADS.pdf#section.0.10\<close>.\<close>

lemma (in subspace) subspace_dim:
  assumes "vectorspace.fin_dim K V"
  shows "vectorspace.fin_dim K (V\<lparr>carrier := W\<rparr>)"
    and "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) \<le> vectorspace.dim K V"
    and "vectorspace.dim K (V\<lparr>carrier := W\<rparr>) = vectorspace.dim K V \<Longrightarrow> W = carrier V"
proof -
  interpret V: vectorspace K V by (fact vs)
  interpret W: vectorspace K \<open>V.vs W\<close>
    by (simp add: V.subspace_is_vs subspace_axioms)
  have subset: "finite S \<and> card S \<le> vectorspace.dim K V" if "S\<subseteq>W" "W.lin_indpt S" for S
  proof
    from that(1) have "S \<subseteq> carrier V"
      by (meson dual_order.trans submod V.submoduleE(1))
    from that have "V.lin_indpt S"
      using submod V.span_li_not_depend(2) by auto
    with \<open>S \<subseteq> carrier V\<close> show "finite S" "card S \<le> vectorspace.dim K V"
      by (simp_all add: assms V.li_le_dim)
  qed
  from W.lin_indpt_empty obtain B where B: "finite B \<and> maximal B (\<lambda>B. B \<subseteq> W \<and> W.lin_indpt B)"
    using maximal_exists[OF subset, of _ "{}"] by fastforce
  then have B_lin_indpt: "B \<subseteq> W \<and> W.lin_indpt B"
    by (simp add: maximal_def)
  from B have B_spans_W: "W.span B = W"
    by (simp add: W.max_li_is_gen)
  then show "W.fin_dim"
    using B B_lin_indpt W.fin_dim_def by auto
  show "W.dim \<le> V.dim"
    using W.basis_def W.dim_basis W.finite_basis_exists \<open>W.fin_dim\<close> subset by auto
  from B B_lin_indpt B_spans_W assms show "W.dim = V.dim \<Longrightarrow> W = carrier V"
    by (smt W.carrier_vs_is_self module.span_li_not_depend(1,2) V.submoduleE(1)
        partial_object.surjective partial_object.update_convs(1) submod subset_trans
        vectorspace.axioms(1) V.basis_def V.dim_li_is_basis W.gen_ge_dim vs)
qed

subsubsection \<open>Direct Sum of Vector Spaces\<close>

text \<open>These lemmas cannot avoid the \<^const>\<open>vectorspace.fin_dim\<close> assumption because
  \<^const>\<open>vectorspace.dim\<close> is only defined in this case:\<close>

lemma (in vectorspace) dim_deficient: "fin_dim \<or> dim = (THE _. False)"
  unfolding fin_dim_def dim_def Least_def by meson

lemma (in linear_map) emb_image_dim:
  assumes "inj_on T (carrier V)"
  assumes V.fin_dim
  shows "V.dim = vectorspace.dim K (vs imT)"
  using assms inj_imp_dim_ker0 rank_nullity by linarith

lemma (in linear_map) iso_preserves_dim:
  assumes "bij_betw T (carrier V) (carrier W)"
  assumes V.fin_dim
  shows "W.fin_dim" "V.dim = W.dim"
  using assms by (simp_all add: bij_betw_def rank_nullity_main(2) dim_eq)

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
  assumes W.fin_dim
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
  proof
    show "ds.span ?Bds \<subseteq> carrier (direct_sum V W)"
      using calculation(2) by (simp add: ds.span_is_subset2)
  next
    {
      fix a b
      assume in_carrier: "a \<in> carrier V" "b \<in> carrier W"
      then obtain f A g B
        where lincomb1: "module.lincomb V f A = a" "finite A" "A\<subseteq>Bv" "f \<in> A\<rightarrow>carrier K"
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
      then have "(a, b) \<in> ds.span (inj1 V W ` Bv \<union> inj2 V W ` Bw)"
        unfolding inj1_def inj2_def direct_sum_def using assms[unfolded vectorspace_def] in_carrier
        by (simp add: module_def abelian_group_def abelian_monoid.l_zero abelian_monoid.r_zero)
    }
    then show "carrier (direct_sum V W) \<subseteq> ds.span ?Bds"
      by (auto simp: direct_sum_def)
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
    by (simp add: subspace_dim(1) module.finite_lin_indpt2 vectorspace.dim_li_is_basis vectorspace_def)
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

lemma (in vectorspace) dim_0_implies_zvs:
  "fin_dim \<Longrightarrow> dim = 0 \<Longrightarrow> carrier V = {\<zero>\<^bsub>V\<^esub>}"
  by (metis basis_def card_0_eq dim_basis finite_basis_exists span_empty)

lemma (in vectorspace) nonzvs_implies_dim_greater_0:
  "fin_dim \<Longrightarrow> carrier V \<noteq> {\<zero>\<^bsub>V\<^esub>} \<Longrightarrow> dim > 0"
  using dim_0_implies_zvs by blast

subsubsection \<open>Ring Itself as Module\<close>

abbreviation "module_of K \<equiv> \<comment> \<open>\<^term>\<open>K\<close>, viewed as a module (i.e. \<^term>\<open>mult K\<close> as \<^const>\<open>smult\<close>)\<close>
  \<lparr>carrier = carrier K, mult = undefined, one = undefined, zero = \<zero>\<^bsub>K\<^esub>, add = (\<oplus>\<^bsub>K\<^esub>), smult = (\<otimes>\<^bsub>K\<^esub>)\<rparr>"

lemma (in cring) self_module: "module R (module_of R)"
  apply (rule module_criteria) apply auto
       apply (fact cring_axioms)
      apply (fact add.m_comm)
     apply (fact add.m_assoc)
    apply (fact m_assoc)
   apply (fact l_distr)
  by (simp add: r_distr)

subsubsection \<open>Field Itself as Vector Space\<close>

abbreviation (input) "vs_of \<equiv> module_of" \<comment> \<open>This is not yet optimal...\<close>

sublocale field \<subseteq> self_vs: vectorspace R \<open>vs_of R\<close>
  rewrites "carrier (vs_of R) = carrier R"
  by (simp_all add: vectorspace_def self_module field_axioms)

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

text \<open>The following corresponds to theorem 11.7 of \<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LADS.pdf#section.0.11\<close>\<close>
lemma (in vectorspace) decompose_step:
  assumes fin_dim
  assumes "dim > 0"
  shows "\<exists>h V'. linear_map K V (direct_sum (vs_of K) (vs V')) h
    \<and> bij_betw h (carrier V) (carrier K \<times> V')
    \<and> subspace K V' V
    \<and> vectorspace.dim K (vs V') = dim - 1"
proof - \<comment> \<open>Possibly easier if the map definition were swapped as in Kemper's proof.\<close>
  from assms obtain B where B: "basis B" "card B > 0"
    using dim_basis finite_basis_exists by auto
  then obtain b where "b \<in> B"
    by fastforce
  let ?B = "B - {b}"
  have liB: "lin_indpt ?B" and BiV: "?B \<subseteq> carrier V" "finite ?B"
      apply (meson B(1) Diff_subset subset_li_is_li basis_def)
    using B(1) basis_def apply blast
    using B(2) card_infinite neq0_conv by blast
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
    let ?restricted = "\<lambda>bv\<in>B. r \<otimes>\<^bsub>K\<^esub> coeffs m bv"
    have "(\<lambda>bv. r \<otimes>\<^bsub>K\<^esub> coeffs m bv) \<in> B \<rightarrow> carrier K"
      using mV okese(1) rK by fastforce
    then have
      "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) B = lincomb ?restricted B"
      "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow>\<^sub>E carrier K"
      "?restricted \<in> B \<rightarrow>\<^sub>E carrier K"
        by (simp_all add: mV okese(1) rK, metis B(1) PiE_restrict lincomb_restrict_simp
            lincomb_smult mV okese rK restrict_PiE smult_closed basis_def)
    then have "coeffs (r \<odot>\<^bsub>V\<^esub> m) = ?restricted"
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
      have f7: "B - {b} \<subseteq> carrier V"
        by (simp add: BiV(1))
      have f8: "insert b (B - {b}) = B"
        using \<open>b \<in> B\<close> by blast
      have "\<forall>f c C fa. (f \<in> Pi (insert (c::'c) C) fa) = (f \<in> Pi C fa \<and> (f c::'a) \<in> fa c)"
        by blast
      then have f9: "cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) \<in> B - {b} \<and> r \<otimes>\<^bsub>K\<^esub> coeffs m (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<noteq> coeffs (r \<odot>\<^bsub>V\<^esub> m) (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<or> lincomb (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) = lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b})"
        using f8 f7 f6 a1 by (metis (no_types))
      have "coeffs m \<in> B - {b} \<rightarrow> carrier K \<and> coeffs m b \<in> carrier K"
        using f8 a3 by auto
      then show "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b}) = r \<odot>\<^bsub>V\<^esub> lincomb (coeffs m) (B - {b})"
        using f9 f7 a4 a2 lincomb_smult by fastforce
    qed
  qed
  then interpret linmap: linear_map K V \<open>direct_sum (vs_of K) ?V\<close> ?T .
  {
    fix v
    assume "v \<in> carrier V"
    let ?c = "coeffs v"
    have c: "?c \<in> B \<rightarrow>\<^sub>E carrier K" "v = lincomb ?c B"
      using okese by (simp add: \<open>v \<in> carrier V\<close>)+
    then have c0s: "v = \<zero>\<^bsub>V\<^esub> \<Longrightarrow> coeffs v \<in> B \<rightarrow> {\<zero>\<^bsub>K\<^esub>}"
      by (metis B(1) Diff_cancel Diff_eq_empty_iff PiE_restrict assms(1) li_le_dim(1) not_lindepD restrict_PiE basis_def)
    have "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else ?c bv) ?B = \<zero>\<^bsub>V\<^esub> \<longleftrightarrow> ?c \<in> ?B\<rightarrow>{\<zero>\<^bsub>K\<^esub>}"
      apply standard
      using not_lindepD
       apply (smt BiV(2) Diff_cancel Diff_eq_empty_iff Diff_iff PiE_mem Pi_I c(1) liB lin_dep_crit singletonI)
      by (smt BiV(1) Diff_not_in Pi_cong lincomb_zero)
    then have "?T v = \<zero>\<^bsub>direct_sum (vs_of K) (vs (span ?B))\<^esub> \<longrightarrow> v = \<zero>\<^bsub>V\<^esub>"
      unfolding direct_sum_def by auto (smt B(1) Pi_split_insert_domain \<open>b \<in> B\<close> c(2) insertCI
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
    using subspace.subspace_dim(3)[OF linmap.imT_is_subspace] \<open>vs_span_B.fin_dim\<close>
      direct_sum_dim(1) self_vs.vectorspace_axioms self_vs_fin_dim vs_span_B.vectorspace_axioms by auto
  note goal_2b = this[unfolded linmap.im_def direct_sum_def, simplified]
  from goal_1 goal_2a goal_2b goal_3 goal_4 show ?thesis
    unfolding bij_betw_def by blast
qed


subsection \<open>Vectors\<close>

txt "Use the existing \<^const>\<open>ring.func_space\<close>. Sadly, there are almost no lemmas for it."
definition (in ring) nspace where "nspace n = func_space {..<n::nat}"

lemma (in cring) nspace_is_module: "module R (nspace n)"
  unfolding nspace_def by (fact func_space_is_module)

(*
sublocale cring \<subseteq> nspace: module R \<open>nspace n\<close>
  by (fact nspace_is_module)
*)

lemma (in field) nspace_is_vs: "vectorspace R (nspace n)"
  unfolding nspace_def by (fact func_space_is_vs)

sublocale field \<subseteq> nspace: vectorspace R \<open>nspace n\<close>
  by (fact nspace_is_vs)

lemma (in ring) nspace_simps:
  "carrier (nspace n) = {..<n} \<rightarrow>\<^sub>E carrier R"
  "mult (nspace n) = undefined"
  "one (nspace n) = undefined"
  "add (nspace n) = (\<lambda>f g. \<lambda>i\<in>{..<n}. f i \<oplus> g i)"
  "zero (nspace n) = (\<lambda>_\<in>{..<n}. \<zero>)"
  "smult (nspace n) = (\<lambda>c f. \<lambda>i\<in>{..<n}. c \<otimes> f i)"
  unfolding nspace_def func_space_def by simp_all

lemma (in cring) nspace_neg:
  "v \<in> carrier (nspace n) \<Longrightarrow> \<ominus>\<^bsub>nspace n\<^esub> v = (\<lambda>i\<in>{..<n}. \<ominus>\<^bsub>R\<^esub> v i)" unfolding nspace_def
  using func_space_neg \<comment> \<open>Why suddenly \<^const>\<open>If\<close> and not \<^const>\<open>restrict\<close>?\<close> by fastforce

lemma (in vectorspace) nspace_iso:
  assumes fin_dim
  shows "\<exists>\<phi>. linear_map K (nspace dim) V \<phi> \<and>
    bij_betw \<phi> (carrier (nspace dim)) (carrier V)"
proof -
  from assms obtain bs where bs: "basis (set bs)" "distinct bs"
    using finite_basis_exists finite_distinct_list by blast
  have set_B_list: "set bs \<subseteq> carrier V"
    using bs(1) basis_def by auto
  have length_B: "length bs = dim"
    using bs dim_basis distinct_card by fastforce
  define ind where "ind = the_inv_into {..<dim} ((!) bs)"
  have inj_on_inds: "inj_on ((!) bs) {..<dim}"
    by (simp add: bs(2) inj_on_nth length_B)
  then have ind_less_dim: "ind b \<in> {..<dim}" if "b \<in> set bs" for b
    unfolding ind_def by (rule the_inv_into_into; use bs(2) distinct_Ex1 length_B that in fastforce)
  have v_o_ind: "v \<circ> ind \<in> set bs \<rightarrow> carrier K" if "v \<in> carrier (nspace dim)" for v
    using that ind_less_dim by (auto simp: nspace_simps)
  from ind_less_dim have "ind ` set bs = {..<dim}" unfolding image_def apply auto
    by (metis ind_def inj_on_inds length_B lessThan_iff nth_mem the_inv_into_f_f)
  from funcset_compose'[OF this] have v_is_zero: "v \<in> {..<dim} \<rightarrow> {\<zero>\<^bsub>K\<^esub>}" if "v \<circ> ind \<in> set bs \<rightarrow> {\<zero>\<^bsub>K\<^esub>}" for v
    using that by blast
  define \<phi> where "\<phi> v = lincomb (v \<circ> ind) (set bs)" for v
  interpret \<phi>: linear_map K \<open>nspace dim\<close> V \<phi>
    apply unfold_locales
    unfolding module_hom_def apply auto
    apply (simp add: \<phi>_def)
    using bs(1) basis_def v_o_ind apply auto[1]
     apply (simp add: \<phi>_def nspace_simps)
    using lincomb_sum apply (smt finite_set Pi_iff R.add.m_closed ind_less_dim lincomb_cong nspace_simps(1) o_apply restrict_apply' set_B_list v_o_ind)
    apply (simp add: \<phi>_def nspace_simps)
    by (smt Pi_iff ind_less_dim lincomb_cong lincomb_smult m_closed nspace_simps(1) o_apply restrict_apply' set_B_list v_o_ind)
  from bs(1) have li: "lin_indpt (set bs)"
    using basis_def by blast
  have v_is_zero': "v = (\<lambda>_\<in>{..<dim}. \<zero>\<^bsub>K\<^esub>)" if "v \<in> {..<dim} \<rightarrow>\<^sub>E carrier K" "\<forall>i\<in>{..<dim}. v i = \<zero>\<^bsub>K\<^esub>" for v
    using that by fastforce
  have "\<phi>.ker = {\<zero>\<^bsub>nspace dim\<^esub>}"
    apply (auto simp: \<phi>.ker_def \<phi>_def)
     apply (simp add: nspace_simps)
     apply (rule v_is_zero') apply blast
    using not_lindepD[OF li _ _ v_o_ind, unfolded nspace_simps] apply simp
     apply (smt List.finite_set \<open>ind ` set bs = {..<local.dim}\<close> comp_apply imageE li lin_dep_crit nspace_simps(1) order_refl v_o_ind)
    using \<phi>.f0_is_0 \<phi>_def by auto
  then have "inj_on \<phi> (carrier (nspace dim))"
    using \<phi>.Ke0_iff_inj by simp
  from bs(1) have gs: "gen_set (set bs)"
    by (simp add: basis_def)
  have "\<phi>.im = carrier V"
  proof (auto simp: \<phi>.im_def)
    fix vec_im
    assume "vec_im \<in> carrier V"
    with gs obtain c where c: "vec_im = lincomb c (set bs)" "c \<in> set bs \<rightarrow> carrier K"
      using finite_in_span set_B_list by blast
    define vec where "vec = (\<lambda>i\<in>{..<dim}. c (bs!i))"
    with c have "vec \<in> carrier (nspace dim)"
      by (simp add: Pi_iff length_B nspace_simps(1))
    moreover
    have "bs!(ind b) = b" if "b \<in> set bs" for b
      using that bs(2) distinct_Ex1 ind_def inj_on_inds length_B the_inv_into_f_f by fastforce
    then have "\<phi> vec = vec_im"
      unfolding \<phi>_def vec_def using c ind_less_dim lincomb_cong set_B_list by fastforce
    ultimately show "vec_im \<in> \<phi> ` carrier (nspace local.dim)"
      by blast
  qed
  with \<open>inj_on \<phi> (carrier (nspace dim))\<close> show ?thesis
    using inj_on_imp_bij_betw \<phi>.im_def \<phi>.linear_map_axioms by fastforce
qed

subsubsection \<open>Canonical Unit Vectors, Standard Basis\<close>

txt (in module) "\<^const>\<open>lincomb\<close>, \<^const>\<open>lin_dep\<close> etc are set-based."
lemmas [iff del] = lessThan_iff

context ring
begin

definition "cunit_vector n i = (\<lambda>i'\<in>{..<n}. if i=i' then \<one> else \<zero>)"

lemma cunit_vector_def': "cunit_vector n i = (\<lambda>i'\<in>{..<n}. if i'=i then \<one> else \<zero>)"
  by (auto simp: cunit_vector_def)

abbreviation "standard_basis n \<equiv> cunit_vector n ` {..<n}"

lemma cunit_vector_in_carrier[simp, intro]: "i\<in>{..<n} \<Longrightarrow> cunit_vector n i \<in> carrier (nspace n)"
  by (simp add: cunit_vector_def nspace_simps)

lemma cunit_vector_swap: "i\<in>{..<n} \<Longrightarrow> j\<in>{..<n} \<Longrightarrow> cunit_vector n i j = cunit_vector n j i"
  unfolding cunit_vector_def by simp

lemma finite_standard_basis: "finite (standard_basis n)" "card (standard_basis n) \<le> n"
  by simp (use card_image_le in force)

end

context domain \<comment> \<open>actually, \<^locale>\<open>cring\<close> + \<^prop>\<open>\<zero>\<noteq>\<one>\<close> is enough for much of this\<close>
begin

lemma cunit_vector_eq_iff[simp]:
  "i\<in>{..<n} \<Longrightarrow> cunit_vector n i = cunit_vector n i' \<longleftrightarrow> i = i'"
  unfolding cunit_vector_def by (smt restrict_apply' restrict_ext zero_not_one)

lemma inj_cunit_vector: "inj_on (cunit_vector n) {..<n}"
  apply (rule inj_onI) by simp

lemma card_standard_basis[simp]: "card (standard_basis n) = n"
  by (simp add: card_image inj_cunit_vector)

lemma (in cring) finsum_nspace_components:
  assumes "m \<in> A \<rightarrow> carrier (nspace n)"
  shows "finsum (nspace n) m A = (\<lambda>i\<in>{..<n}. finsum R (\<lambda>v. m v i) A)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x F)
  then have "(\<lambda>v. m v i) \<in> insert x F \<rightarrow> carrier R" if "i \<in> {..<n}" for i
    using PiE_E Pi_I Pi_mem nspace_simps(1) that by auto
  then have need_this: "(\<lambda>v. m v i) \<in> F \<rightarrow> carrier R" "m x i \<in> carrier R" if "i \<in> {..<n}" for i
    using that by auto
  have "abelian_monoid (nspace n)"
    using abelian_group.axioms(1) module.axioms(2) nspace_is_module by auto
  note abelian_monoid.finsum_insert[OF this, unfolded nspace_simps, OF insert(1-2)]
  then have "finsum (nspace n) m (insert x F) = (\<lambda>i\<in>{..<n}. m x i \<oplus> finsum (nspace n) m F i)"
    using insert.prems nspace_simps(1) by auto
  also have "\<dots> = (\<lambda>i\<in>{..<n}. m x i \<oplus> (\<Oplus>v\<in>F. m v i))"
    using insert.IH insert.prems by auto
  also have "\<dots> = (\<lambda>i\<in>{..<n}. \<Oplus>v\<in>insert x F. m v i)"
    using finsum_insert[OF insert.hyps(1-2), of "\<lambda>v. m v i" for i, OF need_this]
    by auto
  finally show ?case.
qed (simp_all add: finsum_def finprod_def nspace_simps)

lemma (in comm_monoid) finprod_not_depend':
  assumes "f \<in> A \<rightarrow> carrier G" and "\<And>a. a \<in> A \<Longrightarrow> f a = g a"
  shows "(\<Otimes>v\<in>A. f v) = (\<Otimes>v\<in>A. g v)"
  by (simp add: assms finprod_cong2)
lemmas (in abelian_monoid) finsum_not_depend' = add.finprod_not_depend'

lemma genset_standard_basis: "module.gen_set R (nspace n) (standard_basis n)"
proof
  show "carrier (nspace n) \<subseteq> module.span R (nspace n) (standard_basis n)"
  proof
    fix v
    assume v: "v \<in> carrier (nspace n)"
    define ind where "ind = the_inv_into {..<n} (cunit_vector n)"
    have ind[simp]: "ind uv \<in> {..<n}" "cunit_vector n (ind uv) = uv" if "uv \<in> standard_basis n" for uv
      unfolding ind_def apply (meson inj_cunit_vector subsetI that the_inv_into_into)
      using that by (simp add: f_the_inv_into_f inj_cunit_vector)
    have ind': "ind (cunit_vector n i) = i" if "i \<in> {..<n}" for i
      using that by (simp add: ind_def inj_cunit_vector the_inv_into_f_eq)
    note [simp] = nspace_simps(6)
    define c where "c i = (\<lambda>uv. v (ind uv) \<otimes> uv i)" for i
    have a: "c i \<in> standard_basis n \<rightarrow> carrier R" if "i \<in> {..<n}" for i
      unfolding nspace_simps(1) c_def using v ind(1) that
      by (smt PiE_restrict Pi_I' coeff_in_ring cunit_vector_in_carrier ind(2) m_closed nspace_simps(1) restrict_PiE)
    note rm_this = finsum_reindex[OF this inj_cunit_vector]
    from a have b: "(\<lambda>uv. (v \<circ> ind) uv \<odot>\<^bsub>nspace n\<^esub> uv) \<in> standard_basis n \<rightarrow> carrier (nspace n)"
      by (smt PiE_restrict Pi_I' coeff_in_ring comp_def cunit_vector_in_carrier ind module.smult_closed nspace_is_module nspace_simps(1) restrict_PiE v)
    note finsum_nspace_components[OF this, simplified]
    then have "module.lincomb (nspace n) (v\<circ>ind) (standard_basis n) =
      (\<lambda>i\<in>{..<n}. \<Oplus>uv\<in>standard_basis n. if i\<in>{..<n} then v (ind uv) \<otimes> uv i else undefined)"
      unfolding module.lincomb_def[OF nspace_is_module] by simp
    also have "\<dots> = (\<lambda>i\<in>{..<n}. \<Oplus>uv\<in>standard_basis n. v (ind uv) \<otimes> uv i)"
      by fastforce
    also have "\<dots> = (\<lambda>i\<in>{..<n}. \<Oplus>j\<in>{..<n}. v (ind (cunit_vector n j)) \<otimes> cunit_vector n j i)"
      using finsum_reindex[OF a[unfolded c_def] inj_cunit_vector] by auto
    also have "\<dots> = v"
    proof -
      have "(\<Oplus>j\<in>{..<n}. v (ind (cunit_vector n j)) \<otimes> cunit_vector n j i)
      = (\<Oplus>j\<in>{..<n}. v j \<otimes> cunit_vector n j i)" if "i\<in>{..<n}" for i
        apply (intro finsum_not_depend')
        using nspace_simps(1) that v apply fastforce
        by (simp add: ind')
      also have "\<dots> i = (\<Oplus>j\<in>{..<n}. v j \<otimes> (if i=j then \<one> else \<zero>))" if "i\<in>{..<n}" for i
        unfolding cunit_vector_def
        apply (intro finsum_not_depend')
        using that nspace_simps(1) v by auto
      also have "\<dots> i = (\<Oplus>j\<in>{..<n}. if i=j then v j else \<zero>)" if "i\<in>{..<n}" for i
        apply (intro finsum_not_depend')
        using that nspace_simps(1) v apply fastforce
        by (metis (full_types) PiE_mem nspace_simps(1) r_null r_one v)
      also have "\<dots> i = v i" if "i\<in>{..<n}" for i
        apply (intro finsum_singleton)
        using that nspace_simps(1) v by auto
      finally \<comment> \<open>fixme: remove redundancy. The same at linear independence\<close> show ?thesis
        using nspace_simps(1) v by fastforce
    qed
    finally have "v = module.lincomb (nspace n) (v \<circ> ind) (standard_basis n)"
      unfolding module.lincomb_def[OF nspace_is_module]..
    then show "v \<in> module.span R (nspace n) (standard_basis n)"
      unfolding module.span_def[OF nspace_is_module] apply auto
    proof -
      assume a1: "v = module.lincomb (nspace n) (v \<circ> ind) (standard_basis n)"
      have "v \<circ> ind \<in> standard_basis n \<rightarrow> carrier R"
        using ind(1) nspace_simps(1) v by auto
      then show "\<exists>f F. v = module.lincomb (nspace n) f F \<and> finite F \<and> F \<subseteq> standard_basis n \<and> f \<in> F \<rightarrow> carrier R"
        using a1 by blast
    qed
  qed
qed (meson cunit_vector_in_carrier image_subsetI module.span_is_subset2 nspace_is_module)

text \<open>In @{locale field}, one could now use @{thm linear_map.rank_nullity}, @{thm
  vectorspace.nspace_iso}, the Koordinatenfunktional and induction to show linear independence, but
  it also hold in @{locale cring}:\<close>
lemma lin_indpt_standard_basis:
  "module.lin_indpt R (nspace n) (standard_basis n)"
proof (rule module.finite_lin_indpt2[OF nspace_is_module])
  fix a
  assume a_is_coefficient: "a \<in> standard_basis n \<rightarrow> carrier R"
  and "module.lincomb (nspace n) a (standard_basis n) = \<zero>\<^bsub>nspace n\<^esub>"
  then have finsum_is_zero: "(\<Oplus>\<^bsub>nspace n\<^esub>uv\<in>standard_basis n. (\<lambda>i\<in>{..<n}. a uv \<otimes> uv i)) = \<zero>\<^bsub>nspace n\<^esub>"
    by (simp add: module.lincomb_def[OF nspace_is_module] nspace_simps)
  show "\<forall>uv\<in>standard_basis n. a uv = \<zero>"
  proof -
    have scaling: "(\<lambda>uv. \<lambda>i\<in>{..<n}. a uv \<otimes> uv i) \<in> standard_basis n \<rightarrow> (carrier (nspace n))"
      using a_is_coefficient nspace_simps(1) by fastforce
    note finsum_nspace_components[OF scaling]
    then have "(\<lambda>i\<in>{..<n}. \<Oplus>uv\<in>standard_basis n. a uv \<otimes> uv i) = \<zero>\<^bsub>nspace n\<^esub>"
      using finsum_is_zero by auto
    then have "\<zero> = (\<Oplus>uv\<in>standard_basis n. a uv \<otimes> uv i)" if "i\<in>{..<n}" for i
      by (simp add: nspace_simps(5), metis (mono_tags) restrict_apply' that)
    also have "\<dots> i = (\<Oplus>uv\<in>standard_basis n. a uv \<otimes> uv i)" if "i\<in>{..<n}" for i
      using that by (simp add: nspace_simps(6))
    also have "\<dots> i = (\<Oplus>j\<in>{..<n}. a (cunit_vector n j) \<otimes> cunit_vector n j i)" if "i\<in>{..<n}" for i
    proof -
      have "(\<lambda>uv. a uv \<otimes> uv i) \<in> standard_basis n \<rightarrow> carrier R" if "i\<in>{..<n}" for i
        using a_is_coefficient nspace_simps(1) that by fastforce
      note finsum_reindex[OF this inj_cunit_vector[of n]]
      with that show ?thesis
        by blast
    qed
    also have "\<dots> i = (\<Oplus>j\<in>{..<n}. a (cunit_vector n j) \<otimes> (if j=i then \<one> else \<zero>))" if "i\<in>{..<n}" for i
      using that by (simp add: cunit_vector_def)
    also have "\<dots> i = (\<Oplus>j\<in>{..<n}. if j=i then a (cunit_vector n j) \<otimes> \<one> else a (cunit_vector n j) \<otimes> \<zero>)" for i
    proof -
      have "(\<forall>na. (a (cunit_vector n na) \<otimes> \<zero> = a (cunit_vector n na) \<otimes> (if na = i then \<one> else \<zero>) \<or> i = na) \<and> (a (cunit_vector n na) \<otimes> \<one> = a (cunit_vector n na) \<otimes> (if na = i then \<one> else \<zero>) \<or> i \<noteq> na)) \<or> (\<Oplus>na\<in>{..<n}. a (cunit_vector n na) \<otimes> (if na = i then \<one> else \<zero>)) = (\<Oplus>na\<in>{..<n}. if na = i then a (cunit_vector n na) \<otimes> \<one> else a (cunit_vector n na) \<otimes> \<zero>)"
        by presburger
      then show ?thesis
        by (metis (no_types))
    qed
    also have "\<dots> i = (\<Oplus>j\<in>{..<n}. if j=i then a (cunit_vector n j) else a (cunit_vector n j) \<otimes> \<zero>)" if "i\<in>{..<n}" for i
      using a_is_coefficient coeff_in_ring that by fastforce
    also have "\<dots> i = (\<Oplus>j\<in>{..<n}. if j=i then a (cunit_vector n j) else \<zero>)" if "i\<in>{..<n}" for i
      by (smt Pi_iff a_is_coefficient finsum_cong2 image_eqI r_null zero_closed)
    also have "\<dots> i = a (cunit_vector n i)" if "i\<in>{..<n}" for i
      using finsum_singleton'[OF that]
      by (smt PiE a_is_coefficient finite_lessThan finsum_eqI image_eqI that)
    finally show ?thesis
      by force
  qed
qed fastforce+

end

lemma (in field) basis_standard_basis: "nspace.basis n (standard_basis n)"
  using genset_standard_basis lin_indpt_standard_basis by (simp add: image_subsetI nspace.basis_def)

lemma (in field) nspace_dim[simp]: "nspace.fin_dim n" "nspace.dim n = n"
  unfolding nspace.fin_dim_def using genset_standard_basis finite_standard_basis(1)
  by (fast, simp add: nspace.dim_basis[OF _ basis_standard_basis])

lemmas [iff] = lessThan_iff \<comment> \<open>reverse the declaration from above. to-do: use context?\<close>

subsubsection \<open>Koordinatenfunktional\<close>

lemma (in cring) \<comment> \<open>Kemper's \<^emph>\<open>Koordinatenfunktional\<close>. Need an English name...\<close>
  assumes "i<n" shows coo_mod_hom: "mod_hom R (nspace n) (module_of R) (\<lambda>v. v i)"
  apply (simp add: mod_hom_def nspace_is_module self_module)
  unfolding mod_hom_axioms_def module_hom_def by (simp add: nspace_simps, use assms in blast)

lemma (in cring) nspace_1_iso_self:
  "mod_hom R (nspace 1) (module_of R) (\<lambda>v. v 0)"
  "bij_betw (\<lambda>v. v 0) (carrier (nspace 1)) (carrier R)"
proof (rule coo_mod_hom)
  have "{..< 1::nat} = {0}"
    by auto
  then show "bij_betw (\<lambda>v. v 0) (carrier (nspace 1)) (carrier R)"
    by (simp add: nspace_simps singleton_PiE_bij)
qed simp

lemma (in field) coo_linear_map: "i\<in>{..<n} \<Longrightarrow> linear_map R (nspace n) (vs_of R) (\<lambda>v. v i)"
  unfolding linear_map_def by (auto simp: coo_mod_hom nspace_is_vs self_vs.vectorspace_axioms)

lemma (in field) nspace_1_iso_self:
  "linear_map R (nspace 1) (vs_of R) (\<lambda>v. v 0)"
  "bij_betw (\<lambda>v. v 0) (carrier (nspace 1)) (carrier R)"
  unfolding linear_map_def
  by (simp_all add: nspace_1_iso_self nspace_is_vs self_vs.vectorspace_axioms del: One_nat_def)


subsection \<open>Linear Maps\<close>

lemma (in subring) module_wrt_subring:
  "module R M \<Longrightarrow> module (R\<lparr>carrier:=H\<rparr>) M"
  unfolding module_def module_axioms_def by (simp add: cring.subring_cring subring_axioms)

lemma (in subfield) vectorspace_wrt_subfield:
  "vectorspace R V \<Longrightarrow> vectorspace (R\<lparr>carrier:=K\<rparr>) V" unfolding vectorspace_def
  by (auto simp: module_wrt_subring ring.subfield_iff(2) cring.axioms(1) module.axioms(1) subfield_axioms)

lemma (in subring) hom_wrt_subring:
  "h \<in> module_hom R M N \<Longrightarrow> h \<in> module_hom (R\<lparr>carrier:=H\<rparr>) M N"
  by (simp add: module_hom_def)

lemma (in subfield) linear_wrt_subfield:
  "linear_map R M N T \<Longrightarrow> linear_map (R\<lparr>carrier:=K\<rparr>) M N T" unfolding linear_map_def
  by (auto simp: vectorspace_wrt_subfield hom_wrt_subring mod_hom_axioms_def mod_hom_def module_wrt_subring)


subsection \<open>Fields\<close>

context field begin \<comment> \<open>"Let @{term R} be a field."\<close>

lemma nonzero_has_inv: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

lemma nonzero_inv_nonzero: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<noteq> \<zero>"
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
    by (simp add: subdomainE(2) subdomain_axioms)
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
  then have f: "comm_monoid \<lparr>carrier = K, mult = (\<oplus>), one = \<zero>, \<dots> = undefined::'b\<rparr>"
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

lemma (in UP_cring) weak_long_div_theorem: \<comment> \<open>barely weaker. Used to prove \<^term>\<open>euclidean_domain (UP K) degree\<close>.\<close>
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


end
