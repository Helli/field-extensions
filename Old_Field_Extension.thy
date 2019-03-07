(* Author: Fabian Hellauer, 2018 *)
section \<open>Old Development\<close>
theory Old_Field_Extension
  imports "HOL-Algebra.Subrings"
begin

lemma (in abelian_group) contains_trivial:
  "a1\<in>carrier G \<Longrightarrow> a2\<in>carrier G \<Longrightarrow> \<ominus>a1 \<oplus> a2 \<in> carrier G"
    by simp

lemma carrier_K: "carrier (L\<lparr>carrier:=K\<rparr>) = K"
  by simp

lemma (in abelian_monoid) intersect_nonzeros:
  "\<M> \<noteq> {} \<Longrightarrow> \<Inter>\<M> - {\<zero>} = \<Inter>{M - {\<zero>}| M . M \<in> \<M>}"
  by auto

lemma add_monoid_update[simp]: "add_monoid (R\<lparr>carrier := S\<rparr>) = add_monoid R \<lparr>carrier := S\<rparr>"
  by simp

lemma (in field) mult_of_update[intro]: "\<zero> \<notin> S \<Longrightarrow> mult_of (R\<lparr>carrier := S\<rparr>) = mult_of R\<lparr>carrier := S\<rparr>"
  by simp

context subgroup
begin

lemma "\<Inter>_is_supergroup":
  "group G \<Longrightarrow> \<M> \<noteq> {} \<Longrightarrow> \<forall>M\<in>\<M>. H \<subseteq> M \<and> subgroup M G \<Longrightarrow> subgroup H (G\<lparr>carrier:=\<Inter>\<M>\<rparr>)"
\<comment> \<open>Cannot use @{thm group.subgroupI} because @{locale subgroup} does not extend @{locale group}\<close>
  apply unfold_locales apply auto using group.subgroups_Inter
  by (metis (mono_tags) Collect_mem_eq Inf_greatest empty_Collect_eq group.subgroup_incl
      subgroup.m_inv_closed subgroup_axioms)

lemma generated_group:
  "S \<subseteq> carrier G \<Longrightarrow> group G \<Longrightarrow> subgroup H (G\<lparr>carrier:=(\<lambda>M. subgroup M G \<and> H \<subseteq> M) hull S\<rparr>)"
  unfolding hull_def apply (intro "\<Inter>_is_supergroup") apply auto
  by (meson group.subgroup_self rcosets_carrier subgroup_in_rcosets)

end

subsection \<open>Subrings\<close>

context ring begin

lemma nonzero_ring_one (*rm*): "card (carrier R) \<noteq> 1 \<Longrightarrow> one R \<noteq> zero R"
  using is_singleton_altdef is_singleton_def one_zeroD by blast

definition old_sr where
  "old_sr S \<longleftrightarrow>
    carrier S \<subseteq> carrier R \<and>
    ring S \<and>
    one R \<in> carrier S \<and>
    (\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. add S r1 r2 = add R r1 r2 \<and> monoid.mult S r1 r2 = monoid.mult R r1 r2)"

lemma "old_sr S \<Longrightarrow> Units S \<subseteq> Units R"
  unfolding Units_def apply auto
  using old_sr_def apply blast
  unfolding old_sr_def apply auto
  by (metis (no_types, hide_lams) contra_subsetD r_one ring.ring_simprules(12) ring.ring_simprules(6))

lemma old_sr_refl: "old_sr R"
  unfolding old_sr_def using ring_axioms by blast

lemma old_sr_fullI: "\<lbrakk>A \<subseteq> carrier R; \<one>\<in>A; \<forall>r1\<in>A.\<forall>r2\<in>A. r1\<otimes>r2\<in>A \<and> \<ominus>r1\<oplus>r2\<in>A\<rbrakk>
  \<Longrightarrow> old_sr (R\<lparr>carrier:=A\<rparr>)"
  unfolding old_sr_def apply auto
  apply (rule ringI)
     apply (rule abelian_groupI)
          apply auto
         apply (metis add.inv_closed minus_minus r_zero ring_simprules(9) subsetCE)
  using l_neg apply fastforce
       apply (meson add.m_assoc subsetCE)
  apply (meson add.m_comm subsetCE)
     apply (metis add.inv_closed r_zero ring_simprules(9) subset_eq)
    apply (rule monoidI)
  apply auto
    apply (meson m_assoc subsetCE)
    apply (meson l_distr subsetCE)
    by (meson ring_axioms ring.ring_simprules(23) subsetCE)

lemma old_sr_zero: "old_sr S \<Longrightarrow> zero S = \<zero>"
  by (metis (full_types) l_zero add.right_cancel ring.ring_simprules(15)
      ring.ring_simprules(2) old_sr_def subsetCE zero_closed)

lemma normalize_old_sr: "old_sr S \<Longrightarrow> old_sr (R\<lparr>carrier:=carrier S\<rparr>)"
  apply (rule old_sr_fullI)
  using old_sr_def apply blast
  using old_sr_def apply blast
  unfolding old_sr_def ring_def
    apply auto
   apply (metis monoid.m_closed)
  using abelian_group.contains_trivial[of S]
proof -
  fix r1 :: 'a and r2 :: 'a
  assume a1: "r1 \<in> carrier S"
  assume a2: "r2 \<in> carrier S"
  assume a3: "carrier S \<subseteq> carrier R"
  assume a4: "abelian_group S"
  assume a5: "\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. r1 \<oplus>\<^bsub>S\<^esub> r2 = r1 \<oplus> r2 \<and> r1 \<otimes>\<^bsub>S\<^esub> r2 = r1 \<otimes> r2"
  assume a6: "\<And>a1 a2. \<lbrakk>abelian_group S; a1 \<in> carrier S; a2 \<in> carrier S\<rbrakk> \<Longrightarrow> \<ominus>\<^bsub>S\<^esub> a1 \<oplus>\<^bsub>S\<^esub> a2 \<in> carrier S"
  have "\<ominus>\<^bsub>S\<^esub> r1 \<in> carrier S"
    using a4 a1 by (simp add: abelian_group.a_inv_closed)
  then show "\<ominus> r1 \<oplus> r2 \<in> carrier S"
    using a6 a5 a4 a3 a2 a1 by (metis (full_types) abelian_group.r_neg2 add.inv_closed add.m_lcomm r_neg2 subsetCE)
qed

lemma old_sr_nontrivial: "card (carrier R) \<noteq> 1 \<Longrightarrow> old_sr S \<Longrightarrow> card (carrier S) \<noteq> 1"
  by (metis add.r_cancel_one' card_1_singletonE nonzero_ring_one one_closed ring.ring_simprules(15)
      ring.ring_simprules(2) singleton_iff old_sr_def)

lemma old_sr_trivial_iff: "old_sr S \<Longrightarrow> card (carrier R) = 1 \<longleftrightarrow> card (carrier S) = 1"
  by (metis card_1_singletonE contra_subsetD monoid.one_closed ring.nonzero_ring_one ring_def
      singleton_iff old_sr_def old_sr_nontrivial old_sr_zero zero_closed)

lemma subgroup_to_old_sr:
  "\<lbrakk>additive_subgroup A R; \<one>\<in>A; \<forall>a\<in>A. \<forall>b\<in>A. a\<otimes>b\<in>A\<rbrakk>
    \<Longrightarrow> old_sr (R\<lparr>carrier:=A\<rparr>)" using old_sr_fullI
  by (simp add: additive_subgroup.a_closed additive_subgroup.a_inv_closed additive_subgroup.a_subset)

lemma subyada_to_old_sr:
  "\<lbrakk>additive_subgroup A R; submonoid A R\<rbrakk> \<Longrightarrow> old_sr (R\<lparr>carrier:=A\<rparr>)"
  apply (rule subgroup_to_old_sr) apply auto
  apply (simp add: submonoid.one_closed)
  by (simp add: submonoid.m_closed)

lemma old_sr_imp_subgroup:
  "old_sr S \<Longrightarrow> additive_subgroup (carrier S) R"
  apply (rule additive_subgroup.intro, rule subgroup.intro)
     apply (auto simp: old_sr_def)
  apply (metis ring.ring_simprules(1))
  apply (metis (no_types, hide_lams) add.r_cancel_one' ring.ring_simprules(15)
      ring.ring_simprules(2) ring.ring_simprules(5) submonoid.intro submonoid.mem_carrier)
proof -
fix x :: 'a
  assume a1: "carrier S \<subseteq> carrier R"
  assume a2: "\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. r1 \<oplus>\<^bsub>S\<^esub> r2 = r1 \<oplus> r2 \<and> r1 \<otimes>\<^bsub>S\<^esub> r2 = r1 \<otimes> r2"
  assume a3: "ring S"
assume a4: "x \<in> carrier S"
  have "\<forall>a. a \<in> carrier R \<or> a \<notin> carrier S"
using a1 by (meson subsetCE)
  then show "inv\<^bsub>add_monoid R\<^esub> x \<in> carrier S"
using a4 a3 a2 by (metis (no_types) a_inv_def abelian_group.a_inv_closed add.r_cancel_one'
    minus_equality ring.ring_simprules(15) ring.ring_simprules(2) ring.ring_simprules(9) ring_def)
qed

lemma old_sr_imp_submonoid:
  "old_sr S \<Longrightarrow> submonoid (carrier S) R"
  unfolding old_sr_def apply auto
  by (metis ring.ring_simprules(5) submonoid.intro)

lemma intermediate_ring_1:
  "old_sr S \<Longrightarrow> carrier S \<subseteq> M \<Longrightarrow> M \<subseteq> carrier R \<Longrightarrow> ring (R\<lparr>carrier:=M\<rparr>) \<Longrightarrow> old_sr (R\<lparr>carrier:=M\<rparr>)"
  unfolding old_sr_def by auto
lemma intermediate_ring_2:
  "old_sr S \<Longrightarrow> carrier S \<subseteq> M \<Longrightarrow> ring (R\<lparr>carrier:=M\<rparr>)
    \<Longrightarrow> ring.old_sr (R\<lparr>carrier:=M\<rparr>) S"
  unfolding old_sr_def ring.old_sr_def by auto

lemma old_sr_ring_hom_ring: "old_sr S \<Longrightarrow> ring_hom_ring S R id"
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def apply auto
  using old_sr_def apply blast
  apply (rule ring_axioms)
  apply (auto intro!: ring_hom_memI simp: old_sr_def)
  by (metis (no_types, lifting) r_one ring.ring_simprules(12) ring.ring_simprules(6) subsetCE)

end

lemma (in cring) old_sr_cring: "old_sr S \<Longrightarrow> cring S" unfolding old_sr_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

lemma (in cring) old_sr_ring_hom_cring: "old_sr S \<Longrightarrow> ring_hom_cring S R id"
  by (simp add: RingHom.ring_hom_cringI is_cring old_sr_cring old_sr_ring_hom_ring)

context field begin

lemma has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

definition old_sf where
  "old_sf K \<longleftrightarrow> old_sr K \<and> field K"

lemma old_sf_refl: "old_sf R"
  by (simp add: field_axioms old_sf_def old_sr_refl)

lemma old_sf_zero: "old_sf S \<Longrightarrow> zero S = \<zero>"
  unfolding old_sf_def using old_sr_zero by blast

lemma old_sf_one: "old_sf S \<Longrightarrow> one S = \<one>"
proof -
  assume a1: "old_sf S"
  then have "carrier S \<subseteq> carrier R \<and> ring S \<and> \<one> \<in> carrier S \<and> (\<forall>a. a \<notin> carrier S \<or> (\<forall>aa. aa \<notin>
    carrier S \<or> a \<oplus>\<^bsub>S\<^esub> aa = a \<oplus> aa \<and> a \<otimes>\<^bsub>S\<^esub> aa = a \<otimes> aa))"
    by (simp add: field.old_sf_def field_axioms old_sr_def)
  then show ?thesis
    using a1 by (metis (no_types, hide_lams) contra_subsetD ring_axioms monoid.r_one
        ring.ring_simprules(6,12) ring_def)
qed

lemma normalize_old_sf: "old_sf S \<Longrightarrow> old_sf (R\<lparr>carrier:=carrier S\<rparr>)"
  unfolding old_sf_def apply auto
   apply (simp add: normalize_old_sr)
  apply (rule cring.cring_fieldI2)
    apply auto
  using normalize_old_sr old_sr_cring apply auto[1]
  unfolding old_sr_def apply auto
  by (metis (no_types, lifting) field.has_inverse[simplified] old_sf_def old_sf_one old_sr_def old_sr_zero)

lemma old_sfI:
  assumes "additive_subgroup A R"
  and "subgroup (A-{\<zero>}) (mult_of R)"
shows "old_sf (R\<lparr>carrier:=A\<rparr>)"
  unfolding old_sf_def apply auto apply (rule subgroup_to_old_sr)
     apply (simp add: assms(1)) apply auto
  using assms(2) subgroup.one_closed apply fastforce
subgoal for a b
proof -
  assume a1: "b \<in> A"
  assume a2: "a \<in> A"
  have f3: "insert \<zero> (A - {\<zero>}) = A"
    by (metis additive_subgroup.a_subgroup assms(1) insert_Diff monoid.simps(2) subgroup_def)
  have "(a \<otimes> b = \<zero>) = (a = \<zero> \<or> b = \<zero>)"
    using a2 a1 by (meson additive_subgroup.a_subset assms(1) integral_iff set_rev_mp)
  then show ?thesis
    using f3 a2 a1 by (metis (no_types) assms(2) insertCI insertE mult_mult_of subgroup_def)
qed
  apply (rule cring.cring_fieldI2[of "R\<lparr>carrier:=A\<rparr>"])
    apply auto
  apply (rule old_sr_cring) apply (rule subyada_to_old_sr)
  apply (simp add: assms(1))
  apply (metis (mono_tags, lifting) Diff_subset \<open>\<And>b a. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a\<otimes>b \<in> A\<close>
    additive_subgroup.a_subset assms ring_axioms monoid_incl_imp_submonoid one_mult_of
    ring.is_monoid ring.subgroup_to_old_sr ring.old_sr_def subgroup.one_closed subsetCE)
proof -
  fix a :: 'a
  assume a1: "a \<in> A"
  assume a2: "a \<noteq> \<zero>"
  have "\<forall>a. (a \<in> {\<zero>} \<or> a \<in> Units R) \<or> a \<notin> A"
    by (metis (no_types) Diff_iff assms(2) carrier_mult_of contra_subsetD field_Units subgroup_def)
  then show "\<exists>aa\<in>A. a \<otimes> aa = \<one>"
    using a2 a1 by (metis (no_types) Diff_iff Units_r_inv assms(2) empty_iff mult_of_is_Units insert_iff subgroup_def units_of_inv)
qed

lemma subgroup_add: \<open>old_sf S \<Longrightarrow> abelian_subgroup (carrier S) R\<close>
  by (simp add: abelian_subgroupI3 is_abelian_group old_sf_def old_sr_imp_subgroup)

lemma old_sf_imp_subgroup:
  "old_sf S \<Longrightarrow> subgroup (carrier S-{\<zero>}) (mult_of R)"
  apply (drule normalize_old_sf)
  apply (rule group.subgroupI)
  apply (simp add: field_mult_group) unfolding old_sf_def old_sr_def apply auto[]
  apply simp
    apply auto[1] apply simp
  using field.has_inverse[of "R\<lparr>carrier := carrier S\<rparr>", simplified] monoid.inv_unique[of
      "R\<lparr>carrier := carrier S\<rparr>", simplified] apply auto
  using set_rev_mp  Units_one_closed comm_inv_char mult_of_is_Units units_of_inv
  apply (metis (no_types, lifting) insert_Diff insert_iff field_Units zero_closed)
subgoal
proof -
  fix a :: 'a
  assume a1: "a \<in> carrier S"
  assume a2: "carrier S \<subseteq> carrier R"
assume a3: "a \<noteq> \<zero>"
  assume a4: "inv\<^bsub>mult_of R\<^esub> a = \<zero>"
  have "a \<in> carrier R"
  using a2 a1 by auto
  then show False
    using a4 a3 by (metis (no_types) carrier_mult_of insert_Diff insert_iff field_Units m_inv_mult_of monoid.Units_r_inv monoid_axioms r_null zero_closed zero_not_one)
qed
  apply (metis monoid_incl_imp_submonoid ring.is_monoid submonoid_def)
  by (metis (full_types) integral monoid.monoid_incl_imp_submonoid monoid_axioms ring.is_monoid
      submonoid.mem_carrier)

lemma old_sf_altdef: \<open>old_sf (R\<lparr>carrier := S\<rparr>) \<longleftrightarrow>
  additive_subgroup S R \<and> subgroup (S-{\<zero>}) (mult_of R)\<close>
  apply auto using subgroup_add abelian_subgroup_def apply force
  using old_sf_imp_subgroup apply force
  using old_sfI by blast

end


locale old_fe = field L for L (structure) +
  fixes K :: "'a set" \<comment> \<open>I see no reason why not to inherit @{term \<zero>}, @{term \<one>} and the
 operations. @{locale subgroup} does the same.\<close>
  assumes L_extends_K: "old_sf (L\<lparr>carrier:=K\<rparr>)"
begin \<comment> \<open>"Let @{term L}/@{term K} be a field extension."\<close>

(* replace by interpretation K: field "L\<lparr>carrier:K\<rparr>" ? *)
lemma K_field: "field (L\<lparr>carrier:=K\<rparr>)"
  using L_extends_K by (simp add: old_sf_def)

lemma K_old_sr: "old_sr (L\<lparr>carrier:=K\<rparr>)"
  using L_extends_K old_sf_def by blast

lemmas K_subgroup =
  L_extends_K[unfolded old_sf_altdef, THEN conjunct1]
  L_extends_K[unfolded old_sf_altdef, THEN conjunct2]

lemma K_inv: "a \<in> K \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> inv a \<in> K"
proof -
  assume a1: "a \<noteq> \<zero>"
  assume a2: "a \<in> K"
  have f3: "carrier (L\<lparr>carrier := K\<rparr>) \<subseteq> carrier L \<and> ring (L\<lparr>carrier := K\<rparr>) \<and> \<one> \<in> carrier (L\<lparr>carrier
    := K\<rparr>) \<and> (\<forall>a. a \<notin> carrier (L\<lparr>carrier := K\<rparr>) \<or> (\<forall>aa. aa \<notin> carrier (L\<lparr>carrier := K\<rparr>) \<or> a
    \<oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> aa = a \<oplus> aa \<and> a \<otimes>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> aa = a \<otimes> aa))"
    by (metis (no_types) K_old_sr old_sr_def)
  then have "\<forall>a. a \<notin> K \<or> a \<in> carrier L"
    by (simp add: subset_eq)
  then show ?thesis
    using f3 a2 a1
    by (metis K_field L_extends_K carrier_K comm_inv_char f3 field.has_inverse old_sf_one old_sf_zero)
qed

end

lemma (in field) old_fe_refl: "old_fe R (carrier R)"
  unfolding old_fe_def old_fe_axioms_def apply auto
  using field_axioms apply blast
  using normalize_old_sf old_sf_refl by auto

lemma (in field) old_fe_iff_old_sf: "old_fe R K \<longleftrightarrow> old_sf (R\<lparr>carrier:=K\<rparr>)"
  using old_fe.L_extends_K old_fe.intro old_fe_axioms_def
    field_axioms by blast


subsection \<open>Intersections of intermediate fields\<close>

context old_fe
begin

lemma intermediate_field_1: "field (L\<lparr>carrier:=M\<rparr>) \<Longrightarrow> K \<subseteq> M \<Longrightarrow> M \<subseteq> carrier L \<Longrightarrow> old_fe L M"
  apply unfold_locales unfolding old_sf_def apply auto unfolding field_def
  using intermediate_ring_1 K_old_sr cring_def domain_def by (metis carrier_K)
lemma intermediate_field_2:
  "K \<subseteq> M \<Longrightarrow> field (L\<lparr>carrier:=M\<rparr>) \<Longrightarrow> old_fe (L\<lparr>carrier:=M\<rparr>) K"
  by (metis K_field K_old_sr carrier_K cring_def domain_def field.old_fe_iff_old_sf
      field.normalize_old_sf field.old_sf_def field_def intermediate_ring_2)

lemma "\<Inter>_is_old_sf": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. old_fe L M \<and> M \<supseteq> K \<Longrightarrow> old_fe L (\<Inter>\<M>)"
  apply (unfold_locales) apply (auto simp add: old_sf_altdef)
  apply (metis add.subgroups_Inter additive_subgroup.a_subgroup additive_subgroupI equals0D
      old_fe.K_subgroup(1))
proof goal_cases
  case (1 M)
  then show ?case using group.subgroups_Inter[OF field_mult_group]
    by (smt equals0D field.old_fe_iff_old_sf field_axioms mem_Collect_eq old_sf_altdef
        intersect_nonzeros)
qed

corollary "16_3_aux": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. old_fe L M \<and> M \<supseteq> K \<Longrightarrow> field (L\<lparr>carrier := \<Inter>\<M>\<rparr>)"
  by (simp add: "\<Inter>_is_old_sf" old_fe.K_field)

text \<open>Proposition 16.3 of Prof. Gregor Kemper's lecture notes @{cite Algebra1}.\<close>

proposition intersection_of_intermediate_fields_is_old_fe[intro]:
  "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. old_fe L M \<and> M \<supseteq> K \<Longrightarrow> old_fe (L\<lparr>carrier:=\<Inter>\<M>\<rparr>) K"
proof goal_cases
  case 1
  note to_old_sf =
    field.old_fe_iff_old_sf[OF "16_3_aux"[OF 1]]
    field.old_sf_altdef[OF "16_3_aux"[OF 1]]
  from 1 show ?case
    unfolding to_old_sf additive_subgroup_def apply safe
    apply (unfold add_monoid_update)
     apply (rule "subgroup.\<Inter>_is_supergroup") apply auto
    apply (simp add: additive_subgroup.a_subgroup old_fe.K_subgroup(1)
        old_fe_axioms)
    using add.is_group apply blast
    using additive_subgroup.a_subgroup old_fe.K_subgroup(1) apply blast
  proof goal_cases
    case 1
    have "mult_of (L\<lparr>carrier := \<Inter>\<M>\<rparr>) = mult_of (L\<lparr>carrier := \<Inter>\<M> - {\<zero>}\<rparr>)"
      by simp
    with \<open>\<M> \<noteq> {}\<close> have minus_swap: "mult_of (L\<lparr>carrier := \<Inter>\<M>\<rparr>) = mult_of (L\<lparr>carrier := \<Inter>{M-{\<zero>}|M. M \<in> \<M>}\<rparr>)"
      by (simp add: intersect_nonzeros)
    have "mult_of (L\<lparr>carrier := \<Inter>{M-{\<zero>} |M. M \<in> \<M>}\<rparr>) = mult_of L\<lparr>carrier := \<Inter>{M-{\<zero>} |M. M \<in> \<M>}\<rparr>"
      using "1"(2) Diff_iff by blast
    then show ?case unfolding minus_swap apply simp
      apply (rule "subgroup.\<Inter>_is_supergroup")
      using 1 apply auto using K_subgroup apply simp
      using field_mult_group apply simp
      using old_fe.K_subgroup(2) by blast
  qed
qed

definition genfield where
  "genfield S = (\<lambda>M. old_fe L M \<and> M \<supseteq> K) hull S"

lemma old_fe_genfield: "S \<subseteq> carrier L \<Longrightarrow> old_fe (L\<lparr>carrier := genfield S\<rparr>) K"
  unfolding genfield_def hull_def
  by (auto simp add: K_subgroup(1) additive_subgroup.a_subset old_fe_refl)

corollary field_genfield: "S \<subseteq> carrier L \<Longrightarrow> field (L\<lparr>carrier := genfield S\<rparr>)"
  using old_fe_genfield old_fe_def by auto

interpretation emb: ring_hom_cring "(L\<lparr>carrier:=K\<rparr>)" L id
  by (simp add: K_old_sr old_sr_ring_hom_cring)

interpretation old_fe_up: UP_pre_univ_prop "L\<lparr>carrier := K\<rparr>" L id "UP (L\<lparr>carrier := K\<rparr>)"
   by intro_locales

end

definition standard_ring
  where "standard_ring A = \<lparr>carrier = A, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

definition univ_ring
  where "univ_ring = \<lparr>carrier = UNIV, monoid.mult = (*) , one = 1, zero = 0, add = (+)\<rparr>"

lemma ring_univ_ring: "Ring.ring (univ_ring::_::Rings.ring_1 ring)"
  unfolding univ_ring_def
  apply (intro ringI abelian_groupI monoidI)
  apply (auto simp: ring_distribs mult.assoc)
  using ab_group_add_class.ab_left_minus apply blast
  done

lemma ring_standard_ring:
  "ring (standard_ring (range rat_of_int))"
  "ring (standard_ring (range real_of_rat))"
  "ring (standard_ring (range complex_of_real))"
  unfolding standard_ring_def
  apply standard
               apply auto
      apply (metis of_int_add range_eqI)
  unfolding Units_def apply auto
     apply (metis add.left_neutral add_diff_cancel_right' add_uminus_conv_diff of_int_add)
  using Ints_def apply auto[1]
        apply (simp add: mult.commute ring_class.ring_distribs(1))
  apply (simp add: ring_class.ring_distribs(1))
  using Rats_def apply auto[]
     apply (smt of_rat_minus)
  using Rats_def apply auto[1]
  using ring_class.ring_distribs(2) apply blast
  apply (simp add: ring_class.ring_distribs(1))
  using Reals_def apply auto[1]
  apply (simp add: add_eq_0_iff)
  using Reals_def apply auto[1]
  by (simp_all add: ring_class.ring_distribs)

lemma old_sr_example: "ring.old_sr univ_ring (standard_ring (range rat_of_int))"
  unfolding ring.old_sr_def[OF ring_univ_ring]
  apply (auto simp add: univ_ring_def) unfolding standard_ring_def
     apply (metis ring_standard_ring(1) standard_ring_def)
  by auto

lemma field_univ_ring: "Ring.field (univ_ring::_::Fields.field ring)"
  apply unfold_locales apply (auto intro: right_inverse simp: univ_ring_def Units_def field_simps)
  by (metis ab_group_add_class.ab_left_minus add.commute)

lemma f_r_o_r: \<open>field (standard_ring (range real_of_rat))\<close>
  apply standard
                   apply (auto simp: standard_ring_def)
  using Rats_add Rats_def apply blast
  unfolding Units_def apply auto
      apply (smt of_rat_minus)
  using Rats_def apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis mult.commute nonzero_mult_div_cancel_left of_rat_eq_1_iff of_rat_mult
      times_divide_eq_right)

lemma old_fe_real_over_rat: "old_fe univ_ring (range real_of_rat)"
  apply (simp add: old_fe_def old_fe_axioms_def field_univ_ring)
proof -
  have f1: "ring \<lparr>carrier = range real_of_rat, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"
    by (metis (no_types) ring_standard_ring(2) standard_ring_def)
  have f2: "univ_ring = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"
    using univ_ring_def by auto
  have "ring \<lparr>carrier = UNIV, monoid.mult = (*), one = 1::real, zero = 0, add = (+)\<rparr>"
    by (metis ring_univ_ring univ_ring_def)
  then have "ring.old_sr \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr> \<lparr>carrier = range real_of_rat, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"
    using f1 by (simp add: ring.old_sr_def)
  then show "field.old_sf univ_ring (univ_ring\<lparr>carrier := range real_of_rat\<rparr>)"
    using f2 by (metis (mono_tags, lifting) f_r_o_r field.old_sf_def field_univ_ring partial_object.update_convs(1) standard_ring_def)
qed

end
