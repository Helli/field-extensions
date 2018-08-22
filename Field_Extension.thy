theory Field_Extension imports
"HOL-Algebra.Algebra"  (* reduce? *)
"VectorSpace_by_HoldenLee/Missing_VectorSpace"
begin

section \<open>convenient locale setup\<close>

locale subfield = subfield K L for K L
  \<comment> \<open>only for renaming. rm.\<close>

locale field_extension = subf'd?: subfield K L + superf'd?: field L for L K

lemmas
  subfield_intro = Subrings.subfield.intro[folded subfield_def]
lemmas (in field)
  generate_fieldE = generate_fieldE[folded subfield_def] and
  subfieldI' = subfieldI'[folded subfield_def] and
  generate_field_min_subfield2 = generate_field_min_subfield2[folded subfield_def]
lemmas (in ring)
  subfield_iff = subfield_iff[folded subfield_def] and
  subfieldI = subfieldI[folded subfield_def] and
  subfield_m_inv = subfield_m_inv[folded subfield_def]


section \<open>missing preliminaries?\<close>

lemma (in subgroup) subgroup_is_comm_group [intro]:
  assumes "comm_group G"
  shows "comm_group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret comm_group G by fact
  have "monoid (G\<lparr>carrier := H\<rparr>)"
    by (simp add: group.is_monoid is_group subgroup_is_group)
  then show ?thesis
    by (simp add: comm_group.intro is_group subgroup_is_group subgroup_is_submonoid
        submonoid_is_comm_monoid)
qed

lemma add_monoid_update[simp]: "add_monoid (R\<lparr>carrier := S\<rparr>) = add_monoid R \<lparr>carrier := S\<rparr>"
  by simp

lemma (in subfield) additive_subgroup: "additive_subgroup K L"
  by (simp add: additive_subgroupI is_subgroup)

lemma (in abelian_monoid) intersect_nonzeros:
  "\<M> \<noteq> {} \<Longrightarrow> \<Inter>\<M> - {\<zero>} = \<Inter>{M - {\<zero>}| M . M \<in> \<M>}"
  by auto

lemmas (in field)
  [simp] = mult_of_is_Units[symmetric] \<comment> \<open>avoid the duplicate constant\<close> and
  [simp] = units_of_inv

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

lemma (in abelian_group) contains_trivial:
  "a1\<in>carrier G \<Longrightarrow> a2\<in>carrier G \<Longrightarrow> \<ominus>a1 \<oplus> a2 \<in> carrier G"
    by simp


subsection \<open>Subrings\<close>

context ring begin \<comment> \<open>"Let @{term R} be a ring."\<close>

lemma ring_card: "card (carrier R) \<ge> 1 \<or> infinite (carrier R)"
  using not_less_eq_eq ring.ring_simprules(6) by fastforce

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
  unfolding old_sr_def using local.ring_axioms by blast

lemma old_sr_fullI: "\<lbrakk>A \<subseteq> carrier R; \<one>\<in>A; \<forall>r1\<in>A.\<forall>r2\<in>A. r1\<otimes>r2\<in>A \<and> \<ominus>r1\<oplus>r2\<in>A\<rbrakk>
  \<Longrightarrow> old_sr (R\<lparr>carrier:=A\<rparr>)"
  unfolding old_sr_def apply auto
  apply (rule ringI)
     apply (rule abelian_groupI)
          apply auto
         apply (metis add.inv_closed local.minus_minus r_zero ring_simprules(9) subsetCE)
  using l_neg apply fastforce
       apply (meson add.m_assoc subsetCE)
  apply (meson add.m_comm subsetCE)
     apply (metis add.inv_closed r_zero ring_simprules(9) subset_eq)
    apply (rule monoidI)
  apply auto
    apply (meson m_assoc subsetCE)
    apply (meson l_distr subsetCE)
    by (meson local.ring_axioms ring.ring_simprules(23) subsetCE)

lemma old_sr_zero: "old_sr S \<Longrightarrow> zero S = \<zero>"
  by (metis (full_types) l_zero local.add.right_cancel ring.ring_simprules(15)
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

lemma old_sr_ring_hom_ring: "old_sr S \<Longrightarrow> ring_hom_ring S R id" apply intro_locales unfolding old_sr_def
  subgoal using abelian_group.axioms(1) ring.is_abelian_group old_sr_def by blast
  subgoal using abelian_group.axioms(2) ring_axioms ring.is_abelian_group old_sr_def by blast
  subgoal using local.ring_axioms ring.is_monoid old_sr_def by blast
  subgoal unfolding old_sr_def by (simp add: ring.axioms(3))
  apply unfold_locales unfolding ring_hom_def apply auto
  by (metis (no_types, lifting) r_one ring.ring_simprules(12) ring.ring_simprules(6) subsetCE)

end

lemma (in cring) old_sr_cring: "old_sr S \<Longrightarrow> cring S" unfolding old_sr_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

lemma (in cring) old_sr_ring_hom_cring: "old_sr S \<Longrightarrow> ring_hom_cring S R id"
  by (simp add: RingHom.ring_hom_cringI is_cring old_sr_cring old_sr_ring_hom_ring)

lemma (in cring) Subring_cring: "subring S R \<Longrightarrow> cring (R\<lparr>carrier:=S\<rparr>)"
  using cring.subcringI' is_cring local.ring_axioms ring.subcring_iff subringE(1) by blast

lemma (in subring) cring_ring_hom_cring:
  "cring R \<Longrightarrow> ring_hom_cring (R\<lparr>carrier:=H\<rparr>) R id"
  by (simp add: cring.axioms(1) cring.old_sr_ring_hom_cring ring.old_sr_fullI subringE(5) subringE(7) subring_axioms subset)

lemma (in ring) subring_m_inv:
  assumes "subring K R" and "k \<in> Units (R\<lparr>carrier:=K\<rparr>)"
  shows "inv k \<in> Units (R\<lparr>carrier:=K\<rparr>)" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
proof -
  have K: "submonoid K R"
    by (simp add: assms(1) subring.axioms(2))
  have monoid: "monoid (R \<lparr> carrier := K \<rparr>)"
    by (simp add: K monoid_axioms submonoid.submonoid_is_monoid)

  from assms(2) have unit_of_R: "k \<in> Units R"
    using assms(2) unfolding Units_def by auto (meson K submonoid.mem_carrier)+
  have "inv\<^bsub>(R \<lparr> carrier := K \<rparr>)\<^esub> k \<in> Units (R \<lparr> carrier := K \<rparr>)"
    by (simp add: assms(2) monoid monoid.Units_inv_Units)
  thus "inv k \<in> Units (R \<lparr> carrier := K \<rparr>)" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
    using Units_l_inv[OF unit_of_R] Units_r_inv[OF unit_of_R]
    using monoid.m_inv_monoid_consistent[OF monoid_axioms assms(2) K] by auto
qed

context field begin \<comment> \<open>"Let @{term R} be a field."\<close>

lemma has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

definition old_sf where
  "old_sf K \<longleftrightarrow> old_sr K \<and> field K"

lemma old_sf_refl: "old_sf R"
  by (simp add: local.field_axioms old_sf_def old_sr_refl)

lemma old_sf_zero: "old_sf S \<Longrightarrow> zero S = \<zero>"
  unfolding old_sf_def using old_sr_zero by blast

lemma old_sf_one: "old_sf S \<Longrightarrow> one S = \<one>"
proof -
  assume a1: "old_sf S"
  then have "carrier S \<subseteq> carrier R \<and> ring S \<and> \<one> \<in> carrier S \<and> (\<forall>a. a \<notin> carrier S \<or> (\<forall>aa. aa \<notin>
    carrier S \<or> a \<oplus>\<^bsub>S\<^esub> aa = a \<oplus> aa \<and> a \<otimes>\<^bsub>S\<^esub> aa = a \<otimes> aa))"
    by (simp add: field.old_sf_def local.field_axioms old_sr_def)
  then show ?thesis
    using a1 by (metis (no_types) cring.cring_simprules(6) field.old_sf_def local.field_axioms
        r_one ring.ring_simprules(12) set_rev_mp old_sr_cring)
qed

lemma normalize_old_sf: "old_sf S \<Longrightarrow> old_sf (R\<lparr>carrier:=carrier S\<rparr>)"
  unfolding old_sf_def apply auto
   apply (simp add: normalize_old_sr)
  apply (rule cring.cring_fieldI2)
    apply auto
  using normalize_old_sr old_sr_cring apply auto[1]
  unfolding old_sr_def apply auto
  by (metis (no_types, lifting) field.has_inverse[simplified] old_sf_def old_sf_one old_sr_def old_sr_zero)

lemmas group_mult_of_subgroup = subgroup.subgroup_is_comm_group[OF _ units_comm_group, simplified]

lemma one_Units [simp]: "one (R\<lparr>carrier:=carrier A - {\<zero>}\<rparr>) = \<one>"
  by simp

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
    by (metis (no_types) Diff_iff assms(2) carrier_mult_of contra_subsetD local.field_Units subgroup_def)
  then show "\<exists>aa\<in>A. a \<otimes> aa = \<one>"
    using a2 a1 by (metis (no_types) Diff_iff Units_r_inv assms(2) empty_iff mult_of_is_Units insert_iff subgroup_def units_of_inv)
qed

lemma subgroup_add: \<open>old_sf S \<Longrightarrow> abelian_subgroup (carrier S) R\<close>
  by (simp add: abelian_subgroupI3 is_abelian_group old_sf_def old_sr_imp_subgroup)

lemma inv_nonzero: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<noteq> \<zero>"
  using Units_inv_Units local.field_Units by simp

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
  apply (metis (no_types, lifting) insert_Diff insert_iff local.field_Units zero_closed)
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
    using a4 a3 by (metis (no_types) carrier_mult_of insert_Diff insert_iff local.field_Units m_inv_mult_of monoid.Units_r_inv monoid_axioms r_null zero_closed zero_not_one)
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


section \<open>Field extensions\<close>

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

lemma (in -) carrier_K[simp]: "carrier (L\<lparr>carrier:=K\<rparr>) = K"
  by simp

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
  using local.field_axioms apply blast
  using normalize_old_sf old_sf_refl by auto

lemma (in field) old_fe_iff_old_sf: "old_fe R K \<longleftrightarrow> old_sf (R\<lparr>carrier:=K\<rparr>)"
  using old_fe.L_extends_K old_fe.intro old_fe_axioms_def
    local.field_axioms by blast

lemma (in subfield) finsum_simp: (* unused *)
  assumes \<open>ring L\<close>
  assumes "v ` A \<subseteq> K"
  shows "(\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i \<in> A. v i) = (\<Oplus>\<^bsub>L\<^esub>i \<in> A. v i)"
  unfolding finsum_def apply auto using assms
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case
    by (simp add: finprod_def)
next
  case empty
  have "\<zero>\<^bsub>L\<^esub> \<in> K"
    by (metis monoid.select_convs(2) subgroup_axioms subgroup_def)
  then show ?case
      by (simp add: finprod_def)
next
  case (insert x F)
  have a: "v \<in> F \<rightarrow> K"
    using insert.prems(2) by auto
  moreover have "K \<subseteq> carrier L"
    by (simp add: subset)
  ultimately have b: "v \<in> F \<rightarrow> carrier L"
    by fast
  have d: "v x \<in> K"
    using insert.prems(2) by auto
  then have e: "v x \<in> carrier L"
    using \<open>K \<subseteq> carrier L\<close> by blast
  have "abelian_monoid (L\<lparr>carrier := K\<rparr>)" using assms(1)
    using abelian_group_def ring.subring_iff ring_def subring_axioms subset by auto
  then have f: "comm_monoid \<lparr>carrier = K, monoid.mult = (\<oplus>\<^bsub>L\<^esub>), one = \<zero>\<^bsub>L\<^esub>, \<dots> = undefined::'b\<rparr>"
    by (simp add: abelian_monoid_def)
  note comm_monoid.finprod_insert[of "add_monoid L", simplified, OF _ insert.hyps b e, simplified]
  then have "finprod (add_monoid L) v (insert x F) = v x \<oplus>\<^bsub>L\<^esub> finprod (add_monoid L) v F"
    using abelian_group.a_comm_group assms(1) comm_group_def ring_def by blast
  with comm_monoid.finprod_insert[of "add_monoid (L\<lparr>carrier := K\<rparr>)", simplified, OF f insert.hyps a d, simplified]
  show ?case
    by (simp add: a image_subset_iff_funcset insert.IH insert.prems(1))
qed

lemma (in field) field_extension_refl: "field_extension R (carrier R)"
  by (simp add: field_extension.intro local.field_axioms subfield_iff(1))


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
    by (smt equals0D field.old_fe_iff_old_sf local.field_axioms mem_Collect_eq old_sf_altdef
        intersect_nonzeros)
qed

corollary "16_3_aux": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. old_fe L M \<and> M \<supseteq> K \<Longrightarrow> field (L\<lparr>carrier := \<Inter>\<M>\<rparr>)"
  by (simp add: "\<Inter>_is_old_sf" old_fe.K_field)

lemma (in field) mult_of_update[intro]: "\<zero> \<notin> S \<Longrightarrow> mult_of (R\<lparr>carrier := S\<rparr>) = mult_of R\<lparr>carrier := S\<rparr>" by simp

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

(*to-do: swap summands? remove qualifiers? It would be good if \<open>P\<close> appeared a bit more often (e.g.
as operator subscript) so that it does not come "out of nowhere" in the few places where it's used.*)
locale field_extension_with_UP = pol?: UP_univ_prop "L\<lparr>carrier := K\<rparr>" L id + field_extension L K
  for L (structure) and K
begin
txt \<open>The above locale header defines the ring \<^term>\<open>P\<close> of univariate polynomials over the field
  \<^term>\<open>K\<close>, which \<^term>\<open>Eval\<close> evaluates in the superfield \<^term>\<open>L\<close> at a fixed \<^term>\<open>s\<close>.\<close>

(* rm these two? *)
lemmas L_assoc = R.m_assoc[simplified]
lemmas one_is_neutral[simp] = R.l_one[simplified] R.r_one[simplified]

lemma Eval_x[simp]: (*rm?*)
  "Eval (UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1) = s" using eval_monom1 Eval_def by simp

lemma Eval_cx[simp]: "c \<in> K \<Longrightarrow> Eval (UnivPoly.monom P c 1) = c \<otimes>\<^bsub>L\<^esub> s"
proof goal_cases
  case 1
  then have "UnivPoly.monom P c 1 = c \<odot> UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1"
    using monom_mult_smult[of c "\<one>\<^bsub>L\<^esub>" 1, simplified] apply simp
    done
  then show ?case using "1" Eval_smult Eval_x subfield_axioms One_nat_def id_apply monom_closed
      carrier_K by (metis one_closed)
qed

lemma Eval_constant[simp]: "x \<in> K \<Longrightarrow> Eval (UnivPoly.monom P x 0) = x" unfolding
  Eval_monom[simplified] by auto

end


subsection \<open>Finitely generated field extensions\<close>

locale finitely_generated_field_extension = field_extension +
  assumes "\<exists>S. finite S \<and> generate_field L (S \<union> K) = carrier L"
(*  \<comment> \<open>Maybe remove quantifier by fixing \<open>S\<close>? Or replace locale by a simple predicate?\<close>
or simply add one of these:
begin
definition "S \<equiv> THE S. finite S \<and> generate_field L (S \<union> K) = carrier L"
definition "S \<equiv> SOME S. finite S \<and> generate_field L (S \<union> K) = carrier L"
What is the difference?
end
*)

lemma (in field) sum_of_fractions:
      "n1 \<in> carrier R \<Longrightarrow>
       n2 \<in> carrier R \<Longrightarrow>
       d1 \<in> carrier R \<Longrightarrow>
       d2 \<in> carrier R \<Longrightarrow>
       d1 \<noteq> \<zero> \<Longrightarrow>
       d2 \<noteq> \<zero> \<Longrightarrow>
          n1 \<otimes>inv d1 \<oplus> n2 \<otimes>inv d2 = (n1\<otimes>d2\<oplus>n2\<otimes>d1) \<otimes>inv (d1\<otimes>d2)"
proof goal_cases
  case 1
  then have
    "n1\<otimes>inv d1 = (n1\<otimes>d2)\<otimes>inv (d1\<otimes>d2)"
    "n2\<otimes>inv d2 = (n2\<otimes>d1)\<otimes>inv (d1\<otimes>d2)"
    by (smt comm_inv_char has_inverse m_closed m_lcomm r_one)+
  then show ?case
    by (simp add: 1 field_Units integral_iff l_distr)
qed

corollary (in field) fraction_sumE:
  assumes "n1 \<in> carrier R" "n2 \<in> carrier R" "d1 \<in> carrier R" "d2 \<in> carrier R"
  and "d1 \<noteq> \<zero>" "d2 \<noteq> \<zero>"
obtains n3 d3 where "n1 \<otimes>inv d1 \<oplus> n2 \<otimes>inv d2 = n3 \<otimes>inv d3"
  and "n3 \<in> carrier R" and "d3 \<in> carrier R" and "d3 \<noteq> \<zero>"
  by (simp add: assms integral_iff sum_of_fractions)

lemma (in field) inv_of_fraction[simp]:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  and "a \<noteq> \<zero>" "b \<noteq> \<zero>"
shows "inv (a \<otimes>inv b) = b \<otimes>inv a"
proof -
  from assms have "(a \<otimes>inv b) \<otimes> (b \<otimes>inv a) = \<one>"
  proof -
    have "\<forall>a aa ab. ((a \<otimes> ab \<otimes> aa = ab \<otimes> (a \<otimes> aa) \<or> aa \<notin> carrier R) \<or> a \<notin> carrier R) \<or> ab \<notin> carrier R"
      using m_assoc m_comm by force
    then have "(a \<otimes> (b \<otimes> inv a \<otimes> inv b) = \<one> \<and> b \<otimes> inv a \<in> carrier R) \<and> inv b \<in> carrier R"
      by (metis (no_types) Diff_iff Units_inv_closed Units_one_closed Units_r_inv assms empty_iff
          insert_iff inv_one local.field_Units m_assoc m_closed)
    then show ?thesis
      by (metis (no_types) assms(1) m_assoc m_comm)
  qed
  then show ?thesis
    by (simp add: assms comm_inv_char)
qed

text \<open>Proposition 16.5 of Prof. Gregor Kemper's lecture notes @{cite Algebra1} (only for \<^prop>\<open>S
  = {s}\<close>).\<close>

lemma pow_simp[simp]:
  fixes n :: nat
  shows "x [^]\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> n = x [^]\<^bsub>L\<^esub> n"
  unfolding nat_pow_def by simp

lemma (in field_extension_with_UP) intermediate_field_eval: (* inline? *)
  assumes "subfield M L"
  assumes "K \<subseteq> M"
  assumes "s \<in> M"
  shows "Eval = UnivPoly.eval (L\<lparr>carrier := K\<rparr>) (L\<lparr>carrier := M\<rparr>) id s"
  unfolding Eval_def eval_def apply auto apply (fold P_def)
proof -
  have "field (L\<lparr>carrier:=M\<rparr>)"
    using subfield_def S.subfield_iff(2) assms(1) by blast
  have a: "(\<lambda>i. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i) \<in> {..deg (L\<lparr>carrier := K\<rparr>) p} \<rightarrow> M"
    if "p \<in> carrier P" for p
  proof auto
    fix i
    assume "i \<le> deg (L\<lparr>carrier := K\<rparr>) p"
    then have "UnivPoly.coeff P p i \<in> M" and "s [^]\<^bsub>L\<^esub> i \<in> M"
      using assms coeff_closed that apply auto
      apply (auto intro!: monoid.nat_pow_closed[of "L\<lparr>carrier:=M\<rparr>",
            simplified]) using \<open>field (L\<lparr>carrier:=M\<rparr>)\<close>
      apply (simp add: cring_def domain_def field_def ring.is_monoid)
      done
    then show "UnivPoly.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i \<in> M"
      using assms(1) by (simp add: subfield_def Subrings.subfield.axioms(1) subdomainE(6))
  qed
  have "finsum (L\<lparr>carrier := M\<rparr>) f A = finsum L f A" if "f \<in> A \<rightarrow> M" for f and A :: "'c set"
    apply (intro ring_hom_cring.hom_finsum[of "L\<lparr>carrier:=M\<rparr>" L id, simplified])
    by (intro subring.cring_ring_hom_cring)
      (simp_all add: Field_Extension.subfield.axioms assms(1) subfieldE(1) S.is_cring that)
  from a[THEN this] show
    "(\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i) =
    (\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<lparr>carrier := M\<rparr>\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub>i)"
    by fastforce
qed

lemma (in field_extension_with_UP) insert_s_K: "insert s K \<subseteq> carrier L"
  \<comment>\<open>\<^term>\<open>s\<close> is already fixed in this locale (via @{locale UP_univ_prop})\<close>
  by (simp add: subset)

proposition (in field_extension_with_UP) genfield_singleton_explicit:
  "generate_field L (insert s K) =
    {Eval f \<otimes>\<^bsub>L\<^esub>inv\<^bsub>L\<^esub> Eval g | f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  unfolding generate_field_min_subfield2[OF insert_s_K] apply simp
proof -
  (* to-do: replace by define? *)
  let ?L' = "{Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  and ?\<M> = "{M. subfield M L \<and> s \<in> M \<and> K \<subseteq> M}"
  have "?L' \<in> ?\<M>"
  proof auto
    show "subfield ?L' L"
      apply (rule subfieldI')
    proof (rule S.subringI)
      fix h
      assume "h \<in> ?L'"
      then show "\<ominus>\<^bsub>L\<^esub> h \<in> ?L'"
        by (smt P.add.inv_closed S.l_minus inverse_exists mem_Collect_eq ring.hom_a_inv
            ring.hom_closed)
    next
      fix h1 h2
      assume "h1 \<in> ?L'" "h2 \<in> ?L'"
      then show "h1 \<otimes>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>f2"], rule exI[where x = "g1\<otimes>g2"]) using 1 apply
            auto
          apply (smt S.comm_inv_char S.m_lcomm S.one_closed S.r_null S.r_one S.ring_axioms
              inv_nonzero inv_of_fraction inverse_exists monoid.m_closed ring.hom_closed ring_def)
          using integral by blast
      qed
      from \<open>h1 \<in> ?L'\<close> \<open>h2 \<in> ?L'\<close> show "h1 \<oplus>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>g2\<oplus>f2\<otimes>g1"], rule exI[where x = "g1\<otimes>g2"])
          by (simp add: 1 integral_iff sum_of_fractions)
      qed
    next
      fix k
      assume "k \<in> ?L' - {\<zero>\<^bsub>L\<^esub>}"
      then show "inv\<^bsub>L\<^esub> k \<in> ?L'" by auto (use integral_iff in auto)
    qed force+
  next
    show "\<exists>f g. s = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1"], rule exI[where x = "\<one>"])
      by (auto simp del: One_nat_def)
  next
    fix \<alpha>
    assume "\<alpha> \<in> K"
    show "\<exists>f g. \<alpha> = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "UnivPoly.monom P \<alpha> 0"], rule exI[where x = "\<one>"])
      by (simp add: \<open>\<alpha> \<in> K\<close>)
  qed
  then have "?L' \<in> ?\<M>".

  moreover {
    fix M
    assume "M \<in> ?\<M>"
    then have L_over_M: "subfield M L" by auto
    have *: "K \<subseteq> M" and **: "s \<in> M"
      using \<open>M \<in> ?\<M>\<close> by auto
    interpret field_M: field "(L\<lparr>carrier:=M\<rparr>)"
      by (simp add: L_over_M S.subfield_iff(2))
    have "?L' \<subseteq> M"
    proof auto
      fix f g
      assume "f \<in> carrier P" "g \<in> carrier P"
      assume "Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      have double_update: "L\<lparr>carrier := K\<rparr> = L\<lparr>carrier:=M, carrier:=K\<rparr>" by simp
      interpret M_over_K: UP_univ_prop "L\<lparr>carrier:=K\<rparr>" "L\<lparr>carrier:=M\<rparr>" id
          apply (auto simp: P_def) \<comment> \<open>to-do: easier if I port @{thm [source]
          old_fe.intermediate_field_2} to the new setup?\<close>
        unfolding UP_univ_prop_def UP_pre_univ_prop_def apply auto
        unfolding double_update
        apply (intro subring.cring_ring_hom_cring) apply auto
           apply (intro ring.ring_incl_imp_subring) apply auto
        apply (simp add: field_M.ring_axioms)
        using * apply blast
        apply (simp add: R.ring_axioms)
        apply (simp add: field_M.is_cring)
        apply (fact is_UP_cring)
         apply (simp add: "**" UP_univ_prop_axioms_def)
        unfolding Eval_def apply (rule eq_reflection)
        apply (intro field_extension_with_UP.intermediate_field_eval)
        by (simp_all add: field_extension_with_UP_axioms L_over_M * **)
      from \<open>f \<in> carrier P\<close> have "Eval f \<in> M"
        using M_over_K.hom_closed by simp
      from \<open>g \<in> carrier P\<close> have "Eval g \<in> M"
        using M_over_K.hom_closed by simp
      with \<open>Eval g \<noteq> \<zero>\<^bsub>L\<^esub>\<close> have "inv\<^bsub>L\<^esub> Eval g \<in> M"
        using L_over_M S.subfield_m_inv(1) by auto
      with \<open>Eval f \<in> M\<close> show "Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<in> M"
        using field_M.m_closed[simplified] by simp
    qed
  }
  ultimately show "\<Inter>?\<M> = ?L'"
    by (meson cInf_eq_minimum)
qed


subsection \<open>Polynomial Divisibility\<close>

text \<open>use something along the lines of\<close>
definition (in UP_ring) "monic p \<longleftrightarrow> lcoeff p = \<one>"

text \<open>keep an eye out whether I need something from @{url
  "https://github.com/DeVilhena-Paulo/GaloisCVC4/blob/master/Polynomial_Divisibility.thy"}\<close>


subsection \<open>Degree of a field extension\<close>
text \<open>Todo: proposition 16.14\<close>

hide_const (open) degree

abbreviation "vs_of K \<equiv> \<comment> \<open>\<open>K\<close> extended with \<open>(\<otimes>\<^bsub>K\<^esub>)\<close> as \<^const>\<open>smult\<close>\<close>
  \<lparr>carrier = carrier K, monoid.mult = (\<otimes>\<^bsub>K\<^esub>), one = \<one>\<^bsub>K\<^esub>, zero = \<zero>\<^bsub>K\<^esub>, add = (\<oplus>\<^bsub>K\<^esub>), smult = (\<otimes>\<^bsub>K\<^esub>)\<rparr>"

context field_extension begin

lemma vectorspace_satisfied: "vectorspace (L\<lparr>carrier:=K\<rparr>) (vs_of L)"
  apply (rule vs_criteria) apply auto
       apply (simp add: subfield_axioms subfield_iff(2))
      apply (simp add: add.m_comm)
     apply (simp add: add.m_assoc)
    apply (simp add: m_assoc)
   apply (simp add: l_distr)
  by (simp add: semiring.semiring_simprules(13) semiring_axioms)

interpretation vecs: vectorspace "L\<lparr>carrier:=K\<rparr>" "vs_of L"
  by (fact vectorspace_satisfied)

abbreviation "fin \<equiv> vecs.fin_dim"
\<comment> \<open>Prop. 14.16 would look much better if I also had an abbreviation for infinite degree\<close>

definition degree where
  "degree \<equiv> if fin then vecs.dim else 0"
 \<comment> \<open>This uses the pragmatic tradition \<open>\<infinity> = 0\<close>. Adapting it to another notion of cardinality
 (ecard / enat) should not be too difficult.\<close>

lemma fin_dim_nonzero: "fin \<Longrightarrow> vecs.dim > 0"
  by (rule vecs.dim_greater_0) (auto dest: one_zeroI)

corollary degree_0_iff[simp]: "degree \<noteq> 0 \<longleftrightarrow> fin"
  by (simp add: degree_def fin_dim_nonzero)

end

locale finite_field_extension = field_extension +
  assumes fin

lemma (in field) field_is_vecs_over_itself: "vectorspace R (vs_of R)"
  by (fact field_extension.vectorspace_satisfied[OF field_extension_refl, simplified])

lemma (in field) trivial_degree[simp]: "field_extension.degree R (carrier R) = 1"
proof -
(* to-do: can this\<down> provide "vecs." lemmas and definitions? Probably if I use sublocale for vecs,
 but do I want/need this? Only when \<^bold>n\<^bold>o\<^bold>t working in field_extension...

  interpret asdfasdffe: field_extension R "carrier R"
    by (fact field_extension_refl)
*)
  interpret vecs: vectorspace R "vs_of R" by (fact field_is_vecs_over_itself)
  let ?A = "{\<one>}"
  have A_generates_R: "finite ?A \<and> ?A \<subseteq> carrier R \<and> vecs.gen_set ?A"
  proof auto
    show "x \<in> vecs.span {\<one>}" if "x \<in> carrier R" for x
      unfolding vecs.span_def apply auto apply (rule exI[of _ "\<lambda>_. x"]) \<comment> \<open>coefficient \<^term>\<open>x\<close>\<close>
      by (rule exI[of _ ?A]) (auto simp: that vecs.lincomb_def)
  qed (metis (mono_tags, lifting) empty_subsetI insert_subset module.span_is_subset2 one_closed
        partial_object.select_convs(1) subsetCE vecs.module_axioms)
  then have vecs.fin_dim "vecs.dim \<le> 1"
    using vecs.fin_dim_def apply force
    using A_generates_R vecs.dim_le1I by auto
  then show ?thesis unfolding field_extension.degree_def[OF field_extension_refl]
    using field_extension.fin_dim_nonzero[OF field_extension_refl] by simp
qed

lemma (in module) id_module_hom: "id \<in> module_hom R M M"
  unfolding module_hom_def by simp

find_theorems linear_map bij
term a_kernel
term kernel
term "linear_map.kerT"
find_theorems direct_sum vectorspace.dim

term bij_betw
lemma (in linear_map) emb_image_dim:
  assumes "inj_on T (carrier V)" \<comment> \<open>A module-monomorphism\<close>
  assumes V.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.dim = vectorspace.dim K (vs imT)"
  using assms inj_imp_dim_ker0 rank_nullity by linarith

lemma (in linear_map) iso_preserves_dim: (* rm *)
  assumes "bij_betw T (carrier V) (carrier W)" \<comment> \<open>A module-isomorphism\<close>
  assumes V.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.dim = W.dim"
  using assms by (simp add: bij_betw_def dim_eq) \<comment> \<open>uses Missing\_VectorSpace (*rm*)\<close>

lemma (in vectorspace) zero_not_in_basis:
  "basis B \<Longrightarrow> \<zero>\<^bsub>V\<^esub> \<notin> B"
  by (simp add: basis_def vs_zero_lin_dep)

lemma direct_sum_dim:
  assumes "vectorspace K V" "vectorspace.fin_dim K V"
  assumes "vectorspace K W" "vectorspace.fin_dim K W"
  shows "vectorspace.fin_dim K (direct_sum V W)"
    and "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
proof -
  from assms obtain Bv Bw where
    Bv: "finite Bv" "vectorspace.basis K V Bv" and
    Bw: "finite Bw" "vectorspace.basis K W Bw"
    using vectorspace.finite_basis_exists (* blast loops, but not in sledgehammer oO *)
    by metis
  oops

lemma direct_sum_dim: \<comment> \<open>cannot use @{thm[source] linear_map.rank_nullity} directly because the
 sum's dimension is not yet shown to be finite...\<close>
  assumes "vectorspace K V" "vectorspace.fin_dim K V"
  assumes "vectorspace K W" "vectorspace.fin_dim K W"
  shows "vectorspace.fin_dim K (direct_sum V W)"
    and "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
proof -
  interpret ds: vectorspace K "direct_sum V W"
    by (simp add: assms(1) assms(3) direct_sum_is_vs)

  txt \<open>embeddings into @{term "direct_sum V W"}\<close>
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
       apply (metis (mono_tags, lifting) f g ds.span_def lincomb1(1) lincomb2(1) mem_Collect_eq)+
      done
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
  out too tiresome. Instead, I use @{thm[source] linear_map.rank_nullity[OF _ \<open>ds.fin_dim\<close>]}:\<close>
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
    interpret T: linear_map K "direct_sum V W" "direct_sum V W" ?T
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
      using T.rank_nullity by auto
  qed
  with propagate_dims show "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
    by simp
qed (* to-do: use \<^sub> *)

proposition degree_multiplicative:
  assumes "Subrings.subfield K (M\<lparr>carrier:=L\<rparr>)" "Subrings.subfield L M" "field M"
  shows
    "field_extension.degree M K = field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
proof -
  let ?L = "M\<lparr>carrier:=L\<rparr>" and ?K = "M\<lparr>carrier:=K\<rparr>"

  have "K \<subseteq> L"
    using Field_Extension.subfield_def assms(1) subfieldE(3) by force
  then have "K \<subseteq> carrier M"
    by (meson assms(2) order.trans subfieldE(3))
  then have M_over_K: "field_extension M K"
    by (metis (no_types, lifting) field.generate_fieldE(1) subfield.axioms \<open>K \<subseteq> L\<close> assms(1-3)
        field.generate_fieldI field.generate_field_is_field field.subfield_gen_equality
        field_extension.intro monoid.surjective partial_object.update_convs(1) subfieldE(3)
        subset_refl)

  have "\<not>field_extension.fin M K" if "\<not>field_extension.fin ?L K"
  proof
    from M_over_K interpret enclosing: vectorspace ?K "vs_of M"
      by (simp add: field_extension.vectorspace_satisfied)
    have subspace: "subspace ?K L (vs_of M)"
      unfolding subspace_def apply (simp add: enclosing.vectorspace_axioms)
      apply (rule enclosing.module.module_incl_imp_submodule)
      apply (simp add: Field_Extension.subfield.axioms assms(2) field_extension.axioms(1)
          subfieldE(3))
      subgoal proof -
      from assms have "field_extension ?L K"
        using subfield.intro Subrings.ring.subfield_iff(2) cring_def domain_def field_def
          field_extension.intro by blast
      note field_extension.vectorspace_satisfied[OF this]
      then show ?thesis by (auto simp: vectorspace_def)
    qed done
    assume enclosing.fin_dim
    with that show False
      using subspace.corollary_5_16[OF subspace] by simp
  qed

  moreover have "\<not>field_extension.fin M K" if "\<not>field_extension.fin M L"
  proof
    interpret a: module ?L "vs_of M"
      by (simp add: subfield_def assms(2-3) field_extension.vectorspace_satisfied field_extension_def vectorspace.axioms(1))
    from that have "\<not>(\<exists>\<comment>\<open>Avoid latex dependency\<close>B. finite B \<and> B \<subseteq> carrier M \<and> a.span B = carrier M)"
      using subfield_def assms(2-3) field_extension.vectorspace_satisfied
        field_extension_def vectorspace.fin_dim_def[of ?L "vs_of M", simplified] by blast
    then have "\<And>B. finite B \<Longrightarrow> B \<subseteq> carrier M \<Longrightarrow> a.span B \<subset> carrier M"
      using a.span_is_subset2 by auto
    note 1 = this[unfolded a.span_def a.lincomb_def, simplified]
    interpret b: module ?K "vs_of M"
      by (simp add: M_over_K field_extension.vectorspace_satisfied vectorspace.axioms(1))
    assume "field_extension.fin M K"
    then have "\<exists>B. finite B \<and> B \<subseteq> carrier M \<and> b.span B = carrier M"
      using M_over_K field_extension.vectorspace_satisfied vectorspace.fin_dim_def by fastforce
    note 2 = this[unfolded b.span_def b.lincomb_def, simplified]
    from \<open>K \<subseteq> L\<close> have "f \<in> A \<rightarrow> L" if "f \<in> A \<rightarrow> K" for f and A::"'a set"
      using that by auto
    with 1 2 show False
      by (smt mem_Collect_eq psubsetE subsetI)
  qed

  moreover {
    assume "field_extension.fin M L" "field_extension.fin ?L K"
    have "field_extension.degree M K =
      vectorspace.dim ?L (vs_of M) *
      vectorspace.dim ?K (vs_of ?L)"
      sorry
  }

  ultimately
  show ?thesis
    by (smt ring.subfield_iff(1) M_over_K Subrings.ring.subfield_iff(2) assms cring.axioms(1)
        domain_def field_def field_extension.degree_def field_extension.intro monoid.surjective
        mult_is_0 partial_object.update_convs(1) subfieldE(3))
qed


section \<open>Observations (*rm*)\<close>

text \<open>@{locale subgroup} was the inspiration to just use sets for the substructure. However, that
locale is somewhat odd in that it does not impose @{locale group} on neither \<open>G\<close> nor \<open>H\<close>.\<close>

context subgroup begin
lemma "group G" oops
lemma "group (G\<lparr>carrier:=H\<rparr>)" oops
end

thm genideal_def cgenideal_def \<comment> \<open>This naming could be improved.\<close>
text \<open>@{const Ideal.genideal} could be defined using @{const hull}...\<close>

text \<open>@{thm[source] field_simps} are *not* available in general. Re-prove them?\<close>

value INTEG value "\<Z>" \<comment> \<open>duplicate definition\<close>

end
