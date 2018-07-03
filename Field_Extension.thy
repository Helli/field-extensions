theory Field_Extension imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.Multiplicative_Group" (* Polynomials *)
"HOL-Algebra.Group_Action"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above. rm? *)
begin


section \<open>missing preliminaries?\<close>

lemma (in field) comm_group_mult_of:
  shows "comm_group (mult_of R)"
  apply (rule group.group_comm_groupI groupI)
  apply (fact field_mult_group)
  by (auto simp: mult_of_simps m_comm)

lemma (in subgroup) subgroup_is_comm_group [intro]:
  assumes "comm_group G"
  shows "comm_group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret comm_group G by fact
  have "Group.monoid (G\<lparr>carrier := H\<rparr>)"
    by (simp add: group.is_monoid is_group subgroup_is_group)
  then show ?thesis
    by (simp add: comm_group.intro is_group subgroup_is_group subgroup_is_submonoid
        submonoid_is_comm_monoid)
qed

lemma (in field) deduplicate[simp]: "units_of R = mult_of R"
  unfolding mult_of_def units_of_def by (simp add: field_Units)

lemmas [simp] = mult_of_simps
lemmas (in field) [simp] = units_of_inv[simplified] units_of_inv

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

lemma (in comm_group) subgroup_group:
  "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. a1\<otimes>a2\<in>A \<and> m_inv G a1\<in>A\<rbrakk> \<Longrightarrow> comm_group (G\<lparr>carrier:=A\<rparr>)"
  by (metis all_not_in_conv comm_group_axioms comm_group_def subgroup.subgroup_is_group subgroupI
      submonoid_def submonoid_is_comm_monoid)

lemma (in comm_group) subgroup_group': "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. inv a1 \<otimes> a2 \<in> A\<rbrakk>
  \<Longrightarrow> comm_group (G\<lparr>carrier:=A\<rparr>)"
  by (metis (no_types, lifting) Units_def Units_eq Units_inv_inv r_one set_mp subgroup.m_inv_closed
      subgroup_group subgroup_self)

lemma (in abelian_group) contains_trivial:
  "a1\<in>carrier G \<Longrightarrow> a2\<in>carrier G \<Longrightarrow> \<ominus>a1 \<oplus> a2 \<in> carrier G"
    by simp


section \<open>Subrings\<close>

context ring begin \<comment> \<open>\<triangleq> "Let @{term R} be a ring."\<close>

lemma ring_card: "card (carrier R) \<ge> 1 \<or> infinite (carrier R)"
  using not_less_eq_eq ring.ring_simprules(6) by fastforce

lemma nonzero_ring_one: "card (carrier R) \<noteq> 1 \<Longrightarrow> one R \<noteq> zero R"
  using is_singleton_altdef is_singleton_def one_zeroD by blast

definition subring where
  "subring S \<longleftrightarrow>
    carrier S \<subseteq> carrier R \<and>
    ring S \<and>
    one R \<in> carrier S \<and>
    (\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. add S r1 r2 = add R r1 r2 \<and> mult S r1 r2 = mult R r1 r2)"

lemma "subring S \<Longrightarrow> Units S \<subseteq> Units R"
  unfolding Units_def apply auto
  using subring_def apply blast
  unfolding subring_def apply auto
  by (metis (no_types, hide_lams) contra_subsetD r_one ring.ring_simprules(12) ring.ring_simprules(6))

lemma subring_refl: "subring R"
  unfolding subring_def using local.ring_axioms by blast

lemma subring_fullI: "\<lbrakk>A \<subseteq> carrier R; \<one>\<in>A; \<forall>r1\<in>A.\<forall>r2\<in>A. r1\<otimes>r2\<in>A \<and> (\<ominus>r1)\<oplus>r2\<in>A\<rbrakk>
  \<Longrightarrow> subring (R\<lparr>carrier:=A\<rparr>)"
  unfolding subring_def apply auto
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

lemma subring_zero: "subring S \<Longrightarrow> zero S = \<zero>"
  by (metis (full_types) l_zero local.add.right_cancel ring.ring_simprules(15)
      ring.ring_simprules(2) subring_def subsetCE zero_closed)

lemma normalize_subring: "subring S \<Longrightarrow> subring (R\<lparr>carrier:=carrier S\<rparr>)"
  apply (rule subring_fullI)
  using subring_def apply blast
  using subring_def apply blast
  unfolding subring_def ring_def
    apply auto
   apply (metis monoid.m_closed)
  using abelian_group.contains_trivial[of S]
proof -
  fix r1 :: 'a and r2 :: 'a
  assume a1: "r2 \<in> carrier S"
  assume a2: "abelian_group S"
  assume a3: "r1 \<in> carrier S"
  assume a4: "carrier S \<subseteq> carrier R"
  assume a5: "Group.monoid S"
  assume a6: "ring_axioms S"
  assume a7: "\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. r1 \<oplus>\<^bsub>S\<^esub> r2 = r1 \<oplus> r2 \<and> r1 \<otimes>\<^bsub>S\<^esub> r2 = r1 \<otimes> r2"
  have f8: "\<forall>a A Aa. (a::'a) \<notin> A \<or> \<not> A \<subseteq> Aa \<or> a \<in> Aa"
    by blast
  then have f9: "r1 \<in> carrier R"
    using a4 a3 by presburger
  then have f10: "\<ominus> r1 \<in> carrier R"
    by simp
  have f11: "\<ominus>\<^bsub>S\<^esub> r1 \<in> carrier S"
    using a6 a5 a3 a2 by (simp add: ring.ring_simprules(3) ring_def)
  have f12: "\<zero>\<^bsub>S\<^esub> \<in> carrier R"
    using f8 a6 a5 a4 a2 a1 by (metis \<open>\<And>a2 a1. \<lbrakk>abelian_group S; a1 \<in> carrier S; a2 \<in> carrier S\<rbrakk> \<Longrightarrow>
        \<ominus>\<^bsub>S\<^esub> a1 \<oplus>\<^bsub>S\<^esub> a2 \<in> carrier S\<close> abelian_group.r_neg ring.ring_simprules(3) ring_def)
  have "\<ominus>\<^bsub>S\<^esub> r1 \<in> carrier R"
  using f11 f8 a4 by presburger
  then show "\<ominus> r1 \<oplus> r2 \<in> carrier S"
    using f12 f10 f9 a7 a6 a5 a3 a2 a1 by (metis (full_types) \<open>\<And>a2 a1. \<lbrakk>abelian_group S; a1 \<in>
        carrier S; a2 \<in> carrier S\<rbrakk> \<Longrightarrow> \<ominus>\<^bsub>S\<^esub> a1 \<oplus>\<^bsub>S\<^esub> a2 \<in> carrier S\<close> abelian_group.axioms(1)
        abelian_group.r_neg abelian_group.r_neg2 abelian_monoid.a_ac(2) local.ring_axioms
        ring.ring_simprules(3) ring_def)
qed

lemma subring_nontrivial: "card (carrier R) \<noteq> 1 \<Longrightarrow> subring S \<Longrightarrow> card (carrier S) \<noteq> 1"
  by (metis add.r_cancel_one' card_1_singletonE nonzero_ring_one one_closed ring.ring_simprules(15)
      ring.ring_simprules(2) singleton_iff subring_def)

lemma subring_trivial_iff: "subring S \<Longrightarrow> card (carrier R) = 1 \<longleftrightarrow> card (carrier S) = 1"
  by (metis card_1_singletonE contra_subsetD monoid.one_closed ring.nonzero_ring_one ring_def
      singleton_iff subring_def subring_nontrivial subring_zero zero_closed)

lemma subgroup_to_subring:
  "\<lbrakk>additive_subgroup A R; \<one>\<in>A; \<forall>a\<in>A. \<forall>b\<in>A. a\<otimes>b\<in>A\<rbrakk>
    \<Longrightarrow> subring (R\<lparr>carrier:=A\<rparr>)" using subring_fullI
  by (simp add: additive_subgroup.a_closed additive_subgroup.a_inv_closed additive_subgroup.a_subset)

lemma subyada_to_subring:
  "\<lbrakk>additive_subgroup A R; submonoid A R\<rbrakk> \<Longrightarrow> subring (R\<lparr>carrier:=A\<rparr>)"
  apply (rule subgroup_to_subring) apply auto
  apply (simp add: submonoid.one_closed)
  by (simp add: submonoid.m_closed)

lemma subring_imp_subgroup:
  "subring S \<Longrightarrow> additive_subgroup (carrier S) R"
  apply (rule additive_subgroup.intro, rule subgroup.intro)
     apply (auto simp: subring_def)
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

lemma subring_imp_submonoid:
  "subring S \<Longrightarrow> submonoid (carrier S) R"
  unfolding subring_def apply auto
  by (metis ring.ring_simprules(5) submonoid.intro)

lemma intermediate_ring_1:
  "subring S \<Longrightarrow> carrier S \<subseteq> M \<Longrightarrow> M \<subseteq> carrier R \<Longrightarrow> ring (R\<lparr>carrier:=M\<rparr>) \<Longrightarrow> subring (R\<lparr>carrier:=M\<rparr>)"
  unfolding subring_def by auto
lemma intermediate_ring_2:
  "subring S \<Longrightarrow> carrier S \<subseteq> M \<Longrightarrow> ring (R\<lparr>carrier:=M\<rparr>)
    \<Longrightarrow> ring.subring (R\<lparr>carrier:=M\<rparr>) S"
  unfolding subring_def ring.subring_def by auto

lemma subring_ring_hom_ring: "subring S \<Longrightarrow> ring_hom_ring S R id" apply intro_locales unfolding subring_def
  subgoal using abelian_group.axioms(1) ring.is_abelian_group subring_def by blast
  subgoal using abelian_group.axioms(2) ring_axioms ring.is_abelian_group subring_def by blast
  subgoal using local.ring_axioms ring.is_monoid subring_def by blast
  subgoal unfolding subring_def by (simp add: ring.axioms(3))
  apply unfold_locales unfolding ring_hom_def apply auto
  by (metis (no_types, lifting) r_one ring.ring_simprules(12) ring.ring_simprules(6) subsetCE)

end

lemma (in cring) subring_cring: "subring S \<Longrightarrow> cring S" unfolding subring_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

lemma (in cring) subring_ring_hom_cring: "subring S \<Longrightarrow> ring_hom_cring S R id"
  by (simp add: RingHom.ring_hom_cringI is_cring subring_cring subring_ring_hom_ring)

context field begin \<comment> \<open>\<triangleq> "Let @{term R} be a field."\<close>

lemma has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

definition subfield where
  \<comment> \<open>Maybe remove this definition and put it in the assumption of field_extension...
    (requires use of rewrite-clauses to avoid a name clash?)\<close>
  "subfield K \<longleftrightarrow> subring K \<and> field K"

lemma subfield_refl: "subfield R"
  by (simp add: local.field_axioms subfield_def subring_refl)

lemma subfield_zero: "subfield S \<Longrightarrow> zero S = \<zero>"
  unfolding subfield_def using subring_zero by blast

lemma subfield_one: "subfield S \<Longrightarrow> one S = \<one>"
proof -
  assume a1: "subfield S"
  then have "carrier S \<subseteq> carrier R \<and> ring S \<and> \<one> \<in> carrier S \<and> (\<forall>a. a \<notin> carrier S \<or> (\<forall>aa. aa \<notin>
    carrier S \<or> a \<oplus>\<^bsub>S\<^esub> aa = a \<oplus> aa \<and> a \<otimes>\<^bsub>S\<^esub> aa = a \<otimes> aa))"
    by (simp add: field.subfield_def local.field_axioms subring_def)
  then show ?thesis
    using a1 by (metis (no_types) cring.cring_simprules(6) field.subfield_def local.field_axioms
        r_one ring.ring_simprules(12) set_rev_mp subring_cring)
qed

lemma normalize_subfield: "subfield S \<Longrightarrow> subfield (R\<lparr>carrier:=carrier S\<rparr>)"
  unfolding subfield_def apply auto
   apply (simp add: normalize_subring)
  apply (rule cring.cring_fieldI2)
    apply auto
  using normalize_subring subring_cring apply auto[1]
  unfolding subring_def apply auto
  by (metis (no_types, lifting) field.has_inverse[simplified] subfield_def subfield_one subring_def subring_zero)

lemmas group_mult_of_subgroup = subgroup.subgroup_is_comm_group[OF _ units_comm_group, simplified]

lemma one_Units [simp]: "one (R\<lparr>carrier:=carrier A - {\<zero>}\<rparr>) = \<one>"
  by simp

interpretation (*todo: useful? as global_interpretation? name needed? already in ring or even in monoid?*)
fsdf: comm_group "mult_of R" by (fact units_comm_group[simplified])
    \<comment> \<open>@{thm[source] group_mult_of_subgroup} exists, but does not give commutativity...\<close>

lemma subfieldI:
  assumes "additive_subgroup A R"
  and "subgroup (A-{\<zero>}) (mult_of R)"
shows "subfield (R\<lparr>carrier:=A\<rparr>)"
  unfolding subfield_def apply auto apply (rule subgroup_to_subring)
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
  apply (rule subring_cring) apply (rule subyada_to_subring)
  apply (simp add: assms(1))
  apply (metis (mono_tags, lifting) Diff_subset \<open>\<And>b a. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> A\<close>
    additive_subgroup.a_subset assms ring_axioms monoid_incl_imp_submonoid
    one_mult_of ring.is_monoid ring.subgroup_to_subring ring.subring_def subgroup.one_closed
    subsetCE)
proof -
  fix a :: 'a
  assume a1: "a \<in> A"
  assume a2: "a \<noteq> \<zero>"
  have f3: "\<forall>Aa. a \<in> A - Aa \<or> a \<in> Aa"
    using a1 by blast
  then have f4: "a \<in> {\<zero>} \<or> inv\<^bsub>mult_of R\<^esub> a \<in> A"
    by (metis (no_types) Diff_iff assms(2) subgroup_def)
  have f5: "A - {\<zero>} \<subseteq> carrier (mult_of R)"
    by (metis (no_types) assms(2) subgroup_def)
  have f6: "\<forall>aa. a = aa \<or> a \<in> insert aa A - {aa}"
using a1 by fastforce
  have f7: "\<one>\<^bsub>mult_of R\<^esub> \<in> carrier (mult_of R)"
    by blast
  have "inv\<^bsub>mult_of R\<^esub> a \<in> carrier (mult_of R)"
    using f5 f3 a2 by blast
then show "\<exists>aa\<in>A. a \<otimes> aa = \<one>"
  using f7 f6 f5 f4 f3 a2 by (metis (no_types) Diff_iff contra_subsetD fsdf.inv_solve_left fsdf.r_one mult_mult_of one_mult_of)
qed

lemma subgroup_add: \<open>subfield S \<Longrightarrow> abelian_subgroup (carrier S) R\<close>
  by (simp add: abelian_subgroupI3 is_abelian_group subfield_def subring_imp_subgroup)

lemma operation_ok (*rm*): \<open>submonoid (carrier R-{\<zero>}) R\<close>
  by (metis Diff_subset Units_m_closed Units_one_closed field_Units submonoid.intro)

lemma inv_nonzero (*rm*): "x \<in> carrier R-{\<zero>} \<Longrightarrow> inv x \<noteq> \<zero>"
  using Units_inv_Units field_Units by auto

lemma inv_nonzero': "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<noteq> \<zero>"
  by (simp add: inv_nonzero local.field_axioms)

lemmas maybe_useful[simp] = group.m_inv_consistent[OF units_group, simplified]

lemma subfield_imp_subgroup:
  "subfield S \<Longrightarrow> subgroup (carrier S-{\<zero>}) (mult_of R)"
  apply (drule normalize_subfield)
  apply (rule group.subgroupI)
  apply (simp add: fsdf.is_group) unfolding subfield_def subring_def apply auto[]
  apply simp
    apply auto[1] apply simp
  using field.has_inverse[of "R\<lparr>carrier := carrier S\<rparr>", simplified] monoid.inv_unique[of
      "R\<lparr>carrier := carrier S\<rparr>", simplified] apply auto
  using set_rev_mp
  apply (metis (no_types, lifting) Units_one_closed comm_inv_char deduplicate unit_factor units_of_inv)
  apply (metis (no_types) carrier_mult_of fsdf.l_inv insertE insert_Diff l_null mult_mult_of
      one_mult_of subsetCE zero_closed zero_not_one)
  apply (metis monoid_incl_imp_submonoid ring.is_monoid submonoid_def)
  by (metis (full_types) integral monoid.monoid_incl_imp_submonoid monoid_axioms ring.is_monoid
      submonoid.mem_carrier)

lemma subfield_sane: (*also a better def?*) \<open>subfield (R\<lparr>carrier := S\<rparr>) \<longleftrightarrow>
  additive_subgroup S R \<and> subgroup (S-{\<zero>}) (mult_of R)\<close>
  apply auto using subgroup_add abelian_subgroup_def apply force
  using subfield_imp_subgroup apply force
  using subfieldI by blast

end

locale field_extension = field L for L (structure) +
  fixes K :: "'a set" \<comment> \<open>I see no reason why not to inherit \<zero>, \<one> and the operations. @{locale
    subgroup} does the same.\<close>
  assumes L_extends_K: "subfield (L\<lparr>carrier:=K\<rparr>)"
begin \<comment> \<open>\<triangleq> "Let @{term L}/@{term K} be a field extension."\<close>

lemma K_field: "field (L\<lparr>carrier:=K\<rparr>)"
  using L_extends_K by (simp add: subfield_def)

lemma K_subring: "subring (L\<lparr>carrier:=K\<rparr>)"
  using L_extends_K subfield_def by blast

lemmas K_subgroup =
  L_extends_K[unfolded subfield_sane, THEN conjunct1]
  L_extends_K[unfolded subfield_sane, THEN conjunct2]

lemma carrier_K[simp]: "carrier (L\<lparr>carrier:=K\<rparr>) = K"
  by simp

lemma K_inv: "a \<in> K \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> inv a \<in> K"
proof -
  assume a1: "a \<noteq> \<zero>"
  assume a2: "a \<in> K"
  have f3: "carrier (L\<lparr>carrier := K\<rparr>) \<subseteq> carrier L \<and> ring (L\<lparr>carrier := K\<rparr>) \<and> \<one> \<in> carrier (L\<lparr>carrier
    := K\<rparr>) \<and> (\<forall>a. a \<notin> carrier (L\<lparr>carrier := K\<rparr>) \<or> (\<forall>aa. aa \<notin> carrier (L\<lparr>carrier := K\<rparr>) \<or> a
    \<oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> aa = a \<oplus> aa \<and> a \<otimes>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> aa = a \<otimes> aa))"
    by (metis (no_types) K_subring subring_def)
  then have "\<forall>a. a \<notin> K \<or> a \<in> carrier L"
    by (simp add: subset_eq)
  then show ?thesis
    using f3 a2 a1
    by (metis K_field L_extends_K carrier_K comm_inv_char f3 field.has_inverse subfield_one subfield_zero)
qed

end

lemma (in field) f_e_refl : "field_extension R (carrier R)"
  unfolding field_extension_def field_extension_axioms_def apply auto
  using local.field_axioms apply blast
  using normalize_subfield subfield_refl by auto

lemma (in field) f_e_iff_subfield: "field_extension R K \<longleftrightarrow> subfield (R\<lparr>carrier:=K\<rparr>)"
  using field_extension.L_extends_K field_extension.intro field_extension_axioms_def
    local.field_axioms by blast

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

context field_extension
begin

lemma intermediate_field_1: "field (L\<lparr>carrier:=M\<rparr>) \<Longrightarrow> K \<subseteq> M \<Longrightarrow> M \<subseteq> carrier L \<Longrightarrow> field_extension L M"
  apply unfold_locales unfolding subfield_def apply auto unfolding field_def
  using intermediate_ring_1 K_subring cring_def domain_def by (metis carrier_K)
lemma intermediate_field_2:
  "K \<subseteq> M \<Longrightarrow> field (L\<lparr>carrier:=M\<rparr>) \<Longrightarrow> field_extension (L\<lparr>carrier:=M\<rparr>) K"
  by (metis K_field K_subring carrier_K cring_def domain_def field.f_e_iff_subfield
      field.normalize_subfield field.subfield_def field_def intermediate_ring_2)

lemma trivial (*todo: put outside*):
  "add_monoid (L\<lparr>carrier := A\<rparr>) = (add_monoid L)\<lparr>carrier := A\<rparr>"
  "\<M> \<noteq> {} \<Longrightarrow> \<Inter>\<M> - {\<zero>} = \<Inter>{M - {\<zero>}| M . M \<in> \<M>}"
  by auto

lemma "\<Inter>_is_subfield": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. field_extension L M \<and> M \<supseteq> K \<Longrightarrow> field_extension L (\<Inter>\<M>)"
  apply (unfold_locales) apply (auto simp add: subfield_sane)
  apply (metis add.subgroups_Inter additive_subgroup.a_subgroup additive_subgroupI equals0D
      field_extension.K_subgroup(1))
proof goal_cases
  case (1 M)
  then show ?case using group.subgroups_Inter[OF field_mult_group]
    by (smt equals0D field.f_e_iff_subfield local.field_axioms mem_Collect_eq subfield_sane
        trivial(2))
qed

corollary "16_3_aux": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. field_extension L M \<and> M \<supseteq> K \<Longrightarrow> field (L\<lparr>carrier := \<Inter>\<M>\<rparr>)"
  by (simp add: "\<Inter>_is_subfield" field_extension.K_field)

lemma (in field) mult_of_update[intro]: "\<zero> \<notin> S \<Longrightarrow> mult_of (R\<lparr>carrier := S\<rparr>) = mult_of R\<lparr>carrier := S\<rparr>" by simp

thm group.subgroups_Inter
  "subgroup.\<Inter>_is_supergroup"[of _ L]
  "subgroup.\<Inter>_is_supergroup"[of _ "L\<lparr>carrier := carrier L -{\<zero>}\<rparr>", simplified]
proposition "16_3_"[intro]:
  "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. field_extension L M \<and> M \<supseteq> K \<Longrightarrow> field_extension (L\<lparr>carrier:=\<Inter>\<M>\<rparr>) K"
proof goal_cases
  case 1
  note to_subfield =
    field.f_e_iff_subfield[OF "16_3_aux"[OF 1]]
    field.subfield_sane[OF "16_3_aux"[OF 1]]
  from 1 show ?case
    unfolding to_subfield additive_subgroup_def apply safe
    apply (unfold trivial)
     apply (rule "subgroup.\<Inter>_is_supergroup") apply auto
    apply (simp add: additive_subgroup.a_subgroup field_extension.K_subgroup(1)
        field_extension_axioms)
    using add.is_group apply blast
    using additive_subgroup.a_subgroup field_extension.K_subgroup(1) apply blast
  proof goal_cases
    case 1
    have "mult_of (L\<lparr>carrier := \<Inter>\<M>\<rparr>) = mult_of (L\<lparr>carrier := \<Inter>\<M> - {\<zero>}\<rparr>)"
      by simp
    with \<open>\<M> \<noteq> {}\<close> have minus_swap: "mult_of (L\<lparr>carrier := \<Inter>\<M>\<rparr>) = mult_of (L\<lparr>carrier := \<Inter>{M-{\<zero>}|M. M \<in> \<M>}\<rparr>)"
      by (simp add: trivial(2))
    have "mult_of (L\<lparr>carrier := \<Inter>{M-{\<zero>} |M. M \<in> \<M>}\<rparr>) = mult_of L\<lparr>carrier := \<Inter>{M-{\<zero>} |M. M \<in> \<M>}\<rparr>"
      using "1"(2) Diff_iff by blast
    then show ?case unfolding minus_swap apply simp
      apply (rule "subgroup.\<Inter>_is_supergroup")
      using 1 apply auto using K_subgroup apply simp
      using field_mult_group apply simp
      using field_extension.K_subgroup(2) by blast
  qed
qed

term genideal \<comment> \<open>Use this naming? Or \<open>gen\<close> (set) and \<open>genfield\<close> (structure)?\<close> term cgenideal\<comment>\<open>does not fit\<close>
definition genfield where
  "genfield S = (\<lambda>M. field_extension L M \<and> M \<supseteq> K) hull S"

lemma f_e_genfield: "S \<subseteq> carrier L \<Longrightarrow> field_extension (L\<lparr>carrier := genfield S\<rparr>) K"
  unfolding genfield_def hull_def
  by (auto simp add: K_subgroup(1) additive_subgroup.a_subset f_e_refl)

corollary field_genfield: "S \<subseteq> carrier L \<Longrightarrow> field (L\<lparr>carrier := genfield S\<rparr>)"
  using f_e_genfield field_extension_def by auto

interpretation emb: ring_hom_cring "(L\<lparr>carrier:=K\<rparr>)" L id
  by (simp add: K_subring subring_ring_hom_cring)

interpretation f_e_up: UP_pre_univ_prop "L\<lparr>carrier := K\<rparr>" L id "UP (L\<lparr>carrier := K\<rparr>)"
   by intro_locales

lemma pow_simp[simp]:
  fixes n :: nat
  shows "x \<in> K \<Longrightarrow> x [^]\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> n = x [^]\<^bsub>L\<^esub> n"
  using emb.hom_pow by auto

lemma "\<Oplus>_simp"[simp]:
  assumes "v ` A \<subseteq> K"
  shows "(\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i \<in> A. v i) = (\<Oplus>\<^bsub>L\<^esub>i \<in> A. v i)"
  unfolding finsum_def apply auto using assms apply (induction A rule: infinite_finite_induct)
  apply (simp add: finprod_def)
   apply (simp add: finprod_def K_subgroup(1) additive_subgroup.zero_closed)
proof goal_cases
  case (1 x F)
  have a: "v \<in> F \<rightarrow> K"
    using "1"(4) by blast
  moreover have "K \<subseteq> carrier L"
    by (simp add: K_subgroup(1) additive_subgroup.a_subset)
  ultimately have b: "v \<in> F \<rightarrow> carrier L"
    by fast
  have d: "v x \<in> K"
    using "1"(4) by blast
  then have e: "v x \<in> carrier L"
    using \<open>K \<subseteq> carrier L\<close> by blast
  have "abelian_monoid (L\<lparr>carrier := K\<rparr>)"
    using emb.abelian_monoid_axioms by blast
  then have f: "comm_monoid \<lparr>carrier = K, monoid.mult = (\<oplus>), one = \<zero>, \<dots> = undefined::'b\<rparr>"
    by (simp add: abelian_monoid_def)
  note comm_monoid.finprod_insert[of "add_monoid L", simplified, OF _ 1(1,2) b e, simplified]
  then have "finprod (add_monoid L) v (insert x F) = v x \<oplus> finprod (add_monoid L) v F"
    using local.add.comm_monoid_axioms by blast
  with 1 comm_monoid.finprod_insert[of "add_monoid (L\<lparr>carrier := K\<rparr>)", simplified, OF f 1(1,2) a d, simplified]
  show ?case
    by auto
qed

end

locale f_g_field_extension = field_extension +
  assumes "\<exists>S. carrier L = genfield S \<and> finite S" \<comment> \<open>Maybe remove quantifier by fixing \<open>S\<close>?\<close>

locale f_e_UP = UP_univ_prop "L\<lparr>carrier := K\<rparr>" L id + field_extension L K for L (structure) and K
begin

lemma Eval_x[simp]: (*rm?*)
  "Eval (monom P \<one>\<^bsub>L\<^esub> 1) = s" using eval_monom1 Eval_def by simp

lemma Eval_cx[simp]: "c \<in> K \<Longrightarrow> Eval (monom P c 1) = c\<otimes>\<^bsub>L\<^esub>s"
proof goal_cases
  case 1
  then have "monom P c 1 = c \<odot> monom P \<one>\<^bsub>L\<^esub> 1"
    using monom_mult_smult[of c "\<one>\<^bsub>L\<^esub>" 1, simplified] apply simp
    by (metis K_subgroup(1) L_extends_K S.r_one additive_subgroup.a_Hcarr carrier_K cring_def
        domain_def field_def ring.ring_simprules(6) subfield_def subfield_one)
  then show ?case
    by (metis "1" Eval_smult Eval_x L_extends_K One_nat_def S.subring_def carrier_K id_apply
        monom_closed subfield_def)
qed

lemma Eval_constant[simp]: "x \<in> K \<Longrightarrow> Eval (monom P x 0) = x" unfolding
  Eval_monom[simplified] apply auto
  by (meson K_subgroup(1) S.r_one additive_subgroup.a_Hcarr)

lemma simple_stuff[simp]:
  "monom P \<zero>\<^bsub>L\<^esub> 0 = \<zero>"
  "monom P \<one>\<^bsub>L\<^esub> 0 = \<one>"
  using monom_zero monom_one by auto

lemmas simpler_stuff =
  monom_inj[simplified]
  monom_closed[simplified]
  monom_mult_smult[simplified]

thm UP_ring.monom_inj

lemma wert:
  assumes "p1 \<in> carrier P" "p2 \<in> carrier P"
  obtains p3 where "p3 \<in> carrier P" and "Eval p1 \<oplus>\<^bsub>L\<^esub> Eval p2 = Eval p3"
  using assms by (metis UP_a_closed hom_add)

lemma wertwert:
  assumes "p1 \<in> carrier P" "p2 \<in> carrier P"
  obtains p3 where "p3 \<in> carrier P" and "Eval p1 \<otimes>\<^bsub>L\<^esub> Eval p2 = Eval p3"
  using assms by (metis UP_mult_closed hom_mult)

lemma wertwertwert:
  assumes "p1 \<in> carrier P" "p2 \<in> carrier P" "p1 \<noteq> \<zero>" \<open>p2 \<noteq> \<zero>\<close>
  obtains p3 where "p3 \<in> carrier P" and "Eval p1 \<otimes>\<^bsub>L\<^esub> Eval p2 = Eval p3" and "p3 \<noteq> \<zero>"
  using assms by (metis (no_types, hide_lams) integral ring.hom_zero ring_hom_closed
      ring_hom_cring.homh ring_hom_cring_axioms wertwert)

proposition "16_5_light" \<comment> \<open>only for singletons\<close>:
  shows "genfield {s} = \<comment> \<open>\<^term>\<open>s\<close> is already fixed in this locale (via @{locale UP_univ_prop})\<close>
    {Eval f \<otimes>\<^bsub>L\<^esub>inv\<^bsub>L\<^esub> Eval g | f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  unfolding genfield_def hull_def apply simp
proof -
  show "\<Inter>{t. field_extension L t \<and> K \<subseteq> t \<and> s \<in> t} = {Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in>
    carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
    (is "\<Inter>?\<M> = ?L'")
  proof -
    have in_field: "\<And>f. f \<in> carrier P \<Longrightarrow> Eval f \<in> carrier L" by simp
    interpret asdf: field_extension L ?L'
      apply standard apply (rule subfieldI) apply standard
      apply (smt S.comm_inv_char S.m_closed has_inverse mem_Collect_eq
          partial_object.select_convs(1) ring.hom_closed subsetI)
    proof goal_cases
      case (1 x y)
      then show ?case apply auto
      proof goal_cases
        case (1 n1 n2 d1 d2)
        show ?case apply (rule exI[where x = "n1\<otimes>d2\<oplus>n2\<otimes>d1"], rule exI[of _ "d1\<otimes>d2"])
          by (simp add: 1 integral_iff sum_of_fractions)
      qed
    next
      case 2
      then show ?case by force
    next
      case (3 x)
      have inv_simp: "inv\<^bsub>add_monoid L\<^esub> x = \<ominus>\<^bsub>L\<^esub> x"
        by (simp add: a_inv_def)
      from 3 show ?case apply (auto simp: inv_simp)
      proof goal_cases
        case (1 f g)
        show ?case apply (rule exI[of _ "\<ominus>f"], rule exI[of _ "g"]) using 1 apply auto
          by (metis S.comm_inv_char S.l_minus has_inverse in_field)
      qed
    next
      case 4
      then show ?case apply auto
        by (metis S.comm_inv_char S.m_closed has_inverse hom_closed)
    next
      case (5 x y)
      then show ?case apply auto
      proof goal_cases
        case (1 f1 g1 f2 g2)
        show ?case apply (rule exI[of _ "f1\<otimes>f2"], rule exI[of _ "g1\<otimes>g2"]) using 1 apply auto
          apply (smt S.comm_inv_char S.l_one S.m_closed S.m_comm cring.cring_simprules(11)
              domain.integral_iff domain_def field_def field_extension_axioms field_extension_def
              has_inverse in_field)
          using local.integral by blast
      qed (metis S.comm_inv_char S.m_closed has_inverse local.integral ring.hom_closed)
    next
      case 6
      then show ?case by force
    next
      case (7 x)
      have [simp]: "x \<in> carrier L \<Longrightarrow> m_inv (mult_of L) x = m_inv L x"
        using "7" m_inv_mult_of by auto
      with 7 have [simp]: "m_inv (mult_of L) x = m_inv L x"
        apply auto
        by (metis S.comm_inv_char S.m_closed \<open>x \<in> carrier L \<Longrightarrow> inv\<^bsub>mult_of L\<^esub> x = inv\<^bsub>L\<^esub> x\<close>
            has_inverse in_field)
      from 7 show ?case apply auto
      proof goal_cases
        case (1 f g)
        then have Eval_f_nonzero: "Eval f \<noteq> \<zero>\<^bsub>L\<^esub>"
          by (metis S.comm_inv_char S.semiring_axioms has_inverse in_field semiring.l_null)
        show ?case apply (rule exI[of _ "g"], rule exI[of _ "f"]) using 1 Eval_f_nonzero
          apply auto
          by (smt S.comm_inv_char S.cring_fieldI2 S.l_one S.m_closed S.m_comm
              cring.cring_simprules(11) domain_def field_def has_inverse in_field zero_not_one)
        case 2 then show ?case
          by (metis S.comm_inv_char S.semiring_axioms has_inverse ring.hom_closed semiring.r_null
              semiring.semiring_simprules(3))
      qed
    qed
    have "?L' \<in> ?\<M>" apply safe
    proof goal_cases
      case (2 x)
      show ?case apply (rule exI[of _ "monom P x 0"]) apply (rule exI[of _ \<open>\<one>\<close>]) apply safe
        apply auto
        using "2" K_subgroup(1) additive_subgroup.a_Hcarr apply fastforce
        by (simp add: "2" simpler_stuff)
    next
      case 3
      show ?case apply (rule exI[of _ "monom P \<one>\<^bsub>L\<^esub> 1"]) apply (rule exI[of _ \<open>\<one>\<close>]) apply safe
  apply auto
        using Eval_x One_nat_def S.r_one indet_img_carrier apply presburger
        apply (intro simpler_stuff(2))
        using K_subring S.subring_def carrier_K by blast
    qed (rule asdf.field_extension_axioms)
    moreover {
      fix M
      assume "M \<in> ?\<M>"
      then have "?L' \<subseteq> M" apply auto
      proof goal_cases
        case (1 f g)
        define P' where "P' = UP (L\<lparr>carrier := K\<rparr>)"
        define Eval' where "Eval' = eval (L\<lparr>carrier := K\<rparr>) (L\<lparr>carrier := M\<rparr>) id s"
        from 1 interpret asdfasdf: f_e_UP P' s Eval' "L\<lparr>carrier := M\<rparr>" K
            apply auto
          subgoal unfolding f_e_UP_def UP_univ_prop_def apply auto
          proof goal_cases
            case 1
            note intermediate_field_2[of M]
            then have tmp: "field_extension (L\<lparr>carrier := M\<rparr>) K" (*to-do: pull out one level*)
              using 1 field_extension.K_field by blast
            then show ?case
              by (metis "1"(2) K_subring S.intermediate_ring_2 UP_pre_univ_prop_def carrier_K
                  cring.subring_ring_hom_cring cring_def domain_def field_def field_extension_def
                  is_UP_cring)
          next
            case 2
            then show ?case
              by (simp add: UP_univ_prop_axioms_def)
          next
            case 3
            then show ?case
              using f_e_iff_subfield intermediate_field_2 subfield_def by blast
          qed
          by (simp_all add: P'_def Eval'_def)
        have M_mult_closed: "\<And>a b. a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> a \<otimes>\<^bsub>L\<^esub> b \<in> M"
          by (metis (no_types, lifting) "1"(1) S.subring_def field_extension.K_subring
              field_extension.carrier_K ring.ring_simprules(5))
        have "p \<in> carrier P \<Longrightarrow>
          (\<lambda>i. coeff (UP (L\<lparr>carrier := K\<rparr>)) p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i) ` {..deg (L\<lparr>carrier := K\<rparr>) p} \<subseteq> M"
          (is "?assms \<Longrightarrow> ?v ` ?A \<subseteq> M") for p
        proof -
          assume ?assms
          {
            fix i
            assume "i \<in> ?A"
            then have "coeff (UP (L\<lparr>carrier := K\<rparr>)) p i \<in> M" "s [^]\<^bsub>L\<^esub> i \<in> M"
              using "1"(2) P_def UP.coeff_closed \<open>p \<in> carrier P\<close> carrier_K apply blast
              using "1"(3) S.nat_pow_consistent asdfasdf.S.nat_pow_closed by auto
            then have "?v i \<in> M"
              using \<open>\<And>b a. \<lbrakk>a \<in> M; b \<in> M\<rbrakk> \<Longrightarrow> a \<otimes>\<^bsub>L\<^esub> b \<in> M\<close> by blast
          }
          then show ?thesis by auto
        qed
        note * =
          "field_extension.\<Oplus>_simp"[OF 1(1) this[OF \<open>f \<in> carrier P\<close>]]
          "field_extension.\<Oplus>_simp"[OF 1(1) this[OF \<open>g \<in> carrier P\<close>]]
        from 1 have "f \<in> carrier P'" "g \<in> carrier P'"
          unfolding P'_def P_def by blast+
        with 1 have "Eval' f \<in> M" "Eval' g \<in> M"
          using field_extension.carrier_K by blast+
        then have "Eval f \<in> M" "Eval g \<in> M" unfolding Eval_def Eval'_def
          unfolding eval_def by (auto simp: *
              field_extension.pow_simp[OF 1(1,3)])
        then show ?case apply (intro M_mult_closed) apply auto
          by (simp add: "1"(1) "1"(6) field_extension.K_inv)
      qed
    }
    ultimately show ?thesis
      by (meson cInf_eq_minimum)
  qed
qed

end

section\<open>Observations\<close>

text \<open>@{locale subgroup} was the inspiration to just use sets for the substructure. However, that
locale is somewhat odd in that it does not impose @{locale group} on neither \<open>G\<close> nor \<open>H\<close>.\<close>

context subgroup begin
lemma "group G" oops
lemma "group (G\<lparr>carrier:=H\<rparr>)" oops
end

text \<open>@{const Ideal.genideal} could be defined using @{const hull}...\<close>

text \<open>@{thm field_simps} are *not* available in general. Re-prove them? Collect them?\<close>

text\<open>The following is an easy generalisation of @{thm field.finite_mult_of}\<close>
lemma finite_mult_of: "finite (carrier R) \<Longrightarrow> finite (carrier (mult_of R))"
  by simp

(* duplicate: *)
value INTEG
value "\<Z>"
thm INTEG_def

find_theorems field
thm
QuotRing.maximalideal.quotient_is_field
Ideal.field.all_ideals
UnivPoly.INTEG.R.trivialideals_eq_field

end
