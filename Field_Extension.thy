theory Field_Extension imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above. rm? *)
begin


section \<open>missing preliminaries?\<close>

context subgroup
begin

lemma "\<Inter>_is_supergroup":
  "group G \<Longrightarrow> \<M> \<noteq> {} \<Longrightarrow> \<forall>M\<in>\<M>. H \<subseteq> M \<and> subgroup M G \<Longrightarrow> subgroup H (G\<lparr>carrier:=\<Inter>\<M>\<rparr>)"
\<comment> \<open>Cannot use @{thm group.subgroupI} because @{locale subgroup} does not extend @{locale group}\<close>
  apply unfold_locales apply auto using group.subgroups_Inter
  by (metis (mono_tags) Collect_mem_eq Inf_greatest contra_subsetD empty_Collect_eq
      group.subgroup_inv_equality subgroup.m_inv_closed subgroup_axioms)

lemma generated_group:
  "S \<subseteq> carrier G \<Longrightarrow> group G \<Longrightarrow> subgroup H (G\<lparr>carrier:=(\<lambda>M. subgroup M G \<and> H \<subseteq> M) hull S\<rparr>)"
  unfolding hull_def apply (intro "\<Inter>_is_supergroup") apply auto
  by (meson group.subgroup_self rcosets_carrier subgroup_in_rcosets)

end

lemma (in comm_group) subgroup_group:
  "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. a1\<otimes>a2\<in>A \<and> m_inv G a1\<in>A\<rbrakk> \<Longrightarrow> comm_group (G\<lparr>carrier:=A\<rparr>)"
  apply standard                                     
        apply auto
    apply (simp add: m_assoc subset_iff)
   apply (meson m_comm subsetCE)
  unfolding Units_def
proof goal_cases
  case (1 x)
  then have "x \<in> carrier G" by blast
  then show ?case using 1 by force
qed

lemma (in comm_group) subgroup_group': "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. inv a1 \<otimes> a2 \<in> A\<rbrakk>
  \<Longrightarrow> comm_group (G\<lparr>carrier:=A\<rparr>)"
  by (metis (full_types) contra_subsetD inv_inv r_one subgroup_def subgroup_group subgroup_self)

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

lemma abolishedI: "\<lbrakk>A \<subseteq> carrier R; \<one>\<in>A; \<forall>r1\<in>A.\<forall>r2\<in>A. r1\<otimes>r2\<in>A \<and> (\<ominus>r1)\<oplus>r2\<in>A\<rbrakk>
  \<Longrightarrow> subring (R\<lparr>carrier:=A\<rparr>)"
  unfolding subring_def apply auto
  apply (rule ringI)
     apply auto
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
  apply (rule abolishedI)
  using subring_def apply blast
  using subring_def apply blast
  unfolding subring_def ring_def
    apply auto
   apply (metis monoid.m_closed)
  using abelian_group.contains_trivial[of S]
proof -
  fix r1 :: 'a and r2 :: 'a
  assume a1: "r1 \<in> carrier S"
  assume a2: "r2 \<in> carrier S"
  assume a3: "abelian_group S"
  assume a4: "carrier S \<subseteq> carrier R"
  assume a5: "Group.monoid S"
  assume a6: "ring_axioms S"
  assume a7: "\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. r1 \<oplus>\<^bsub>S\<^esub> r2 = r1 \<oplus> r2 \<and> r1 \<otimes>\<^bsub>S\<^esub> r2 = r1 \<otimes> r2"
  have f8: "\<forall>A Aa a. \<not> A \<subseteq> Aa \<or> (a::'a) \<notin> A \<or> a \<in> Aa"
    by (meson subsetCE)
  then have f9: "r1 \<in> carrier R"
    using a4 a1 by meson
  have f10: "ring S"
    using a6 a5 a3 ring.intro by auto
    then have f11: "\<ominus>\<^bsub>S\<^esub> r1 \<in> carrier S"
      using a1 by (metis ring.ring_simprules(3))
    have f12: "\<zero>\<^bsub>S\<^esub> \<in> carrier R"
    using f10 f8 a4 a3 a1 by (metis (full_types) \<open>\<And>a2 a1. \<lbrakk>abelian_group S; a1 \<in> carrier S; a2 \<in>
        carrier S\<rbrakk> \<Longrightarrow> \<ominus>\<^bsub>S\<^esub> a1 \<oplus>\<^bsub>S\<^esub> a2 \<in> carrier S\<close> ring.ring_simprules(16) ring.ring_simprules(3))
      have "\<ominus>\<^bsub>S\<^esub> r1 \<in> carrier R"
using f11 a4 by blast
  then show "\<ominus> r1 \<oplus> r2 \<in> carrier S"
    using f12 f10 f9 a7 a3 a2 a1 by (metis (no_types) \<open>\<And>a2 a1. \<lbrakk>abelian_group S; a1 \<in> carrier S; a2
        \<in> carrier S\<rbrakk> \<Longrightarrow> \<ominus>\<^bsub>S\<^esub> a1 \<oplus>\<^bsub>S\<^esub> a2 \<in> carrier S\<close> local.ring_axioms ring.ring_simprules(15)
        ring.ring_simprules(16) ring.ring_simprules(17) ring.ring_simprules(3))
qed

lemma subring_nontrivial: "card (carrier R) \<noteq> 1 \<Longrightarrow> subring S \<Longrightarrow> card (carrier S) \<noteq> 1"
  by (metis add.r_cancel_one' card_1_singletonE nonzero_ring_one one_closed ring.ring_simprules(15)
      ring.ring_simprules(2) singleton_iff subring_def)

lemma subring_trivial_iff: "subring S \<Longrightarrow> card (carrier R) = 1 \<longleftrightarrow> card (carrier S) = 1"
  by (metis card_1_singletonE contra_subsetD monoid.one_closed ring.nonzero_ring_one ring_def
      singleton_iff subring_def subring_nontrivial subring_zero zero_closed)

lemma subringI:
  "subgroup A \<lparr>carrier=carrier R,mult=(\<oplus>),one=\<zero>\<rparr> \<Longrightarrow> \<one>\<in>A \<Longrightarrow> \<forall>a\<in>A. \<forall>b\<in>A. a\<otimes>b\<in>A \<Longrightarrow> subring (R\<lparr>carrier:=A\<rparr>)"
  by (simp add: a_inv_def subgroup_def abolishedI)

lemma subring_imp_subgroup:
  "subring S \<Longrightarrow> subgroup (carrier S) \<lparr>carrier = carrier R, mult = (\<oplus>), one = \<zero>\<rparr>"
  unfolding subring_def apply unfold_locales apply auto
  apply (metis ring.ring_simprules(1))
  apply (metis add.transpose_inv local.ring_axioms rev_subsetD ring.ring_simprules(15)
      ring.ring_simprules(2))
  by (smt a_inv_def abelian_group.a_inv_closed add.transpose_inv local.ring_axioms
    ring.ring_simprules(15) ring.ring_simprules(2) ring.ring_simprules(9) ring_def subsetCE)

lemma intermediate_ring_1:
  "subring S \<Longrightarrow> carrier S \<subseteq> M \<Longrightarrow> M \<subseteq> carrier R \<Longrightarrow> ring (R\<lparr>carrier:=M\<rparr>) \<Longrightarrow> subring (R\<lparr>carrier:=M\<rparr>)"
  unfolding subring_def by auto

end

context cring begin \<comment> \<open>\<triangleq> "Let @{term R} be a commutative ring."\<close>

lemma subring_cring: "subring S \<Longrightarrow> cring S" unfolding subring_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

end

context field begin \<comment> \<open>\<triangleq> "Let @{term R} be a field."\<close>

lemma field_has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  using Units_r_inv_ex field_Units by fastforce

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
    using a1 by (metis (no_types) cring.cring_simprules(12) cring.subring_cring field.subfield_def
        is_cring local.field_axioms r_one ring.ring_simprules(6) subsetCE)
qed

lemma normalize_subfield: "subfield S \<Longrightarrow> subfield (R\<lparr>carrier:=carrier S\<rparr>)"
  unfolding subfield_def apply auto
   apply (simp add: normalize_subring)
  apply (rule cring.cring_fieldI2)
    apply auto
  using normalize_subring subring_cring apply auto[1]
  unfolding subring_def apply auto
  by (metis (no_types, lifting) field.field_has_inverse subfield_def subfield_one subring_def subring_zero)

lemma subfieldI: \<comment> \<open>Improvable?\<close>
  assumes "subgroup A \<lparr>carrier=carrier R,mult=(\<oplus>),one=\<zero>\<rparr>"
  and "\<one>\<in>A"
  and "\<forall>a\<in>A. \<forall>b\<in>A. a\<otimes>b\<in>A"
  and "\<forall>a\<in>A. a\<noteq>\<zero> \<longrightarrow> inv a \<in> A"
shows "subfield (R\<lparr>carrier:=A\<rparr>)"
  unfolding subfield_def apply auto
   apply (rule subringI) using assms apply auto[3]
  apply (rule cring.cring_fieldI2[of "R\<lparr>carrier:=A\<rparr>"])
    apply auto
  apply (rule subring_cring)
  using assms(1) assms(2) assms(3) subringI apply blast
  using assms
  by (metis Units_one_closed Units_r_inv field_has_inverse partial_object.select_convs(1)
      subgroup.mem_carrier unit_factor)

end

locale field_extension = field L for L (structure) +
  fixes K :: "'a set" \<comment> \<open>I see no reason why not to inherit \<zero>, \<one> and the operations. @{locale
    subgroup} does the same.\<close>
  assumes L_extends_K: "subfield (L\<lparr>carrier:=K\<rparr>)"
begin \<comment> \<open>\<triangleq> "Let @{term L}/@{term K} be a field extension."\<close>

lemma K_field: "field (L\<lparr>carrier:=K\<rparr>)"
  using L_extends_K by (simp add: subfield_def)

lemma K_subring: "subring (abolished K)"
  using L_extends_K subfield_def by blast

lemma K_subgroup: "subgroup K \<lparr>carrier=carrier L,mult=(\<oplus>),one=\<zero>\<rparr>"
  using subring_imp_subgroup[of "abolished K"] by (simp add: K_subring)

lemma K_inv: "a \<in> K \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> inv a \<in> K"
proof -
  assume a1: "a \<noteq> \<zero>"
assume a2: "a \<in> K"
  obtain aa :: "'a \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> 'a" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> carrier x1 \<and> x0 \<otimes>\<^bsub>x1\<^esub> v2 = \<one>\<^bsub>x1\<^esub>) = (aa x0 x1 \<in> carrier x1 \<and> x0 \<otimes>\<^bsub>x1\<^esub> aa x0 x1 = \<one>\<^bsub>x1\<^esub>)"
    by moura
  then have "aa a (abolished K) \<in> carrier (abolished K) \<and> a \<otimes>\<^bsub>abolished K\<^esub> aa a (abolished K) = \<one>\<^bsub>abolished K\<^esub>"
using a2 a1 by (metis (no_types) K_field L_extends_K field.field_has_inverse subfield_zero abolished_carrier)
  then show ?thesis
    using a2 by (metis (no_types) K_subring L_extends_K comm_inv_char subfield_one subring_def abolished_carrier subsetCE)
qed

end

lemma (in field) f_e_refl : "field_extension R (carrier R)"
  unfolding field_extension_def field_extension_axioms_def apply auto
  using local.field_axioms apply blast
  using normalize_subfield subfield_refl abolished_def by auto

lemma (in field) f_e_iff_subfield: "field_extension R K \<longleftrightarrow> subfield (abolished K)"
  using field_extension.L_extends_K field_extension.intro field_extension_axioms_def
    local.field_axioms by blast

context field_extension
begin

lemma indermediate_field_1: "field (abolished M) \<Longrightarrow> K \<subseteq> M \<Longrightarrow> M \<subseteq> carrier L \<Longrightarrow> field_extension L M"
  apply unfold_locales unfolding subfield_def apply auto unfolding field_def
  using intermediate_ring_1 by (metis K_subring cring_def domain_def abolished_carrier)

proposition "16_3_": "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. field_extension L M \<and> M \<supseteq> K \<Longrightarrow> field_extension L (\<Inter>\<M>)"
  apply (unfold_locales)
  apply (rule subfieldI)
     apply (simp add: add.subgroups_Inter field_extension.K_subgroup)
    apply (metis K_subring cInf_greatest contra_subsetD subring_def abolished_carrier)
  apply auto
  apply (metis field.f_e_iff_subfield field.subfield_def field_extension_def monoid.m_closed
      ring_def subring_def abolished_carrier)
  by (simp add: field_extension.K_inv)
(*
thm group.subgroups_Inter "subgroup.\<Inter>_is_supergroup" field_extension_axioms
proposition "16_3_actual":
  "\<M>\<noteq>{} \<Longrightarrow> \<forall>M\<in>\<M>. field_extension L M \<and> M \<supseteq> K \<Longrightarrow> field_extension (abolished (\<Inter>\<M>)) K"
proof goal_cases
  case 1
  then have "\<forall>M\<in>\<M>. field (abolished M)"
    by (simp add: field_extension.K_field)
  with "1"(2) have "\<forall>M\<in>\<M>. field.subfield (abolished M) (abolished K)"
    sledgehammer
  unfolding field_extension_def field_extension_axioms_def apply auto
   apply (metis "16_3_" empty_iff f_e_iff_subfield field_extension.K_field)
  apply (rule field.subfieldI) apply auto
      apply (metis "16_3_" equals0D f_e_iff_subfield field_extension.K_field)
     apply (rule group.subgroupI) apply auto
apply (metis "16_3_" abelian_group.a_group cring_def domain_def empty_iff f_e_iff_subfield field_def field_extension.K_field ring_def abolished_carrier)
       apply (metis K_subring all_not_in_conv cring_def is_cring ring.subring_def abolished_carrier)
  unfolding subfield_def using field_extension.K_subgroup[of _ K] sledgehammer

  thm hull_def
definition ext_of_gen where
  (* K\<le>M\<le>L, the \<lambda>-term, must be a predicate about the \<^bold>s\<^bold>e\<^bold>t M *)
  "S \<subseteq> carrier L \<Longrightarrow> ext_of_gen S = (\<lambda>M. carrier M) hull S"
*)
lemma "field (abolished K)" "field L" "field.subfield L (abolished K)" oops

end


section\<open>Observations\<close>

text \<open>@{locale subgroup} was the inspiration to just use sets for the substructure. However, that
locale is somewhat odd in that it does not impose @{locale group} on neither \<open>G\<close> nor \<open>H\<close> with the
  operations of \<open>G\<close>\<close>

context subgroup begin
lemma "subgroup H G" by (fact subgroup_axioms)
lemma "group G" oops
lemma "group (G\<lparr>carrier:=H\<rparr>)" oops
end

text \<open>@{const Ideal.genideal} could be defined using @{const hull}...\<close>

term field
\<comment> \<open>field_simps are *not* available in general. Re-prove them? Collect them?\<close>

text\<open>The following is an easy generalisation of @{thm field.finite_mult_of}\<close>
lemma finite_mult_of: "finite (carrier R) \<Longrightarrow> finite (carrier (mult_of R))"
  by (auto simp: mult_of_simps)

(* duplicate: *)
value INTEG
value "\<Z>"
thm INTEG_def

find_theorems field
thm
field_axioms_def
QuotRing.maximalideal.quotient_is_field
Ideal.field.all_ideals
UnivPoly.INTEG.R.trivialideals_eq_field

end
