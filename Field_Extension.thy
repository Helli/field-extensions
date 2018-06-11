theory Field_Extension imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above. rm? *)
begin


section \<open>missing preliminaries?\<close>

lemma (in comm_group) subgroup_group:
  "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. a1\<otimes>a2\<in>A \<and> m_inv G a1\<in>A\<rbrakk> \<Longrightarrow> comm_group \<lparr>carrier = A, mult=(\<otimes>), one=\<one>\<rparr>"
  apply standard                                     
        apply auto
    apply (simp add: m_assoc subset_iff)
   apply (meson m_comm subsetCE)
  unfolding Units_def
proof -
fix x :: 'a
assume a1: "x \<in> A"
  assume a2: "A \<subseteq> carrier G"
  assume "\<one> \<in> A"
  assume a3: "\<forall>a1\<in>A. \<forall>a2\<in>A. a1 \<otimes> a2 \<in> A \<and> inv a1 \<in> A"
  have "x \<in> carrier G"
    using a2 a1 by blast
then show "x \<in> {a \<in> carrier \<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>. \<exists>aa\<in>carrier \<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>. aa \<otimes>\<^bsub>\<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>\<^esub> a = \<one>\<^bsub>\<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>\<^esub> \<and> a \<otimes>\<^bsub>\<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>\<^esub> aa = \<one>\<^bsub>\<lparr>carrier = A, mult = (\<otimes>), one = \<one>\<rparr>\<^esub>}"
  using a3 a1 by force
qed

lemma (in comm_group) subgroup_group': "\<lbrakk>A \<subseteq> carrier G; \<one>\<in>A; \<forall>a1\<in>A.\<forall>a2\<in>A. inv a1 \<otimes> a2 \<in> A\<rbrakk>
  \<Longrightarrow> comm_group \<lparr>carrier = A, mult=(\<otimes>), one=\<one>\<rparr>"
  by (metis (no_types, hide_lams) contra_subsetD inv_inv r_one subgroup_def subgroup_group subgroup_self)

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

lemma subring_refl: "subring R"
  unfolding subring_def using local.ring_axioms by blast

definition subring_of :: "'a set \<Rightarrow> 'a ring" where
  "subring_of A = \<lparr>carrier = A, mult = (\<otimes>), one = \<one>, zero = \<zero>, add = (\<oplus>)\<rparr>"

lemma subring_ofI: "\<lbrakk>A \<subseteq> carrier R; \<one>\<in>A; \<forall>r1\<in>A.\<forall>r2\<in>A. r1\<otimes>r2\<in>A \<and> (\<ominus>r1)\<oplus>r2\<in>A\<rbrakk>
  \<Longrightarrow> subring (subring_of A)"
  unfolding subring_def subring_of_def apply auto
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

lemma normalize_subring: "subring S \<Longrightarrow> subring (subring_of (carrier S))"
  apply (rule subring_ofI)
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

lemma normalize_subfield: "subfield S \<Longrightarrow> subfield (subring_of (carrier S))"
  unfolding subfield_def apply auto
   apply (simp add: normalize_subring)
  unfolding subring_of_def
  apply (rule cring.cring_fieldI2)
    apply auto
  using normalize_subring subring_cring subring_of_def apply auto[1]
  unfolding subring_def apply auto
proof goal_cases
  case (1 a)
  interpret sdf: field S
    by (simp add: "1"(1))
  have "a \<noteq> zero S" using sdf.subring_zero
    by (simp add: "1"(3) "1"(4) "1"(6) "1"(7) sdf.ring_axioms subring_def subring_zero)
  with sdf.field_has_inverse have "\<exists>b\<in>carrier S. mult S a b = one S"
    using "1"(2) by blast
  then show ?case
    by (metis "1"(2) "1"(4) "1"(6) "1"(7) r_one ring.ring_simprules(12) sdf.one_closed sdf.ring_axioms subsetD)
qed

end

locale field_extension = field L for L (structure) +
  fixes K :: "'a set"
  assumes L_extends_K: "subfield (subring_of K)"
begin \<comment> \<open>\<triangleq> "Let @{term L}/@{term K} be a field extension."\<close>

lemma K_field: "field (subring_of K)"
  using L_extends_K by (simp add: subfield_def)

end

lemma (in field) f_e_refl : "field_extension R (carrier R)"
  unfolding field_extension_def field_extension_axioms_def apply auto
  using local.field_axioms apply blast
  using normalize_subfield subfield_refl subring_of_def by auto

lemma (in field) f_e_iff_subfield: "field_extension R K \<longleftrightarrow> subfield K"
  by (simp add: field_extension_axioms_def field_extension_def local.field_axioms)

context field_extension
begin

thm hull_def
definition ext_of_gen where
  (* K\<le>M\<le>L, the \<lambda>-term, must be a predicate about the \<^bold>s\<^bold>e\<^bold>t M *)
  "S \<subseteq> carrier L \<Longrightarrow> ext_of_gen S = (\<lambda>M. carrier M) hull S"

lemma "field K" oops
lemma "field L" oops
lemma "field.subfield L K" oops

end


section\<open>Observations\<close>

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
