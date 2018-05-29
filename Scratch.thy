theory Scratch imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above *)
begin

lemma easy: "of_int ` (\<int>::int set) \<subseteq> (\<rat>:: rat set)" by auto

section \<open>Subrings\<close>

lemma ring_card: "ring R \<Longrightarrow> card (carrier R) \<ge> 1 \<or> infinite (carrier R)"
  using not_less_eq_eq ring.ring_simprules(6) by fastforce

lemma nonzero_ring_one: "ring R \<Longrightarrow> card (carrier R) \<noteq> 1 \<Longrightarrow> one R \<noteq> zero R"
  using is_singleton_altdef is_singleton_def ring.one_genideal ring.zero_genideal by fastforce

definition subring where
  "subring R1 R2 \<longleftrightarrow> ring R1 \<and> ring R2
    \<and> carrier R1 \<subseteq> carrier R2
    \<and> mult R1 = mult R2 \<comment> \<open>Do we need to relax this...\<close>
    \<and> add R1 = add R2 \<comment> \<open>...and this?\<close>
    \<and> one R1 = one R2
    \<and> zero R1 = zero R2"

lemma subring_altdef: "subring R1 R2 \<longleftrightarrow> ring R1 \<and> ring R2
  \<and> carrier R1 \<subseteq> carrier R2
  \<and> mult R1 = mult R2
  \<and> add R1 = add R2
  \<and> one R2 \<in> carrier R1"
  by (smt monoid.l_one monoid.r_one ring.is_monoid ring.ring_simprules(15) ring.ring_simprules(18)
      ring.ring_simprules(2) ring.ring_simprules(6) subring_def subset_iff)

lemma "subring R1 R2 \<Longrightarrow> \<one> \<in> R1"
(*todo introrule*)
lemma "subring R1 R2 \<Longrightarrow> ring r2 \<Longrightarrow> ring R1"
lemma "subring R1 R2 \<Longrightarrow> cring R1 \<Longrightarrow> cring R2"


section \<open>quick test\<close>

definition univ_ring ("\<U>")
  where "univ_ring \<equiv> \<lparr>carrier = UNIV, mult = ( *) , one = 1, zero = 0, add = (+)\<rparr>"

lemma \<U>_cring: "Ring.cring (\<U>::_::Fields.field ring)"
  by (auto intro!: cringI abelian_groupI comm_monoidI
    left_minus distrib_right simp: univ_ring_def)

lemma \<U>_field: "Ring.field (\<U>::_::Fields.field ring)"
  apply (rule cring.cring_fieldI2)
    apply (fact \<U>_cring) apply (auto simp: univ_ring_def) using dvd_field_iff
  by (metis dvdE)

definition rat_field::"rat ring" where "rat_field = \<U>"
definition real_field::"real ring" where "real_field = \<U>"
definition complex_field::"complex ring" where "complex_field = \<U>"

lemma "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def real_field_def complex_field_def by (fact \<U>_field)+

abbreviation \<K>::"_::field ring" where "\<K> \<equiv> univ_ring"

lemma \<K>_id_eval:
  "UP_pre_univ_prop \<K> \<K> id"
  using UP_pre_univ_propI \<U>_cring id_ring_hom by blast

definition standard_ring
  where "standard_ring A = \<lparr>carrier = A, mult = ( *), one = 1, zero = 0, add = (+)\<rparr>"

lemma
  assumes "ring (\<U>::'a::{one,times,plus,zero} ring)"
  assumes one_in_S: "1 \<in> S"
  assumes zero_in_S: "0 \<in> S"
  assumes closed_mult: "\<forall>a\<in>S. \<forall>b\<in>S. a*b \<in> S"
  assumes closed_plus: "\<forall>a\<in>S. \<forall>b\<in>S. a+b \<in> S"
  shows "ring (standard_ring (S::'a set))"
  oops

lemma
  assumes "cring (\<U>::'a::{one,times,plus,zero} ring)"
  (*todo*)
  shows "cring (standard_ring (S::'a set))"
  oops

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