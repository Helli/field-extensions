theory Scratch imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above *)
begin

lemma easy: "of_int ` (\<int>::int set) \<subseteq> (\<rat>:: rat set)" by auto

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
    (\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier R. add S r1 r2 = add R r1 r2 \<and> mult S r1 r2 = mult R r1 r2)"

lemma "card (carrier R) \<noteq> 1 \<Longrightarrow> subring S \<Longrightarrow> card (carrier S) \<noteq> 1"
  by (metis add.r_cancel_one' card_1_singletonE nonzero_ring_one one_closed ring.ring_simprules(15)
      ring.ring_simprules(2) singleton_iff subring_def)

end

context cring begin \<comment> \<open>\<triangleq> "Let @{term R} be a commutative ring."\<close>

lemma subring_cring: "subring S \<Longrightarrow> cring S" unfolding subring_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

end
thm ring.subring_def

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