theory Scratch imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.More_Ring"            (* This imports Rings. *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above *)
begin

section\<open>Quick test\<close>

definition univ_ring ("\<U>")
  where "univ_ring \<equiv> \<lparr>carrier = UNIV, mult = ( *) , one = 1, zero = 0, add = (+)\<rparr>"

lemma \<U>_cring: "Ring.cring (\<U>::_::Fields.field ring)"
  by (auto intro!: cringI abelian_groupI comm_monoidI
    left_minus distrib_right simp: univ_ring_def)

lemma \<U>_field: "Ring.field (\<U>::_::Fields.field ring)"
  apply (rule cring.cring_fieldI2)
    apply (fact \<U>_cring) apply (auto simp: univ_ring_def) using dvd_field_iff
  by (metis dvdE)

definition rat_field::"rat ring" ("\<rat>") where "\<rat> = \<U>"
definition real_field::"real ring" ("\<real>") where "\<real> = \<U>"
definition complex_field::"complex ring" ("\<complex>") where "\<complex> = \<U>"

lemma "field \<rat>" unfolding rat_field_def by (fact \<U>_field)
lemma "field \<real>" unfolding real_field_def by (fact \<U>_field)
lemma "field \<complex>" unfolding complex_field_def by (fact \<U>_field)

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