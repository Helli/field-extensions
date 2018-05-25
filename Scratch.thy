theory Scratch imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.More_Ring"            (* This imports Rings. *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above *)
begin

section\<open>Quick test\<close>

abbreviation standard_ring :: "_::{one,times,plus,zero} ring" ("\<S>")
  where "standard_ring \<equiv> \<lparr>carrier = UNIV, mult = op *, one = 1, zero = 0, add = op +\<rparr>"

lemma \<S>_cring: "Ring.cring (\<S>::_::Fields.field ring)"
  by (auto intro!: cringI abelian_groupI comm_monoidI
    left_minus distrib_right)

lemma \<S>_field: "Ring.field (\<S>::_::Fields.field ring)"
  apply (rule cring.cring_fieldI2)
    apply (fact \<S>_cring) apply auto using dvd_field_iff
  by (metis dvdE)

definition rat_field::"rat Ring.ring" ("\<rat>") where "\<rat> = \<S>"
definition real_field::"real ring" ("\<real>") where "\<real> = \<S>"
definition complex_field::"complex ring" ("\<complex>") where "\<complex> = \<S>"

lemma "field \<rat>" unfolding rat_field_def by (fact \<S>_field)
lemma "field \<real>" unfolding real_field_def by (fact \<S>_field)
lemma "field \<complex>" unfolding complex_field_def by (fact \<S>_field)

abbreviation \<K>::"_::field ring" where "\<K> \<equiv> \<S>"

lemma \<K>_id_eval:
  "UP_pre_univ_prop \<K> \<K> id"
  by (simp add: UP_pre_univ_propI \<S>_cring rat_field_def)

section\<open>Observations\<close>

term field
--\<open>field_simps are *not* available in general. Re-prove them? Collect them?\<close>

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