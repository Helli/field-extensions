section \<open>Quick Tests\<close>
theory Examples imports Field_Extension
begin

definition standard_ring
  where "standard_ring A = \<lparr>carrier = A, mult = ( *), one = 1, zero = 0, add = (+)\<rparr>"

definition univ_ring ("\<U>")
  where "univ_ring \<equiv> \<lparr>carrier = UNIV, mult = ( *) , one = 1, zero = 0, add = (+)\<rparr>"

lemma \<U>_ring: "Ring.ring (\<U>::_::Rings.ring_1 ring)"
  unfolding univ_ring_def
  apply (intro ringI abelian_groupI monoidI)
  apply (auto simp: ring_distribs mult.assoc)
  using ab_group_add_class.ab_left_minus apply blast
  done

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

lemma field_examples: "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def real_field_def complex_field_def by (fact \<U>_field)+

(*rm*)abbreviation \<K>::"_::field ring" where "\<K> \<equiv> univ_ring"

lemma \<K>_id_eval:
  "UP_pre_univ_prop \<K> \<K> id"
  using UP_pre_univ_propI \<U>_cring id_ring_hom by blast

lemma ring_standard_ring:
  "ring (standard_ring (range rat_of_int))"
  "ring (standard_ring (range real_of_rat))"
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
  by (simp add: ring_class.ring_distribs(1))
(*interpretation r_s_r: ring "standard_ring (range rat_of_int)" by (simp add: ring_standard_ring)*)

lemma subring_example: "ring.subring rat_field (standard_ring (range rat_of_int))"
  unfolding rat_field_def ring.subring_def[OF \<U>_ring]
  apply (auto simp add: univ_ring_def) unfolding standard_ring_def
     apply (metis ring_standard_ring(1) standard_ring_def)
  by auto

lemma f_r: (*rm*) "field K \<Longrightarrow> ring K"
  by (simp add: cring.axioms(1) domain.axioms(1) field.axioms(1))

lemma f_r_o_r: \<open>field (standard_ring (range real_of_rat))\<close>
  apply standard
                   apply (auto simp: standard_ring_def)
  using Rats_add Rats_def apply blast
  unfolding Units_def apply auto
      apply (smt of_rat_minus)
  using Rats_def apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis mult.commute nonzero_mult_div_cancel_left of_rat_eq_1_iff of_rat_mult times_divide_eq_right)

lemma subfield_example: \<open>field.subfield real_field (standard_ring (range real_of_rat))\<close>
  unfolding field.subfield_def[OF field_examples(2)]
  apply (auto simp: real_field_def ring.subring_def[OF \<U>_ring])
       apply (simp_all add: univ_ring_def ring_standard_ring(2) standard_ring_def)
   apply (metis ring_standard_ring(2) standard_ring_def)
  by (metis f_r_o_r standard_ring_def)

end
