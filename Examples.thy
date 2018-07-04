section \<open>Example instantiations\<close>
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

definition rat_field :: "rat ring" where "rat_field = \<U>"
definition real_field :: "real ring" where "real_field = \<U>"
definition complex_field :: "complex ring" where "complex_field = \<U>"

lemma field_examples: "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def real_field_def complex_field_def by (fact \<U>_field)+

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
(*interpretation r_s_r: ring "standard_ring (range rat_of_int)" by (simp add: ring_standard_ring)*)

subsection \<open>\<int> is a subring of \<rat>\<close>

lemma subring_example: "ring.subring rat_field (standard_ring (range rat_of_int))"
  unfolding rat_field_def ring.subring_def[OF \<U>_ring]
  apply (auto simp add: univ_ring_def) unfolding standard_ring_def
     apply (metis ring_standard_ring(1) standard_ring_def)
  by auto

subsection \<open>\<real> is a field extension of \<rat>\<close>

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

lemma field_extension_real_over_rat: "field_extension real_field (range real_of_rat)"
  apply (simp add: field_extension_def field_extension_axioms_def)
  using subfield_example field.normalize_subfield standard_ring_def
  by (metis field_examples(2) partial_object.select_convs(1))

subsection\<open>\<complex> is a finitely generated field extension of \<real>\<close>

lemma f_r_o_r': \<open>field (standard_ring (range complex_of_real))\<close>
  apply standard
                   apply (auto simp: standard_ring_def)
  using Reals_def apply auto[1]
  unfolding Units_def apply auto
      apply (metis add_cancel_left_left add_diff_cancel_right' add_uminus_conv_diff of_real_minus)
  using Reals_def of_real_mult apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis divide_inverse divide_self_if mult.commute of_real_eq_1_iff of_real_mult)

lemma subfield_example': \<open>field.subfield complex_field (standard_ring (range complex_of_real))\<close>
  unfolding field.subfield_def[OF field_examples(3)]
  apply (auto simp: complex_field_def ring.subring_def[OF \<U>_ring])
       apply (simp_all add: univ_ring_def ring_standard_ring(2) standard_ring_def)
   apply (metis ring_standard_ring(3) standard_ring_def)
  by (metis f_r_o_r' standard_ring_def)

lemma f_e_example': "field_extension complex_field (range complex_of_real)"
  apply (simp add: field_extension_def field_extension_axioms_def)
  using subfield_example' field.normalize_subfield standard_ring_def
  by (metis field_examples(3) partial_object.select_convs(1))

lemma genfield_\<i>_UNIV: "field_extension.genfield complex_field (range complex_of_real) {\<i>} = UNIV"
proof -
  define P where "P = UP (complex_field\<lparr>carrier := range complex_of_real\<rparr>)"
  define Eval where "Eval = eval (complex_field\<lparr>carrier := range complex_of_real\<rparr>) complex_field id \<i>"
  interpret field_extension_with_UP P \<i> Eval complex_field "range of_real"
    unfolding field_extension_with_UP_def apply (auto simp: f_e_example')
    unfolding UP_univ_prop_def UP_univ_prop_axioms_def apply auto
    unfolding UP_pre_univ_prop_def apply auto
    unfolding ring_hom_cring_def apply auto
    apply (metis \<U>_cring \<U>_field complex_field_def cring.subring_cring field.subfield_def
        partial_object.update_convs(1) standard_ring_def subfield_example' univ_ring_def)
       apply (simp add: \<U>_cring complex_field_def)
    unfolding ring_hom_cring_axioms_def
      apply (simp add: complex_field_def ring_hom_memI univ_ring_def)
    unfolding UP_cring_def
    apply (metis \<U>_cring \<U>_field complex_field_def cring.subring_cring field.subfield_def
        partial_object.update_convs(1) standard_ring_def subfield_example' univ_ring_def)
    apply (simp add: complex_field_def univ_ring_def) unfolding P_def Eval_def by simp+
  show ?thesis unfolding genfield_singleton_explicit apply auto
  proof goal_cases
    case (1 x)
    have [simp]: "inv\<^bsub>complex_field\<^esub> 1 = 1"
      unfolding complex_field_def univ_ring_def m_inv_def by simp
    have "x = (Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x))"
      unfolding complex_field_def univ_ring_def apply (simp del: One_nat_def)
      unfolding complex_field_def univ_ring_def by (auto simp: add.commute complex_eq
          mult.commute)
    show ?case
      apply (rule exI[of _ "monom P (Im x) 1 \<oplus>\<^bsub>P\<^esub> monom P (Re x) 0"])
      apply (rule exI[of _ "monom P 1 0"])
      apply auto
      unfolding complex_field_def univ_ring_def apply auto apply (fold One_nat_def) using
       \<open>x = Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re
          x)\<close> complex_field_def ring.simps(2) univ_ring_def
      by metis
  qed
qed

corollary finitely_generated_field_extension_complex_over_real:
  \<open>finitely_generated_field_extension complex_field (range complex_of_real)\<close>
  unfolding finitely_generated_field_extension_def finitely_generated_field_extension_axioms_def
  apply (auto simp add: f_e_example') using genfield_\<i>_UNIV
  by (metis complex_field_def finite.emptyI finite.insertI partial_object.select_convs(1)
      univ_ring_def)

end
