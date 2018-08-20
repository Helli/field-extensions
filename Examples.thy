subsection \<open>Example instantiations\<close>
theory Examples imports Field_Extension
begin

definition standard_ring
  where "standard_ring A = \<lparr>carrier = A, monoid.mult = ( *), one = 1, zero = 0, add = (+)\<rparr>"

definition univ_ring
  where "univ_ring = \<lparr>carrier = UNIV, monoid.mult = ( *) , one = 1, zero = 0, add = (+)\<rparr>"

lemma ring_univ_ring: "Ring.ring (univ_ring::_::Rings.ring_1 ring)"
  unfolding univ_ring_def
  apply (intro ringI abelian_groupI monoidI)
  apply (auto simp: ring_distribs mult.assoc)
  using ab_group_add_class.ab_left_minus apply blast
  done

lemma field_univ_ring: "Ring.field (univ_ring::_::Fields.field ring)"
  apply unfold_locales apply (auto intro: right_inverse simp: univ_ring_def Units_def field_simps)
  by (metis ab_group_add_class.ab_left_minus add.commute)

definition rat_field :: "rat ring" where "rat_field = univ_ring"
definition real_field :: "real ring" where "real_field = univ_ring"
definition complex_field :: "complex ring" where "complex_field = univ_ring"

lemma field_examples: "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def real_field_def complex_field_def by (fact field_univ_ring)+

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

text \<open>\<open>\<int>\<close> is a subring of \<open>\<rat>\<close>:\<close>

lemma old_sr_example: "ring.old_sr rat_field (standard_ring (range rat_of_int))"
  unfolding rat_field_def ring.old_sr_def[OF ring_univ_ring]
  apply (auto simp add: univ_ring_def) unfolding standard_ring_def
     apply (metis ring_standard_ring(1) standard_ring_def)
  by auto

text \<open>\<open>\<real>\<close> is a field extension of \<open>\<rat>\<close>:\<close>

lemma f_r_o_r: \<open>field (standard_ring (range real_of_rat))\<close>
  apply standard
                   apply (auto simp: standard_ring_def)
  using Rats_add Rats_def apply blast
  unfolding Units_def apply auto
      apply (smt of_rat_minus)
  using Rats_def apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis mult.commute nonzero_mult_div_cancel_left of_rat_eq_1_iff of_rat_mult
      times_divide_eq_right)

lemma inv_standard_ring:
  fixes x::"_::ring"
  shows "inv\<^bsub>\<lparr>carrier = UNIV, monoid.mult = (+), one = 0\<rparr>\<^esub> x = - x"
  unfolding m_inv_def apply auto
  using add.inverse_unique add_eq_0_iff eq_neg_iff_add_eq_0 by fastforce

lemma subfield_example: \<open>subfield (range real_of_rat) real_field\<close>
  apply unfold_locales apply (auto simp: real_field_def univ_ring_def)
  using Rats_add Rats_def apply blast
  apply (metis Rats_def Rats_minus_iff Rats_of_rat inv_standard_ring)
  using Rats_def apply auto[1] using Rats_def
  apply (metis (mono_tags, hide_lams) monoid.Units_closed partial_object.select_convs(1) ring_def
      ring_standard_ring(2) standard_ring_def)
  apply (simp add: Units_def)+
  by (metis mult.commute nonzero_of_rat_inverse of_rat_eq_0_iff right_inverse)

lemma old_fe_real_over_rat: "old_fe real_field (range real_of_rat)"
  apply (simp add: old_fe_def old_fe_axioms_def field_examples)
proof -
  have f1: "ring \<lparr>carrier = range real_of_rat, monoid.mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"
    by (metis (no_types) ring_standard_ring(2) standard_ring_def)
  have f2: "real_field = \<lparr>carrier = UNIV, monoid.mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"
    using real_field_def univ_ring_def by auto
  have "ring \<lparr>carrier = UNIV, monoid.mult = ( * ), one = 1::real, zero = 0, add = (+)\<rparr>"
    by (metis ring_univ_ring univ_ring_def)
  then have "ring.old_sr \<lparr>carrier = UNIV, monoid.mult = ( * ), one = 1, zero = 0, add = (+)\<rparr> \<lparr>carrier = range real_of_rat, monoid.mult = ( * ), one = 1, zero = 0, add = (+)\<rparr>"
    using f1 by (simp add: ring.old_sr_def)
  then show "field.old_sf real_field (real_field\<lparr>carrier := range real_of_rat\<rparr>)"
    using f2 by (metis f_r_o_r field.old_sf_def field_examples(2) partial_object.update_convs(1) standard_ring_def)
qed

text \<open>\<open>\<complex>\<close> is a finitely generated field extension of \<open>\<real>\<close>:\<close>

lemma f_r_o_r': \<open>field (standard_ring (range complex_of_real))\<close>
  apply standard
                   apply (auto simp: standard_ring_def)
  using Reals_def apply auto[1]
  unfolding Units_def apply auto
      apply (metis add_cancel_left_left add_diff_cancel_right' add_uminus_conv_diff of_real_minus)
  using Reals_def of_real_mult apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis divide_inverse divide_self_if mult.commute of_real_eq_1_iff of_real_mult)

lemma subfield_example': "subfield (range complex_of_real) complex_field"
  unfolding complex_field_def univ_ring_def apply unfold_locales apply auto
  apply (metis of_real_add rangeI)
  apply (simp add: inv_standard_ring)
  apply (metis of_real_mult range_eqI)
  apply (simp add: Units_def)+
  by (metis Groups.mult_ac(2) of_real_eq_0_iff of_real_inverse right_inverse)

lemma generate_field_\<i>_UNIV: "generate_field complex_field (insert \<i> (range complex_of_real)) = UNIV"
proof -
  define P where "P = UP (complex_field\<lparr>carrier := range complex_of_real\<rparr>)"
  define Eval where "Eval = eval (complex_field\<lparr>carrier := range complex_of_real\<rparr>) complex_field id \<i>"
  interpret field_extension_with_UP P \<i> Eval complex_field "range of_real"
    unfolding field_extension_with_UP_def apply auto
    unfolding UP_univ_prop_def UP_univ_prop_axioms_def apply auto
    unfolding UP_pre_univ_prop_def apply auto
    unfolding ring_hom_cring_def apply auto
    apply (metis (full_types) complex_field_def domain_def f_r_o_r' field_def
        partial_object.update_convs(1) standard_ring_def univ_ring_def)
    using fieldE(1) field_examples(3) apply blast
    unfolding ring_hom_cring_axioms_def
      apply (simp add: complex_field_def ring_hom_memI univ_ring_def)
    unfolding UP_cring_def
    apply (metis (full_types) complex_field_def domain_def f_r_o_r' field_def
        partial_object.update_convs(1) standard_ring_def univ_ring_def)
    apply (simp add: complex_field_def univ_ring_def) unfolding P_def Eval_def
    by (simp_all add: field_examples(3) field_extension_def subfield_example')
  show ?thesis unfolding genfield_singleton_explicit apply auto
  proof goal_cases
    case (1 x)
    have [simp]: "inv\<^bsub>complex_field\<^esub> 1 = 1"
      unfolding complex_field_def univ_ring_def m_inv_def by simp
    have "x = Eval (UnivPoly.monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)"
      unfolding complex_field_def univ_ring_def apply (simp del: One_nat_def)
      unfolding complex_field_def univ_ring_def by (auto simp: add.commute complex_eq
          mult.commute)
    show ?case
      apply (rule exI[of _ "UnivPoly.monom P (Im x) 1 \<oplus>\<^bsub>P\<^esub> UnivPoly.monom P (Re x) 0"])
      apply (rule exI[of _ "UnivPoly.monom P 1 0"])
      apply auto
      unfolding complex_field_def univ_ring_def apply auto apply (fold One_nat_def) using
        \<open>x = Eval (UnivPoly.monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)\<close>
        complex_field_def ring.simps(2) univ_ring_def
      by metis
  qed
qed

corollary finitely_generated_field_extension_complex_over_real:
  "finitely_generated_field_extension complex_field (range complex_of_real)"
  unfolding finitely_generated_field_extension_def finitely_generated_field_extension_axioms_def
  by (simp add: field_examples(3) field_extension_def subfield_example')
    (metis Un_commute Un_insert_left complex_field_def finite.emptyI finite.insertI
      generate_field_\<i>_UNIV partial_object.select_convs(1) sup_bot.right_neutral univ_ring_def)

find_theorems mod_hom bij
find_theorems linear_map bij
term a_kernel
term kernel
term "linear_map.kerT"
find_theorems direct_sum vectorspace.dim

term bij_betw

lemma (in linear_map) mod_iso_preserves_dim:
  assumes "bij_betw T (carrier V) (carrier W)" \<comment> \<open>A module-isomorphism\<close>
  assumes V.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.dim = W.dim"
  using assms by (simp add: bij_betw_def dim_eq) \<comment> \<open>uses \<^theory>\<open>Draft.Missing_VectorSpace\<close>\<close>

end
