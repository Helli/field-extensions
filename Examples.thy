(* Author: Fabian Hellauer, 2018 *)
subsection \<open>Example instantiations\<close>
theory Examples imports Field_Extension
begin

definition standard_ring (* replace by abbreviation, it is never used on its own *)
  where "standard_ring carr = \<lparr>carrier = carr, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

definition univ_ring
  where "univ_ring = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

lemma ring_univ_ring: "Ring.ring (univ_ring::_::Rings.ring_1 ring)"
  unfolding univ_ring_def
  apply (intro ringI abelian_groupI monoidI)
  apply (auto simp: ring_distribs mult.assoc)
  using ab_group_add_class.ab_left_minus apply blast
  done

lemma field_univ_ring: "Ring.field (univ_ring::_::Fields.field ring)"
  apply unfold_locales apply (auto intro: right_inverse simp: univ_ring_def Units_def field_simps)
  by (metis ab_group_add_class.ab_left_minus add.commute)

definition rat_field where "rat_field = standard_ring \<rat>"
definition real_field :: "real ring" where "real_field = univ_ring"
definition complex_field :: "complex ring" where "complex_field = univ_ring"

lemma field_examples: "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def standard_ring_def real_field_def complex_field_def
  apply unfold_locales[] apply (auto simp: Units_def)
  using ab_group_add_class.ab_left_minus apply fastforce
  apply (simp add: distrib_right)
  apply (simp add: semiring_normalization_rules(34))
  using Rats_inverse apply force by (fact field_univ_ring)+

lemma cring_Ints: "cring (standard_ring \<int>)"
  "cring (standard_ring (range complex_of_real))" (*rm*)
  unfolding rat_field_def standard_ring_def
  apply standard
               apply auto unfolding Units_def apply auto
  using Ints_minus add.left_inverse add.right_inverse apply blast
  using mult.assoc apply blast
  using distrib_right apply blast
  using ring_class.ring_distribs(1) apply blast
  apply (metis Ints_cases mult_of_int_commute)
  using ring_class.ring_distribs apply auto
     apply (simp_all add: ring_class.ring_distribs)
    apply (metis of_real_add rangeI)
   apply (smt ab_group_add_class.ab_left_minus of_real_minus)
  by (metis of_real_mult rangeI)

text \<open>\<open>\<int>\<close> is a subdomain of \<open>\<rat>\<close>:\<close>

lemma subdomain_example: "subdomain \<int> rat_field"
proof -
  interpret field rat_field by (fact field_examples(1))
  show ?thesis
    apply (rule subdomainI)
    apply (rule subcringI')
    apply (rule ring.ring_incl_imp_subring)
      apply (simp add: ring_axioms)
    unfolding rat_field_def apply (simp add: Ints_subset_Rats standard_ring_def)
    using cring_Ints unfolding standard_ring_def cring_def by auto
qed

text \<open>\<open>\<real>\<close> is a field extension of \<open>\<rat>\<close>:\<close>

lemma subfield_example: \<open>subfield \<rat> real_field\<close>
  apply (rule ring.subfield_iff(1))
  apply (simp add: real_field_def ring_univ_ring)
  apply (metis field_examples(1) partial_object.update_convs(1) rat_field_def real_field_def
      standard_ring_def univ_ring_def)
  by (simp add: real_field_def univ_ring_def)

text \<open>\<open>\<complex>\<close> is a finitely generated field extension of \<open>\<real>\<close>:\<close>

lemma f_r_o_r': "field (standard_ring (range complex_of_real))"
  apply standard
                   apply (auto simp: standard_ring_def)
  using Reals_def apply auto[1]
  unfolding Units_def apply auto
      apply (metis add_cancel_left_left add_diff_cancel_right' add_uminus_conv_diff of_real_minus)
  using Reals_def of_real_mult apply auto[1]
  apply (simp_all add: ring_class.ring_distribs)
  by (metis divide_inverse divide_self_if mult.commute of_real_eq_1_iff of_real_mult)

lemma subfield_example': "subfield (range complex_of_real) complex_field"
  apply (rule ring.subfield_iff(1))
  apply (simp add: complex_field_def ring_univ_ring)
  apply (metis (full_types) complex_field_def f_r_o_r' partial_object.update_convs(1) standard_ring_def
      univ_ring_def)
  by (simp add: complex_field_def univ_ring_def)

lemma generate_field_\<i>_UNIV: "generate_field complex_field (insert \<i> (range complex_of_real)) = UNIV"
proof -
  define P where "P = UP (complex_field\<lparr>carrier := range complex_of_real\<rparr>)"
  interpret UP_field_extension complex_field \<open>range of_real\<close> P \<i>
    unfolding UP_field_extension_def UP_field_extension_axioms_def
       apply (simp add: field_examples(3) field_extension_def subfield_example')
      apply (simp_all add: complex_field_def univ_ring_def P_def)
    done
  show ?thesis unfolding genfield_singleton_explicit apply auto
  proof goal_cases
    case (1 x)
    have [simp]: "inv\<^bsub>complex_field\<^esub> 1 = 1"
      unfolding complex_field_def univ_ring_def m_inv_def by simp
    have "x = Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)"
      unfolding complex_field_def univ_ring_def apply (simp del: One_nat_def)
      unfolding complex_field_def univ_ring_def using add.commute complex_eq mult.commute
      by (metis Reals_def Reals_of_real Eval_cx complex_field_def monoid.simps(1) univ_ring_def)
    show ?case
      apply (rule exI[of _ "monom P (Im x) 1 \<oplus>\<^bsub>P\<^esub> monom P (Re x) 0"])
      apply (rule exI[of _ "monom P 1 0"])
      apply auto
      unfolding complex_field_def univ_ring_def apply auto apply (fold One_nat_def) using
        \<open>x = Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)\<close>
        complex_field_def ring.simps(2) univ_ring_def by metis
  qed
qed

corollary finitely_generated_field_extension_complex_over_real:
  "finitely_generated_field_extension complex_field (range complex_of_real)"
  unfolding finitely_generated_field_extension_def using generate_field_\<i>_UNIV
  by (metis complex_field_def field_examples(3) field_extension_def finite.emptyI finite.insertI
      insert_is_Un partial_object.select_convs(1) subfield_example' univ_ring_def)


end
