(* Author: Fabian Hellauer, 2018 *)
subsection \<open>Example instantiations\<close>
theory Examples imports Field_Extension
begin

definition standard_ring (* to-do: replace by abbreviation, it is never used on its own *)
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
definition real_field where "real_field = standard_ring \<real>"
definition complex_field :: "complex ring" where "complex_field = univ_ring"

lemma field_examples: "field rat_field" "field real_field" "field complex_field"
  unfolding rat_field_def standard_ring_def real_field_def complex_field_def
    apply unfold_locales[2]
                      apply (auto intro: right_inverse simp: Units_def algebra_simps)
  using Rats_minus_iff add.right_inverse apply blast
  using add.right_inverse apply fastforce
  apply (smt Reals_cases Reals_of_real mult_scaleR_right of_real_def of_real_diff of_real_mult
      scaleR_conv_of_real semiring_normalization_rules(12))
  apply (smt Reals_cases Reals_minus_iff div_0 nonzero_mult_div_cancel_left of_real_def
      of_real_eq_0_iff of_real_mult)
  apply (metis (no_types, hide_lams) Reals_cases Reals_of_real divide_inverse_commute divide_self_if
      mult.right_neutral mult_scaleR_right of_real_0 of_real_1 of_real_mult scaleR_conv_of_real)
  by (fact field_univ_ring)

lemma cring_example: "cring (standard_ring \<int>)"
  unfolding rat_field_def standard_ring_def
  apply standard
               apply auto unfolding Units_def apply auto
  using Ints_minus add.left_inverse add.right_inverse apply blast
  using mult.assoc apply blast
  using distrib_right apply blast
  using ring_class.ring_distribs(1) apply blast
  apply (metis Ints_cases mult_of_int_commute)
  done

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
    using cring_example unfolding standard_ring_def cring_def by auto
qed

text \<open>\<open>\<real>\<close> is a field extension of \<open>\<rat>\<close>:\<close>
(* rename section? to-do *)

lemma of_real_of_rat_eq[simp]: "of_real (of_rat q) = of_rat q"
proof (cases q)
  case (Fract a b)
  obtain rr :: "real \<Rightarrow> rat" where
    f3: "\<forall>r. r \<notin> \<rat> \<or> r = real_of_rat (rr r)"
    by (metis (no_types) Rats_cases)
  have f4: "\<forall>i. (of_rat (rat_of_int i)::'a) = of_real (real_of_int i)"
    by simp
  have f5: "rat_of_int 1 = 1"
      by blast
  have f6: "\<forall>i. rat_of_int i = rr (real_of_int i)"
    using f3 by (metis of_rat_of_int_eq Rats_of_rat of_rat_eq_iff)
  then have f7: "inverse (rr (real_of_int b)) * rr (real_of_int a) = q"
    by (simp add: Fract(1) Fract_of_int_quotient inverse_eq_divide)
  have f8: "\<forall>r. real_of_rat (inverse r) = inverse (real_of_rat r)"
    by (metis (no_types) divide_inverse mult.left_neutral of_rat_1 of_rat_divide)
  have f9: "\<forall>r. of_real r * of_real (inverse r) = (1::'a) \<or> r = 0"
    using f5 f4 by (metis of_rat_of_int_eq Real_Vector_Spaces.of_real_mult of_rat_1 right_inverse)
  have f10: "of_real (inverse (real_of_int b)) * (of_real (real_of_int a)::'a) = of_real (real_of_rat q)"
    using f8 f7 f3 by (metis of_rat_of_int_eq Rats_of_rat Real_Vector_Spaces.of_real_mult of_rat_eq_iff of_rat_mult)
  have "inverse (of_real (real_of_int b)) * of_real (real_of_int a) = (of_rat q::'a)"
    using f7 f6 f4 by (metis (no_types) divide_inverse mult.left_neutral of_rat_1 of_rat_divide of_rat_mult)
  then show ?thesis
    using f10 f9 Fract(2) by (metis (no_types) divide_inverse mult.right_neutral mult_zero_left nonzero_mult_div_cancel_left of_int_0_eq_iff one_neq_zero order_less_irrefl)
qed

lemma Reals_of_rat[simp]: "of_rat z \<in> \<real>"
  by (subst of_real_of_rat_eq [symmetric]) (rule Reals_of_real)

lemma Rats_subset_Reals: "\<rat> \<subseteq> \<real>"
  using Rats_cases by force

lemma subfield_example: "subfield \<rat> real_field" (* to-do: inline *)
  apply (rule ring.subfield_iff(1))
  apply (simp add: cring.axioms(1) fieldE(1) field_examples(2))
proof -
  have "rat_field = \<lparr>carrier = \<rat>::'a set, monoid.mult = (*), one = 1::'a, zero = 0::'a, add = (+)\<rparr>"
    by (simp add: rat_field_def standard_ring_def)
  then show "field (real_field\<lparr>carrier := \<rat>::'a set\<rparr>)"
    by (simp add: field_examples(1) real_field_def standard_ring_def)
qed (simp add: Rats_subset_Reals real_field_def standard_ring_def)

text \<open>\<open>\<complex>\<close> is a finitely generated field extension of \<open>\<real>\<close>:\<close>

lemma subfield_example': "subfield \<real> complex_field" (* to-do: rename *)
  apply (rule ring.subfield_iff(1))
    apply (simp add: complex_field_def ring_univ_ring)
  unfolding complex_field_def univ_ring_def by (auto simp: field_examples(2)[unfolded real_field_def standard_ring_def])

lemma generate_field_\<i>_UNIV: "generate_field complex_field (insert \<i> \<real>) = UNIV"
proof -
  define P where "P = UP (complex_field\<lparr>carrier := \<real>\<rparr>)"
  interpret UP_field_extension complex_field \<real> P \<i>
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
      by (metis Reals_of_real Eval_cx complex_field_def monoid.simps(1) univ_ring_def)
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
  "finitely_generated_field_extension complex_field \<real>"
  unfolding finitely_generated_field_extension_def using generate_field_\<i>_UNIV
  by (metis complex_field_def field_examples(3) field_extension_def finite.emptyI finite.insertI
      insert_is_Un partial_object.select_convs(1) subfield_example' univ_ring_def)


end
