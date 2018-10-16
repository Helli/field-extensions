(* Author: Fabian Hellauer, 2018 *)
subsection \<open>Example instantiations\<close>
theory Examples imports Field_Extension
begin

abbreviation standard_ring
  where "standard_ring carr \<equiv> \<lparr>carrier = carr, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

definition "Ints_ring = standard_ring \<int>"
definition "rat_field = standard_ring \<rat>" (* rename to Rats_field etc? *)
definition "real_field = standard_ring \<real>"
txt \<open>There seems to be no \<open>of_complex\<close> available. However, restricting the type is no problem here
  since it is the largest example anyway.\<close>
definition complex_field :: "complex ring"
  where "complex_field = \<lparr>carrier = UNIV, monoid.mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

lemma examples:
  shows cring_Ints_ring: "cring Ints_ring"
    and field_rat_field: "field rat_field"
    and field_real_field: "field real_field"
    and field_complex_field: "field complex_field"
  unfolding Ints_ring_def rat_field_def real_field_def complex_field_def
     apply unfold_locales
                      apply (auto intro: add.right_inverse right_inverse simp: Units_def algebra_simps)
  apply (metis (full_types) Ints_cases mult_of_int_commute)
    apply (metis (full_types) Reals_cases linordered_field_class.sign_simps(24) of_real_mult)
   apply (metis (full_types) Reals_cases mult_eq_0_iff of_real_eq_0_iff of_real_mult)
  by (metis (no_types, hide_lams) Reals_cases Reals_of_real left_inverse mult.left_neutral
      mult.right_neutral mult_scaleR_left mult_scaleR_right of_real_0 of_real_1 of_real_def
      of_real_mult scaleR_conv_of_real)

text \<open>\<open>\<int>\<close> is a subdomain of \<open>\<rat>\<close>:\<close>

lemma subdomain_example: "subdomain \<int> rat_field"
proof -
  interpret field rat_field by (fact examples(2))
  show ?thesis
    apply (rule subdomainI)
    apply (rule subcringI')
    apply (rule ring.ring_incl_imp_subring)
      apply (simp add: ring_axioms)
    unfolding rat_field_def apply (simp add: Ints_subset_Rats)
    using examples(1)[unfolded Ints_ring_def] unfolding cring_def by auto
qed

text \<open>\<open>\<real>\<close> is a field extension of \<open>\<rat>\<close>:\<close>

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

lemma "field_extension real_field \<rat>"
proof (auto simp add: field_extension_def)
  show "subfield \<rat> real_field"
    apply (rule ring.subfield_iff(1))
      apply (simp add: cring.axioms(1) examples(3) fieldE(1))
     apply (metis examples(2) partial_object.update_convs(1) rat_field_def real_field_def)
    by (simp add: Rats_subset_Reals real_field_def)
qed (fact examples(3))

text \<open>\<open>\<complex>\<close> is a finitely generated field extension of \<open>\<real>\<close>:\<close>

lemma subfield_Rats_complex_field: "subfield \<real> complex_field"
  apply (rule ring.subfield_iff(1))
  apply (simp add: cring.axioms(1) examples(4) fieldE(1))
  unfolding complex_field_def by (auto simp: examples(3)[unfolded real_field_def])

lemma generate_field_\<i>_UNIV: "generate_field complex_field (insert \<i> \<real>) = UNIV"
proof -
  define P where "P = UP (standard_ring \<real> :: complex ring)"
  interpret UP_field_extension complex_field \<real> P \<i>
    unfolding UP_field_extension_def UP_field_extension_axioms_def
       apply (simp add: examples(4) field_extension_def subfield_Rats_complex_field)
      apply (simp_all add: complex_field_def P_def)
    done
  show ?thesis unfolding genfield_singleton_explicit apply auto
  proof goal_cases
    case (1 x)
    have [simp]: "inv\<^bsub>complex_field\<^esub> 1 = 1"
      unfolding complex_field_def m_inv_def by simp
    have "x = Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)"
      unfolding complex_field_def apply (simp del: One_nat_def)
      using add.commute complex_eq mult.commute
      by (metis Eval_cx Reals_of_real complex_field_def monoid.simps(1))
    show ?case
      apply (rule exI[of _ "monom P (Im x) 1 \<oplus>\<^bsub>P\<^esub> monom P (Re x) 0"])
      apply (rule exI[of _ "monom P 1 0"])
      apply auto
      unfolding complex_field_def apply auto apply (fold One_nat_def) using
        \<open>x = Eval (monom P (complex_of_real (Im x)) 1) \<oplus>\<^bsub>complex_field\<^esub> complex_of_real (Re x)\<close>
        complex_field_def ring.simps(2) by metis
  qed
qed

corollary finitely_generated_field_extension_complex_over_real:
  "finitely_generated_field_extension complex_field \<real>"
  unfolding finitely_generated_field_extension_def using generate_field_\<i>_UNIV
  by (metis complex_field_def examples(4) field_extension_def finite.emptyI finite.insertI
      insert_is_Un partial_object.select_convs(1) subfield_Rats_complex_field)


end
