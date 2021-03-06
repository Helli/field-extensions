(* Author: Fabian Hellauer, 2018 *)
section \<open>Field Extensions\<close>
theory Field_Extension
  imports
    "HOL-Algebra.Generated_Fields"
    Missing
begin

subsection \<open>Locale Setup\<close>

locale field_extension = K?: subfield K L + L?: field L for L K

lemma (in field) trivial_extension: "field_extension R (carrier R)"
  by (simp add: field_extension.intro field_axioms subfield_iff(1))

locale UP_field_extension = fe?: field_extension + fixes P (structure) and \<alpha>
  defines "P \<equiv> UP (L\<lparr>carrier:=K\<rparr>)"
  assumes \<alpha>_in_L: "\<alpha> \<in> carrier L"
begin

definition "Eval = eval (L\<lparr>carrier:=K\<rparr>) L id \<alpha>"  (*Do the same for P (there with notation)*)

txt \<open>The above commands define the ring \<^term>\<open>P\<close> of univariate polynomials over the field
  \<^term>\<open>K\<close>, which \<^const>\<open>Eval\<close> evaluates in the superfield \<^term>\<open>L\<close> at a fixed \<^term>\<open>\<alpha>\<close>.\<close>

text \<open>Since @{thm \<alpha>_in_L}, \<^const>\<open>Eval\<close> is a homomorphism \<open>P \<rightarrow> L\<close>:\<close>

sublocale pol?: UP_univ_prop \<open>L\<lparr>carrier := K\<rparr>\<close> L id _ \<alpha> Eval
  rewrites "carrier (L\<lparr>carrier:=K\<rparr>) = K"
    and "id x = x"
proof -
  interpret field \<open>L\<lparr>carrier:=K\<rparr>\<close>
    by (simp add: subfield_axioms subfield_iff(2))
  show "UP_univ_prop (L\<lparr>carrier := K\<rparr>) L id \<alpha>"
    apply unfold_locales
     apply (simp add: ring_hom_ring.homh subring_axioms L.subring_ring_hom_ring)
    by (simp add: \<alpha>_in_L)
qed (simp_all add: P_def Eval_def)

sublocale UP_domain \<open>L\<lparr>carrier:=K\<rparr>\<close>
proof (simp_all add: P_def UP_domain_def)
  show "domain (L\<lparr>carrier:=K\<rparr>)"
    using L.subdomain_iff subdomain_axioms by blast
qed

sublocale euclidean_domain P degree
proof unfold_locales
  have "field (L\<lparr>carrier:=K\<rparr>)"
    by (simp add: L.subfield_iff(2) subfield_axioms)
  fix f assume f: "f \<in> carrier P - {\<zero>}"
  fix g assume g: "g \<in> carrier P - {\<zero>}"
  then have "lcoeff g \<in> Units (L\<lparr>carrier:=K\<rparr>)"
    unfolding field.field_Units[OF \<open>field (L\<lparr>carrier:=K\<rparr>)\<close>]
    using lcoeff_nonzero2 by auto
  from f g weak_long_div_theorem[OF _ _ this] show
    "\<exists>q r. q \<in> carrier P \<and> r \<in> carrier P \<and> f = g \<otimes> q \<oplus> r \<and>
      (r = \<zero> \<or> deg (L\<lparr>carrier := K\<rparr>) r < deg (L\<lparr>carrier := K\<rparr>) g)"
    using R.carrier_one_not_zero by auto
qed


subsection \<open>Evaluation of Polynomials in Field Extensions\<close>

lemma Eval_cx[simp]: "c \<in> K \<Longrightarrow> Eval (monom P c 1) = c \<otimes>\<^bsub>L\<^esub> \<alpha>"
  by (simp add: Eval_monom id_def)

lemma Eval_constant[simp]: "c \<in> K \<Longrightarrow> Eval (monom P c 0) = c"
  unfolding Eval_monom by simp

lemma eval_monom_expr': \<comment> \<open>copied and relaxed. Could be further relaxed to non-id homomorphisms?\<close>
  assumes a: "a \<in> K"
  shows "eval (L\<lparr>carrier:=K\<rparr>) L id a (monom P \<one>\<^bsub>L\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) = \<zero>\<^bsub>L\<^esub>"
  (is "eval (L\<lparr>carrier:=K\<rparr>) L id a ?g = _")
proof -
  interpret UP_pre_univ_prop \<open>L\<lparr>carrier:=K\<rparr>\<close> L id unfolding id_def by unfold_locales
  have eval_ring_hom: "eval (L\<lparr>carrier:=K\<rparr>) L id a \<in> ring_hom P L"
    using eval_ring_hom a by (simp add: eval_ring_hom)
  interpret ring_hom_cring P L \<open>eval (L\<lparr>carrier:=K\<rparr>) L id a\<close> by unfold_locales (rule eval_ring_hom)
  have mon1_closed: "monom P \<one>\<^bsub>L\<^esub> 1 \<in> carrier P"
    and mon0_closed: "monom P a 0 \<in> carrier P"
    and min_mon0_closed: "\<ominus>\<^bsub>P\<^esub> monom P a 0 \<in> carrier P"
    using a R.a_inv_closed by auto
  have "eval (L\<lparr>carrier:=K\<rparr>) L id a ?g = eval (L\<lparr>carrier:=K\<rparr>) L id a (monom P \<one>\<^bsub>L\<^esub> 1) \<ominus>\<^bsub>L\<^esub> eval
    (L\<lparr>carrier:=K\<rparr>) L id a (monom P a 0)"
    by (simp add: a_minus_def mon0_closed)
  also have "\<dots> = a \<ominus>\<^bsub>L\<^esub> a"
    using assms eval_const eval_monom1 by simp
  also have "\<dots> = \<zero>\<^bsub>L\<^esub>"
    using a by simp
  finally show ?thesis by simp
qed

end


subsection \<open>Finitely Generated Field Extensions\<close>

lemma (in field) sum_of_fractions:
  "n1 \<in> carrier R \<Longrightarrow> n2 \<in> carrier R \<Longrightarrow> d1 \<in> carrier R \<Longrightarrow> d2 \<in> carrier R \<Longrightarrow>
    d1\<noteq>\<zero> \<Longrightarrow> d2\<noteq>\<zero> \<Longrightarrow> n1 \<otimes> inv d1 \<oplus> n2 \<otimes> inv d2 = (n1\<otimes>d2\<oplus>n2\<otimes>d1) \<otimes> inv (d1\<otimes>d2)"
  by (smt comm_inv_char nonzero_has_inv l_distr m_lcomm m_closed monoid_axioms r_one)

corollary (in field) fraction_sumE:
  assumes "n1 \<in> carrier R" "n2 \<in> carrier R" "d1 \<in> carrier R" "d2 \<in> carrier R"
  and "d1 \<noteq> \<zero>" "d2 \<noteq> \<zero>"
obtains n3 d3 where "n1 \<otimes>inv d1 \<oplus> n2 \<otimes>inv d2 = n3 \<otimes>inv d3"
  and "n3 \<in> carrier R" and "d3 \<in> carrier R" and "d3 \<noteq> \<zero>"
  by (simp add: assms integral_iff sum_of_fractions)

lemma (in field) inv_of_fraction[simp]:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  and "a \<noteq> \<zero>" "b \<noteq> \<zero>"
shows "inv (a \<otimes>inv b) = b \<otimes>inv a"
proof -
  from assms have "(a \<otimes>inv b) \<otimes> (b \<otimes>inv a) = \<one>"
  proof -
    have "\<forall>a aa ab. ((a \<otimes> ab \<otimes> aa = ab \<otimes> (a \<otimes> aa) \<or> aa \<notin> carrier R) \<or> a \<notin> carrier R) \<or> ab \<notin> carrier R"
      using m_assoc m_comm by force
    then have "(a \<otimes> (b \<otimes> inv a \<otimes> inv b) = \<one> \<and> b \<otimes> inv a \<in> carrier R) \<and> inv b \<in> carrier R"
      by (metis assms comm_inv_char m_closed nonzero_has_inv r_one)
    then show ?thesis
      by (metis (no_types) assms(1) m_assoc m_comm)
  qed
  then show ?thesis
    by (simp add: assms comm_inv_char)
qed

text \<open>Proposition 16.5 of Prof. Gregor Kemper's lecture notes @{cite Algebra1} (only for \<^prop>\<open>S
  = {s}\<close>).\<close>

lemma pow_simp[simp]:
  fixes n :: nat
  shows "x [^]\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub> n = x [^]\<^bsub>L\<^esub> n"
  unfolding nat_pow_def by simp

lemma (in UP_field_extension) intermediate_field_eval: (* inline? *)
  assumes "subfield M L"
  assumes "K \<subseteq> M"
  assumes "\<alpha> \<in> M"
  shows "Eval = eval (L\<lparr>carrier := K\<rparr>) (L\<lparr>carrier := M\<rparr>) id \<alpha>"
  unfolding Eval_def eval_def apply auto apply (fold P_def)
proof -
  from assms(1) have "field (L\<lparr>carrier:=M\<rparr>)"
    by (simp add: L.subfield_iff(2))
  have a: "(\<lambda>i. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> \<alpha> [^]\<^bsub>L\<^esub> i) \<in> {..deg (L\<lparr>carrier := K\<rparr>) p} \<rightarrow> M"
    if "p \<in> carrier P" for p
  proof auto
    fix i
    assume "i \<le> degree p"
    then have "coeff P p i \<in> M" and "\<alpha> [^]\<^bsub>L\<^esub> i \<in> M"
      using assms that
      apply (auto intro!: monoid.nat_pow_closed[of "L\<lparr>carrier:=M\<rparr>",
            simplified]) using \<open>field (L\<lparr>carrier:=M\<rparr>)\<close>
      apply (simp add: cring_def domain_def field_def ring.is_monoid)
      done
    then show "coeff P p i \<otimes>\<^bsub>L\<^esub> \<alpha> [^]\<^bsub>L\<^esub> i \<in> M"
      by (simp add: assms(1) subdomainE(6) subfield.axioms(1))
  qed
  have "finsum (L\<lparr>carrier := M\<rparr>) f A = finsum L f A" if "f \<in> A \<rightarrow> M" for f and A :: "'c set"
    apply (intro ring_hom_cring.hom_finsum[of "L\<lparr>carrier:=M\<rparr>" L id, simplified])
    by (intro subring.cring_ring_hom_cring)
      (simp_all add: subfield.axioms assms(1) subfieldE(1) L.is_cring that)
  from a[THEN this] show
    "(\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> \<alpha> [^]\<^bsub>L\<^esub> i) =
    (\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<lparr>carrier := M\<rparr>\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> \<alpha> [^]\<^bsub>L\<^esub>i)"
    by fastforce
qed

proposition (in UP_field_extension) genfield_singleton_explicit:
  "generate_field L (insert \<alpha> K) =
    {Eval f \<otimes>\<^bsub>L\<^esub>inv\<^bsub>L\<^esub> Eval g | f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
proof (simp add: generate_field_min_subfield2[of "insert \<alpha> K"] subset)
  (* to-do: replace by define? *)
  let ?L' = "{Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  and ?\<M> = "{M. subfield M L \<and> \<alpha> \<in> M \<and> K \<subseteq> M}"
  have "?L' \<in> ?\<M>"
  proof auto
    show "subfield ?L' L"
      apply (rule subfieldI')
    proof (rule L.subringI)
      fix h
      assume "h \<in> ?L'"
      then show "\<ominus>\<^bsub>L\<^esub> h \<in> ?L'"
        by (smt P.add.inv_closed L.l_minus inverse_exists mem_Collect_eq ring.hom_a_inv
            ring.hom_closed)
    next
      fix h1 h2
      assume "h1 \<in> ?L'" "h2 \<in> ?L'"
      then show "h1 \<otimes>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>f2"], rule exI[where x = "g1\<otimes>g2"]) using 1 apply
            auto apply (smt L.comm_inv_char L.m_lcomm L.one_closed L.r_null L.r_one L.ring_axioms
              nonzero_inv_nonzero inv_of_fraction inverse_exists monoid.m_closed ring.hom_closed ring_def)
          using L.integral by blast
      qed
      from \<open>h1 \<in> ?L'\<close> \<open>h2 \<in> ?L'\<close> show "h1 \<oplus>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>g2\<oplus>f2\<otimes>g1"], rule exI[where x = "g1\<otimes>g2"])
          by (simp add: 1 L.integral_iff sum_of_fractions)
      qed
    next
      fix k
      assume "k \<in> ?L' - {\<zero>\<^bsub>L\<^esub>}"
      then show "inv\<^bsub>L\<^esub> k \<in> ?L'" by auto (use L.integral_iff in auto)
    qed force+
  next
    show "\<exists>f g. \<alpha> = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "monom P \<one>\<^bsub>L\<^esub> 1"], rule exI[where x = "\<one>"])
      by (auto simp del: One_nat_def)
  next
    fix \<alpha>
    assume "\<alpha> \<in> K"
    show "\<exists>f g. \<alpha> = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "monom P \<alpha> 0"], rule exI[where x = "\<one>"])
      by (simp add: \<open>\<alpha> \<in> K\<close>)
  qed
  then have "?L' \<in> ?\<M>".

  moreover {
    fix M
    assume "M \<in> ?\<M>"
    then have L_over_M: "subfield M L" by auto
    have *: "K \<subseteq> M" and **: "\<alpha> \<in> M"
      using \<open>M \<in> ?\<M>\<close> by auto
    have "?L' \<subseteq> M"
    proof auto
      fix f g
      assume "f \<in> carrier P" "g \<in> carrier P"
      assume "Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      have double_update: "L\<lparr>carrier := K\<rparr> = L\<lparr>carrier:=M, carrier:=K\<rparr>" by simp
      interpret M_over_K: UP_univ_prop \<open>L\<lparr>carrier:=K\<rparr>\<close> \<open>L\<lparr>carrier:=M\<rparr>\<close> id _ \<alpha> Eval
          apply (auto simp: P_def) \<comment> \<open>to-do: easier if I port \<open>old_fe.intermediate_field_2\<close> to the
          new setup?\<close>
        unfolding UP_univ_prop_def UP_pre_univ_prop_def apply auto
        unfolding double_update
        apply (intro subring.cring_ring_hom_cring) apply auto
           apply (intro ring.ring_incl_imp_subring) apply auto
        apply (simp add: subfield.axioms L_over_M L.subring_is_ring subfieldE(1))
        using * apply blast
            apply (simp add: R.ring_axioms)
           apply (simp add: L_over_M L.subring_cring subfieldE(1))
          apply (fact is_UP_cring)
         apply (simp add: ** UP_univ_prop_axioms_def)
        using "*" "**" L_over_M intermediate_field_eval Eval_def by auto
      from \<open>f \<in> carrier P\<close> have "Eval f \<in> M"
        using M_over_K.hom_closed by simp
      from \<open>g \<in> carrier P\<close> have "Eval g \<in> M"
        using M_over_K.hom_closed by simp
      with \<open>Eval g \<noteq> \<zero>\<^bsub>L\<^esub>\<close> have "inv\<^bsub>L\<^esub> Eval g \<in> M"
        using L_over_M L.subfield_m_inv(1) by auto
      with \<open>Eval f \<in> M\<close> show "Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<in> M"
        using M_over_K.m_closed by simp
    qed
  }
  ultimately show "\<Inter>?\<M> = ?L'"
    by (meson cInf_eq_minimum)
qed

definition "finitely_generated_field_extension L K \<longleftrightarrow>
  field_extension L K \<and> (\<exists>S. finite S \<and> generate_field L (S \<union> K) = carrier L)"


subsection \<open>Degree of a Field Extension\<close>

context field_extension begin

lemma vectorspace: "vectorspace (L\<lparr>carrier:=K\<rparr>) (vs_of L)"
  apply (rule vs_criteria) apply auto
       apply (simp add: subfield_axioms subfield_iff(2))
      apply (simp add: add.m_comm)
     apply (simp add: add.m_assoc)
    apply (simp add: m_assoc)
   apply (simp add: l_distr)
  by (simp add: r_distr)

interpretation vs: vectorspace \<open>L\<lparr>carrier:=K\<rparr>\<close> \<open>vs_of L\<close>
\<^cancel>\<open>rewrites 1: "carrier (L\<lparr>carrier := K\<rparr>) = K"
    and 2: "carrier (vs_of L) = carrier L"
    and 3: "zero (vs_of R) = zero R"
    and 4: "smult (vs_of R) = monoid.mult R"
    and 5: "add (vs_of R) = add R"
    and 6: "(\<Oplus>\<^bsub>vs_of L\<^esub>v\<in>A. a v) = (\<Oplus>\<^bsub>L\<^esub>v\<in>A. a v)"
    and 7: "(\<odot>\<^bsub>vs_of L\<^esub>) = (\<otimes>\<^bsub>L\<^esub>)"\<close>
  by (fact vectorspace) (*(simp_all add: finsum_def finprod_def)*)

definition finite where "finite = vs.fin_dim"

text\<open>I encode the infinite degree as \<open>0\<close>.\<close>
definition degree where
  "degree = (if finite then vs.dim else 0)"

text\<open>Adapting this to another notion of cardinality (ecard / enat) should not be too difficult
 because the actual 0 does not occur as degree:\<close>

lemma finite_nonzero_dim: "finite \<Longrightarrow> vs.dim > 0"
  by (rule vs.nonzvs_implies_dim_greater_0) (auto dest: one_zeroI simp: finite_def)

corollary degree_nonzero_iff_finite: "degree \<noteq> 0 \<longleftrightarrow> finite"
  by (simp add: degree_def finite_nonzero_dim)

end

lemma (in field) trivial_extension_size:
  shows trivial_extension_finite: "field_extension.finite R (carrier R)"
    and trivial_extension_degree: "field_extension.degree R (carrier R) = 1"
  using self_vs_size by (simp_all add: field_extension.finite_def field_extension.degree_def trivial_extension)

proposition tower_rule:
  assumes "subfield K (M\<lparr>carrier:=L\<rparr>)" "subfield L M" "field M" \<comment> \<open>Relax to ring?\<close>
  shows degree_multiplicative:
    "field_extension.degree M K = field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
proof -
  \<comment> \<open>to-do: use more \<^theory_text>\<open>interpret\<close>, especially in the "finite" part. Maybe first define a locale
  \<open>fin_dim_vec_space\<close>?\<close>

  let ?L = "M\<lparr>carrier:=L\<rparr>" and ?K = "M\<lparr>carrier:=K\<rparr>"

  have "K \<subseteq> L"
    using assms(1) subfieldE(3) by fastforce
  then have "K \<subseteq> carrier M"
    by (meson assms(2) order.trans subfieldE(3))
  then have "field_extension M K"
    by (metis (no_types) \<open>K \<subseteq> L\<close> assms cring.axioms(1) domain_def field.generate_fieldE(1)
        field.generate_fieldI field.subfield_gen_equality field_def field_extension.intro order_refl
        ring.subfield_iff(2) subfieldE(3))
  then interpret M_over_K: vectorspace ?K \<open>vs_of M\<close>
    rewrites "carrier (M\<lparr>carrier:=K\<rparr>) = K"
    by (simp_all add: field_extension.vectorspace)

  from \<open>K \<subseteq> L\<close> have supfuncset_intro: "f \<in> A \<rightarrow> L" if "f \<in> A \<rightarrow> K" for f A
    using that by auto

  have "ring M" (* rm *)
    using assms(3) cring.axioms(1) domain_def field_def by blast
  consider
    (L_over_K_infinite) "\<not>field_extension.finite ?L K" |
    (M_over_L_infinite) "\<not>field_extension.finite M L" |
    (both_finite) "field_extension.finite M L" "field_extension.finite ?L K"
    by blast
  then show ?thesis
  proof cases
    case L_over_K_infinite
    have subspace: "subspace ?K L (vs_of M)"
      unfolding subspace_def apply (simp add: M_over_K.vectorspace_axioms)
      apply (rule M_over_K.module.module_incl_imp_submodule)
       apply (simp add: assms(2) subfieldE(3)) \<comment> \<open>to-do: use more \<^theory_text>\<open>interpret\<close>\<close>
      using assms cring.axioms(1) domain_def field_def field_extension.intro field_extension.vectorspace ring.subfield_iff(2) vectorspace.axioms(1) by fastforce
    with L_over_K_infinite have "\<not>M_over_K.fin_dim"
      using subspace.subspace_dim(1)[OF subspace]
      using M_over_K.fin_dim_def assms cring.axioms(1) domain_def field_def
        field_extension.finite_def field_extension.intro ring.subfield_iff(2) by fastforce
    then show ?thesis
      by (simp add: L_over_K_infinite \<open>field_extension M K\<close> \<open>ring M\<close> assms(1,2) field_extension.degree_def field_extension.finite_def field_extension.intro ring.subfield_iff(2))
  next
    case M_over_L_infinite
    interpret a: vectorspace ?L \<open>vs_of M\<close>
      rewrites "carrier (M\<lparr>carrier:=L\<rparr>) = L"
      by (simp_all add: assms(2-3) field_extension.vectorspace field_extension_def)
    have "\<not>M_over_K.fin_dim"
    proof
      assume M_over_K.fin_dim
      then obtain B where B: "finite B" "B \<subseteq> carrier M" "M_over_K.span B = carrier M"
        by (auto simp: M_over_K.fin_dim_def)
      then have "a.span B \<supseteq> carrier M"
        using M_over_K.finite_in_span supfuncset_intro by (fastforce simp: a.span_def)
      moreover from M_over_L_infinite have "\<not>(\<exists>B. finite B \<and> B \<subseteq> carrier M \<and> a.span B = carrier M)"
        using a.fin_dim_def assms(2) assms(3) field_extension.finite_def field_extension_def by auto
      ultimately show False
        by (metis B(1,2) a.span_is_subset2 equalityI partial_object.select_convs(1))
    qed
    then show ?thesis
      by (simp add: M_over_L_infinite \<open>field_extension M K\<close> assms(2,3) field_extension.degree_def
          field_extension.finite_def field_extension.intro)
  next
    case both_finite
    define cM where "cM = carrier M"
      \<comment> \<open>This definition is needed: Only the carrier should be "arbitrary" in the induction.\<close>
    have cM_facts: "vectorspace ?L (vs_of M\<lparr>carrier := cM\<rparr>)" "vectorspace.fin_dim ?L (vs_of M\<lparr>carrier := cM\<rparr>)"
      "vectorspace ?K (vs_of M\<lparr>carrier := cM\<rparr>)"
        apply (simp add: assms(2-3) cM_def field_extension.intro field_extension.vectorspace)
      using assms(2) assms(3) both_finite(1) cM_def field_extension.finite_def field_extension.intro apply auto[1]
      by (simp add: M_over_K.vectorspace_axioms cM_def)
    from cM_facts \<comment> \<open>the assumptions with \<^term>\<open>cM\<close> in it\<close>
    have "vectorspace.fin_dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) \<and> vectorspace.dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) =
      vectorspace.dim ?L (vs_of M\<lparr>carrier := cM\<rparr>) * vectorspace.dim ?K (vs_of ?L)"
    proof (induction "vectorspace.dim ?L (vs_of M\<lparr>carrier := cM\<rparr>)" arbitrary: cM)
      case 0
      then have "carrier (vs_of M\<lparr>carrier := cM\<rparr>) = {\<zero>\<^bsub>M\<^esub>}"
        using vectorspace.dim_0_implies_zvs by fastforce
      moreover from calculation have "vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>)"
        using "0.prems"(3) vectorspace.zss_dim(1) by fastforce
      ultimately show "?case"
        using "0.hyps" "0.prems"(3) vectorspace.zss_dim(2) by fastforce
    next
      case (Suc x)
      then obtain h cM' where hM':
        "linear_map (M\<lparr>carrier:=L\<rparr>) (vs_of M\<lparr>carrier:=cM\<rparr>) (direct_sum (vs_of ?L) (vs_of M\<lparr>carrier:=cM'\<rparr>)) h"
        "bij_betw h cM (L \<times> cM')"
        "subspace (M\<lparr>carrier:=L\<rparr>) cM' (vs_of M\<lparr>carrier:=cM\<rparr>)"
        "vectorspace.dim ?L (vs_of M\<lparr>carrier:=cM'\<rparr>) = vectorspace.dim (M\<lparr>carrier:=L\<rparr>) (vs_of M\<lparr>carrier:=cM\<rparr>) - 1"
        using vectorspace.decompose_step[OF Suc.prems(1-2)] by auto
      let ?M' = "vs_of M\<lparr>carrier:=cM'\<rparr>"
      have applied_IH: "vectorspace.fin_dim ?K ?M' \<and> vectorspace.dim ?K ?M' =
        vectorspace.dim ?L ?M' * vectorspace.dim ?K (vs_of ?L)"
        apply (rule Suc.hyps(1))
           apply auto
        using Suc.hyps(2) hM'(4) apply simp
        using Suc.prems(1) hM'(3) partial_object.update_convs(1) vectorspace.subspace_is_vs apply fastforce
        using Suc.prems(2) hM'(3) subspace.subspace_dim(1) apply force
        using hM'(3) assms(1) subfield.vectorspace_wrt_subfield[OF assms(1)] Suc(3)
        by (smt partial_object.surjective partial_object.update_convs(1) vectorspace.subspace_is_vs)
      from hM'(1) have lin_K_map: "linear_map ?K (vs_of M\<lparr>carrier:=cM\<rparr>) (direct_sum (vs_of ?L) ?M') h"
        using subfield.linear_wrt_subfield[OF assms(1)] by auto
      have "vectorspace.fin_dim ?K (direct_sum (vs_of ?L) ?M')"
      proof -
        have f1: "M\<lparr>carrier := K\<rparr> = M\<lparr>carrier := L, carrier := K\<rparr>"
          by simp
        have "vectorspace (M\<lparr>carrier := K\<rparr>) (M_over_K.vs cM')"
          using Suc.prems(1) assms(1) hM'(3) subfield.vectorspace_wrt_subfield vectorspace.subspace_is_vs by fastforce
        then show ?thesis
          using f1 by (metis Suc.prems(1) applied_IH assms(1) direct_sum_dim(1) field_extension.finite_def field_extension.intro field_extension.vectorspace both_finite(2) vectorspace.axioms(2))
      qed
      then have goal1: "vectorspace.fin_dim ?K (vs_of M\<lparr>carrier:=cM\<rparr>)"
        using linear_map.iso_imports_dim(1)[OF lin_K_map] by (simp add: direct_sum_def hM'(2))
      with linear_map.iso_imports_dim[OF lin_K_map] subspace.subspace_dim(1) hM'(2) have
        "vectorspace.dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim ?K (direct_sum (vs_of ?L) ?M')"
      proof -
        have "\<forall>A m p. carrier (p::\<lparr>carrier :: 'a set, monoid.mult :: _ \<Rightarrow> _ \<Rightarrow> _, one :: _, zero :: _, add :: _ \<Rightarrow> _ \<Rightarrow> _, smult :: 'a \<Rightarrow> _ \<Rightarrow> _\<rparr>) \<times> A = carrier (direct_sum p \<lparr>carrier = A, \<dots> = m::\<lparr>monoid.mult :: 'a \<Rightarrow> 'a \<Rightarrow> 'a, one :: 'a, zero :: _, add :: _ \<Rightarrow> _ \<Rightarrow> _, smult :: _ \<Rightarrow> _ \<Rightarrow> _\<rparr>\<rparr>)"
          by (simp add: direct_sum_def)
        then show ?thesis
          using \<open>\<lbrakk>bij_betw h (carrier (vs_of M\<lparr>carrier := cM\<rparr>)) (carrier (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))); vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<rbrakk> \<Longrightarrow> vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<close> \<open>bij_betw h cM (L \<times> cM')\<close> \<open>vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<close> by fastforce
      qed
      also have "\<dots> = vectorspace.dim ?K (vs_of ?L) + vectorspace.dim ?K ?M'"
      proof -
        have f1: "M\<lparr>carrier := K\<rparr> = M\<lparr>carrier := L, carrier := K\<rparr>"
          by simp
        have "vectorspace (M\<lparr>carrier := K\<rparr>) (M_over_K.vs cM')"
          using Suc(3) assms(1) hM'(3) subfield.vectorspace_wrt_subfield vectorspace.subspace_is_vs by fastforce
        then show ?thesis
          using f1 by (metis Suc(3) applied_IH assms(1) direct_sum_dim(2) field_extension.finite_def field_extension.intro field_extension.vectorspace both_finite(2) vectorspace.axioms(2))
      qed
      finally show ?case apply safe using goal1 apply simp
      proof -
        assume a1: "vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of (M\<lparr>carrier := L\<rparr>)) + vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM'\<rparr>)"
        have "x = vectorspace.dim (M\<lparr>carrier := L\<rparr>) (vs_of M\<lparr>carrier := cM'\<rparr>)"
          using Suc.hyps(2) hM'(4) by presburger
      then have "vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) = Suc x * vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of (M\<lparr>carrier := L\<rparr>))"
        using a1 applied_IH mult_Suc by presburger
        then show "vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim (M\<lparr>carrier := L\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) * vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of (M\<lparr>carrier := L\<rparr>))"
          using Suc.hyps(2) by presburger
      qed
    qed
    note this[unfolded cM_def, simplified]
    then show ?thesis
      by (simp add: \<open>field_extension M K\<close> \<open>ring M\<close> assms both_finite field_extension.degree_def
          field_extension.finite_def field_extension.intro ring.subfield_iff(2))
  qed
qed


subsection \<open>Algebraic Field Extensions\<close>

definition (in UP_field_extension) algebraic where
  "algebraic \<longleftrightarrow> (\<exists>p \<in> carrier P - {\<zero>}. Eval p = \<zero>\<^bsub>L\<^esub>)"

definition (in field_extension) algebraic where
  "algebraic \<longleftrightarrow> (\<forall>\<alpha> \<in> carrier L. UP_field_extension.algebraic L K \<alpha>)"

definition (in UP_ring) "monic p \<longleftrightarrow> lcoeff p = \<one>"

lemma (in UP_domain) monic_nonzero: "monic p \<Longrightarrow> p \<noteq> \<zero>\<^bsub>P\<^esub>"
  unfolding monic_def by auto

context UP_field_extension begin
lemmas coeff_smult = coeff_smult[simplified]
lemmas monom_mult_smult = monom_mult_smult[simplified]
lemmas coeff_monom_mult = coeff_monom_mult[simplified]
lemmas coeff_mult = coeff_mult[simplified]
lemmas lcoeff_monom = lcoeff_monom[simplified]
lemmas deg_monom = deg_monom[simplified] (* rm all *)
end

lemma (in field_extension) example_16_8_3: \<comment> \<open>could be moved (see below), but kinda deserves its own spot\<close>
  assumes "\<alpha> \<in> K" shows "UP_field_extension.algebraic L K \<alpha>"
proof -
  define P where "P = UP (L\<lparr>carrier:=K\<rparr>)"
  interpret \<alpha>?: UP_field_extension L K P
    by unfold_locales (simp_all add: assms P_def)
  let ?x_minus_\<alpha> = "monom P \<one>\<^bsub>L\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P \<alpha> 0"
  have goal1: "\<alpha>.Eval ?x_minus_\<alpha> = \<zero>\<^bsub>L\<^esub>"
    unfolding \<alpha>.Eval_def using eval_monom_expr'[OF assms] by blast
  have "?x_minus_\<alpha> \<noteq> \<zero>\<^bsub>P\<^esub>"
    by simp (metis r_right_minus_eq deg_monom assms deg_const monom_closed nat.simps(3) sub_one_not_zero K.one_closed)
  with goal1 show ?thesis unfolding algebraic_def
    using assms by fastforce
qed
lemma (in UP_field_extension) example_16_8_3': "\<alpha> \<in> K \<Longrightarrow> algebraic"
  by (simp add: example_16_8_3)

corollary (in field) trivial_extension_algebraic: "field_extension.algebraic R (carrier R)"
  using field_extension.algebraic_def field_extension.example_16_8_3 trivial_extension by fast


subsection \<open>Divisibility of Polynomials in Field Extensions\<close>

context UP_field_extension
begin

lemma Units_poly: "Units P = {monom P u 0 | u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}}"
proof
  show "Units P \<subseteq> {monom P u 0 |u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}}"
  proof
    fix x assume "x \<in> Units P"
    then obtain inv_x where inv_x: "inv_x \<in> Units P" "inv_x \<otimes> x = \<one>"
      using P.Units_l_inv by blast
    then have "degree inv_x + degree x = degree \<one>"
      using deg_mult by (metis P.Units_closed P.Units_r_inv_ex P.l_null \<open>x \<in> Units P\<close> zero_not_one)
    then have "degree x = 0"
      unfolding deg_one by blast
    then have "\<exists>u. x = monom P u 0 \<and> u \<in> K \<and> u \<noteq> \<zero>\<^bsub>L\<^esub>"
      by (metis Eval_constant P.Units_closed R.zero_closed \<open>x \<in> Units P\<close> deg_zero_impl_monom inv_x
          lcoeff_closed integral_iff zero_not_one monom_zero hom_zero)
    then show "x \<in> {monom P u 0 |u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}}"
      by simp
  qed
next
  show "{monom P u 0 |u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}} \<subseteq> Units P"
  proof
    fix x assume "x \<in> {monom P u 0 |u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}}"
    then obtain u where u: "x = monom P u 0" "u \<in> K-{\<zero>\<^bsub>L\<^esub>}"
      by blast
    then have "monom P (inv\<^bsub>L\<^esub> u) 0 \<otimes> monom P u 0 = monom P (inv\<^bsub>L\<^esub> u \<otimes>\<^bsub>L\<^esub> u) 0"
      using monom_mult_smult monom_mult_is_smult subfield_axioms L.subfield_m_inv(1) by auto
    also have "\<dots> = \<one>\<^bsub>P\<^esub>"
      using L.subfield_m_inv(3) u(2) subfield_axioms monom_one by auto
    finally show "x \<in> Units P"
      by (metis (no_types, lifting) u Diff_iff P.Units_one_closed P.prod_unit_l P.unit_factor
          L.ring_axioms monom_closed ring.subfield_m_inv(1) subfield_axioms)
  qed
qed

lemma lcoeff_mult:
  assumes "p \<in> carrier P" "q \<in> carrier P"
  shows "lcoeff (p \<otimes> q) = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q"
proof (cases "p \<noteq> \<zero>", cases "q \<noteq> \<zero>")
  assume "p \<noteq> \<zero>" "q \<noteq> \<zero>"
  let ?coeff = "\<lambda>i. coeff P p i \<otimes>\<^bsub>L\<^esub> coeff P q (degree p + degree q - i)"
  have "?coeff i = \<zero>\<^bsub>L\<^esub>" if "i \<in> {degree p <.. degree p + degree q}" for i
  proof -
    from that have "i > degree p"
      by force
    then have "coeff P p i = \<zero>\<^bsub>L\<^esub>"
      by (simp add: assms(1) deg_aboveD)
    then show ?thesis
      using assms(2) by auto
  qed
  moreover have "?coeff i = \<zero>\<^bsub>L\<^esub>" if "i \<in> {..< degree p}" for i
  proof -
    from that have "degree p + degree q - i > degree q"
      by fastforce
    then have "coeff P q (degree p + degree q - i) = \<zero>\<^bsub>L\<^esub>"
      by (simp add: assms(2) deg_aboveD)
    then show ?thesis
      using assms(1) by auto
  qed
  moreover have "?coeff i = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q" if "i = degree p" for i
    by (simp add: that)
  ultimately have "(\<lambda>i\<in>{..degree p + degree q}. coeff P p i \<otimes>\<^bsub>L\<^esub> coeff P q (degree p + degree q - i))
    = (\<lambda>i\<in>{..degree p + degree q}. if degree p = i then lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q else \<zero>\<^bsub>L\<^esub>)"
    by auto (smt add_diff_cancel_left' atMost_iff le_eq_less_or_eq nat_le_linear restrict_ext)
  then have "(\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i\<in>{.. degree p + degree q}. coeff P p i \<otimes>\<^bsub>L\<^esub> coeff P q (degree p + degree q - i))
    = (\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i\<in>{.. degree p + degree q}. if degree p = i then lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q else \<zero>\<^bsub>L\<lparr>carrier:=K\<rparr>\<^esub>)"
    using R.finsum_restrict[of _ "{.. degree p + degree q}"] assms by fastforce
  also have "\<dots> = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q"
    by (simp add: R.finsum_singleton' assms(1) assms(2))
  finally show "lcoeff (p \<otimes> q) = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q"
    by (simp add: \<open>p \<noteq> \<zero>\<close> \<open>q \<noteq> \<zero>\<close> assms)
qed (simp_all add: assms)

lemma ex1_associated_monic:
  assumes "p \<in> carrier P - {\<zero>}" shows "\<exists>!q \<in> carrier P. q \<sim> p \<and> monic q"
proof
  from assms have p: "p \<in> carrier P" "lcoeff p \<in> K-{\<zero>\<^bsub>L\<^esub>}"
    using lcoeff_nonzero by auto
  then have inv_ok: "inv\<^bsub>L\<^esub>(lcoeff p) \<in> K"
    using L.subfield_m_inv(1) subfield_axioms by auto
  let ?p = "inv\<^bsub>L\<^esub>(lcoeff p) \<odot> p"
  have "?p \<in> carrier P"
    using inv_ok p(1) by auto
  moreover have "monic ?p" unfolding monic_def
    using L.subfield_m_inv(1) L.subfield_m_inv(3) p subfield_axioms by auto
  moreover have "?p = monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<otimes> p"
    using inv_ok monom_mult_is_smult p(1) by auto
  moreover from p inv_ok have "monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<otimes> monom P (lcoeff p) 0 = \<one>"
    using L.subfield_m_inv(3)[OF subfield_axioms]
    by (metis Diff_iff Eval_constant R.one_closed monom_mult_smult monom_closed monom_mult_is_smult monom_one hom_one)
  then have "monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<in> Units P"
    by (metis P.Units_one_closed P.unit_factor coeff_closed inv_ok monom_closed p(1))
  ultimately show "?p \<in> carrier P \<and> ?p \<sim> p \<and> monic ?p"
    by (simp add: P.Units_closed P.associatedI2' UP_m_comm p(1))
  {
  fix q
  assume "q \<in> carrier P" "q \<sim> p" "monic q"
  then obtain inv_c' where inv_c': "q = inv_c' \<otimes> p" "inv_c' \<in> Units P"
    using ring_associated_iff p(1) by blast
  then obtain inv_c where inv_c'_def: "inv_c' = monom P inv_c 0" and inv_c: "inv_c \<in> K"
    using Units_poly by auto
  have "\<one>\<^bsub>L\<^esub> = lcoeff inv_c' \<otimes>\<^bsub>L\<^esub> lcoeff p"
    using lcoeff_mult \<open>monic q\<close>[unfolded monic_def] by (simp add: P.Units_closed inv_c' p(1))
  then have "\<one>\<^bsub>L\<^esub> = inv_c \<otimes>\<^bsub>L\<^esub> lcoeff p"
    by (simp add: inv_c inv_c'_def)
  then have "inv_c = inv\<^bsub>L\<^esub> lcoeff p"
    by (simp add: L.inv_unique' inv_c p(1) sub_m_comm)
  then have "q = ?p"
    unfolding inv_c' inv_c'_def using monom_mult_is_smult
    using inv_c p(1) by blast
  }
  then show "\<And>q. q \<in> carrier P \<and> q \<sim> p \<and> monic q \<Longrightarrow> q = ?p"
    by blast
qed

lemma nonzero_constant_is_Unit: "p \<in> carrier P-{\<zero>} \<Longrightarrow> degree p = 0 \<Longrightarrow> p \<in> Units P"
  using deg_zero_impl_monom[of p] Units_poly lcoeff_nonzero_nonzero by auto

lemma degree_le_divides_associated:
  assumes "p \<in> carrier P-{\<zero>}" "q \<in> carrier P"
  and "degree p \<le> degree q" "q divides p"
  shows "p \<sim> q"
proof (cases "q = \<zero>")
  case False
  note assms(4)[unfolded factor_def]
  then obtain c where c: "c \<in> carrier P" "p = q \<otimes> c" by auto
  with assms(1) have "c \<noteq> \<zero>"
    using P.r_null assms(2) by blast
  with assms(1-3) c have "degree p = degree q"
    by (simp add: False)
  with \<open>c \<noteq> \<zero>\<close> c have "degree c = 0"
    by (simp add: False assms(2))
  then show ?thesis
    by (simp add: P.associatedI2' \<open>c \<noteq> \<zero>\<close> assms(2) c nonzero_constant_is_Unit)
qed (use assms(4) in auto)


subsection \<open>Minimal Polynomial\<close>

definition irr \<comment> \<open>named after its \<^emph>\<open>irr\<close>educibility (shown later)\<close> (*move into algebraic context?*)
  where "irr = (ARG_MIN degree p. p \<in> carrier P \<and> monic p \<and> Eval p = \<zero>\<^bsub>L\<^esub>)"

subsubsection \<open>Existence\<close>

context
  assumes algebraic
begin

lemma irr_is_arg_min:
  "is_arg_min degree (\<lambda>p. p \<in> carrier P \<and> monic p \<and> Eval p = \<zero>\<^bsub>L\<^esub>) irr"
proof -
  from \<open>algebraic\<close> obtain p where p: "p \<in> carrier P" "lcoeff p \<in> K-{\<zero>\<^bsub>L\<^esub>}" "Eval p = \<zero>\<^bsub>L\<^esub>"
    unfolding algebraic_def using lcoeff_nonzero2 by auto
  then have inv_ok: "inv\<^bsub>L\<^esub>(lcoeff p) \<in> K-{\<zero>\<^bsub>L\<^esub>}"
    using L.subfield_m_inv(1) subfield_axioms by auto
  let ?p = "inv\<^bsub>L\<^esub>(lcoeff p) \<odot> p"
  from inv_ok have "Eval ?p = inv\<^bsub>L\<^esub>(lcoeff p) \<otimes>\<^bsub>L\<^esub> (Eval p)"
    using Eval_smult p(1) by auto
  also have "\<dots> = \<zero>\<^bsub>L\<^esub>"
    using inv_ok p(3) by auto
  finally have "Eval ?p = \<zero>\<^bsub>L\<^esub>" .
  moreover have "?p \<in> carrier P"
    using inv_ok p(1) by auto
  moreover have "monic ?p" unfolding monic_def
    using L.subfield_m_inv(1) L.subfield_m_inv(3) p(1) p(2) subfield_axioms by auto
  ultimately show ?thesis
    unfolding irr_def by (metis (mono_tags, lifting) is_arg_min_arg_min_nat)
qed

corollary irr_exists:
  shows irr_in_P: "irr \<in> carrier P" and monic_irr: "monic irr" and Eval_irr: "Eval irr = \<zero>\<^bsub>L\<^esub>"
  and is_minimal_irr: "\<forall>y. y \<in> carrier P \<and> monic y \<and> Eval y = \<zero>\<^bsub>L\<^esub> \<longrightarrow> degree irr \<le> degree y"
  using irr_is_arg_min[unfolded is_arg_min_linorder] by auto

corollary irr_nonzero: "irr \<noteq> \<zero>"
  by (simp add: monic_irr monic_nonzero)

corollary irr_nonconstant: "degree irr > 0"
proof (rule ccontr)
  assume "\<not> degree irr > 0"
  with monic_irr have "irr = monom P \<one>\<^bsub>L\<^esub> 0"
    using deg_zero_impl_monom irr_in_P monic_def by fastforce
  then show False
    using Eval_irr by simp
qed

subsubsection \<open>Uniqueness\<close>

lemma a_kernel_nontrivial: "a_kernel P L Eval \<supset> {\<zero>}"
  unfolding a_kernel_def' using \<open>algebraic\<close>[unfolded algebraic_def] by auto

lemma PIdl_irr_a_kernel_Eval: "PIdl irr = a_kernel P L Eval"
proof -
  obtain g' where "g' \<in> carrier P" "PIdl g' = a_kernel P L Eval"
    using exists_gen ring.kernel_is_ideal ex1_associated_monic by metis
  then obtain g where g: "g \<in> carrier P" "monic g" "PIdl g = a_kernel P L Eval"
    using ex1_associated_monic by (metis (no_types) DiffD1 DiffD2 associated_iff_same_ideal insertE
      cgenideal_eq_genideal genideal_zero UP_zero_closed a_kernel_nontrivial insert_Diff psubset_imp_ex_mem)
  then have "Eval g = \<zero>\<^bsub>L\<^esub>"
    using P.cgenideal_self ring.kernel_zero by blast
  with g(1,2) have degree_le: "degree irr \<le> degree g"
    using is_minimal_irr by blast
  from Eval_irr have "irr \<in> a_kernel P L Eval"
    unfolding a_kernel_def' by (simp add: irr_in_P)
  then have "g divides irr"
    by (simp add: P.in_PIdl_impl_divided g(1,3))
  with degree_le g(1) irr_in_P have "g \<sim> irr"
    by (simp add: P.associated_sym degree_le_divides_associated irr_nonzero)
  with g(1,3) irr_in_P show "PIdl irr = a_kernel P L Eval"
    using P.associated_iff_same_ideal by auto
qed

lemma irr_unique:
  assumes "is_arg_min degree (\<lambda>p. p \<in> carrier P \<and> monic p \<and> Eval p = \<zero>\<^bsub>L\<^esub>) g" shows "g = irr"
proof -
  have irr_is_unique_gen: "p = irr" if "p \<in> carrier P" "monic p" "PIdl p = a_kernel P L Eval" for p
    using that PIdl_irr_a_kernel_Eval associated_iff_same_ideal ex1_associated_monic
    by (metis UP_zero_closed insertE insert_Diff irr_in_P monic_irr)
  from assms have degree_g_le: "degree g \<le> degree irr"
    by (simp add: Eval_irr irr_in_P is_arg_min_linorder monic_irr)
  from assms have g: "g \<in> carrier P" "monic g" "Eval g = \<zero>\<^bsub>L\<^esub>"
    by (simp_all add: is_arg_min_linorder)
  then have g': "g \<in> carrier P - {\<zero>}" "g \<in> a_kernel P L Eval"
    unfolding a_kernel_def' by (simp_all add: monic_nonzero a_kernel_def)
  with PIdl_irr_a_kernel_Eval have "irr divides g"
    using P.in_PIdl_impl_divided irr_in_P by blast
  with irr_is_unique_gen degree_g_le g'(1) degree_le_divides_associated show ?thesis
    by (metis irr_in_P associated_iff_same_ideal PIdl_irr_a_kernel_Eval g(1,2))
qed

subsubsection \<open>Irreducibility\<close>

text \<open>Kemper shows the following here, but it is a bit pointless since we will soon know
 \<^prop>\<open>field (P Quot PIdl irr)\<close> anyway:\<close>
lemma "domain (P Quot PIdl irr)" \<comment> \<open>unused\<close>
proof -
  have domain_im_Eval: "domain (L\<lparr>carrier := Eval ` carrier P\<rparr>)"
    by (simp add: ring.img_is_domain L.domain_axioms)
  have ring: "ring (P Quot PIdl irr)"
    by (simp add: P.cgenideal_ideal ideal.quotient_is_ring irr_in_P)
  then obtain h where iso_h: "h \<in> ring_iso (L\<lparr>carrier := Eval ` carrier P\<rparr>) (P Quot PIdl irr)"
    using ring_iso_set_sym ring.FactRing_iso_set_aux PIdl_irr_a_kernel_Eval by auto
  note domain.ring_iso_imp_img_domain[OF domain_im_Eval this]
  then show ?thesis
    using iso_h[unfolded ring_iso_def] ring_hom_zero[OF _ ring.img_is_ring ring] by fastforce
qed

text \<open>Instead, usage of some lemmas from \<^theory>\<open>HOL-Algebra.QuotRing\<close> makes for a shorter proof of
  \<^const>\<open>irr\<close>'s irreducibility:\<close>
lemma irr_irreducible_polynomial: "ring_irreducible irr"
proof -
  txt "As the zero ideal's preimage under evaluation \<^term>\<open>PIdl irr\<close> is again a prime ideal:"
  have "primeideal (PIdl irr) P" unfolding PIdl_irr_a_kernel_Eval a_kernel_def'
    using pol.ring.primeideal_vimage[OF cring_axioms L.zeroprimeideal] by simp
  txt "This immediately gives the desired result, as \<^term>\<open>P\<close> is a principal ideal domain:"
  then show "ring_irreducible\<^bsub>P\<^esub> irr"
    using irr_in_P irr_nonzero primeideal_iff_prime primeness_condition by auto
qed

subsubsection \<open>Quotient Forming\<close>

text \<open>Representative evaluation is a well-defined, injective homomorphism:\<close>
lemma repr_Eval_wd_inj:
  "the_elem \<circ> (`) Eval \<in> ring_iso (P Quot PIdl irr) (L\<lparr>carrier := Eval ` carrier P\<rparr>)"
  using ring.FactRing_iso_set_aux by (simp add: o_def PIdl_irr_a_kernel_Eval)

text \<open>Its image (= \<^const>\<open>Eval\<close>'s image) is \<open>K(\<alpha>)\<close>:\<close>
lemma img_Eval_is_generate_field: "Eval ` carrier P = generate_field L (insert \<alpha> K)"
proof
  have "Eval ` carrier P = {Eval f | f. f \<in> carrier P}"
    by fast
  also have "\<dots> \<subseteq> {Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in> carrier P \<and> g = \<one>}"
    by force
  also have "\<dots> \<subseteq> {Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
    by fastforce
  also have "\<dots> = generate_field L (insert \<alpha> K)"
    by (fact genfield_singleton_explicit[symmetric])
  finally show "Eval ` carrier P \<subseteq> generate_field L (insert \<alpha> K)" .
next
  show "Eval ` carrier P \<supseteq> generate_field L (insert \<alpha> K)"
  proof (rule L.generate_field_min_subfield1)
    from irreducible_imp_maximalideal interpret irr: maximalideal \<open>PIdl irr\<close> P
      by (simp add: irr_in_P irr_irreducible_polynomial)
    from irr.quotient_is_field interpret Quot: field \<open>P Quot PIdl irr\<close>
      by (simp add: P.cring)
    from repr_Eval_wd_inj have zero_ok: "(the_elem \<circ> (`) Eval) \<zero>\<^bsub>P Quot PIdl irr\<^esub> = \<zero>\<^bsub>L\<^esub>"
      using ring_hom_zero[OF _ irr.quotient_is_ring ring.img_is_ring] by (auto simp: ring_iso_def)
    from Quot.ring_iso_imp_img_field[OF repr_Eval_wd_inj] have "field (L\<lparr>carrier := Eval ` carrier P\<rparr>)"
      using zero_ok by fastforce
    then show "subfield (Eval ` carrier P) L"
      by (auto intro: ring.subfield_iff(1) simp: L.ring_axioms)
  next
    have "x \<in> Eval ` carrier P" if "x \<in> insert \<alpha> K" for x
    proof (cases "x = \<alpha>")
      case True
      with Eval_cx[of "\<one>\<^bsub>L\<^esub>", simplified] show ?thesis
        using monom_closed by (metis K.one_closed image_eqI)
    next
      case False
      then have "x \<in> K"
        using that by simp
      then show ?thesis
        using Eval_constant monom_closed by (metis imageI)
    qed
    then show "insert \<alpha> K \<subseteq> Eval ` carrier P"
      by fast
  qed fast
qed

text \<open>Theorem 16.9b of @{cite "Algebra1"}:\<close>

theorem the_elem_ring_iso_Quot_generate_field:
  "the_elem \<circ> (`) Eval \<in> ring_iso (P Quot PIdl irr) (L\<lparr>carrier:=generate_field L (insert \<alpha> K)\<rparr>)"
  by (fact repr_Eval_wd_inj[unfolded img_Eval_is_generate_field])

corollary simple_algebraic_extension:
  "P Quot PIdl irr \<simeq> L\<lparr>carrier := generate_field L (insert \<alpha> K)\<rparr>"
  using the_elem_ring_iso_Quot_generate_field is_ring_iso_def by blast

end

end

end
