theory Field_Extension imports
"HOL-Algebra.Algebra"  (* reduce? *)
Missing
begin

section \<open>missing preliminaries?\<close>

lemma (in subgroup) subgroup_is_comm_group [intro]:
  assumes "comm_group G"
  shows "comm_group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret comm_group G by fact
  have "monoid (G\<lparr>carrier := H\<rparr>)"
    by (simp add: group.is_monoid is_group subgroup_is_group)
  then show ?thesis
    by (simp add: comm_group.intro is_group subgroup_is_group subgroup_is_submonoid
        submonoid_is_comm_monoid)
qed

lemmas (in field)
  [simp] = mult_of_is_Units[symmetric] \<comment> \<open>avoid the duplicate constant\<close> and
  [simp] = units_of_inv

lemma carrier_K[simp]: "carrier (L\<lparr>carrier:=K\<rparr>) = K"
  by simp


subsection \<open>Subrings\<close>

context ring begin \<comment> \<open>"Let @{term R} be a ring."\<close>

lemma ring_card: "card (carrier R) \<ge> 1 \<or> infinite (carrier R)"
  using not_less_eq_eq ring.ring_simprules(6) by fastforce

lemma subring_ring_hom_ring: "subring S R \<Longrightarrow> ring_hom_ring (R\<lparr>carrier:=S\<rparr>) R id"
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def
  by (auto simp: subring_is_ring ring_axioms intro!: ring_hom_memI) (use subringE(1) in blast)

end

lemma (in cring) Subring_cring: "subring S R \<Longrightarrow> cring (R\<lparr>carrier:=S\<rparr>)"
  using cring.subcringI' is_cring ring_axioms ring.subcring_iff subringE(1) by blast

lemma (in subring) cring_ring_hom_cring:
  "cring R \<Longrightarrow> ring_hom_cring (R\<lparr>carrier:=H\<rparr>) R id"
  by (simp add: RingHom.ring_hom_cringI cring.Subring_cring cring.axioms(1) ring.subring_ring_hom_ring subring_axioms)

lemma (in ring) subring_m_inv:
  assumes "subring K R" and "k \<in> Units (R\<lparr>carrier:=K\<rparr>)"
  shows "inv k \<in> Units (R\<lparr>carrier:=K\<rparr>)" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
proof -
  have K: "submonoid K R"
    by (simp add: assms(1) subring.axioms(2))
  have monoid: "monoid (R \<lparr> carrier := K \<rparr>)"
    by (simp add: K monoid_axioms submonoid.submonoid_is_monoid)

  from assms(2) have unit_of_R: "k \<in> Units R"
    using assms(2) unfolding Units_def by auto (meson K submonoid.mem_carrier)+
  have "inv\<^bsub>(R \<lparr> carrier := K \<rparr>)\<^esub> k \<in> Units (R \<lparr> carrier := K \<rparr>)"
    by (simp add: assms(2) monoid monoid.Units_inv_Units)
  thus "inv k \<in> Units (R \<lparr> carrier := K \<rparr>)" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
    using Units_l_inv[OF unit_of_R] Units_r_inv[OF unit_of_R]
    using monoid.m_inv_monoid_consistent[OF monoid_axioms assms(2) K] by auto
qed

context field begin \<comment> \<open>"Let @{term R} be a field."\<close>

lemma has_inverse: "a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>carrier R. a\<otimes>b = \<one>"
  by (simp add: Units_r_inv_ex field_Units)

lemmas group_mult_of_subgroup = subgroup.subgroup_is_comm_group[OF _ units_comm_group, simplified]

lemma one_Units [simp]: "one (R\<lparr>carrier:=carrier A - {\<zero>}\<rparr>) = \<one>"
  by simp

lemma inv_nonzero: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<noteq> \<zero>"
  using Units_inv_Units field_Units by simp

end


subsection \<open>Univariate Polynomials\<close>

lemma (in UP_ring) lcoeff_Unit_nonzero:
  "carrier R \<noteq> {\<zero>} \<Longrightarrow> lcoeff p \<in> Units R \<Longrightarrow> p \<noteq> \<zero>\<^bsub>P\<^esub>"
  by (metis R.Units_r_inv_ex R.l_null R.one_zeroD coeff_zero)

lemma (in UP_cring) Unit_scale_zero:
  "c \<in> Units R \<Longrightarrow> r \<in> carrier P \<Longrightarrow> c \<odot>\<^bsub>P\<^esub> r = \<zero>\<^bsub>P\<^esub> \<Longrightarrow> r = \<zero>\<^bsub>P\<^esub>"
  by (metis R.Units_closed R.Units_l_inv_ex UP_smult_one smult_assoc_simp smult_r_null)

lemma (in UP_cring) Unit_scale_deg[simp]:
  "c \<in> Units R \<Longrightarrow> r \<in> carrier P \<Longrightarrow> deg R (c \<odot>\<^bsub>P\<^esub> r) = deg R r"
  by (metis R.Units_closed R.Units_l_inv_ex deg_smult_decr le_antisym smult_assoc_simp smult_closed smult_one)

lemma (in UP_cring) weak_long_div_theorem:
  assumes g_in_P [simp]: "g \<in> carrier P" and f_in_P [simp]: "f \<in> carrier P"
  and lcoeff_g: "lcoeff g \<in> Units R" and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  shows "\<exists>q r. q \<in> carrier P \<and> r \<in> carrier P \<and> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (r = \<zero>\<^bsub>P\<^esub> \<or> deg R r < deg R g)"
proof -
  from long_div_theorem[OF g_in_P f_in_P] obtain q r and k::nat where qrk: "q \<in> carrier P"
    "r \<in> carrier P" "lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r" "r = \<zero>\<^bsub>P\<^esub> \<or> deg R r < deg R g"
    using R_not_trivial lcoeff_Unit_nonzero lcoeff_g by auto
  from lcoeff_g have inv: "lcoeff g [^] k \<in> Units R"
    by (induction k) simp_all
  let ?inv = "inv (lcoeff g [^] k)"
  have inv_ok: "?inv \<in> Units R" "?inv \<in> carrier R"
    using inv by simp_all
  from inv have "f = ?inv \<otimes> lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f"
    by simp
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> (lcoeff g [^] k \<odot>\<^bsub>P\<^esub> f)"
    by (simp add: local.inv smult_assoc_simp)
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r)"
    by (simp add: qrk)
  also have "\<dots> = ?inv \<odot>\<^bsub>P\<^esub> g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r"
    by (simp add: UP_smult_assoc2 UP_smult_r_distr inv_ok qrk(1-2))
  also have "\<dots> = g \<otimes>\<^bsub>P\<^esub> (?inv \<odot>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r"
    using UP_m_comm inv_ok qrk(1) smult_assoc2 by auto
  finally have "f = g \<otimes>\<^bsub>P\<^esub> (?inv \<odot>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>P\<^esub> ?inv \<odot>\<^bsub>P\<^esub> r" .
  moreover have "?inv \<odot>\<^bsub>P\<^esub> q \<in> carrier P" "?inv \<odot>\<^bsub>P\<^esub> r \<in> carrier P"
    by (simp_all add: inv_ok qrk(1-2))
  moreover have "?inv \<odot>\<^bsub>P\<^esub> r = \<zero>\<^bsub>P\<^esub> \<or> deg R (?inv \<odot>\<^bsub>P\<^esub> r) < deg R (?inv \<odot>\<^bsub>P\<^esub> g)"
    using Unit_scale_deg inv_ok(1) qrk(2,4) by auto
  ultimately show ?thesis using inv_ok(1) by auto
qed


section \<open>Field Extensions\<close>

subsection \<open>convenient locale setup\<close>

locale subfield = subfield K L for K L
  \<comment> \<open>only for renaming. rm.\<close>

locale field_extension = subf'd?: subfield K L + superf'd?: field L for L K

lemmas
  subfield_intro = Subrings.subfield.intro[folded subfield_def]
lemmas (in field)
  generate_fieldE = generate_fieldE[folded subfield_def] and
  subfieldI' = subfieldI'[folded subfield_def] and
  generate_field_min_subfield2 = generate_field_min_subfield2[folded subfield_def]
lemmas (in ring)
  subfield_iff = subfield_iff[folded subfield_def] and
  subfieldI = subfieldI[folded subfield_def] and
  subfield_m_inv = subfield_m_inv[folded subfield_def]

lemma (in field) field_extension_refl: "field_extension R (carrier R)"
  by (simp add: field_extension.intro field_axioms subfield_iff(1))

lemma (in subfield) additive_subgroup: "additive_subgroup K L"
  by (simp add: additive_subgroupI is_subgroup)

lemma (in subfield) finsum_simp: (* unused *)
  assumes \<open>ring L\<close>
  assumes "v ` A \<subseteq> K"
  shows "(\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i \<in> A. v i) = (\<Oplus>\<^bsub>L\<^esub>i \<in> A. v i)"
  unfolding finsum_def apply auto using assms
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case
    by (simp add: finprod_def)
next
  case empty
  have "\<zero>\<^bsub>L\<^esub> \<in> K"
    by (metis monoid.select_convs(2) subgroup_axioms subgroup_def)
  then show ?case
      by (simp add: finprod_def)
next
  case (insert x F)
  have a: "v \<in> F \<rightarrow> K"
    using insert.prems(2) by auto
  moreover have "K \<subseteq> carrier L"
    by (simp add: subset)
  ultimately have b: "v \<in> F \<rightarrow> carrier L"
    by fast
  have d: "v x \<in> K"
    using insert.prems(2) by auto
  then have e: "v x \<in> carrier L"
    using \<open>K \<subseteq> carrier L\<close> by blast
  have "abelian_monoid (L\<lparr>carrier := K\<rparr>)" using assms(1)
    using abelian_group_def ring.subring_iff ring_def subring_axioms subset by auto
  then have f: "comm_monoid \<lparr>carrier = K, monoid.mult = (\<oplus>\<^bsub>L\<^esub>), one = \<zero>\<^bsub>L\<^esub>, \<dots> = undefined::'b\<rparr>"
    by (simp add: abelian_monoid_def)
  note comm_monoid.finprod_insert[of "add_monoid L", simplified, OF _ insert.hyps b e, simplified]
  then have "finprod (add_monoid L) v (insert x F) = v x \<oplus>\<^bsub>L\<^esub> finprod (add_monoid L) v F"
    using abelian_group.a_comm_group assms(1) comm_group_def ring_def by blast
  with comm_monoid.finprod_insert[of "add_monoid (L\<lparr>carrier := K\<rparr>)", simplified, OF f insert.hyps a d, simplified]
  show ?case
    by (simp add: a image_subset_iff_funcset insert.IH insert.prems(1))
qed

(*to-do: swap summands? remove qualifiers? It would be good if \<open>P\<close> appeared a bit more often (e.g.
as operator subscript) so that it does not come "out of nowhere" in the few places where it's used.*)
locale UP_of_field_extension = pol?: UP_univ_prop "L\<lparr>carrier := K\<rparr>" L id + fe?: field_extension
begin
txt \<open>The above locale header defines the ring \<^term>\<open>P\<close> of univariate polynomials over the field
  \<^term>\<open>K\<close>, which \<^term>\<open>Eval\<close> evaluates in the superfield \<^term>\<open>L\<close> at a fixed \<^term>\<open>s\<close>.\<close>

sublocale UP_domain "L\<lparr>carrier:=K\<rparr>" apply intro_locales
  using S.subfield_iff(2) domain_def field_def subfield_axioms by auto

abbreviation "dg \<equiv> deg (L\<lparr>carrier:=K\<rparr>)"

sublocale euclidean_domain P "dg"
proof unfold_locales
  have "field (L\<lparr>carrier:=K\<rparr>)"
    by (simp add: S.subfield_iff(2) subfield_axioms)
  fix f assume f: "f \<in> carrier P - {\<zero>}"
  fix g assume g: "g \<in> carrier P - {\<zero>}"
  then have "lcoeff g \<in> Units (L\<lparr>carrier:=K\<rparr>)"
    unfolding field.field_Units[OF \<open>field (L\<lparr>carrier:=K\<rparr>)\<close>]
    using coeff_closed lcoeff_nonzero2 by auto
  from f g weak_long_div_theorem[OF _ _ this] show
    "\<exists>q r. q \<in> carrier P \<and> r \<in> carrier P \<and> f = g \<otimes> q \<oplus> r \<and>
      (r = \<zero> \<or> deg (L\<lparr>carrier := K\<rparr>) r < deg (L\<lparr>carrier := K\<rparr>) g)"
    using R.carrier_one_not_zero by auto
qed

(* rm these two? *)
lemmas L_assoc = R.m_assoc[simplified]
lemmas one_is_neutral[simp] = R.l_one[simplified] R.r_one[simplified]

lemma Eval_x[simp]: (*rm?*)
  "Eval (UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1) = s" using eval_monom1 Eval_def by simp

lemma Eval_cx[simp]: "c \<in> K \<Longrightarrow> Eval (UnivPoly.monom P c 1) = c \<otimes>\<^bsub>L\<^esub> s"
proof goal_cases
  case 1
  then have "UnivPoly.monom P c 1 = c \<odot> UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1"
    using monom_mult_smult[of c "\<one>\<^bsub>L\<^esub>" 1, simplified] apply simp
    done
  then show ?case using "1" Eval_smult Eval_x subfield_axioms One_nat_def id_apply monom_closed
      carrier_K by (metis one_closed)
qed

lemma Eval_constant[simp]: "x \<in> K \<Longrightarrow> Eval (UnivPoly.monom P x 0) = x" unfolding
  Eval_monom[simplified] by auto

end


subsection \<open>Finitely generated field extensions\<close>

locale finitely_generated_field_extension = field_extension +
  assumes "\<exists>S. finite S \<and> generate_field L (S \<union> K) = carrier L"
(*  \<comment> \<open>Maybe remove quantifier by fixing \<open>S\<close>? Or replace locale by a simple predicate?\<close>
or simply add one of these:
begin
definition "S \<equiv> THE S. finite S \<and> generate_field L (S \<union> K) = carrier L"
definition "S \<equiv> SOME S. finite S \<and> generate_field L (S \<union> K) = carrier L"
What is the difference?
end
*)

lemma (in field) sum_of_fractions:
      "n1 \<in> carrier R \<Longrightarrow>
       n2 \<in> carrier R \<Longrightarrow>
       d1 \<in> carrier R \<Longrightarrow>
       d2 \<in> carrier R \<Longrightarrow>
       d1 \<noteq> \<zero> \<Longrightarrow>
       d2 \<noteq> \<zero> \<Longrightarrow>
          n1 \<otimes>inv d1 \<oplus> n2 \<otimes>inv d2 = (n1\<otimes>d2\<oplus>n2\<otimes>d1) \<otimes>inv (d1\<otimes>d2)"
proof goal_cases
  case 1
  then have
    "n1\<otimes>inv d1 = (n1\<otimes>d2)\<otimes>inv (d1\<otimes>d2)"
    "n2\<otimes>inv d2 = (n2\<otimes>d1)\<otimes>inv (d1\<otimes>d2)"
    by (smt comm_inv_char has_inverse m_closed m_lcomm r_one)+
  then show ?case
    by (simp add: 1 field_Units integral_iff l_distr)
qed

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
      by (metis (no_types) Diff_iff Units_inv_closed Units_one_closed Units_r_inv assms empty_iff
          insert_iff inv_one field_Units m_assoc m_closed)
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

lemma (in UP_of_field_extension) intermediate_field_eval: (* inline? *)
  assumes "subfield M L"
  assumes "K \<subseteq> M"
  assumes "s \<in> M"
  shows "Eval = UnivPoly.eval (L\<lparr>carrier := K\<rparr>) (L\<lparr>carrier := M\<rparr>) id s"
  unfolding Eval_def eval_def apply auto apply (fold P_def)
proof -
  have "field (L\<lparr>carrier:=M\<rparr>)"
    using subfield_def S.subfield_iff(2) assms(1) by blast
  have a: "(\<lambda>i. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i) \<in> {..deg (L\<lparr>carrier := K\<rparr>) p} \<rightarrow> M"
    if "p \<in> carrier P" for p
  proof auto
    fix i
    assume "i \<le> deg (L\<lparr>carrier := K\<rparr>) p"
    then have "UnivPoly.coeff P p i \<in> M" and "s [^]\<^bsub>L\<^esub> i \<in> M"
      using assms coeff_closed that apply auto
      apply (auto intro!: monoid.nat_pow_closed[of "L\<lparr>carrier:=M\<rparr>",
            simplified]) using \<open>field (L\<lparr>carrier:=M\<rparr>)\<close>
      apply (simp add: cring_def domain_def field_def ring.is_monoid)
      done
    then show "UnivPoly.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i \<in> M"
      using assms(1) by (simp add: subfield_def Subrings.subfield.axioms(1) subdomainE(6))
  qed
  have "finsum (L\<lparr>carrier := M\<rparr>) f A = finsum L f A" if "f \<in> A \<rightarrow> M" for f and A :: "'c set"
    apply (intro ring_hom_cring.hom_finsum[of "L\<lparr>carrier:=M\<rparr>" L id, simplified])
    by (intro subring.cring_ring_hom_cring)
      (simp_all add: subfield.axioms assms(1) subfieldE(1) S.is_cring that)
  from a[THEN this] show
    "(\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub> i) =
    (\<lambda>p\<in>carrier P. \<Oplus>\<^bsub>L\<lparr>carrier := M\<rparr>\<^esub>i\<in>{..deg (L\<lparr>carrier := K\<rparr>) p}. up_ring.coeff P p i \<otimes>\<^bsub>L\<^esub> s [^]\<^bsub>L\<^esub>i)"
    by fastforce
qed

lemma (in UP_of_field_extension) insert_s_K: "insert s K \<subseteq> carrier L"
  \<comment>\<open>\<^term>\<open>s\<close> is already fixed in this locale (via @{locale UP_univ_prop})\<close>
  by (simp add: subset)

proposition (in UP_of_field_extension) genfield_singleton_explicit:
  "generate_field L (insert s K) =
    {Eval f \<otimes>\<^bsub>L\<^esub>inv\<^bsub>L\<^esub> Eval g | f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  unfolding generate_field_min_subfield2[OF insert_s_K] apply simp
proof -
  (* to-do: replace by define? *)
  let ?L' = "{Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g |f g. f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>}"
  and ?\<M> = "{M. subfield M L \<and> s \<in> M \<and> K \<subseteq> M}"
  have "?L' \<in> ?\<M>"
  proof auto
    show "subfield ?L' L"
      apply (rule subfieldI')
    proof (rule S.subringI)
      fix h
      assume "h \<in> ?L'"
      then show "\<ominus>\<^bsub>L\<^esub> h \<in> ?L'"
        by (smt P.add.inv_closed S.l_minus inverse_exists mem_Collect_eq ring.hom_a_inv
            ring.hom_closed)
    next
      fix h1 h2
      assume "h1 \<in> ?L'" "h2 \<in> ?L'"
      then show "h1 \<otimes>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>f2"], rule exI[where x = "g1\<otimes>g2"]) using 1 apply
            auto
          apply (smt S.comm_inv_char S.m_lcomm S.one_closed S.r_null S.r_one S.ring_axioms
              inv_nonzero inv_of_fraction inverse_exists monoid.m_closed ring.hom_closed ring_def)
          using superf'd.integral by blast
      qed
      from \<open>h1 \<in> ?L'\<close> \<open>h2 \<in> ?L'\<close> show "h1 \<oplus>\<^bsub>L\<^esub>h2 \<in> ?L'"
        apply auto
      proof goal_cases
        case (1 f1 f2 g1 g2)
        show ?case apply (rule exI[where x = "f1\<otimes>g2\<oplus>f2\<otimes>g1"], rule exI[where x = "g1\<otimes>g2"])
          by (simp add: 1 superf'd.integral_iff sum_of_fractions)
      qed
    next
      fix k
      assume "k \<in> ?L' - {\<zero>\<^bsub>L\<^esub>}"
      then show "inv\<^bsub>L\<^esub> k \<in> ?L'" by auto (use superf'd.integral_iff in auto)
    qed force+
  next
    show "\<exists>f g. s = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "UnivPoly.monom P \<one>\<^bsub>L\<^esub> 1"], rule exI[where x = "\<one>"])
      by (auto simp del: One_nat_def)
  next
    fix \<alpha>
    assume "\<alpha> \<in> K"
    show "\<exists>f g. \<alpha> = Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<and> f \<in> carrier P \<and> g \<in> carrier P \<and> Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      apply (rule exI[where x = "UnivPoly.monom P \<alpha> 0"], rule exI[where x = "\<one>"])
      by (simp add: \<open>\<alpha> \<in> K\<close>)
  qed
  then have "?L' \<in> ?\<M>".

  moreover {
    fix M
    assume "M \<in> ?\<M>"
    then have L_over_M: "subfield M L" by auto
    have *: "K \<subseteq> M" and **: "s \<in> M"
      using \<open>M \<in> ?\<M>\<close> by auto
    have "?L' \<subseteq> M"
    proof auto
      fix f g
      assume "f \<in> carrier P" "g \<in> carrier P"
      assume "Eval g \<noteq> \<zero>\<^bsub>L\<^esub>"
      have double_update: "L\<lparr>carrier := K\<rparr> = L\<lparr>carrier:=M, carrier:=K\<rparr>" by simp
      interpret M_over_K: UP_univ_prop "L\<lparr>carrier:=K\<rparr>" "L\<lparr>carrier:=M\<rparr>" id
          apply (auto simp: P_def) \<comment> \<open>to-do: easier if I port \<open>old_fe.intermediate_field_2\<close> to the
          new setup?\<close>
        unfolding UP_univ_prop_def UP_pre_univ_prop_def apply auto
        unfolding double_update
        apply (intro subring.cring_ring_hom_cring) apply auto
           apply (intro ring.ring_incl_imp_subring) apply auto
        apply (simp add: subfield.axioms L_over_M S.subring_is_ring subfieldE(1))
        using * apply blast
        apply (simp add: R.ring_axioms)
        using subfield_def L_over_M S.Subring_cring subfieldE(1) apply blast
          apply (fact is_UP_cring)
         apply (simp add: ** UP_univ_prop_axioms_def)
        unfolding Eval_def apply (rule eq_reflection)
        apply (intro UP_of_field_extension.intermediate_field_eval)
        by (simp_all add: UP_of_field_extension_axioms L_over_M * **)
      from \<open>f \<in> carrier P\<close> have "Eval f \<in> M"
        using M_over_K.hom_closed by simp
      from \<open>g \<in> carrier P\<close> have "Eval g \<in> M"
        using M_over_K.hom_closed by simp
      with \<open>Eval g \<noteq> \<zero>\<^bsub>L\<^esub>\<close> have "inv\<^bsub>L\<^esub> Eval g \<in> M"
        using L_over_M S.subfield_m_inv(1) by auto
      with \<open>Eval f \<in> M\<close> show "Eval f \<otimes>\<^bsub>L\<^esub> inv\<^bsub>L\<^esub> Eval g \<in> M"
        using M_over_K.m_closed[simplified] by simp
    qed
  }
  ultimately show "\<Inter>?\<M> = ?L'"
    by (meson cInf_eq_minimum)
qed


subsection \<open>Polynomial Divisibility\<close>

text \<open>keep an eye out whether I need something from @{url
  "https://github.com/DeVilhena-Paulo/GaloisCVC4/blob/master/Polynomial_Divisibility.thy"}\<close>


subsection \<open>Degree of a field extension\<close>

hide_const (open) degree

abbreviation "vs_of K \<equiv> \<comment> \<open>\<open>K\<close> extended with \<open>(\<otimes>\<^bsub>K\<^esub>)\<close> as \<^const>\<open>smult\<close>\<close>
  \<lparr>carrier = carrier K, monoid.mult = (\<otimes>\<^bsub>K\<^esub>), one = \<one>\<^bsub>K\<^esub>, zero = \<zero>\<^bsub>K\<^esub>, add = (\<oplus>\<^bsub>K\<^esub>), smult = (\<otimes>\<^bsub>K\<^esub>)\<rparr>"

context field_extension begin

lemma vectorspace_satisfied: "vectorspace (L\<lparr>carrier:=K\<rparr>) (vs_of L)"
  apply (rule vs_criteria) apply auto
       apply (simp add: subfield_axioms subfield_iff(2))
      apply (simp add: add.m_comm)
     apply (simp add: add.m_assoc)
    apply (simp add: m_assoc)
   apply (simp add: l_distr)
  by (simp add: semiring.semiring_simprules(13) semiring_axioms)

interpretation vecs: vectorspace "L\<lparr>carrier:=K\<rparr>" "vs_of L"
  by (fact vectorspace_satisfied)

abbreviation finite where "finite \<equiv> vecs.fin_dim"
\<comment> \<open>Prop. 14.16 would look much better if I also had an abbreviation for infinite degree\<close>

definition degree where
  "degree \<equiv> if finite then vecs.dim else 0"
 \<comment> \<open>This uses the pragmatic tradition \<open>\<infinity> = 0\<close>. Adapting it to another notion of cardinality
 (ecard / enat) should not be too difficult.\<close>

lemma fin_dim_nonzero: "finite \<Longrightarrow> vecs.dim > 0"
  by (rule vecs.dim_greater_0) (auto dest: one_zeroI)

corollary degree_0_iff[simp]: "degree \<noteq> 0 \<longleftrightarrow> finite"
  by (simp add: degree_def fin_dim_nonzero)

end

locale finite_field_extension = field_extension +
  assumes finite

lemma (in field) field_is_vecs_over_itself: "vectorspace R (vs_of R)"
  by (fact field_extension.vectorspace_satisfied[OF field_extension_refl, simplified])

lemma (in field) trivial_degree[simp]: "field_extension.degree R (carrier R) = 1"
proof -
(* to-do: can this\<down> provide "vecs." lemmas and definitions? Probably if I use sublocale for vecs,
 but do I want/need this? Only when \<^bold>n\<^bold>o\<^bold>t working in field_extension...

  interpret asdfasdffe: field_extension R "carrier R"
    by (fact field_extension_refl)
*)
  interpret vecs: vectorspace R "vs_of R" by (fact field_is_vecs_over_itself)
  let ?A = "{\<one>}"
  have A_generates_R: "finite ?A \<and> ?A \<subseteq> carrier R \<and> vecs.gen_set ?A"
  proof auto
    show "x \<in> vecs.span {\<one>}" if "x \<in> carrier R" for x
      unfolding vecs.span_def apply auto apply (rule exI[of _ "\<lambda>_. x"]) \<comment> \<open>coefficient \<^term>\<open>x\<close>\<close>
      by (rule exI[of _ ?A]) (auto simp: that vecs.lincomb_def)
  qed (metis (mono_tags, lifting) empty_subsetI insert_subset module.span_is_subset2 one_closed
        partial_object.select_convs(1) subsetCE vecs.module_axioms)
  then have vecs.fin_dim "vecs.dim \<le> 1"
    using vecs.fin_dim_def apply force
    using A_generates_R vecs.dim_le1I by auto
  then show ?thesis unfolding field_extension.degree_def[OF field_extension_refl]
    using field_extension.fin_dim_nonzero[OF field_extension_refl] by simp
qed

lemma (in module) id_module_hom: "id \<in> module_hom R M M"
  unfolding module_hom_def by simp

find_theorems linear_map bij
term a_kernel
term kernel
term "linear_map.kerT"
find_theorems direct_sum vectorspace.dim

term bij_betw
lemma (in linear_map) emb_image_dim:
  assumes "inj_on T (carrier V)" \<comment> \<open>A module-monomorphism\<close>
  assumes V.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.dim = vectorspace.dim K (vs imT)"
  using assms inj_imp_dim_ker0 rank_nullity by linarith

lemma (in linear_map) iso_preserves_dim:
  assumes "bij_betw T (carrier V) (carrier W)" \<comment> \<open>A module-isomorphism\<close>
  assumes V.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "W.fin_dim" "V.dim = W.dim"
  using assms apply (simp add: bij_betw_def rank_nullity_main(2))
  using assms by (simp add: bij_betw_def dim_eq) \<comment> \<open>uses Missing\_VectorSpace (*rm*)\<close>

lemma (in mod_hom) mod_hom_the_inv:
  assumes bij: "bij_betw f (carrier M) (carrier N)"
  shows "mod_hom R N M (the_inv_into (carrier M) f)" (is "mod_hom R N M ?inv_f")
proof (unfold_locales; auto simp: module_hom_def)
  fix n1 n2 assume ns_carrier: "n1 \<in> carrier N" "n2 \<in> carrier N"
  then have ms_carrier: "?inv_f n1 \<in> carrier M" "?inv_f n2 \<in> carrier M"
    by (metis bij bij_betw_def order_refl the_inv_into_into)+
  from bij have "f (?inv_f (n1 \<oplus>\<^bsub>N\<^esub> n2)) = n1 \<oplus>\<^bsub>N\<^esub> n2"
    by (simp add: bij_betw_def f_the_inv_into_f ns_carrier)
  also from bij have "... = f(?inv_f n1) \<oplus>\<^bsub>N\<^esub> f(?inv_f n2)"
    by (simp add: bij_betw_def f_the_inv_into_f ns_carrier)
  also from bij[unfolded bij_betw_def] f_add have "\<dots> = f(?inv_f n1 \<oplus>\<^bsub>M\<^esub> ?inv_f n2)"
    by (simp add: ns_carrier the_inv_into_into)
  finally show "?inv_f (n1 \<oplus>\<^bsub>N\<^esub> n2) = ?inv_f n1 \<oplus>\<^bsub>M\<^esub> ?inv_f n2"
    using bij[unfolded bij_betw_def, THEN conjunct1, unfolded inj_on_def] ms_carrier
    by (simp add: bij[unfolded bij_betw_def] ns_carrier the_inv_into_into)
next
  fix r n assume "r \<in> carrier R" "n \<in> carrier N"
  then have "?inv_f n \<in> carrier M"
    by (simp add: bij[unfolded bij_betw_def] the_inv_into_into)
  have "?inv_f (r \<odot>\<^bsub>N\<^esub> n) = ?inv_f (r \<odot>\<^bsub>N\<^esub> f(?inv_f n))"
    by (simp add: bij[unfolded bij_betw_def] \<open>n \<in> carrier N\<close> f_the_inv_into_f)
  also have "... = ?inv_f (f (r \<odot>\<^bsub>M\<^esub> ?inv_f n))"
    by (simp add: \<open>r \<in> carrier R\<close> \<open>?inv_f n \<in> carrier M\<close>)
  finally show "?inv_f (r \<odot>\<^bsub>N\<^esub> n) = r \<odot>\<^bsub>M\<^esub> ?inv_f n"
    by (metis M.smult_closed bij[unfolded bij_betw_def] \<open>r \<in> carrier R\<close> \<open>?inv_f n \<in> carrier M\<close> the_inv_into_f_f)
qed (metis bij bij_betw_def order_refl the_inv_into_into)

corollary (in linear_map) linear_map_the_inv:
  "bij_betw T (carrier V) (carrier W) \<Longrightarrow> linear_map K W V (the_inv_into (carrier V) T)"
  by (meson linear_map_axioms linear_map_def mod_hom_the_inv)

lemma (in linear_map) iso_imports_dim: (* rm *)
  assumes "bij_betw T (carrier V) (carrier W)" \<comment> \<open>A module-isomorphism\<close>
  assumes W.fin_dim \<comment> \<open>Needed because otherwise \<^term>\<open>dim\<close> is not defined...\<close>
  shows "V.fin_dim" "V.dim = W.dim"
  by (simp_all add: linear_map.iso_preserves_dim[OF linear_map_the_inv] assms bij_betw_the_inv_into)

lemma (in vectorspace) zero_not_in_basis:
  "basis B \<Longrightarrow> \<zero>\<^bsub>V\<^esub> \<notin> B"
  by (simp add: basis_def vs_zero_lin_dep)

lemma direct_sum_dim:
  assumes "vectorspace K V" "vectorspace.fin_dim K V"
  assumes "vectorspace K W" "vectorspace.fin_dim K W"
  shows "vectorspace.fin_dim K (direct_sum V W)"
    and "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
proof -
  from assms obtain Bv Bw where
    Bv: "finite Bv" "vectorspace.basis K V Bv" and
    Bw: "finite Bw" "vectorspace.basis K W Bw"
    using vectorspace.finite_basis_exists (* blast loops, but not in sledgehammer oO *)
    by metis
  oops

lemma direct_sum_dim:
  assumes "vectorspace K V" "vectorspace.fin_dim K V"
  assumes "vectorspace K W" "vectorspace.fin_dim K W"
  shows "vectorspace.fin_dim K (direct_sum V W)"
    and "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
proof -
  interpret ds: vectorspace K "direct_sum V W"
    by (simp add: assms(1) assms(3) direct_sum_is_vs)

  txt \<open>embeddings into @{term "direct_sum V W"}:\<close>
  have lin1: "linear_map K V (direct_sum V W) (inj1 V W)"
    and lin2: "linear_map K W (direct_sum V W) (inj2 V W)"
    by (simp_all add: assms(1-4) inj1_linear inj2_linear)
  have inj1: "inj_on (inj1 V W) (carrier V)"
    and inj2: "inj_on (inj2 V W) (carrier W)"
    by (simp_all add: inj1_def inj2_def inj_on_def)

  from assms obtain Bv Bw where
    Bv: "finite Bv" "Bv \<subseteq> carrier V" "module.gen_set K V Bv" and
    Bw: "finite Bw" "Bw \<subseteq> carrier W" "module.gen_set K W Bw"
    by (meson vectorspace.fin_dim_def)
  let ?Bv = "inj1 V W ` Bv" and ?Bw = "inj2 V W ` Bw"
  let ?Bds = "?Bv \<union> ?Bw"
  from Bv(1) Bw(1) have "finite ?Bds"
    by simp_all
  moreover
    from Bv(2) Bw(2) have "?Bds \<subseteq> carrier (direct_sum V W)"
    unfolding direct_sum_def by (auto simp: inj1_def inj2_def)
      (meson assms vectorspace.span_closed vectorspace.span_zero)+
  moreover have "module.gen_set K (direct_sum V W) ?Bds"
    apply auto using calculation(2) ds.span_closed apply blast
  proof goal_cases
    case (1 a b)
    then have in_carrier: "a \<in> carrier V" "b \<in> carrier W"
      by (simp_all add: direct_sum_def)
    then obtain f A g B where lincomb1: "module.lincomb V f A = a" "finite A" "A\<subseteq>Bv" "f \<in> A\<rightarrow>carrier K"
      and lincomb2: "module.lincomb W g B = b" "finite B" "B\<subseteq>Bw" "g \<in> B\<rightarrow>carrier K"
      by (metis Bv Bw assms(1,3) module.finite_in_span subsetI vectorspace_def)
    have f: "f = f\<circ>fst \<circ> inj1 V W" and g: "g = g\<circ>snd \<circ> inj2 V W"
      unfolding inj1_def inj2_def by fastforce+
    note im_lincomb =
      linear_map.lincomb_linear_image[OF lin1 inj1, where a="f\<circ>fst" and A=A]
      linear_map.lincomb_linear_image[OF lin2 inj2, where a="g\<circ>snd" and A=B]
    let ?A = "inj1 V W ` A" and ?B = "inj2 V W ` B"
    have
      "ds.lincomb (f\<circ>fst) ?A = inj1 V W (module.lincomb V (f\<circ>fst \<circ> inj1 V W) A)"
      "ds.lincomb (g\<circ>snd) ?B = inj2 V W (module.lincomb W (g\<circ>snd \<circ> inj2 V W) B)"
      apply (auto intro!: im_lincomb)
      using Bv(2) lincomb1(3) apply blast
      apply (simp add: ds.coeff_in_ring2 inj1_def lincomb1(4))
      apply (simp add: lincomb1(2))
      using Bw(2) lincomb2(3) apply blast
      apply (simp add: ds.coeff_in_ring2 inj2_def lincomb2(4))
      by (simp add: lincomb2(2))
    moreover have "?A \<subseteq> ?Bv" "?B \<subseteq> ?Bw"
      by (simp_all add: image_mono lincomb1(3) lincomb2(3))
    moreover have "finite ?A" "finite ?B"
      by (simp_all add: lincomb1(2) lincomb2(2))
    moreover have "f\<circ>fst \<in> ?A \<rightarrow> carrier K" "g\<circ>snd \<in> ?B \<rightarrow> carrier K"
      unfolding inj1_def inj2_def using lincomb1(4) lincomb2(4)by auto
    ultimately have "inj1 V W a \<in> ds.span ?Bv" "inj2 V W b \<in> ds.span ?Bw"
      by (auto simp: f[symmetric] g[symmetric] ds.span_def lincomb1(1) lincomb2(1)) metis+
    then have "inj1 V W a \<in> ds.span ?Bds" "inj2 V W b \<in> ds.span ?Bds"
      by (meson contra_subsetD ds.span_is_monotone le_sup_iff order_refl)+
    then have "inj1 V W a \<oplus>\<^bsub>direct_sum V W\<^esub> inj2 V W b \<in> ds.span ?Bds"
      using ds.span_add1[OF \<open>?Bds \<subseteq> carrier (direct_sum V W)\<close>] by simp
    then show ?case unfolding inj1_def inj2_def
      unfolding direct_sum_def using assms(1,3)[unfolded vectorspace_def] in_carrier
      by (simp add: module_def abelian_group_def abelian_monoid.l_zero abelian_monoid.r_zero)
  qed
  ultimately show "ds.fin_dim" unfolding ds.fin_dim_def
    by meson

txt \<open>I had planned to adapt the proof above to also show that @{term ?Bds} is minimal, but it turned
  out too tiresome. Instead, I use @{thm[source] linear_map.rank_nullity[OF _ this]}:\<close>
  note inj1 inj2
  moreover have emb1: "inj1 V W ` carrier V = carrier V \<times> {\<zero>\<^bsub>W\<^esub>}"
    and emb2: "inj2 V W ` carrier W = {\<zero>\<^bsub>V\<^esub>} \<times> carrier W"
    unfolding inj1_def inj2_def by blast+
  ultimately
  have "vectorspace.dim K V = vectorspace.dim K (ds.vs (mod_hom.im V (inj1 V W)))"
    and "vectorspace.dim K W = vectorspace.dim K (ds.vs (mod_hom.im W (inj2 V W)))"
    by (simp_all add: lin1 lin2 assms(2,4) linear_map.emb_image_dim)
  then have propagate_dims: "vectorspace.dim K V = vectorspace.dim K (ds.vs (carrier V \<times> {\<zero>\<^bsub>W\<^esub>}))"
    "vectorspace.dim K W = vectorspace.dim K (ds.vs ({\<zero>\<^bsub>V\<^esub>} \<times> carrier W))" apply auto
    apply (metis emb1 lin1 linear_map_def mod_hom.im_def)
    apply (metis emb2 lin2 linear_map_def mod_hom.im_def)
    done

  have "ds.dim = vectorspace.dim K (ds.vs (carrier V \<times> {\<zero>\<^bsub>W\<^esub>})) + vectorspace.dim K (ds.vs ({\<zero>\<^bsub>V\<^esub>} \<times> carrier W))"
  proof -
    let ?T = "\<lambda>(v,w). (v,\<zero>\<^bsub>W\<^esub>)"
    interpret T: linear_map K "direct_sum V W" "direct_sum V W" ?T
      apply unfold_locales unfolding module_hom_def apply auto
      unfolding direct_sum_def apply auto
      using Module.module_def abelian_groupE(2) assms(3) vectorspace.axioms(1) apply blast
      apply (metis Module.module_def abelian_group_def abelian_monoid.r_zero
          abelian_monoid.zero_closed assms(3) vectorspace.axioms(1))
      by (metis (no_types, hide_lams) Module.module_def abelian_group.r_neg1 abelian_group_def
          abelian_monoid.r_zero abelian_monoid.zero_closed assms(3) module.smult_closed
          module.smult_r_distr vectorspace_def)
    have mod_hom_T: "mod_hom K (direct_sum V W) (direct_sum V W) ?T" by intro_locales
    have ker_is_V: "T.ker = {\<zero>\<^bsub>V\<^esub>} \<times> carrier W" unfolding T.ker_def
      unfolding mod_hom.ker_def[OF mod_hom_T] direct_sum_def apply auto
      using Module.module_def abelian_groupE(2) assms(1) vectorspace.axioms(1) by blast
    have "T.im = carrier V \<times> {\<zero>\<^bsub>W\<^esub>}" unfolding T.im_def mod_hom.im_def[OF mod_hom_T]
      unfolding direct_sum_def apply auto
    proof -
      fix a :: 'c
      assume a1: "a \<in> carrier V"
      have f2: "(fst \<zero>\<^bsub>direct_sum V W\<^esub>, \<zero>\<^bsub>W\<^esub>) = \<zero>\<^bsub>direct_sum V W\<^esub>"
        by (metis (no_types) T.f0_is_0 split_def)
      have "carrier V \<times> carrier W = carrier (direct_sum V W)"
        by (simp add: direct_sum_def)
      then have "\<zero>\<^bsub>W\<^esub> \<in> carrier W"
        using f2 by (metis (no_types) ds.M.zero_closed mem_Sigma_iff)
      then show "(a, \<zero>\<^bsub>W\<^esub>) \<in> (\<lambda>(c, e). (c, \<zero>\<^bsub>W\<^esub>)) ` (carrier V \<times> carrier W)"
        using a1 by auto
    qed
    with \<open>ds.fin_dim\<close> ker_is_V show ?thesis
      using T.rank_nullity by simp
  qed
  with propagate_dims show "vectorspace.dim K (direct_sum V W) = vectorspace.dim K V + vectorspace.dim K W"
    by simp
qed (* to-do: use \<^sub> in part 1*)

definition "zvs = \<comment> \<open>to-do: add type\<close> \<comment> \<open>use @{const undefined}?\<close>
  \<lparr>carrier={\<some>_.True}, monoid.mult=undefined, one=undefined, zero=\<some>_.True, add=\<lambda>_ _.\<some>_.True, smult=\<lambda>_ _.\<some>_.True\<rparr>"

lemma (in cring) module_zvs: "module R zvs" unfolding zvs_def
  by unfold_locales (simp_all add: Units_def)

lemma zvs_simps[simp]:
"carrier zvs = {\<some>_.True}"
"zero zvs = (\<some>_.True)"
"add zvs = (\<lambda>_ _.\<some>_.True)"
  by (simp_all add: zvs_def)

lemma (in field) vectorspace_zvs: "vectorspace R zvs"
  by (simp add: field_axioms module_zvs vectorspace_def)

lemma (in module) submodule_zsm: "submodule {\<zero>\<^bsub>M\<^esub>} R M"
  using M.r_neg submoduleI by fastforce

lemma (in module) module_zsm: "module R (md {\<zero>\<^bsub>M\<^esub>})"
  by (simp add: submodule_is_module submodule_zsm)

lemma (in vectorspace) vectorspace_zss: "vectorspace K (vs {\<zero>\<^bsub>V\<^esub>})"
  using module_zsm vectorspace_axioms vectorspace_def by blast

lemma (in subspace) dim0_zss:
  "vectorspace.fin_dim K V \<Longrightarrow> vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = 0 \<Longrightarrow> W = {\<zero>\<^bsub>V\<^esub>}"
proof -
  have vs: "vectorspace K (V\<lparr>carrier:=W\<rparr>)"
    by (simp add: subspace_axioms vectorspace.subspace_is_vs vs)
  assume "vectorspace.fin_dim K V" "vectorspace.dim K (V\<lparr>carrier:=W\<rparr>) = 0"
  with vs have "vectorspace.basis K (V\<lparr>carrier:=W\<rparr>) {}"
    by (simp add: corollary_5_16(1) module.finite_lin_indpt2 vectorspace.dim_li_is_basis vectorspace_def)
  then show ?thesis
    using vectorspace.basis_def vectorspace.span_empty vs by fastforce
qed

lemma (in vectorspace) basis_zss: "vectorspace.basis K (vs {\<zero>\<^bsub>V\<^esub>}) {}"
  by (simp add: LinearCombinations.module.finite_lin_indpt2 span_empty module_zsm
      span_li_not_depend(1) submodule_zsm vectorspace.basis_def vectorspace_zss)

corollary (in vectorspace) zss_dim:
  "vectorspace.fin_dim K (vs {\<zero>\<^bsub>V\<^esub>})" "vectorspace.dim K (vs {\<zero>\<^bsub>V\<^esub>}) = 0"
  using basis_zss vectorspace.basis_def vectorspace.fin_dim_def vectorspace_zss apply fastforce
  using basis_zss vectorspace.dim_basis vectorspace_zss by fastforce

lemma (in field) dim_zvs: "vectorspace.dim R zvs = 0"
  unfolding vectorspace.dim_def[OF vectorspace_zvs] apply simp
proof -
  have "\<exists>C. finite C \<and> card C = 0 \<and> C \<subseteq> {\<some>_.True} \<and> LinearCombinations.module.span R zvs C = {\<some>_.True}"
by (metis (no_types) vectorspace.span_empty[OF vectorspace_zvs] card_empty finite.emptyI subset_insertI zvs_simps(2))
  then show "(LEAST n. \<exists>C. finite C \<and> card C = n \<and> C \<subseteq> {\<some>_.True} \<and> LinearCombinations.module.span R zvs C = {\<some>_.True}) = 0"
  proof -
    obtain DD :: "'d set" where
      "(\<exists>v0. finite v0 \<and> card v0 = 0 \<and> v0 \<subseteq> {SOME uu. True::'d} \<and> LinearCombinations.module.span R zvs v0 = {SOME uu. True}) = (finite DD \<and> card DD = 0 \<and> DD \<subseteq> {SOME uu. True} \<and> LinearCombinations.module.span R zvs DD = {SOME uu. True})"
      by (metis (no_types))
    then have "finite DD \<and> card DD = 0 \<and> DD \<subseteq> {SOME d. True} \<and> LinearCombinations.module.span R zvs DD = {SOME d. True}"
      by (metis \<open>\<exists>C. finite C \<and> card C = 0 \<and> C \<subseteq> {SOME _. True} \<and> LinearCombinations.module.span R zvs C = {SOME _. True}\<close>) (* failed *)
    then have "\<exists>D. finite D \<and> card D = 0 \<and> D \<subseteq> {SOME d. True::'d} \<and> LinearCombinations.module.span R zvs D = {SOME d. True}"
      by blast
    then show ?thesis
      using Least_eq_0 by presburger
  qed
qed

lemma (in vectorspace) dim_0_trivial:
  "fin_dim \<Longrightarrow> dim = 0 \<Longrightarrow> carrier V = {\<zero>\<^bsub>V\<^esub>}"
  using dim_greater_0 by linarith

lemma (in subring) module_wrt_subring:
  "module R M \<Longrightarrow> module (R\<lparr>carrier:=H\<rparr>) M"
  unfolding module_def module_axioms_def by (simp add: cring.Subring_cring subring_axioms)

lemma (in subfield) vectorspace_wrt_subfield:
  "vectorspace L V \<Longrightarrow> vectorspace (L\<lparr>carrier:=K\<rparr>) V" unfolding vectorspace_def
  by (auto simp: module_wrt_subring ring.subfield_iff(2) cring.axioms(1) module.axioms(1) subfield_axioms)

lemma (in subring) hom_wrt_subring:
  "h \<in> module_hom R M N \<Longrightarrow> h \<in> module_hom (R\<lparr>carrier:=H\<rparr>) M N"
  by (simp add: LinearCombinations.module_hom_def)

lemma (in subfield) linear_wrt_subfield:
  "linear_map L M N T \<Longrightarrow> linear_map (L\<lparr>carrier:=K\<rparr>) M N T" unfolding linear_map_def
  by (auto simp: vectorspace_wrt_subfield hom_wrt_subring mod_hom_axioms_def mod_hom_def module_wrt_subring)

lemma (in module) lincomb_restrict_simp[simp, intro]:
  assumes U: "U \<subseteq> carrier M"
      and a: "a : U \<rightarrow> carrier R" (* needed? *)
  shows "lincomb (restrict a U) U = lincomb a U"
  by (meson U a lincomb_cong restrict_apply')

abbreviation "fdvs K V \<equiv> vectorspace K V \<and> vectorspace.fin_dim K V"

text \<open>The following corresponds to theorem 11.7 of \<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LADS_no_dates.pdf#section.0.11\<close>\<close>
lemma (in vectorspace) decompose_step: (* use obtains? *)
  assumes fin_dim
  assumes "dim > 0"
  shows "\<exists>h V'. linear_map K V (direct_sum (vs_of K) (V\<lparr>carrier:=V'\<rparr>)) h
    \<and> bij_betw h (carrier V) (carrier K \<times> V')
    \<and> subspace K V' V
    \<and> vectorspace.dim K (V\<lparr>carrier:=V'\<rparr>) = dim - 1"
proof - \<comment> \<open>Possibly easier if the map definition is swapped as in Kemper's proof.\<close>
  from assms obtain B where B: "basis B" "card B > 0"
    using dim_basis finite_basis_exists by auto
  then obtain b where "b \<in> B"
    by fastforce
  let ?B = "B - {b}"
  have liB: "lin_indpt ?B" and BiV: "?B \<subseteq> carrier V" "finite ?B"
    apply (meson B(1) Diff_subset basis_def supset_ld_is_ld)
    using B(1) basis_def apply blast using B
    using card_infinite neq0_conv by blast
  let ?V = "vs (span ?B)"
  note goal_3 = span_is_subspace[OF BiV(1)]
  then interpret vs_span_B: vectorspace K ?V
    using subspace_is_vs by blast
  from liB have liB': "vs_span_B.lin_indpt ?B"
    by (simp add: BiV in_own_span span_is_subspace span_li_not_depend(2))
  then have new_basis: "vs_span_B.basis ?B"
    by (simp add: BiV(1) in_own_span span_is_submodule span_li_not_depend(1) vs_span_B.basis_def)
  moreover have "card ?B = dim - 1"
    using B(1) BiV(2) \<open>b \<in> B\<close> dim_basis by auto
  ultimately have "vs_span_B.fin_dim" and goal_4: "vs_span_B.dim = dim - 1"
    unfolding vs_span_B.fin_dim_def apply -
     apply (metis BiV(2) vectorspace.basis_def vs_span_B.vectorspace_axioms)
    using BiV(2) vs_span_B.dim_basis by presburger
  define coeffs where "coeffs \<equiv> the_inv_into (B \<rightarrow>\<^sub>E carrier K) (\<lambda>a. lincomb a B)"
  have coeffs_unique: "\<exists>!c. c \<in> B \<rightarrow>\<^sub>E carrier K \<and> lincomb c B = v" if "v \<in> carrier V" for v
    using basis_criterion by (metis (full_types) B basis_def card_ge_0_finite that)
  have okese: "coeffs v \<in> B \<rightarrow>\<^sub>E carrier K" "v = lincomb (coeffs v) B" if "v \<in> carrier V" for v
    using that theI'[OF coeffs_unique] by (simp_all add: coeffs_def the_inv_into_def)
  have c_sum: "coeffs (v1\<oplus>\<^bsub>V\<^esub>v2) \<in> B \<rightarrow>\<^sub>E carrier K"
    "v1\<oplus>\<^bsub>V\<^esub>v2 = lincomb (coeffs (v1\<oplus>\<^bsub>V\<^esub>v2)) B" if "v1 \<in> carrier V" "v2 \<in> carrier V" for v1 v2
    apply (simp add: okese(1) that(1) that(2))
    apply (simp add: okese(2) that(1) that(2))
    done
  have c_sum': "lincomb (\<lambda>v. coeffs v1 v \<oplus>\<^bsub>K\<^esub> coeffs v2 v) B = lincomb (coeffs (v1\<oplus>\<^bsub>V\<^esub>v2)) B" if "v1 \<in> carrier V" "v2 \<in> carrier V" for v1 v2
  proof -
    note b = okese(2)[OF that(1)] okese(2)[OF that(2)]
    note a = okese(1)[OF that(1)] okese(1)[OF that(2)]
    then have "coeffs v1 \<in> B \<rightarrow> carrier K" "coeffs v2 \<in> B \<rightarrow> carrier K"
      by blast+
    note lincomb_sum[OF _ _ this, folded b]
    then show ?thesis
      using B(1) B(2) basis_def c_sum(2) that(1) that(2) by force
  qed
  let ?T = "\<lambda>v. (coeffs v b, lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs v bv) (B - {b}))"
  have goal_1: "linear_map K V (direct_sum (vs_of K) ?V) ?T"
    unfolding linear_map_def apply auto
    apply (simp add: vectorspace_axioms)
    unfolding mod_hom_def module_hom_def mod_hom_axioms_def apply auto
    using direct_sum_is_vs field_is_vecs_over_itself vs_span_B.vectorspace_axioms apply blast
    apply (simp add: module.module_axioms)
    using direct_sum_is_module field_is_vecs_over_itself vectorspace_def vs_span_B.module_axioms apply blast
    unfolding direct_sum_def apply auto
    using \<open>b \<in> B\<close> okese(1) apply fastforce
    using vs_span_B.lincomb_closed[simplified]
        apply (smt BiV DiffE finite_span PiE_mem Pi_I coeff_in_ring insertCI mem_Collect_eq module_axioms okese(1))
  proof -
    fix m1 m2
    assume mcV: "m1 \<in> carrier V" "m2 \<in> carrier V"
    then have B_to_K_map: "(\<lambda>bv. coeffs m1 bv \<oplus>\<^bsub>K\<^esub> coeffs m2 bv) \<in> B \<rightarrow> carrier K"
      by (smt PiE_mem Pi_I R.add.m_closed okese(1))
    let ?restricted = "restrict (\<lambda>bv. coeffs m1 bv \<oplus>\<^bsub>K\<^esub> coeffs m2 bv) B"
    have "lincomb (coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2)) B = lincomb ?restricted B"
      using mcV B(1) basis_def c_sum' B_to_K_map by auto
    moreover have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow>\<^sub>E carrier K"
      "?restricted \<in> B \<rightarrow>\<^sub>E carrier K"
       apply (simp add: mcV c_sum(1))
      by (simp add: B_to_K_map)
    ultimately
      have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) = ?restricted"
      using basis_criterion
      by (metis (no_types, lifting) mcV B(1) B(2) M.add.m_closed basis_def c_sum(2)
          card_ge_0_finite)
    then have distr: "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) b = coeffs m1 b \<oplus>\<^bsub>K\<^esub> coeffs m2 b" if "b \<in> B" for b
      by (simp add: that)
    then show "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) b = coeffs m1 b \<oplus>\<^bsub>K\<^esub> coeffs m2 b"
      by (simp add: \<open>b \<in> B\<close>)
    have [simp]: "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else xyz bv) (B-{b})
      = lincomb xyz (B-{b})" if "xyz \<in> B \<rightarrow> carrier K" for xyz
      using that
      by (smt BiV(1) Diff_not_in Pi_split_insert_domain \<open>b \<in> B\<close> insert_Diff lincomb_cong)
    have "coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow> carrier K"
      "coeffs m1 \<in> B \<rightarrow> carrier K"
      "coeffs m2 \<in> B \<rightarrow> carrier K"
      using \<open>coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) \<in> B \<rightarrow>\<^sub>E carrier K\<close> apply auto[1]
      using mcV okese(1) by fastforce+
    with distr show "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs (m1 \<oplus>\<^bsub>V\<^esub> m2) bv) (B-{b})
      = lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m1 bv) (B-{b})
      \<oplus>\<^bsub>V\<^esub> lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m2 bv) (B-{b})" apply simp
      by (smt BiV DiffE Pi_split_insert_domain \<open>b \<in> B\<close> insert_Diff lincomb_cong lincomb_sum)
(* next *)
    fix r m
    assume rK: "r \<in> carrier K" and mV: "m \<in> carrier V"
    have sane: "(\<lambda>bv. r \<otimes>\<^bsub>K\<^esub> coeffs m bv) \<in> B \<rightarrow> carrier K"
      using mV okese(1) rK by fastforce
    let ?restricted = "\<lambda>bv\<in>B. r \<otimes>\<^bsub>K\<^esub> coeffs m bv"
    have "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) B = lincomb ?restricted B"
      by (metis B(1) PiE_restrict basis_def lincomb_distrib lincomb_restrict_simp mV okese rK
          restrict_PiE sane smult_closed)
    moreover have "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow>\<^sub>E carrier K" "?restricted \<in> B \<rightarrow>\<^sub>E carrier K"
       apply (simp add: mV okese(1) rK)
      by (simp add: sane)
    ultimately have "coeffs (r \<odot>\<^bsub>V\<^esub> m) = ?restricted"
      by (metis coeffs_unique mV okese(2) rK smult_closed)
    then have scale: "coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b" if "b \<in> B" for b
      by (simp add: that)
    then show "coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b"
      using \<open>b \<in> B\<close> by blast
    have "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow> carrier K"
      "coeffs m \<in> B \<rightarrow> carrier K"
      using \<open>coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow>\<^sub>E carrier K\<close> apply auto[1]
      using mV okese(1) by fastforce
    with scale \<open>r \<in> carrier K\<close> show "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs (r \<odot>\<^bsub>V\<^esub> m) bv) (B-{b}) =
    r \<odot>\<^bsub>V\<^esub> lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else coeffs m bv) (B-{b})"
    proof simp
      assume a1: "coeffs (r \<odot>\<^bsub>V\<^esub> m) \<in> B \<rightarrow> carrier K"
      assume a2: "r \<in> carrier K"
      assume a3: "coeffs m \<in> B \<rightarrow> carrier K"
      assume a4: "\<And>b. b \<in> B \<Longrightarrow> coeffs (r \<odot>\<^bsub>V\<^esub> m) b = r \<otimes>\<^bsub>K\<^esub> coeffs m b"
      have f5: "\<forall>C Ca f fa. (C \<noteq> Ca \<or> \<not> C \<subseteq> carrier V \<or> (\<exists>c. c \<in> C \<and> f c \<noteq> fa c) \<or> fa \<notin> Ca \<rightarrow> carrier K) \<or> lincomb f C = lincomb fa Ca"
        by (metis (no_types) lincomb_cong)
      obtain cc :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'c set \<Rightarrow> 'c" where
        "\<forall>x0 x1 x3. (\<exists>v4. v4 \<in> x3 \<and> x1 v4 \<noteq> x0 v4) = (cc x0 x1 x3 \<in> x3 \<and> x1 (cc x0 x1 x3) \<noteq> x0 (cc x0 x1 x3))"
        by moura
      then have f6: "\<forall>C Ca f fa. (C \<noteq> Ca \<or> \<not> C \<subseteq> carrier V \<or> cc fa f C \<in> C \<and> f (cc fa f C) \<noteq> fa (cc fa f C) \<or> fa \<notin> Ca \<rightarrow> carrier K) \<or> lincomb f C = lincomb fa Ca"
        using f5 by presburger
      have f7: "insert b (B - {b}) = B"
        using \<open>b \<in> B\<close> by blast
      have f8: "\<forall>f c C fa. (f \<in> Pi (insert (c::'c) C) fa) = (f \<in> Pi C fa \<and> (f c::'a) \<in> fa c)"
        by blast
      then have f9: "cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) \<in> B - {b} \<and> r \<otimes>\<^bsub>K\<^esub> coeffs m (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<noteq> coeffs (r \<odot>\<^bsub>V\<^esub> m) (cc (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b})) \<or> lincomb (\<lambda>c. r \<otimes>\<^bsub>K\<^esub> coeffs m c) (B - {b}) = lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b})"
        using f7 f6 a1 by (metis (no_types) \<open>B - {b} \<subseteq> carrier V\<close>)
      have "coeffs m \<in> B - {b} \<rightarrow> carrier K \<and> coeffs m b \<in> carrier K"
        using f8 f7 a3 by (metis (no_types))
      then show "lincomb (coeffs (r \<odot>\<^bsub>V\<^esub> m)) (B - {b}) = r \<odot>\<^bsub>V\<^esub> lincomb (coeffs m) (B - {b})"
        using f9 a4 a2 \<open>B - {b} \<subseteq> carrier V\<close> lincomb_distrib by fastforce
    qed
  qed
  then interpret linmap: linear_map K V "direct_sum (vs_of K) ?V" ?T .
  {
    fix v
    assume "v \<in> carrier V"
    let ?c = "coeffs v"
    have a: "?c \<in> B \<rightarrow>\<^sub>E carrier K" "v = lincomb ?c B"
      using okese by (simp add: \<open>v \<in> carrier V\<close>)+
    have c0s: "v = \<zero>\<^bsub>V\<^esub> \<Longrightarrow> coeffs v \<in> B \<rightarrow> {\<zero>\<^bsub>K\<^esub>}"
      by (metis (no_types, lifting) B(1) B(2) Diff_cancel Diff_eq_empty_iff PiE_mem Pi_I a(1) a(2) basis_def card_ge_0_finite not_lindepD)
    have "lincomb (\<lambda>bv. if bv = b then \<zero>\<^bsub>K\<^esub> else ?c bv) ?B = \<zero>\<^bsub>V\<^esub> \<longleftrightarrow> ?c \<in> ?B\<rightarrow>{\<zero>\<^bsub>K\<^esub>}"
      apply standard
      using not_lindepD
       apply (smt BiV(2) Diff_cancel Diff_eq_empty_iff Diff_iff PiE_mem Pi_I a(1) liB lin_dep_crit singletonI)
      by (smt BiV(1) Diff_not_in Pi_cong lincomb_zero)
    then have "?T v = \<zero>\<^bsub>direct_sum (vs_of K) (vs (span ?B))\<^esub> \<longrightarrow> v = \<zero>\<^bsub>V\<^esub>"
      unfolding direct_sum_def by auto (smt B(1) Pi_split_insert_domain \<open>b \<in> B\<close> a(2) insertCI
          insert_Diff lincomb_zero vectorspace.basis_def vectorspace_axioms)
  }
  then have "linmap.kerT = {\<zero>\<^bsub>V\<^esub>}"
    unfolding linmap.ker_def by auto
  then have goal_2a: "inj_on ?T (carrier V)"
    by (simp add: linmap.Ke0_imp_inj)
  have "vectorspace.fin_dim K (vs_of K)" "vectorspace.dim K (vs_of K) = 1"
    using trivial_degree[unfolded field_extension.degree_def[OF field_extension_refl]]
    apply auto[] apply presburger
  proof -
    have "\<forall>p. p\<lparr>carrier := carrier p\<rparr> = p"
      by fastforce
    then show "vectorspace.dim K (vs_of K) = 1"
      using field_extension.degree_def field_extension_refl by fastforce
  qed
  with \<open>vs_span_B.fin_dim\<close> have "linmap.W.dim = 1 + vs_span_B.dim"
    by (simp add: direct_sum_dim(2) field_is_vecs_over_itself vs_span_B.vectorspace_axioms)
  also from goal_4 have "\<dots> = dim" using \<open>dim > 0\<close> by force
  also have "\<dots> = vectorspace.dim K (linmap.W.vs linmap.im)"
    using assms(1) linmap.emb_image_dim goal_2a by blast
  finally have "carrier (direct_sum (vs_of K) ?V) = linmap.imT"
    using subspace.corollary_5_16(3)[OF linmap.imT_is_subspace] \<open>vectorspace.fin_dim K (vs_of K)\<close>
      \<open>vs_span_B.fin_dim\<close> direct_sum_dim(1) field_is_vecs_over_itself vs_span_B.vectorspace_axioms
    by auto
  note goal_2b = this[unfolded linmap.im_def direct_sum_def, simplified]
  from goal_1 goal_2a goal_2b goal_3 goal_4 show ?thesis
    unfolding bij_betw_def by blast
qed

proposition tower_rule: \<comment> \<open>Maybe this works better when following the comment on line 500 here: @{url
  "https://bitbucket.org/isa-afp/afp-devel/src/d41812ff2a3f59079e08709845d64deed6e2fe15/thys/VectorSpace/LinearCombinations.thy"}\<close>
  assumes "Subrings.subfield K (M\<lparr>carrier:=L\<rparr>)" "Subrings.subfield L M" "field M" \<comment> \<open>Relax to ring?\<close>
  shows degree_multiplicative:
    "field_extension.degree M K = field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
proof -
  \<comment> \<open>to-do: use more \<^theory_text>\<open>interpret\<close>, especially in the "finite" part. Maybe first define a locale
  \<open>fin_dim_vec_space\<close>?\<close>

  let ?L = "M\<lparr>carrier:=L\<rparr>" and ?K = "M\<lparr>carrier:=K\<rparr>"

  have "K \<subseteq> L"
    using subfield_def assms(1) subfieldE(3) by force
  then have "K \<subseteq> carrier M"
    by (meson assms(2) order.trans subfieldE(3))
  then have M_over_K: "field_extension M K"
    by (metis (no_types, lifting) field.generate_fieldE(1) subfield.axioms \<open>K \<subseteq> L\<close> assms(1-3)
        field.generate_fieldI field.generate_field_is_field field.subfield_gen_equality
        field_extension.intro monoid.surjective partial_object.update_convs(1) subfieldE(3)
        subset_refl)

  have "\<not>field_extension.finite M K" if "\<not>field_extension.finite ?L K"
  proof
    from M_over_K interpret enclosing: vectorspace ?K "vs_of M"
      by (simp add: field_extension.vectorspace_satisfied)
    have subspace: "subspace ?K L (vs_of M)"
      unfolding subspace_def apply (simp add: enclosing.vectorspace_axioms)
      apply (rule enclosing.module.module_incl_imp_submodule)
      apply (simp add: subfield.axioms assms(2) field_extension.axioms(1)
          subfieldE(3))
      subgoal proof -
      from assms have "field_extension ?L K"
        using subfield.intro Subrings.ring.subfield_iff(2) cring_def domain_def field_def
          field_extension.intro by blast
      note field_extension.vectorspace_satisfied[OF this]
      then show ?thesis by (auto simp: vectorspace_def)
    qed done
    assume enclosing.fin_dim
    with that show False
      using subspace.corollary_5_16(1)[OF subspace] by simp
  qed

  moreover have "\<not>field_extension.finite M K" if "\<not>field_extension.finite M L"
  proof
    interpret a: module ?L "vs_of M"
      by (simp add: subfield_def assms(2-3) field_extension.vectorspace_satisfied field_extension_def vectorspace.axioms(1))
    from that have "\<not>(\<exists>\<comment>\<open>Avoid latex dependency\<close>B. finite B \<and> B \<subseteq> carrier M \<and> a.span B = carrier M)"
      using subfield_def assms(2-3) field_extension.vectorspace_satisfied
        field_extension_def vectorspace.fin_dim_def[of ?L "vs_of M", simplified] by blast
    then have "\<And>B. finite B \<Longrightarrow> B \<subseteq> carrier M \<Longrightarrow> a.span B \<subset> carrier M"
      using a.span_is_subset2 by auto
    note 1 = this[unfolded a.span_def a.lincomb_def, simplified]
    interpret b: module ?K "vs_of M"
      by (simp add: M_over_K field_extension.vectorspace_satisfied vectorspace.axioms(1))
    assume "field_extension.finite M K"
    then have "\<exists>B. finite B \<and> B \<subseteq> carrier M \<and> b.span B = carrier M"
      using M_over_K field_extension.vectorspace_satisfied vectorspace.fin_dim_def by fastforce
    note 2 = this[unfolded b.span_def b.lincomb_def, simplified]
    from \<open>K \<subseteq> L\<close> have "f \<in> A \<rightarrow> L" if "f \<in> A \<rightarrow> K" for f and A::"'a set"
      using that by auto
    with 1 2 show False
      by (smt mem_Collect_eq psubsetE subsetI)
  qed

  moreover {
    assume fin: "field_extension.finite M L" "field_extension.finite ?L K"
    define cM where "cM = carrier M" (*"vs_of M = vs_of M\<lparr>carrier:=cM\<rparr>"*)
      \<comment> \<open>This definition is needed: Only the carrier should be "arbitrary" in the induction.\<close>
    have m_facts: "vectorspace ?L (vs_of M\<lparr>carrier := cM\<rparr>)" "vectorspace.fin_dim ?L (vs_of M\<lparr>carrier := cM\<rparr>)"
      "vectorspace ?K (vs_of M\<lparr>carrier := cM\<rparr>)"
      using subfield_def assms(2-3) field.field_is_vecs_over_itself subfield.vectorspace_wrt_subfield
        apply (simp add: subfield_def field.field_is_vecs_over_itself subfield.vectorspace_wrt_subfield cM_def)
      apply (simp add: cM_def fin(1))
      by (simp add: M_over_K cM_def field_extension.vectorspace_satisfied)
    from m_facts \<comment> \<open>The assumptions with \<^term>\<open>M\<close> in it. to-do: remove TrueI\<close>
    have "vectorspace.fin_dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) \<and> vectorspace.dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) =
      vectorspace.dim ?L (vs_of M\<lparr>carrier := cM\<rparr>) * vectorspace.dim ?K (vs_of ?L)"
    proof (induction "vectorspace.dim ?L (vs_of M\<lparr>carrier := cM\<rparr>)" arbitrary: cM)
      case 0
      then have "carrier (vs_of M\<lparr>carrier := cM\<rparr>) = {\<zero>\<^bsub>M\<^esub>}"
        using vectorspace.dim_0_trivial by fastforce
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
      note a = this[simplified]
      let ?M' = "vs_of M\<lparr>carrier:=cM'\<rparr>"
      have applied_IH: "vectorspace.fin_dim ?K ?M' \<and> vectorspace.dim ?K ?M' =
        vectorspace.dim ?L ?M' * vectorspace.dim ?K (vs_of ?L)"
        apply (rule Suc.hyps(1))
           apply auto
        using Suc.hyps(2) a(4) apply simp
        using Suc.prems(1) hM'(3) partial_object.update_convs(1) vectorspace.subspace_is_vs apply fastforce
        using Suc.prems(2) a(3) subspace.corollary_5_16(1) apply force
        using a(3) assms(1) subfield.vectorspace_wrt_subfield[unfolded subfield_def, OF assms(1)] Suc(3)
        by (smt partial_object.surjective partial_object.update_convs(1) vectorspace.subspace_is_vs)
      from hM'(1) have lin_K_map: "linear_map ?K (vs_of M\<lparr>carrier:=cM\<rparr>) (direct_sum (vs_of ?L) ?M') h"
        using subfield.linear_wrt_subfield[unfolded subfield_def, OF assms(1)] by auto
      have "vectorspace.fin_dim ?K (direct_sum (vs_of ?L) ?M')"
        by (smt Field_Extension.subfield_def a(3) applied_IH assms(1) direct_sum_dim(1)
            field.field_is_vecs_over_itself fin(2) monoid.surjective partial_object.update_convs(1)
            subfield.vectorspace_wrt_subfield subspace.vs vectorspace.subspace_is_vs
            vectorspace_def)
      then have goal1: "vectorspace.fin_dim ?K (vs_of M\<lparr>carrier:=cM\<rparr>)"
        using linear_map.iso_imports_dim(1)[OF lin_K_map]
      proof -
        have "bij_betw h (carrier (vs_of M\<lparr>carrier := cM\<rparr>)) (carrier (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>)))"
          by (simp add: direct_sum_def hM'(2))
        then show ?thesis
          using \<open>\<lbrakk>bij_betw h (carrier (vs_of M\<lparr>carrier := cM\<rparr>)) (carrier (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))); vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<rbrakk> \<Longrightarrow> vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>)\<close> \<open>vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<close> by linarith
      qed
      with linear_map.iso_imports_dim[OF lin_K_map] subspace.corollary_5_16(1) hM'(2) have
        "vectorspace.dim ?K (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim ?K (direct_sum (vs_of ?L) ?M')"
      proof -
        have "\<forall>A m p. carrier (p::\<lparr>carrier :: 'a set, monoid.mult :: _ \<Rightarrow> _ \<Rightarrow> _, one :: _, zero :: _, add :: _ \<Rightarrow> _ \<Rightarrow> _, smult :: 'a \<Rightarrow> _ \<Rightarrow> _\<rparr>) \<times> A = carrier (direct_sum p \<lparr>carrier = A, \<dots> = m::\<lparr>monoid.mult :: 'a \<Rightarrow> 'a \<Rightarrow> 'a, one :: 'a, zero :: _, add :: _ \<Rightarrow> _ \<Rightarrow> _, smult :: _ \<Rightarrow> _ \<Rightarrow> _\<rparr>\<rparr>)"
          by (simp add: direct_sum_def)
        then show ?thesis
          using \<open>\<lbrakk>bij_betw h (carrier (vs_of M\<lparr>carrier := cM\<rparr>)) (carrier (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))); vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<rbrakk> \<Longrightarrow> vectorspace.dim (M\<lparr>carrier := K\<rparr>) (vs_of M\<lparr>carrier := cM\<rparr>) = vectorspace.dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<close> \<open>bij_betw h cM (L \<times> cM')\<close> \<open>vectorspace.fin_dim (M\<lparr>carrier := K\<rparr>) (direct_sum (vs_of (M\<lparr>carrier := L\<rparr>)) (vs_of M\<lparr>carrier := cM'\<rparr>))\<close> by fastforce
      qed
      also have "\<dots> = vectorspace.dim ?K (vs_of ?L) + vectorspace.dim ?K ?M'"
      proof -
        have "\<forall>p f A. carrier_update f (p::('a, 'b) ring_scheme)\<lparr>carrier := A\<rparr> = p\<lparr>carrier := A\<rparr>"
          by simp
        then have "vectorspace.fin_dim ?K (vs_of ?L) \<and> vectorspace ?K (vs_of ?L) \<and> vectorspace ?K ?M'"
          by (metis (no_types) Field_Extension.subfield_def a(3) assms(1) field_extension.intro field_extension.vectorspace_satisfied fin(2) partial_object.update_convs(1) subfield.vectorspace_wrt_subfield subspace.vs vectorspace.subspace_is_vs vectorspace_def)
        then show ?thesis
          using applied_IH direct_sum_dim(2) by blast
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
  }

  moreover
  show ?thesis
  proof -
    have f1: "ring M"
      using assms(3) cring.axioms(1) domain_def field_def by blast
    then have "Field_Extension.subfield K ?L"
      by (metis (no_types) ring.subfield_iff(1) Subrings.ring.subfield_iff(2) assms(1-2) cring.axioms(1) domain_def field_def subfieldE(3))
    then show ?thesis using f1
      by (simp add: Field_Extension.ring.subfield_iff(1) M_over_K Subrings.ring.subfield_iff(2) assms(2-3) calculation field_extension.degree_def field_extension.intro subfieldE(3))
  qed
qed


subsection \<open>Polynomial Divisibility\<close>

lemma (in field_extension) UP_univ_prop_exists: "\<alpha> \<in> carrier L \<Longrightarrow> UP_of_field_extension \<alpha> L K"
  unfolding UP_of_field_extension_def apply auto
  apply (metis UP_cring.intro UP_pre_univ_prop.intro UP_univ_prop.intro UP_univ_prop_axioms.intro
      cring_ring_hom_cring is_cring ring_hom_cring_def)
  by (simp add: field_extension_axioms)

definition (in UP_of_field_extension) algebraic where
  "algebraic \<longleftrightarrow> (\<exists>p \<in> carrier P - {\<zero>}. Eval p = \<zero>\<^bsub>L\<^esub>)"

definition (in field_extension) algebraic where
  "algebraic \<longleftrightarrow> (\<forall>\<alpha> \<in> carrier L. UP_of_field_extension.algebraic \<alpha> L K)"

definition (in UP_ring) "monic p \<longleftrightarrow> lcoeff p = \<one>"

lemma (in UP_domain) monic_nonzero: "monic p \<Longrightarrow> p \<noteq> \<zero>\<^bsub>P\<^esub>"
  unfolding monic_def by auto

context UP_of_field_extension begin

definition irr where (* mv in algebraic context? *)
  "irr = arg_min (deg (L\<lparr>carrier:=K\<rparr>)) (\<lambda>p. p \<in> carrier P \<and> monic p \<and> Eval p = \<zero>\<^bsub>L\<^esub>)"

lemmas Eval_smult = Eval_smult[simplified]
lemmas coeff_smult = coeff_smult[simplified]
lemmas monom_mult_is_smult = monom_mult_is_smult[simplified]
lemmas monom_mult_smult = monom_mult_smult[simplified]
lemmas coeff_monom_mult = coeff_monom_mult[simplified]
lemmas coeff_mult = coeff_mult[simplified] (* rm all *)

lemma (in cring) test: "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> PIdl a = PIdl b \<Longrightarrow> a \<sim> b"
  by (simp add: associated_iff_same_ideal)

lemma Units_poly: "Units P = {UnivPoly.monom P u 0 | u. u \<in> K-{\<zero>\<^bsub>L\<^esub>}}"
  apply auto
proof goal_cases
  case (1 x)
  then obtain inv_x where inv_x: "inv_x \<in> Units P" "inv_x \<otimes> x = \<one>"
    using P.Units_l_inv by blast
  then have "deg (L\<lparr>carrier:=K\<rparr>) inv_x + deg (L\<lparr>carrier:=K\<rparr>) x = deg (L\<lparr>carrier:=K\<rparr>) \<one>"
    using deg_mult by (smt "1" P.Units_closed local.integral_iff local.zero_not_one)
  then have "deg (L\<lparr>carrier:=K\<rparr>) x = 0"
    unfolding deg_one by blast
  then show ?case
  proof -
    have "x \<in> carrier P"
      using "1" P.Units_closed by blast (* > 1.0 s, timed out *)
    then show ?thesis
      by (metis (no_types) Diff_iff Field_Extension.ring.subfield_m_inv(1) P.Units_closed P.l_null R.nat_pow_0 R.zero_closed R.zero_not_one S.nat_pow_0 S.nat_pow_consistent S.ring_axioms S.subfield_m_inv(3) UP_m_comm \<open>deg (L\<lparr>carrier := K\<rparr>) x = 0\<close> carrier_K coeff_closed coeff_zero deg_zero_impl_monom empty_iff insert_iff inv_x(1) inv_x(2) local.coeff_smult local.zero_not_one monom_closed monom_mult_is_smult monom_zero subfield_axioms)
  qed
next
  case (2 u)
  then have "UnivPoly.monom P (inv\<^bsub>L\<^esub> u) 0 \<otimes> UnivPoly.monom P u 0 = UnivPoly.monom P (inv\<^bsub>L\<^esub> u \<otimes>\<^bsub>L\<^esub> u) 0"
    using Field_Extension.ring.subfield_m_inv(1) S.ring_axioms local.monom_mult_smult
      pol.monom_mult_is_smult subfield_axioms by fastforce
  also have "\<dots> = \<one>"
    using "2" S.subfield_m_inv(3) monom_one subfield_axioms by auto
  finally show ?case
    by (metis (no_types, lifting) "2" Diff_iff Field_Extension.ring.subfield_m_inv(1)
        P.Units_one_closed P.prod_unit_l P.unit_factor R.Units_closed S.ring_axioms monom_closed
        singletonD subfield_Units subfield_axioms)
qed

corollary Units_poly': "Units P = (\<lambda>u. UnivPoly.monom P u 0) ` (K-{\<zero>\<^bsub>L\<^esub>})"
  using Units_poly by auto

lemma "p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> lcoeff (p \<otimes> q) = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q"
  apply (cases "p = \<zero>") using coeff_closed apply auto[1]
  apply (cases "q = \<zero>") using coeff_closed apply auto[1] apply auto
proof goal_cases
  case 1
  let ?coeff = "\<lambda>i. UnivPoly.coeff P p i \<otimes>\<^bsub>L\<^esub> UnivPoly.coeff P q (dg p + dg q - i)"
  have "?coeff i = \<zero>\<^bsub>L\<^esub>" if "i \<in> {dg p <.. dg p + dg q}" for i
  proof -
    from that have "i > dg p"
      by force
    then have "UnivPoly.coeff P p i = \<zero>\<^bsub>L\<^esub>"
      by (simp add: "1"(1) deg_aboveD)
    then show ?thesis
      using "1"(2) coeff_closed by auto
  qed
  moreover have "?coeff i = \<zero>\<^bsub>L\<^esub>" if "i \<in> {..< dg p}" for i
  proof -
    from that have "dg p + dg q - i > dg q"
      by fastforce
    then have "UnivPoly.coeff P q (dg p + dg q - i) = \<zero>\<^bsub>L\<^esub>"
      by (simp add: "1"(2) deg_aboveD)
    then show ?thesis
      using "1"(1) coeff_closed by auto
  qed
  moreover have "?coeff i = lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q" if "i = dg p" for i
    by (simp add: that)
  ultimately have "(\<lambda>i\<in>{..dg p + dg q}. UnivPoly.coeff P p i \<otimes>\<^bsub>L\<^esub> UnivPoly.coeff P q (dg p + dg q - i))
  = (\<lambda>i\<in>{..dg p + dg q}. if dg p = i then lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q else \<zero>\<^bsub>L\<^esub>)"
    by auto (smt add_diff_cancel_left' atMost_iff le_eq_less_or_eq nat_le_linear restrict_ext)
  then have "(\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i\<in>{..dg p + dg q}. if dg p = i then lcoeff p \<otimes>\<^bsub>L\<^esub> lcoeff q else \<zero>\<^bsub>L\<^esub>)
    = (\<Oplus>\<^bsub>L\<lparr>carrier := K\<rparr>\<^esub>i\<in>{..dg p + dg q}. UnivPoly.coeff P p i \<otimes>\<^bsub>L\<^esub> UnivPoly.coeff P q (dg p + dg q - i))"
    using R.finsum_restrict[of _ "{..dg p + dg q}"] sledgehammer apply auto sledgehammer
    sorry
    then show ?case using R.finsum_singleton sledgehammer
qed

  oops
  find_theorems deg "_ \<otimes> _"

lemma ex1_monic_associated:
  assumes "p \<in> carrier P" "p \<noteq> \<zero>" shows "\<exists>!p' \<in> carrier P. p'\<sim> p \<and> monic p'"
proof
  from assms have p: "p \<in> carrier P" "lcoeff p \<in> K-{\<zero>\<^bsub>L\<^esub>}"
    using lcoeff_nonzero coeff_closed by auto
  then have inv_ok: "inv\<^bsub>L\<^esub>(lcoeff p) \<in> K"
    using S.subfield_m_inv(1) subfield_axioms by auto
  let ?p = "inv\<^bsub>L\<^esub>(lcoeff p) \<odot> p"
  have "?p \<in> carrier P"
    using inv_ok p(1) by auto
  moreover have "monic ?p" unfolding monic_def
    using S.subfield_m_inv(1) S.subfield_m_inv(3) p subfield_axioms by auto
  moreover have "?p = UnivPoly.monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<otimes> p"
    using inv_ok monom_mult_is_smult p(1) by auto
  moreover have "UnivPoly.monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<otimes> UnivPoly.monom P (lcoeff p) 0 = \<one>"
    using inv_ok by (metis Eval_constant P_def S.subfield_m_inv(3) UP_cring_def UP_one_closed UP_ring.intro UP_ring.monom_mult_smult carrier_K coeff_closed cring_def deg_one deg_zero_impl_monom is_UP_cring local.coeff_smult monom_closed monom_mult_is_smult p(1) p(2) pol.coeff_smult ring.hom_one subfield_axioms)
  then have "UnivPoly.monom P (inv\<^bsub>L\<^esub> lcoeff p) 0 \<in> Units P"
    by (metis P.Units_one_closed P.unit_factor carrier_K coeff_closed inv_ok monom_closed p(1))
  ultimately show "?p \<in> carrier P \<and> ?p \<sim> p \<and> monic ?p"
    by (simp add: P.Units_closed P.associatedI2' UP_m_comm p(1))
  {
  fix p'
  assume p': "p' \<in> carrier P" "p' \<sim> p" "monic p'"
  then obtain inv_c where "inv_c \<otimes> p' = p" "inv_c \<in> Units P"
    using P.associated_sym local.ring_associated_iff p(1) by blast
  then have "p' = ?p" sledgehamme
  }
  find_theorems lcoeff "(\<odot>)"
  then show "\<And>p'. p' \<in> carrier P \<and> p' \<sim> p \<and> monic p' \<Longrightarrow> p' = ?p"
    by blast
qed

context
  assumes algebraic
begin

lemma is_arg_min_irr:
  "is_arg_min (deg (L\<lparr>carrier:=K\<rparr>)) (\<lambda>p. p \<in> carrier P \<and> monic p \<and> Eval p = \<zero>\<^bsub>L\<^esub>) irr"
proof -
  from \<open>algebraic\<close> obtain p where p: "p \<in> carrier P" "lcoeff p \<in> K-{\<zero>\<^bsub>L\<^esub>}" "Eval p = \<zero>\<^bsub>L\<^esub>"
    unfolding algebraic_def using lcoeff_nonzero2 coeff_closed by auto
  then have inv_ok: "inv\<^bsub>L\<^esub>(lcoeff p) \<in> K-{\<zero>\<^bsub>L\<^esub>}"
    using S.subfield_m_inv(1) subfield_axioms by auto
  let ?p = "inv\<^bsub>L\<^esub>(lcoeff p) \<odot> p"
  from inv_ok have "Eval ?p = inv\<^bsub>L\<^esub>(lcoeff p) \<otimes>\<^bsub>L\<^esub> (Eval p)"
    using Eval_smult p(1) by blast
  also have "\<dots> = \<zero>\<^bsub>L\<^esub>"
    using inv_ok p(3) by auto
  finally have "Eval ?p = \<zero>\<^bsub>L\<^esub>" .
  moreover have "?p \<in> carrier P"
    using inv_ok p(1) by auto
  moreover have "monic ?p" unfolding monic_def
    using S.subfield_m_inv(1) S.subfield_m_inv(3) p(1) p(2) subfield_axioms by auto
  ultimately show ?thesis
    unfolding irr_def by (metis (mono_tags, lifting) is_arg_min_arg_min_nat)
qed

corollary irr_sane:
  shows irr_in_P: "irr \<in> carrier P" and monic_irr: "monic irr" and Eval_irr: "Eval irr = \<zero>\<^bsub>L\<^esub>"
  and is_minimal_irr: "\<forall>y. y \<in> carrier P \<and> monic y \<and> Eval y = \<zero>\<^bsub>L\<^esub> \<longrightarrow>
    deg (L\<lparr>carrier := K\<rparr>) irr \<le> deg (L\<lparr>carrier := K\<rparr>) y" (* rm? *)
  using is_arg_min_irr[unfolded is_arg_min_linorder] by auto

corollary irr_nonzero: "irr \<noteq> \<zero>"
  by (simp add: monic_irr monic_nonzero)

lemma a_kernel_nontrivial: "a_kernel P L Eval \<supset> {\<zero>}"
  unfolding a_kernel_def' using \<open>algebraic\<close>[unfolded algebraic_def] by auto

lemma a: "PIdl irr \<subseteq> a_kernel P L Eval"
  by (metis Eval_irr P.cgenideal_minimal UP_zero_closed abelian_subgroup.a_rcos_const
      additive_subgroup.zero_closed irr_in_P ring.abelian_subgroup_a_kernel
      ring.additive_subgroup_a_kernel ring.hom_zero ring.homeq_imp_rcos ring.kernel_is_ideal)

lemma b: "PIdl irr \<supseteq> a_kernel P L Eval"
proof -
  obtain g where g: "g \<in> carrier P" "PIdl g = a_kernel P L Eval"
    using exists_gen ring.kernel_is_ideal by force
  have "irr \<in> a_kernel P L Eval" (* rm *)
    using P.cgenideal_self a irr_in_P by blast
  have "g divides irr"
    using P.to_contain_is_to_divide a g(1) g(2) irr_in_P by blast
  oops

lemma move_this_up:
  "is_arg_min (deg (L\<lparr>carrier := K\<rparr>)) (\<lambda>g. g \<in> carrier P \<and> monic g \<and> PIdl g = a_kernel P L Eval) irr"
  oops

notepad
begin
  obtain g where g: "g \<in> carrier P \<and> PIdl g = a_kernel P L Eval"
    using exists_gen ring.kernel_is_ideal by metis
  then obtain g' where "is_arg_min (deg (L\<lparr>carrier := K\<rparr>)) (\<lambda>g. g \<in> carrier P \<and> PIdl g = a_kernel P L Eval) g'"
    by (metis (mono_tags, lifting) is_arg_min_arg_min_nat)
  then obtain g'' where
    "is_arg_min (deg (L\<lparr>carrier := K\<rparr>)) (\<lambda>g. g \<in> carrier P \<and> monic g \<and> PIdl g = a_kernel P L Eval) g''"
    \<proof>
  with a_kernel_nontrivial have "g \<noteq> \<zero>"
    using P.cgenideal_eq_genideal P.genideal_zero sorry
  have "a \<in> K - {\<zero>\<^bsub>L\<^esub>} \<Longrightarrow> PIdl (a \<odot> g) = PIdl g" for a
    sorry
end

end

end


section \<open>Observations (*rm*)\<close>

text \<open>@{locale subgroup} was the inspiration to just use sets for the substructure. However, that
locale is somewhat odd in that it does not impose @{locale group} on neither \<open>G\<close> nor \<open>H\<close>.\<close>

context subgroup begin
lemma "group G" oops
lemma "group (G\<lparr>carrier:=H\<rparr>)" oops
end

thm genideal_def cgenideal_def \<comment> \<open>This naming could be improved.\<close>
text \<open>@{const Ideal.genideal} could be defined using @{const hull}...\<close>

text \<open>@{thm[source] field_simps} are *not* available in general. Re-prove them?\<close>

value INTEG value \<Z> \<comment> \<open>duplicate definition\<close>

section \<open>Vector Spaces\<close>

definition (in vectorspace) B where
  "B = (SOME B. basis B)"

lemma (in vectorspace)
  "fin_dim \<Longrightarrow> finite B"
  by (metis B_def basis_def fin_dim_li_fin finite_basis_exists someI_ex)

lemma (in comm_monoid) finprod_singleton':
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and x_in_G: "x \<in> carrier G"
  shows "(\<Otimes>j\<in>A. if i = j then x else \<one>) = x"
  using i_in_A finprod_insert [of "A - {i}" i "(\<lambda>j. if i = j then x else \<one>)"]
    fin_A x_in_G finprod_one [of "A - {i}"]
    finprod_cong [of "A - {i}" "A - {i}" "(\<lambda>j. if i = j then x else \<one>)" "(\<lambda>i. \<one>)"]
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

thm comm_monoid.finprod_singleton
thm comm_monoid.finprod_singleton'[where ?i = i, where ?x = \<open>f i\<close> for f i]
end
