theory Field_Extension imports
"HOL-Algebra.Divisibility"         
"HOL-Algebra.IntRing"              (* Ideals and residue classes? *)
"HOL-Algebra.UnivPoly"             (* Polynomials *)
"HOL-Algebra.Multiplicative_Group"
"HOL-Number_Theory.Residues"       (* \<int>/p\<int> and all(?) of the above. rm? *)
begin


section \<open>Subrings\<close>

context ring begin \<comment> \<open>\<triangleq> "Let @{term R} be a ring."\<close>

lemma ring_card: "card (carrier R) \<ge> 1 \<or> infinite (carrier R)"
  using not_less_eq_eq ring.ring_simprules(6) by fastforce

lemma nonzero_ring_one: "card (carrier R) \<noteq> 1 \<Longrightarrow> one R \<noteq> zero R"
  using is_singleton_altdef is_singleton_def one_zeroD by blast

definition subring where
  "subring S \<longleftrightarrow>
    carrier S \<subseteq> carrier R \<and>
    ring S \<and>
    one R \<in> carrier S \<and>
    (\<forall>r1\<in>carrier S. \<forall>r2\<in>carrier S. add S r1 r2 = add R r1 r2 \<and> mult S r1 r2 = mult R r1 r2)"

lemma subring_refl: "subring R"
  unfolding subring_def using local.ring_axioms by blast

lemma subring_nontrivial: "card (carrier R) \<noteq> 1 \<Longrightarrow> subring S \<Longrightarrow> card (carrier S) \<noteq> 1"
  by (metis add.r_cancel_one' card_1_singletonE nonzero_ring_one one_closed ring.ring_simprules(15)
      ring.ring_simprules(2) singleton_iff subring_def)

end

context cring begin \<comment> \<open>\<triangleq> "Let @{term R} be a commutative ring."\<close>

lemma subring_cring: "subring S \<Longrightarrow> cring S" unfolding subring_def cring_def ring_def
  by (simp add: comm_monoid.m_ac(2) comm_monoid_axioms monoid.monoid_comm_monoidI subset_eq)

end

context field begin \<comment> \<open>\<triangleq> "Let @{term R} be a field."\<close>

definition subfield where
  \<comment> \<open>Maybe remove this definition and put it in the assumption of field_extension...
    (requires use of rewrite-clauses to avoid a name clash?)\<close>
  "subfield K \<longleftrightarrow> subring K \<and> field K"

lemma subfield_refl: "subfield R"
  by (simp add: local.field_axioms subfield_def subring_refl)

end

locale field_extension = field L for L (structure) +
  fixes K
  assumes L_extends_K: "subfield K"
begin \<comment> \<open>\<triangleq> "Let @{term L}/@{term K} be a field extension."\<close>

lemma K_field: "field K"
  using L_extends_K by (simp add: subfield_def)

end

lemma (in field) f_e_refl : "field_extension R R"
  by (simp add: field_extension.intro field_extension_axioms.intro local.field_axioms subfield_refl)

lemma (in field) f_e_iff_subfield: "field_extension R K \<longleftrightarrow> subfield K"
  by (simp add: field_extension_axioms_def field_extension_def local.field_axioms)

context field_extension
begin

thm hull_def
definition ext_of_gen where
  (* K\<le>M\<le>L, the \<lambda>-term, must be a predicate about the \<^bold>s\<^bold>e\<^bold>t M *)
  "S \<subseteq> carrier L \<Longrightarrow> ext_of_gen S = (\<lambda>M. carrier M) hull S"

lemma "field K" oops
lemma "field L" oops
lemma "field.subfield L K" oops

end


section\<open>Observations\<close>

text \<open>@{const Ideal.genideal} could be defined using @{const hull}...\<close>

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
