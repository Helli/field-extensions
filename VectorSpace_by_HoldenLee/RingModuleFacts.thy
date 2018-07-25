section {* Basic facts about rings and modules *}

theory RingModuleFacts
imports Main
  "HOL-Algebra.Module"
  "HOL-Algebra.Coset"
  (*MonoidSums*)
begin

subsection {* Basic facts *}
text {*In a field, every nonzero element has an inverse.*} (* Add to Ring.*)
lemma (in field) inverse_exists [simp, intro]: 
  assumes h1: "a\<in>carrier R"  and h2: "a\<noteq>\<zero>\<^bsub>R\<^esub>"
  shows "inv\<^bsub>R\<^esub> a\<in> carrier R"
proof - 
  have 1: "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>} " by (rule field_Units)
  from h1 h2 1 show ?thesis by auto
qed

text {*Multiplication by $-1$ is the same as negation. May be useful as a simp rule. *}
(*Add to module.*)
lemma (in module) smult_minus_1:
  fixes v
  assumes 0:"v\<in>carrier M"
  shows "(\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v= (\<ominus>\<^bsub>M\<^esub>  v)"
(*(simp add: M.l_neg)*)
proof -
  from 0 have a0: "\<one>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> v = v" by simp
  from 0 have 1: "((\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)\<oplus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v=\<zero>\<^bsub>M\<^esub>" 
    by (simp add:R.l_neg)
  from 0 have 2: "((\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)\<oplus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v=(\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> \<one>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> v"
    by (simp add: smult_l_distr)
  from 1 2 show ?thesis by (metis M.minus_equality R.add.inv_closed 
    a0 assms one_closed smult_closed) 
qed

text {*The version with equality reversed.*}
lemmas (in module)  smult_minus_1_back = smult_minus_1[THEN sym]

text{*-1 is not 0*}
lemma (in field) neg_1_not_0 [simp]: "\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
by (metis minus_minus minus_zero one_closed zero_not_one) 

text {* Note smult-assoc1 is the wrong way around for simplification.
This is the reverse of smult-assoc1. *}(*Add to Module. *)
lemma (in module) smult_assoc_simp:
"[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      a \<odot>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x) = (a \<otimes> b) \<odot>\<^bsub>M\<^esub> x "
by (auto simp add: smult_assoc1)
  
(* Add to Ring? *)
lemmas (in abelian_group) show_r_zero= add.l_cancel_one
lemmas (in abelian_group) show_l_zero= add.r_cancel_one

text {*A nontrivial ring has $0\neq 1$. *}(*Add to Ring.*)
lemma (in ring) nontrivial_ring [simp]:
  assumes "carrier R\<noteq>{\<zero>\<^bsub>R\<^esub>}"
  shows "\<zero>\<^bsub>R\<^esub>\<noteq>\<one>\<^bsub>R\<^esub>"
proof (rule ccontr)
  assume 1: "\<not>(\<zero>\<^bsub>R\<^esub>\<noteq>\<one>\<^bsub>R\<^esub>)"
  {
    fix r
    assume 2: "r\<in>carrier R"
    from 1 2 have 3: "\<one>\<^bsub>R\<^esub>\<otimes>\<^bsub>R\<^esub> r = \<zero>\<^bsub>R\<^esub>\<otimes>\<^bsub>R\<^esub> r" by auto
    from 2 3 have "r = \<zero>\<^bsub>R\<^esub>" by auto
  }
  from this assms show False by auto
qed

text {*Use as simp rule. To show $a-b=0$, it suffices to show $a=b$. *}(*Add to Ring.*)
lemma (in abelian_group) minus_other_side [simp]:
  "\<lbrakk>a\<in>carrier G; b\<in>carrier G\<rbrakk> \<Longrightarrow> (a\<ominus>\<^bsub>G\<^esub>b = \<zero>\<^bsub>G\<^esub>) = (a=b)"
  by (metis a_minus_def add.inv_closed add.m_comm r_neg r_neg2)

end
