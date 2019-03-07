(*<*)
(* Author: Fabian Hellauer, 2018-2019 *)
theory Doc
  imports
    Field_Extensions.Examples
    Field_Extensions.Old_Field_Extension
    "HOL-Algebra.Algebra"
begin
(*>*)

section \<open>Modelling of Algebraic Structures\<close>

text \<open>In Algebra, superstructures generally are defined to be just the inverse of substructures, as
  is the cases for fields. Thus, modelling the notion of subfield also defines field extensions
  (which is just another term for superfield).\<close>

subsection \<open>Subrings\label{sec:sr}\<close>

text \<open>A first try at formalising the notion of a subring is \<^const>\<open>ring.old_sr\<close>: A predicate
 which operates on two full \<^type>\<open>ring\<close> records \<open>R\<close> and \<open>S\<close>. It enforces the well-known
 properties for the subring \<open>S\<close>, and states where \<open>R\<close> and \<open>S\<close> have to equal.

A problem  with this approach is that there are two entities for \<open>\<otimes>\<close> and \<open>\<oplus>\<close> each: Many facts can be
 shown not for any subring \<open>S\<close>, but only for \<^term>\<open>(R\<lparr>carrier := carrier S\<rparr>)\<close> (the structure with
 \<open>\<otimes>\<close>, \<open>\<oplus>\<close>, \<open>\<zero>\<close> and \<open>\<one>\<close> from \<open>R\<close>, but carrier set from the subring \<open>S\<close>). This may differ from \<open>S\<close>
  in where the operations map objects from outside of the carrier set.

 Similarly, \<open>\<zero>\<close> and \<open>\<one>\<close> are fixed twice each. Since they equal between sub- and
 superstructure, there is some degree of freedom in stating lemmas (using one or the other),
 hindering fact uniformity.

To conclude, it seems advisable to fix all needed objects only once within a locale. For
 Algebra, this means: A group or ring needs a full record, but for \<^emph>\<open>sub\<close>structures we should only
 add a \<^emph>\<open>set\<close> to the fixed items.

The newly-added locale \<^locale>\<open>subring\<close> in \<^session>\<open>HOL-Algebra\<close> uses this approach, via
 \<^locale>\<open>subgroup\<close> and \<^locale>\<open>submonoid\<close>. Note however, that \<^locale>\<open>subgroup\<close>'s axioms
 only describe a technical relation to the superstructure, assumed to be a group. In other words,
 \begin{center} @{prop[names_short] \<open>subgroup H G \<Longrightarrow> group (G\<lparr>carrier := H\<rparr>)\<close>} \end{center} does not
 hold without the additional assumption @{prop[names_short] \<open>group G\<close>}, equivalently for ring and
 monoid. It is only under these additional assumptions that these locales coincide with the typical
 textbook definitions.\<close>

subsection \<open>Subfields\label{sec:sf}\<close>

text \<open>The locale \<^locale>\<open>subfield\<close> extends \<^locale>\<open>subring\<close> with the appropriate additional
 assumptions for the substructure. It was also added during my work.

My locale \<^locale>\<open>field_extension\<close> combines \<^locale>\<open>subfield\<close> and \<open>field\<close>. It also renames the
 variables to \<open>L\<close> for the field and \<open>K\<close> for the subfield set.

The locale \<^locale>\<open>UP_field_extension\<close> additionally sets \<open>P\<close> to denote the ring of univariate
  polynomials over \<open>K\<close>, fixes an \<open>\<alpha>\<close> in \<open>L\<close>, and defines \<open>Eval\<close> to be the map \<open>P \<rightarrow> L\<close> which
  evaluates polynomials at \<open>\<alpha>\<close>. The homomorphism property of this map is proven in
  \<^theory>\<open>HOL-Algebra.UnivPoly\<close>.\<close>

subsection \<open>Infinite Dimension\<close>

text \<open>In \<open>VectorSpace.VectorSpace\<close>, the case of an infinite dimension is modelled by \<^const>\<open>vector_space.dim\<close>
 being an unspecified \<^typ>\<open>nat\<close>. My impression from reading that theory is that distinct
 representations would improve the formalisation: For instance, in \<open>VectorSpace\<close>, the dimension
 being finite does not imply @{const vectorspace.fin_dim}, counterintuitively.

As the zero vector space is no field, the degree of a field extension is never \<open>0\<close>. With the above
 consideration in mind, I therefore decided to define the infinite degree to be @{term_type
 "0::nat"}. Incidentally, for the purpose of the tower rule (\<open>\<section>\<close>\ref{sec:tr}), \<open>0\<close> and \<open>\<infinity>\<close> happen to
 have the same absorbing properties in a multiplication.

A more robust implementation would use an extended type of natural numbers, or even the full range
 of cardinal numbers. For field extensions, only one additional number is needed: My template@{cite
 Algebra1} views the degree as number in \<open>\<nat> \<union> {\<infinity>}\<close>.

Whatever the best formalisation is, the change should be made in \<open>VectorSpace\<close>:
 \<^theory>\<open>Field_Extensions.Field_Extension\<close> only uses what is there. Due to there being no
 collision with the actual \<open>0\<close>, my material should be easily adaptable to such a change.\<close>

section \<open>Field Extensions\<close>

subsection \<open>Degree Multiplicativity (Tower Rule)\label{sec:tr}\<close>

text\<open>Remember that infinite field extensions are encoded to have \<open>degree = 0\<close>. This case may occur
  in the following "tower rule":\<close>

proposition degree_multiplicative:
  "\<lbrakk>subfield K (M\<lparr>carrier:=L\<rparr>); subfield L M; field M\<rbrakk> \<Longrightarrow>
  field_extension.degree M K =
    field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"(*<*)by(fact degree_multiplicative)(*>*)

text \<open>The proof is covered by considering three (partially overlapping) cases:
  \<^enum> The lower field extension is infinite.
  \<^enum> The upper field extension is infinite.
  \<^enum> Both extension parts are finite.

Recently, the proposition part about two \<^emph>\<open>finite\<close> extensions (case 3) has also been proven in
 another \<^session>\<open>HOL-Algebra\<close> development\<^footnote>\<open>\<^url>\<open>https://github.com/DeVilhena-Paulo/GaloisCVC4\<close>\<close>.
 It uses the inner product instead of the outer for the proof, thus avoiding the vector space
  terminology as described in \autoref{sec:mvs}.\<close>

subsection \<open>The Minimal Polynomial\<close>
(*<*)context UP_field_extension begin(*>*)
text \<open>Recall the context \<^locale>\<open>UP_field_extension\<close> from \autoref{sec:sf}. For an \<^emph>\<open>algebraic\<close> \<^term>\<open>\<alpha>\<close>,
  I define the minimal polynomial:\<close>
text_raw\<open>\isacommand{definition}\isamarkupfalse%
\ irr\ %
\isamarkupcmt{named after its \emph{irr}educibility (shown later)%
}\ \isanewline
\ \ \isakeyword{where}\ {\isachardoublequoteopen}irr\ {\isacharequal}\isanewline
\ \ \ \ {\isacharparenleft}ARG{\isacharunderscore}MIN\ degree\ p{\isachardot}\ p\ {\isasymin}\ carrier\ P\ {\isasymand}\ monic\ p\ {\isasymand}\ Eval\ p\ {\isacharequal}\ {\isasymzero}\isactrlbsub L\isactrlesub {\isacharparenright}{\isachardoublequoteclose}%\<close>
text \<open>This uses an indefinite description (via @{const arg_min}) because the construction of @{const
 irr} depends on the choice of polynomial for which \<open>\<alpha>\<close> is a root. This formulation is also
  common in textbooks.\<close>

subsection \<open>Classification of Simple Algebraic Extensions\<close>

text \<open>In \<^locale>\<open>UP_field_extension\<close>, within the above-mentioned context of an algebraic
 \<^term>\<open>\<alpha>\<close>, Theorem Kemper/16.9b@{cite Algebra1} applies. Its results are distributed:
  \<^item> @{thm[source] irr_exists}, the existence of \<^term>\<open>\<alpha>\<close>'s minimal polynomial "\<^const>\<open>irr\<close>"
  \<^item> @{thm[source] irr_unique}, the uniqueness of \<^const>\<open>irr\<close>
  \<^item> @{thm[source] irr_irreducible_polynomial}, the irreducibility of \<^const>\<open>irr\<close> in the ring
   \<^term>\<open>P\<close> of polynomials over \<^term>\<open>K\<close>
  \<^item> @{thm[source] the_elem_ring_iso_Quot_irr_generate_field}, the isomorphy of \<^term>\<open>irr\<close>'s
 residue class ring with \<open>K(\<alpha>)\<close>

All of these are on their own useful for a library, so splitting up the theorem seemed appropriate.\<close>
(*<*)end(*>*)

section \<open>Modules and Vector Spaces\label{sec:mvs}\<close>

subsection \<open>Motivation\<close>

text \<open>The motivation for working in this area was Kemper's proof of the field extension tower rule
 (\<open>\<section>\<close>\ref{sec:tr}), which uses vector space results unavailable in \<^session>\<open>HOL-Algebra\<close>. Note
 that the tower rule could be proven more directly using indexed sums\<^footnote>\<open>cf.\ e.g.\
 \<^url>\<open>https://wikipedia.org/wiki/Degree_of_a_field_extension\#The_multiplicativity_formula_for_degrees\<close>\<close>,
  but the material which Kemper uses seemed to be of general usefulness for a vector space library.
 Moreover note that proofs using indexed sums tend to be very cumbersome in \<^session>\<open>HOL-Algebra\<close>.\<close>

subsection \<open>Indexed Products\<close>

text \<open>For a ring \<open>R\<close>, this defines the coordinate space $R^n$:

\<^theory_text>\<open>definition (in ring) nspace where "nspace n = func_space {..<n::nat}"\<close>

Here, \<^term>\<open>ring.func_space\<close> is the well-known module of functions from any set to the ring
 carrier set with pointwise addition and scalar multiplication.

A limitation of this approach is that only sums of the same module can be described, compared to
 \<^const>\<open>direct_sum\<close> (see \<open>\<section>\<close>\ref{sec:ds}), which can even combine modules of different type (over the same
 ring). An obvious advantage is however the variability of \<open>n\<close>.

A well-known theorem about \<open>K\<close>-vector-spaces \<open>V\<close> of finite dimension \<open>dim\<close> is that they are
  isomorphic to $K^{dim}$:\<close>

theorem (in vectorspace) nspace_iso:
  assumes fin_dim
  shows "\<exists>\<phi>. linear_map K (nspace dim) V \<phi> \<and>
    bij_betw \<phi> (carrier (nspace dim)) (carrier V)"(*<*)using assms by(fact nspace_iso)(*>*)

text \<open>In the proof, some lemmas from \isatt{VectorSpace} turned out to be useful, e.g.\ about the
  kernel of injective linear maps.\<close>

subsection \<open>Direct Sums\label{sec:ds}\<close>

text \<open>In \<open>SumSpaces\<close>, one finds the definition \<^const>\<open>direct_sum\<close>. It is misleading in that it
 also defines contents for the unused \<open>mult\<close> and \<open>one\<close> field of the module. I replaced these with
 \<open>undefined\<close>.

The notion gives rise to another view on the previous result:\<close>

lemma decompose_step:
  "\<lbrakk>vectorspace K V; vectorspace.fin_dim K V; 0 < vectorspace.dim K V\<rbrakk>
\<Longrightarrow> \<exists>\<phi> V'.
  linear_map K V (direct_sum (module_of K) (V\<lparr>carrier:=V'\<rparr>)) \<phi> \<and>
  bij_betw \<phi> (carrier V) (carrier K \<times> V') \<and>
  subspace K V' V \<and>
  vectorspace.dim K (V\<lparr>carrier:=V'\<rparr>) = vectorspace.dim K V - 1"(*<*)by(fact vectorspace.decompose_step)(*>*)

text \<open>This variant is used in the proof of the tower rule's finite case, together with induction. In
 retrospect, @{thm[source] vectorspace.nspace_iso} probably could have achieved the same with
 less work. The reason I used \<open>decompose_step\<close> is that I expected some
 material about the direct sum to be available, as \<^const>\<open>direct_sum\<close> was already defined.
 Ultimately, no useful results turned out to exist for this function.

Some ugliness of @{thm[source] vectorspace.decompose_step} comes from the use of a second
  existential quantifier, namely for \<open>V'\<close>. This cannot be avoided elegantly, as the witness
\<^item> is somewhat unhandy (see the proof) and,
\<^item> more importantly, depends on a choice of basis, and a choice of ordering on that basis.\<close>

subsection \<open>Subspaces\<close>

text \<open>These are two other useful results:
  \<^item> Subspaces of finite-dimensional vector spaces are again finite-dimensional: The dimension of the
 subspace is less than or equal to the dimension of the finite-dimensional superspace.
  \<^item> If a subspace of a finite-dimensional vector space has the "full" dimension, then it is the same as
 its superspace, i.e.\ the inclusion is improper.

These facts seem trivial, but they do need a proof even in the template @{cite Algebra1}.

For the proof, I needed the basis extension
 theorem\<^footnote>\<open>\<^url>\<open>http://www-m11.ma.tum.de/fileadmin/w00bnb/www/people/kemper/lectureNotes/LADS.pdf\#section.0.10\<close>\<close>,
at least for finite-dimensional vector spaces and \<^prop>\<open>S = carrier V\<close>. This special case is
 @{thm[source] vectorspace.lin_indpt_extends_to_basis}.

The notion \<^const>\<open>maximal\<close>, where @{thm[show_question_marks = false] maximal_def}, is introduced in
 \<open>VectorSpace.VectorSpace\<close> and not in \<^theory>\<open>HOL.Zorn\<close>. This may be relevant
 when porting the basis extension theorem to allow for infinite dimensions.
\<close>

section \<open>Problems\<close>

subsection \<open>Missing Substructure Theory\<close>

text \<open>The most important problem can be identified easily: the lack of material about substructures.
 A simple \<^theory_text>\<open>find_theorems\<close> invocation for instance reveals that not a single lemma had been
  proven within e.g.\ the \<^locale>\<open>subspace\<close> or \<^locale>\<open>submodule\<close> locales. The theories at
 hand should mitigate this a bit.

The \<^locale>\<open>subspace\<close> locale has a definition quirk which should be re-evaluated before putting
  more work in proving lemmas in it: It states its dependencies as assumptions, not as imports.
  This leads to blown-up proofs because many facts need to be re-constructed e.g.\ via chaining.

Another nuisance is the different argument order for \<^const>\<open>VectorSpace.subspace\<close> and @{const[names_long] submodule}.\<close>

subsection \<open>Non-Canonical Maps\<close>

text \<open>Some results about vector spaces and linear maps depend on a choice of basis. While bases are
 defined a sets, we sometimes need a "first" element, or even a full ordering.

This means that we cannot translate the informal "We fix a basis \<open>B\<close>." to the \<^emph>\<open>Isar formal proof language\<close> like this:\<close>
(*<*)notepad (in vectorspace) begin(*>*)
  fix B
  assume "basis B"
(*<*)end(*>*)

text \<open>Instead, one has to work with a distinct list as basis, and use a conversion function with
 every \<open>\<in>\<close>, \<open>\<subseteq>\<close>, etc. If more such situations arise in the theory of vector spaces, one might consider
  adding something like\<close>

definition (in vectorspace) B where
  "B = (SOME B. distinct B \<and> basis (set B))"
lemma (in vectorspace)
  assumes fin_dim shows "distinct B" and "basis (set B)" (*<*) unfolding B_def
  using assms by (metis (lifting) finite_basis_exists finite_distinct_list someI)+ (*>*)

text \<open>to the library. This is just another way of stating the existence of a finite basis, but might
 be more useful in proofs and lemma statements.

As is known, infinite-dimensional vector spaces have bases, too, but proving this requires more work
 and a different indexing scheme.\<close>

subsection \<open>Old-School Context Elements\<close>

text \<open>The \<^doc>\<open>locales\<close> manual@{cite "isabelle-locale"} states that \<^theory_text>\<open>defines\<close> clauses in locale
 definitions are provided only for backward compatibility, but gives no reason for the deprecation.
 My problem with \<^theory_text>\<open>defines\<close> is that it causes code duplication, e.g.\ @{thm[source]
 UP_field_extension.Eval_def} cannot be derived from @{thm[source] UP_univ_prop.Eval_def}. In my
 development, I tried to avoid \<^theory_text>\<open>defines\<close> for this reason, and used regular definitions instead.
 The only usage is in the definition of @{locale UP_field_extension}, where this seems to be the
 only way to make a \<^theory_text>\<open>(structure)\<close> declaration. An alternative with no \<^theory_text>\<open>defines\<close> at all is in the
 \isatt{no\_defines} branch\<^footnote>\<open>\<^url>\<open>https://github.com/helli/field-extensions/tree/no\_defines\<close>\<close>. This
 needs a lot more subscripts in subsequent statements and proofs, but removes the need to redefine
 \<open>P\<close> for interpretations of the locale, see the proof of @{thm[source] generate_field_\<i>_UNIV}.\<close>

section \<open>Analysis of the Used Libraries\<close>

subsection \<open>Principal Ideal Definitions\<close>

text \<open>There are two definitions of ideals in \<^theory>\<open>HOL-Algebra.Ideal\<close>: \<^const>\<open>Ideal.genideal\<close> and \<^const>\<open>Ideal.cgenideal\<close>. They
 differ not in \<^emph>\<open>c\<close>ommutativity, as their names suggest, but in whether they take a set or single
 element as argument. Confusingly enough, the locales \<^const>\<open>principalideal\<close> and
 \<^const>\<open>principal_domain\<close> are not defined via the same notion of ideal. (They also do not use
 each other in their definitions.)

 @{const[names_long] Ideal.cgenideal} should probably be renamed to
  match its function symbol "\<open>PIdl\<close>" (principal ideal). It could also just abbreviate
  \<^const>\<open>genideal\<close> with \<^prop>\<open>S = {a}\<close>. In this scenario, the
 current @{thm[source] cgenideal_def} would become a lemma, perhaps stated like @{thm[source]
  cring.cgenideal_eq_rcos} to benefit from the huge theory \<^theory>\<open>HOL-Algebra.Coset\<close>.

Moreover note that both functions are hull operations,
  thus using the material from \<^theory>\<open>HOL.Hull\<close> might shorten some proofs.\<close>

subsection \<open>Generated Fields\<close>

text \<open>The function \<^const>\<open>generate_field\<close> was added during my work. This meant that I had to do
 some porting (see \<^theory>\<open>Field_Extensions.Old_Field_Extension\<close> for the state before that).
 However, it turned out to simplify matters overall because it leaves out the "lower bound" field
 found in @{cite Algebra1}/definition 16.4.

A note about the style: Just like in their locale
 definitions (see \<open>\<section>\<close>\ref{sec:sr}), the authors use a technical description with the
  \<^theory_text>\<open>inductive_set\<close> command, instead of using \<^theory_text>\<open>definition\<close> and \<^const>\<open>hull\<close>.\<close>

subsection \<open>Integer Ring Definitions\<close>

text \<open>
Both \<^theory>\<open>HOL-Algebra.UnivPoly\<close> and \<^theory>\<open>HOL-Algebra.IntRing\<close> define an integer ring,
 i.e.\ a ring with the \<^term>\<open>UNIV\<close> of type \<^typ>\<open>int set\<close> as carrier set and the usual
 operations.

Apart from the usual problems of duplicate definitions (\<^const>\<open>INTEG\<close> vs.\ \<open>\<Z>\<close>), they also
 pollute the name space: For instance, \<^theory_text>\<open>find_theorems eval\<close> yields 35 facts, 15 of which
 are about \<^const>\<open>INTEG\<close>. These are too special and therefore useless when doing abstract
 algebra. Note that \<^theory_text>\<open>hide_const INTEG\<close> does not hide the facts, hindering e.g.\ auto-completion.
When going up in the locale hierarchy (e.g.\ \<^locale>\<open>monoid\<close>), lemmas about \<open>\<Z>\<close> come on board, too, if
 \<^theory>\<open>HOL-Algebra.IntRing\<close> is imported.
To me, this is a reason why \<^theory>\<open>HOL-Algebra.Algebra\<close> is not attractive as an import. In future
 revisions of the library, the import of both \<^const>\<open>INTEG\<close> and \<open>\<Z>\<close> should be optional.

\<^const>\<open>INTEG\<close> and \<open>\<Z>\<close> are unused outside of their theories, also in the \<^emph>\<open>Archive of Formal
 Proofs\<close>\<^footnote>\<open>\<^url>\<open>https://www.isa-afp.org\<close>\<close>. A reason may be that they are too special: Since
 \<^const>\<open>UNIV\<close> is already the largest set, they cannot be substructures. The ability to reason
 about substructures is however a common reason to use \<^session>\<open>HOL-Algebra\<close> in the first place.
 \hyperref[sec:ethy]{Section~\ref*{sec:ethy}} follows a different approach using mostly abstract types.
\<close>

subsection \<open>Modelling of Polynomials\<close>

text \<open>The clash of old-school @{type[names_long] up_ring} with @{const[names_long] polynomial} had
 not much effect on my development, but it means that
  \<^theory>\<open>HOL-Algebra.Polynomials\<close> cannot be added to the imports without also switching to long
  identifiers for some entities.

The original motivation to avoid \<^theory>\<open>HOL-Algebra.Polynomials\<close> was the requirement of
  \<^const>\<open>ring.normalize\<close> in definitions, lemmas and proofs. This deficiency stems from
  representing the polynomials as coefficient lists, thereby losing uniqueness. A unification of the
 two approaches is subject of ongoing development, refer to the developers for more information.\<close>

subsection \<open>Side Notes\<close>

text \<open>\<^file>\<open>~~/src/HOL/Algebra/README.html\<close> is completely outdated.\<close>

text \<open>In \<^file>\<open>~~/src/HOL/Algebra/document/root.tex\<close>, I suggest to use\<close>
text \<open>\<^verbatim>\<open>\includegraphics[height=\textheight]{session_graph}\<close>\<close>
text \<open>for the session graph, so that it is
  displayed wholly in the document.\<close>

section \<open>Example Instantiations\label{sec:ethy}\<close>

text \<open>\isatt{Examples.thy} provides instantiations for some of the locales, using commonly known
 rings.
 The theory cannot use the @{theory_text \<open>interpretation\<close>} command due to some more library
  errors:
\begin{figure}[H]
  \includegraphics[width=\linewidth]{"interpretation_error"}
  \caption{@{thm[source] subfield_Reals_complex_field}, if stated as an interpretation: The
 proof works just as in the case of a lemma, but the fact generation fails.}
\end{figure}
The problem traces back to \<^locale>\<open>subring\<close> importing both \<^locale>\<open>submonoid\<close> and
 \<^locale>\<open>subgroup\<close>, which both have an axiom named \<open>subset\<close>. A workaround is known\<^footnote>\<open>see
  \<^url>\<open>https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2018-June/msg00033.html\<close>\<close>, but complicates
  matters quite a bit.\<close>

section \<open>Additional Resources\<close>

text \<open>Readme.MD. Overall, the diff to a recent AFP commit like to-do is designed to be small, so that the changes can be easily reconstructed. Generated Document of the main session
  Field-Extension. In particular, its Contents section might make here-unmentioned lemmas
  easier to find.\<close>

(*<*)
end
(*>*)
