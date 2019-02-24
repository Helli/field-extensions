(*<*)
(* Author: Fabian Hellauer, 2018-2019 *)
theory Doc
  imports
    Field_Extensions.Examples
    Field_Extensions.Old_Field_Extension
    "HOL-Algebra.Algebra"
begin
(*>*)

section \<open>Preface\<close>
(* to-do: make this an actual preface? *)
text\<open>This work is part of an interdisciplinary project between Mathematics and Computer Science,
  supervised by Manuel Eberl and Prof.\ Gregor Kemper. The source files are hosted at
  \<^url>\<open>https://github.com/helli/field-extensions\<close>.\<close>

section \<open>Modelling of Substructures\<close>

text \<open>In Algebra, superstructures generally are defined to be just the inverse of substructures, as
  is the cases for fields. Thus, modelling the notion of subfield also defines field extensions
  (which is just another term for superfield).\<close>

subsection \<open>\<^const>\<open>ring.old_sr\<close>\<close>

text \<open>This is my first try at formalising the notion of a subring (similarly \<^const>\<open>field.old_sf\<close>
  for subfields): Both a ring R and its subring S are full ring records, the predicate
 \<^const>\<open>ring.old_sr\<close> states where 
 they have to equal. The problem is that even with these assumptions, there are two entities for
 each operation, \<open>\<zero>\<close> and \<open>\<one>\<close>. In fact, I can show many facts not for any subring S, but only for
 \<^term>\<open>(R\<lparr>carrier := carrier S\<rparr>)\<close> (the structure with \<open>\<otimes>\<close>, \<open>\<oplus>\<close>, \<open>\<zero>\<close> and \<open>\<one>\<close> from \<open>R\<close>, but
  carrier set from the subring \<open>S\<close>). This may differ from \<open>S\<close> in where the operations map objects
  from outside of the carrier set.\<close>

text \<open>\<open>\<zero>\<close> and \<open>\<one>\<close> are the same for both substructures. This means that there is some degree of
  freedom in stating lemmas (using one or the other).\<close>

text \<open>To sum up, it seems advisable to fix all needed objects (sets or operations) only once within
  a locale. For Algebra this means: A group or ring needs a full record, but for substructures we
  should only add a \<^emph>\<open>set\<close> to the fixed items.\<close>

subsection \<open>\<^const>\<open>subring\<close>\<close>

text \<open>This locale from \<^session>\<open>HOL-Algebra\<close> uses this "set+superstructure"-approach, via \<^locale>\<open>subgroup\<close> and
  \<^locale>\<open>submonoid\<close>. Note however, that \<^locale>\<open>subgroup\<close>'s axioms only describe a technical
  relation to the superstructure, assumed to be a group. In other words, \begin{center}
 @{prop[names_short] \<open>subgroup H G \<Longrightarrow> group (G\<lparr>carrier := H\<rparr>)\<close>} \end{center} does not hold without
 the additional assumption @{prop[names_short] \<open>group G\<close>}, equivalently for ring and monoid. It is
  only under these additional assumptions that these locales coincide with the typical textbook
  definitions.\<close>

subsection \<open>\<^locale>\<open>field_extension\<close>\<close>

subsubsection \<open>Interpretation as Vector Space\<close>
(* combine these subsubsections? *)
subsubsection \<open>Degree\<close>

text \<open>In the \<open>VectorSpace\<close> theory, the infinite dimension is modelled by \<^const>\<open>vector_space.dim\<close>
 being an unspecified \<^typ>\<open>nat\<close>. My impression from reading that theory is that distinct
 representations would improve the formalisation: For instance, in \<open>VectorSpace\<close>, the dimension
 being finite does not imply @{const vectorspace.fin_dim}, counterintuitively.

As the zero vector space is no field, the degree of a field extension is never \<open>0\<close>. With the above
 consideration in mind, I therefore decided to define the infinite degree to be @{term_type "0::nat"}.
 Incidentally, for the purpose of the tower rule (\<open>\<section>\<close>\ref{sec:tr}), \<open>0\<close> and \<open>\<infinity>\<close> happen to have the same
 absorbing properties in a multiplication.

A more robust implementation would use an extended type of natural numbers, or even the full range
 of cardinal numbers. For field extensions, only one additional number is needed: My template@{cite
 Algebra1} views the degree as number in \<open>\<nat> \<union> {\<infinity>}\<close>.

Whatever the best formalisation is, the change should be made in \<open>VectorSpace\<close>: My theories only use
 what is there. Due to there being no collision with the actual \<open>0\<close>, my material should be easily
 adaptable to such a change.\<close>

section \<open>Main Results\<close>

subsection \<open>Classification of Simple Algebraic Extensions\<close>
(*<*)context UP_field_extension begin(*>*)
text \<open>Recall the context \<^locale>\<open>UP_field_extension\<close> from \<open>\<section>to-do\<close>. For an algebraic \<^term>\<open>\<alpha>\<close>,
  I define the minimal polynomial:\<close>
text_raw\<open>\isacommand{definition}
\ irr\ %
\isamarkupcmt{named after its \emph{irr}educibility (shown later)%
}\ \isanewline
\ \ \isakeyword{where}\ {\isachardoublequoteopen}irr\ {\isacharequal}\ {\isacharparenleft}ARG{\isacharunderscore}MIN\ degree\ p{\isachardot}\ p\ {\isasymin}\ carrier\ P\ {\isasymand}\ monic\ p\ {\isasymand}\ Eval\ p\ {\isacharequal}\ {\isasymzero}\isactrlbsub L\isactrlesub {\isacharparenright}{\isachardoublequoteclose}%
\<close>
text \<open>This uses an indefinite description (via @{const arg_min}) because the construction of @{const
 irr} depends on the choice of polynomial for which \<open>\<alpha>\<close> is a root. This formulation is also
  standard for textbooks.\<close>

text \<open>In \<^locale>\<open>UP_field_extension\<close>, within the above-mentioned context of an algebraic
 \<^term>\<open>\<alpha>\<close>, Theorem Kemper/16.9b@{cite Algebra1} applies. Its results are distributed:
  \<^item> @{thm[source] irr_exists}, the existence of \<^term>\<open>\<alpha>\<close>'s minimal polynomial "\<^const>\<open>irr\<close>"
  \<^item> @{thm[source] irr_unique}, the uniqueness of \<^const>\<open>irr\<close>
  \<^item> @{thm[source] irr_irreducible_polynomial}, the irreducibility of \<^const>\<open>irr\<close> in the ring
   \<^term>\<open>P\<close> of polynomials over \<^term>\<open>K\<close>
  \<^item> @{thm[source] the_elem_ring_iso_Quot_irr_generate_field}, the isomorphism of \<^term>\<open>irr\<close>'s
 residue class ring with \<open>K(\<alpha>)\<close>

All of these are on their own useful for a library, so splitting up the theorem seemed appropriate.\<close>
(*<*)end(*>*)

subsection \<open>Degree Multiplicativity (Field Extension Tower Rule)\label{sec:tr}\<close>

lemma degree_multiplicative:
  "\<lbrakk>subfield K (M\<lparr>carrier:=L\<rparr>); subfield L M; field M\<rbrakk> \<Longrightarrow>
  field_extension.degree M K =
    field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
  (*<*)by (fact degree_multiplicative)(*>*)

text \<open>The proof is covered by considering three (partially overlapping) cases:
\<^enum> The lower field extension is infinite.
\<^enum> The upper field extension is infinite.
\<^enum> Both extension parts are finite.\<close>
text\<open>Remember that infinite field extensions are encoded to have \<open>degree = 0\<close>.\<close>

text \<open>Recently, the proposition part about two \<^emph>\<open>finite\<close> extensions (case 3) has also been proven in
 another \<^session>\<open>HOL-Algebra\<close> development\<^footnote>\<open>\<^url>\<open>https://github.com/DeVilhena-Paulo/GaloisCVC4\<close>\<close>. This
 uses the inner product instead of the outer for the proof, thus avoiding the vector space
  terminology as described in \<open>\<section>\<close>\ref{sec:vs}.\<close>

section \<open>Advancements in Formalising Vector Spaces\label{sec:vs}\<close>

subsection \<open>Motivation\<close>

text \<open>The motivation for this was Kemper's proof of the tower rule, which uses results about vector
  spaces unavailable in \<^session>\<open>HOL-Algebra\<close>. Note that the tower rule could be proven more
 directly using indexed sums\<^footnote>\<open>cf.\ e.g.\
 \<^url>\<open>https://wikipedia.org/wiki/Degree_of_a_field_extension\#The_multiplicativity_formula_for_degrees\<close>\<close>,
  but the material which Kemper uses seemed to be of general usefulness for a vector space library.
 Moreover note that proofs using indexed sums tend to be very cumbersome in
  \<^session>\<open>HOL-Algebra\<close>, as explained in following sections.\<close>

subsection \<open>\<^const>\<open>ring.nspace\<close>\<close>

text \<open>This defines the $n$-fold coordinate space of a vector space.\<close>

text \<open>\<^theory_text>\<open>definition (in ring) nspace where "nspace n = func_space {..<n::nat}"\<close>,\<close>

text \<open>where \<^term_type>\<open>ring.func_space\<close> is the usual ${to-do}$\<close>

text \<open>A disadvantage of this approach is that only sums of the \<^bold>\<open>same\<close> module can be described,
  compared to \<^const>\<open>direct_sum\<close>, which can even combine modules of different \<^bold>\<open>type\<close> (over the
  same field).\<close>

text \<open>Moreover, it has been suggested that the definition is too inflexible, and that lemmas should
  maybe be stated using \<^const>\<open>ring.func_space\<close> directly.\<close>

subsection \<open>@{thm[source] vectorspace.nspace_iso}\label{sec:nspace_iso}\<close>

text \<open>This uses the newly defined constant \<^const>\<open>ring.nspace\<close>:\<close>

text "to-do"

subsection \<open>@{thm[source] vectorspace.decompose_step}\<close>

lemma "\<lbrakk>vectorspace K V; vectorspace.fin_dim K V; 0 < vectorspace.dim K V\<rbrakk> \<Longrightarrow>
  \<exists>\<phi> V'.
  linear_map K V (direct_sum (module_of K) (V\<lparr>carrier:=V'\<rparr>)) \<phi> \<and>
  bij_betw \<phi> (carrier V) (carrier K \<times> V') \<and>
  subspace K V' V \<and>
  vectorspace.dim K (V\<lparr>carrier:=V'\<rparr>) = vectorspace.dim K V - 1"
  by (fact vectorspace.decompose_step)

text \<open>This is used in the proof of the tower rule's finite case, together with induction. It needs
  to be compared to @{thm[source] vectorspace.nspace_iso}(see \<open>\<section>\<close>\ref{sec:nspace_iso}), which could
 have achieved the same with
  less work. The reason I used @{thm[source] vectorspace.decompose_step} is that I expected there to
  be some material about the direct sum to be available, as \<^const>\<open>direct_sum\<close> was already
  defined. Ultimately, no useful results turned out to exist for this function (and the definition
  itself turned out to be misleading, see \<open>\<section>\<close> to-do).\<close>

text \<open>Some ugliness of @{thm[source] vectorspace.decompose_step} comes from the use of a second
  existential quantifier for \<open>V'\<close>. This cannot be avoided elegantly, as the witness
\<^item> is somewhat unhandy (see the proof) and,
\<^item> more importantly, depends on a choice of basis, and a choice of ordering on that basis.\<close>

subsection \<open>@{thm[source] subspace.subspace_dim}\<close>

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
 \<^theory>\<open>Field_Extensions.VectorSpace\<close> and not in \<^theory>\<open>HOL.Zorn\<close>. This may be relevant
 when porting the basis extension theorem to allow for infinite dimensions.
\<close>

section \<open>Problems\<close>

subsection \<open>Non-Canonical Maps\<close>

text \<open>Some results about vector spaces and linear maps depend on a choice of basis. While bases are
 defined a sets, we sometimes need a "first" element, or even more.\<close>

text \<open>This means that we cannot translate the informal "We fix a basis B." to the \<^emph>\<open>Isar formal proof language\<close> like this:\<close>
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
 be more useful in proofs and lemma statements.\<close>

text \<open>As is known, infinite vector spaces have bases, too, but proving this requires more work and
  a different indexing scheme.\<close>

subsection \<open>Missing Lemmas\<close> (*to-do: move up? (most important problem)*)

text (* to-do: Missing sentence? *) \<open>A simple \<^theory_text>\<open>find_theorems\<close> invocation for instance reveals that not a single lemma had been
  proven within e.g.\ the \<^locale>\<open>subspace\<close> or \<^locale>\<open>submodule\<close>. However, before working on
  \<^locale>\<open>subspace\<close> one should consider \<open>\<section>\<close>to-do.\<close>

subsection \<open>Old-School Context Elements\<close> (* to-do: move? *)

text \<open>The \<^doc>\<open>locales\<close> manual@{cite "isabelle-locale"} states that \<^theory_text>\<open>defines\<close> clauses in locale
 definitions are provided only for backward compatibility, but gives no reason for the deprecation.
 My problem with \<^theory_text>\<open>defines\<close> is that it causes code duplication, e.g.\ @{thm[source]
 UP_field_extension.Eval_def} cannot be derived from @{thm[source] UP_univ_prop.Eval_def}. In my
 development, I tried to avoid \<^theory_text>\<open>defines\<close> for this reason, and used regular definitions instead.
 The only usage is in the definition of @{locale UP_field_extension}, where this seems to be the
 only way to make a \<^theory_text>\<open>(structure)\<close> declaration. An alternative with no \<^theory_text>\<open>defines\<close> at all is in the
 \isatt{no\_defines} branch\<^footnote>\<open>\<^url>\<open>https://github.com/helli/field-extensions/tree/no\_defines\<close>\<close>. This
 needs a lot more subscripts in subsequent statements and proofs, but removes the need to redefine
 \<open>P\<close> for interpretations of the locale, see the proof of @{thm[source] generate_field_\<i>_UNIV}.
\<close>

subsection \<open>No Imports in \<^locale>\<open>subspace\<close>\<close>

section \<open>Analysis of the Used Libraries\<close>

subsection \<open>\<^session>\<open>HOL-Algebra\<close>\<close> (* to-do: Remove this distinction? *)

subsubsection \<open>\<^const>\<open>Ideal.genideal\<close> and \<^const>\<open>Ideal.cgenideal\<close>\<close>

text \<open>\<^const>\<open>Ideal.genideal\<close> and \<^const>\<open>Ideal.cgenideal\<close> differ not by \<^emph>\<open>c\<close>ommutativity, but
  by whether they take a set or single element as argument. The latter should probably be renamed to
  match its function symbol \<open>PIdl\<close> (principal ideal). It could also just abbreviate
  \<^const>\<open>genideal\<close> with \<^prop>\<open>S = {a}\<close>. In any case, both functions are easy to state as hull,
  and using the material from \<^theory>\<open>HOL.Hull\<close> might shorten some proofs. In this scenario, the
 current @{thm[source] cgenideal_def} would become a lemma, perhaps stated like @{thm[source]
  cring.cgenideal_eq_rcos} to benefit from the huge \<^theory>\<open>HOL-Algebra.Coset\<close>.\<close>

subsubsection \<open>Usage of Function Symbols\<close>

text \<open>plus: it can hide obvious arguments (via \<^theory_text>\<open>structure\<close> declarations)
but the precedence is badly chosen: , which also affects my main result @{thm[source]
  UP_field_extension.simple_algebraic_extension}. Note that I also question some to-do (FactGroup, ...) , so
  there might be no motivation to use special syntax at all.\<close>

subsubsection \<open>\<^const>\<open>generate_field\<close>\<close>

text \<open>This function was added during my work. This meant that I had to do some porting (see
  \<^theory>\<open>Field_Extensions.Old_Field_Extension\<close> for the state before that). On the other hand,
  it leaves out the "lower bound" field found in @{cite Algebra1}/definition 16.4, which turned out
 to simplify matters quite a bit. A note about the style: Just like in their locale definitions, the
 authors use a technical description with the \<^theory_text>\<open>inductive_set\<close> command, instead of using
 \<^theory_text>\<open>definition\<close> and \<^const>\<open>hull\<close>.\<close>

subsubsection \<open>Difference to \<^session>\<open>HOL-Computational_Algebra\<close>\<close>

subsubsection \<open>\<^const>\<open>INTEG\<close> and \<open>\<Z>\<close>\<close>

text \<open>
Both \<^theory>\<open>HOL-Algebra.UnivPoly\<close> and \<^theory>\<open>HOL-Algebra.IntRing\<close> define an integer ring,
 i.e.\ a ring with the \<^term>\<open>UNIV\<close> of type \<^typ>\<open>int set\<close> as carrier set and the usual
 operations.
Apart from the usual problems of duplicate definitions (\<^const>\<open>INTEG\<close> vs.\ \<open>\<Z>\<close>),
they also pollute the name space: For instance,\<close>
find_theorems eval
text\<open>yields 38 facts, 15 of which are about \<^const>\<open>INTEG\<close>. These are too special and therefore
 useless when doing abstract algebra. Note that the import of \<^const>\<open>INTEG\<close> cannot be avoided when using
 old-school (see \<open>\<section>\<close>\ref{sec:poly}) polynomials, and that \<^theory_text>\<open>hide_const INTEG\<close> does not hide the facts.

When going up in the locale hierarchy (e.g. \<^locale>\<open>monoid\<close>), lemmas about \<open>\<Z>\<close> come on board, too, if
 \<^theory>\<open>HOL-Algebra.IntRing\<close> is imported.
To me, this is a reason why \<^theory>\<open>HOL-Algebra.Algebra\<close> is not attractive as an import. In future
 revisions of the library, the import of both \<^const>\<open>INTEG\<close> and \<open>\<Z>\<close> should be optional.\<close>

text\<open>\<^const>\<open>INTEG\<close> and \<open>\<Z>\<close> are unused outside of their theories, also in the
 AFP\<^footnote>\<open>\<^url>\<open>https://www.isa-afp.org\<close>\<close>. A reason may be that they are to special: Since \<^const>\<open>UNIV\<close> is
 already the largest set, they cannot be substructures. The ability to reason about substructures
 is however a common reason to use \<^session>\<open>HOL-Algebra\<close> in the first place. Section \ref{sec:ethy}
 follows a different approach using mostly abstract types.
\<close>

subsubsection \<open>\<^theory>\<open>HOL-Algebra.UnivPoly\<close> vs.\ \<^theory>\<open>HOL-Algebra.Polynomials\<close>\label{sec:poly}\<close>

text \<open>This clash of old-school @{type[names_long] up_ring} with @{const[names_long] polynomial} had
 not much effect on my development, but it means that
  \<^theory>\<open>HOL-Algebra.Polynomials\<close> cannot be added to the imports without also switching to long
  identifiers for some entities.\<close>

text \<open>The original motivation to avoid \<^theory>\<open>HOL-Algebra.Polynomials\<close> was the requirement of
  \<^const>\<open>ring.normalize\<close> in definitions, lemmas and proofs. This deficiency origins from
  representing the polynomials as coefficient lists, thereby losing uniqueness. A unification of the
 two approaches is subject of ongoing development, refer to the developers for more information.\<close>

subsubsection \<open>Side Notes\<close>

text \<open>\<^file>\<open>~~/src/HOL/Algebra/README.html\<close> is completely outdated.\<close>

text \<open>In \<^file>\<open>~~/src/HOL/Algebra/document/root.tex\<close>, I suggest to use\<close>
text \<open>\<^verbatim>\<open>\includegraphics[height=\textheight]{session_graph}\<close>\<close>
text \<open>for the session graph, so that it is
  displayed wholly in the document.\<close>

subsection \<open>\isatt{VectorSpace}\<close>

subsubsection\<open>Side Notes\<close>

(*to-do: move the observation section into these subsubsections*)

section \<open>\isatt{Examples.thy}\label{sec:ethy}\<close>

text \<open>This theory cannot use the @{theory_text \<open>interpretation\<close>} command due to some library
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

subsection \<open>Implicit properties of \<^term>\<open>\<int>\<close> etc.\<close>

text \<open>Note that \<^prop>\<open>domain Ints_ring\<close> does not hold: ...\<close>

(*<*)
end
(*>*)
