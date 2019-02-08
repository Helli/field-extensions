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
  supervised by Prof.\ Gregor Kemper and Manuel Eberl. The source files are hosted at
  \<^url>\<open>https://github.com/helli/field-extensions\<close>.\<close>

section \<open>Modelling of Substructures\<close>

text \<open>In Algebra, superstructures generally are defined to be just the inverse of substructures, as
  is the cases for fields. Thus, modelling the notion of subfield also defines field extensions
  (which is just another term for superfield).\<close>

subsection \<open>\<^const>\<open>ring.old_sr\<close>\<close>

(* to-do: explain (G\<lparr>carrier := H\<rparr>) somewhere around here *)

text \<open>To sum up, it seems advisable to fix all needed objects (sets or operations) only once within
  a locale. For Algebra this means: A group/ring needs a full record, but for substructures we
  should only add a \<^emph>\<open>set\<close> to the fixed items.\<close>

subsection \<open>\<^const>\<open>subring\<close>\<close>

text \<open>This locale from \<^session>\<open>HOL-Algebra\<close> uses this "set+superstructure"-approach, via \<^locale>\<open>subgroup\<close> and
  \<^locale>\<open>submonoid\<close>. Note however, that \<^locale>\<open>subgroup\<close>'s axioms only describe a technical
  relation to the superstructure, assumed to be a group. In other words, \begin{center}
 @{prop[names_short] \<open>subgroup H G \<Longrightarrow> group (G\<lparr>carrier := H\<rparr>)\<close>} \end{center} does not hold without
 the additional assumption @{prop[names_short] \<open>group G\<close>}, equivalently for ring and monoid. It is
  only under these additional assumptions that these locales coincide with the typical textbook
  definitions.\<close>

section \<open>The locale \<^locale>\<open>field_extension\<close>\<close>

section \<open>Main Results\<close>

subsection \<open>Classification of Simple Algebraic Extensions\<close>
(*<*)context UP_field_extension begin(*>*)
text \<open>The results of Theorem Kemper/16.9b@{cite Algebra1} are distributed over @{thm[source]
 irr_exists}, @{thm[source] irr_unique}, @{thm[source] irr_irreducible_polynomial} and @{thm[source]
 the_elem_ring_iso_Quot_irr_generate_field} (all in \<^locale>\<open>UP_field_extension\<close>). All of them are
 on their own useful for a library, so splitting
 up the theorem seemed more appropriate. Definition 16.10 is preponed to avoid confusing extra
 variables like \<open>g'\<close> or \<open>p'\<close> in later proofs. This is done via the indefinite description that
 @{const arg_min} provides:\<close>
(*<*)end(*>*)
text_raw\<open>
\isacommand{definition}\ {\isacharparenleft}\isakeyword{in}\ UP{\isacharunderscore}field{\isacharunderscore}extension{\isacharparenright}
irr\ \isakeyword{where}\ \isanewline
\ \ {\isachardoublequoteopen}irr\ {\isacharequal}\ {\isacharparenleft}ARG{\isacharunderscore}MIN\
 degree\ p{\isachardot}\ p\ {\isasymin}\ carrier\ P\ {\isasymand}\ monic\ p\ {\isasymand}\ Eval\ p\
 {\isacharequal}\ {\isasymzero}\isactrlbsub L\isactrlesub {\isacharparenright}{\isachardoublequoteclose}%
\<close>

subsection \<open>Degree Multiplicativity (Field Extension Tower Rule)\<close>

lemma "\<lbrakk>subfield K (M\<lparr>carrier:=L\<rparr>); subfield L M; field M\<rbrakk> \<Longrightarrow>
  field_extension.degree M K = field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
  by (fact degree_multiplicative)

text \<open>The proof is covered by considering three (partially overlapping) cases:
\<^enum> The lower field extension is infinite.
\<^enum> The upper field extension is infinite.
\<^enum> Both extension parts are finite.\<close>
text\<open>Remember that infinite field extensions are encoded to have \<open>degree = 0\<close>.\<close>

text \<open>Note that recently, the statement about combining finite extensions (case 3) has also been proven in
  another development\<^footnote>\<open>\<^url>\<open>https://github.com/DeVilhena-Paulo/GaloisCVC4\<close>\<close>. This uses the inner
 product instead of the outer for the proof, thus avoiding the vector space terminology as described
  in section \ref{sec:vs}.\<close>

section \<open>Advancements in Formalising Vector Spaces\label{sec:vs}\<close>

subsection \<open>Motivation\<close>

text \<open>The motivation for this was Kemper's proof of the tower rule, which uses results about vector
  spaces unavailable in \<^session>\<open>HOL-Algebra\<close>. Note that the tower rule could be proven more
 directly using indexed sums\<^footnote>\<open>see, e.g.
  \<^url>\<open>https://en.wikipedia.org/wiki/Degree_of_a_field_extension\#The_multiplicativity_formula_for_degrees\<close>\<close>,
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
  to be compared to @{thm[source] vectorspace.nspace_iso}(see \ref{sec:nspace_iso}), which could
 have achieved the same with
  less work. The reason I used @{thm[source] vectorspace.decompose_step} is that I expected there to
  be some material about the direct sum to be available, as \<^const>\<open>direct_sum\<close> was already
  defined. Ultimately, no useful results turned out to exist for this function (and the definition
  itself turned out to be misleading, see (section) to-do).\<close>

text \<open>Some ugliness of @{thm[source] vectorspace.decompose_step} comes from the use of a second
  existential quantifier for \<open>V'\<close>. This cannot be avoided elegantly, as the witness
\<^item> is somewhat unhandy (see the proof)
and, more importantly, it
\<^item> depends on a choice of basis, and a choice of ordering on that basis.\<close>

subsection \<open>@{thm[source] subspace.subspace_dim}\<close>

text \<open>These are two other useful results: to-do\<close>

section \<open>Library Analysis\<close>

subsection \<open>\<^session>\<open>HOL-Algebra\<close>\<close>

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
 old-school\ref{sec:poly} polynomials, and that \<^theory_text>\<open>hide_const INTEG\<close> does not hide the facts.

When going up in the locale hierarchy (e.g. \<^locale>\<open>monoid\<close>), lemmas about \<open>\<Z>\<close> come on board, too, if
 \<^theory>\<open>HOL-Algebra.IntRing\<close> is imported.
To me, this is a reason why \<^theory>\<open>HOL-Algebra.Algebra\<close> is not attractive as an import. In future
 revisions of the library, the import of this ring should be optional.\<close>

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
\begin{figure}
  \includegraphics[width=\linewidth]{"interpretation_error"}
  \caption[jkioj]{@{thm[source] subfield_Reals_complex_field} when stated as an interpretation: The
 proof works just as in the case of a lemma, but the fact generation fails.}
\end{figure}
\<close>
text \<open>The problem traces back to \<^locale>\<open>subring\<close> importing both \<^locale>\<open>submonoid\<close> and
 \<^locale>\<open>subgroup\<close>, which both have an axiom named \<open>subset\<close>. A workaround is known, but it
 complicated matters quite a bit, see
  \<^url>\<open>https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2018-June/msg00033.html\<close>.\<close>

subsection \<open>Implicit properties of \<^term>\<open>\<int>\<close> etc.\<close>

text \<open>Note that \<^prop>\<open>domain Ints_ring\<close> does not hold: ...\<close>

(*<*)
end
(*>*)
