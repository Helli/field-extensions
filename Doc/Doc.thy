(*<*)
theory Doc
  imports
    Field_Extensions.Examples
    Field_Extensions.Old_Field_Extension
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

subsection \<open>\<^const>\<open>subring\<close>\<close>

text \<open>This locale from \<^session>\<open>HOL-Algebra\<close> uses the "set+superstructure"-approach, via \<^locale>\<open>subgroup\<close> and
  \<^locale>\<open>submonoid\<close>. Note however, that \<^locale>\<open>subgroup\<close>'s axioms only describe a technical
  relation to the superstructure, assumed to be a group. In other words, \begin{center}
 @{prop[names_short] \<open>subgroup H G \<Longrightarrow> group (G\<lparr>carrier := H\<rparr>)\<close>} \end{center} does not hold without
 the additional assumption @{prop[names_short] \<open>group G\<close>}, equivalently for ring and monoid. It is
  only under these additional assumptions that these locales coincide with the textbook definitions.\<close>

section \<open>The locale \<^locale>\<open>field_extension\<close>\<close>

section \<open>Main Results\<close>

subsection \<open>Degree Multiplicativity (Field Extension Tower Rule)\<close>

lemma "\<lbrakk>subfield K (M\<lparr>carrier:=L\<rparr>); subfield L M; field M\<rbrakk> \<Longrightarrow>
  field_extension.degree M K = field_extension.degree M L * field_extension.degree (M\<lparr>carrier:=L\<rparr>) K"
  by (fact degree_multiplicative)

text \<open>The proof is covered by considering three cases:
\<^enum> The lower field extension is infinite.
\<^enum> The upper field extension is infinite.
\<^enum> Both extension parts are finite.\<close>
text\<open>Remember that an infinite field extension is encoded to have \<open>degree = 0\<close>.\<close>

text \<open>Note that recently, the statement about combining finite extensions (case 3) has also been proven in
  another development\<^footnote>\<open>\<^url>\<open>https://github.com/DeVilhena-Paulo/GaloisCVC4\<close>\<close>. This uses the inner
 product instead of the outer, thus avoiding the vector space terminology as described in section \ref{sec:vs}.\<close>

subsection \<open>Advancements in Formalising Vector Spaces\label{sec:vs}\<close>

text \<open>The motivation for this was Kemper's proof of the tower rule, which uses results about vector
  spaces unavailable in \<^session>\<open>HOL-Algebra\<close>. Note that the proof could be done more
  directly\<^footnote>\<open>see, e.g. \<^url>\<open>https://en.wikipedia.org/wiki/Degree_of_a_field_extension\#The_multiplicativity_formula_for_degrees\<close>\<close>\<close>

section \<open>Library Analysis\<close>

subsection \<open>\<^session>\<open>HOL-Algebra\<close>\<close>

subsubsection\<open>Difference to \<^session>\<open>HOL-Computational_Algebra\<close>\<close>

subsubsection\<open>Side Notes\<close>

text \<open>\<^file>\<open>~~/src/HOL/Algebra/README.html\<close> is completely outdated.\<close>

subsection \<open>\isatt{VectorSpace}\<close>

subsubsection\<open>Side Notes\<close>

(*to-do: move the observation section into these subsubsections*)

section \<open>\isatt{Examples.thy}\<close>

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

(*<*)
end
(*>*)
