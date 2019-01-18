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

section \<open>Library Analysis\<close>

subsection \<open>\<^session>\<open>HOL-Algebra\<close>\<close>

subsubsection\<open>Side Notes\<close>

text \<open>\<^file>\<open>~~/src/HOL/Algebra/README.html\<close> is completely outdated.\<close>

subsection \<open>\isatt{VectorSpace}\<close>

subsubsection\<open>Side Notes\<close>

(*to-do: move the observation section into these subsubsections*)

(*<*)
end
(*>*)
