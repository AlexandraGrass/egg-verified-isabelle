theory Base
  imports
    Collections.Partial_Equivalence_Relation
    "Union_Find.Union_Find"
begin

subsection \<open>Nodes and Terms\<close>

type_synonym eId = nat
datatype 'funSym eNode = nd 'funSym "eId list"
datatype 'funSym eTerm = tm 'funSym "'funSym eTerm list"

(* declare eNode.split[split] eNode.splits[split] *)

subsubsection \<open>Projections\<close>

abbreviation f\<^sub>p :: "'funSym eNode \<Rightarrow> 'funSym" where
  "f\<^sub>p n \<equiv> case n of nd f as \<Rightarrow> f"

abbreviation as\<^sub>p :: "'funSym eNode \<Rightarrow> eId list" where
  "as\<^sub>p n \<equiv> case n of nd f as \<Rightarrow> as"

lemma nd_projections_simp[simp]:
  "nd (f\<^sub>p n) (as\<^sub>p n) = n"
  by (cases n) simp

subsubsection \<open>valid_eNode\<close>

inductive valid_eNode :: "'funSym set \<Rightarrow> ('funSym \<Rightarrow> nat) \<Rightarrow> eId set \<Rightarrow> 'funSym eNode \<Rightarrow> bool" where
  introNd: "f\<^sub>p n \<in> D\<^sub>f \<Longrightarrow> length (as\<^sub>p n) = ary (f\<^sub>p n) \<Longrightarrow> list_all (\<lambda>a. a \<in> D\<^sub>a) (as\<^sub>p n)
      \<Longrightarrow> valid_eNode D\<^sub>f ary D\<^sub>a n"

lemmas valid_eNode.simps[simplified, of D\<^sub>f ary D\<^sub>a n for D\<^sub>f ary D\<^sub>a n, simp]
lemma valid_eNode_simps[simp]:
  "valid_eNode D\<^sub>f ary D\<^sub>a (nd f as) \<longleftrightarrow> (f \<in> D\<^sub>f \<and> length as = ary f \<and> list_all (\<lambda>a. a \<in> D\<^sub>a) as)"
  by simp

lemma no_valid_eNode_if_empty_D\<^sub>f[simp]: "\<not> valid_eNode {} ary D\<^sub>a n"
  by simp

subsubsection \<open>Helper lemmas\<close>

 (* Dual to ufa_rep_of_in_Field_ufa_\<alpha>I *)
lemma canonicalized_id_list_elements_in_Field_ufa_\<alpha>I[simp, intro!]:
  assumes "D\<^sub>a = Field (ufa_\<alpha> ufa)"
      and "list_all (\<lambda>a. a \<in> D\<^sub>a) as"
    shows "list_all (\<lambda>a. a \<in> D\<^sub>a) (map (\<lambda>a. ufa_rep_of ufa a) as)"
  by (auto simp: assms list.pred_map comp_def intro: list.pred_mono_strong[OF assms(2)])

lemma canonicalization_of_valid_ids_is_idempotent[simp, intro!]:
  assumes "D\<^sub>a = Field (ufa_\<alpha> ufa)"
      and "list_all (\<lambda>a. a \<in> D\<^sub>a) as"
    shows "map (\<lambda>a. (ufa_rep_of ufa \<circ> ufa_rep_of ufa) a) as = map (\<lambda>a. ufa_rep_of ufa a) as"
  by (auto simp: assms(2)[simplified assms(1) list_all_iff])

subsection \<open>Invariants\<close>

definition "H_dom_invar H D\<^sub>f ary D\<^sub>a \<equiv> \<forall> n \<in> dom H. valid_eNode D\<^sub>f ary D\<^sub>a n"
definition "H_ran_invar H D\<^sub>a \<equiv> \<forall> a \<in> ran H. a \<in> D\<^sub>a"

lemma H_dom_invarD:
  assumes "H_dom_invar H D\<^sub>f ary D\<^sub>a"
      and "n \<in> dom H"
  shows "valid_eNode D\<^sub>f ary D\<^sub>a n"
  using assms unfolding H_dom_invar_def by blast

lemma H_ran_invarD:
  assumes "H_ran_invar H D\<^sub>a"
      and "a \<in> ran H"
  shows " a \<in> D\<^sub>a"
  using assms unfolding H_ran_invar_def by blast

subsection \<open>E-graphs as a 4-tuple\<close>

type_synonym 'a egg_tuple = "'a set \<times> ('a \<Rightarrow> nat) \<times> ufa \<times> ('a eNode \<rightharpoonup> nat)"

subsubsection \<open>Projections\<close>

abbreviation D\<^sub>f\<^sub>p :: "'a egg_tuple \<Rightarrow> 'a set" where
  "D\<^sub>f\<^sub>p egg \<equiv> fst egg"

abbreviation ary\<^sub>p :: "'a egg_tuple \<Rightarrow> 'a \<Rightarrow> nat" where
  "ary\<^sub>p egg \<equiv> (fst \<circ> snd) egg"

abbreviation H\<^sub>p :: "'a egg_tuple \<Rightarrow> 'a eNode \<rightharpoonup> nat" where
  "H\<^sub>p egg \<equiv> (snd \<circ> snd \<circ> snd) egg"

abbreviation U\<^sub>p :: "'a egg_tuple \<Rightarrow> ufa" where
  "U\<^sub>p egg \<equiv> (fst \<circ> snd \<circ> snd) egg"

abbreviation D\<^sub>a\<^sub>p :: "'a egg_tuple \<Rightarrow> nat set" where
  "D\<^sub>a\<^sub>p egg \<equiv> Field (ufa_\<alpha> (U\<^sub>p egg))"

(*
- Do we need some sort of lemma saying "\<forall> a, b \<in> ran H. find a = find b \<longleftrightarrow> _"?
- What about constants (nd "x" []) allowed by D\<^sub>f and ary that do not show up in H?
  But maybe that does not matter – we can just assume stuff is only added via supplied interface
  and therefore added to the system consistently.
- lemma egg_canoncicalize_on_const_in_D\<^sub>f_is_id
- connect valid eNodes and lookup?
- lemmas showing properties about predicates, e.g. that valid eNodes only contain valid ids?
*)

subsubsection \<open>egg_invar\<close>

definition egg_invar :: "'a egg_tuple \<Rightarrow> bool" where
  "egg_invar egg \<equiv> H_dom_invar (H\<^sub>p egg) (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg)
                    \<and> H_ran_invar (H\<^sub>p egg) (D\<^sub>a\<^sub>p egg)"

lemmas egg_invar_def_unfolded =
  egg_invar_def[unfolded H_dom_invar_def H_ran_invar_def,
                of "(D\<^sub>f, ary, ufa, H)" for D\<^sub>f ary ufa H, simplified]

lemma egg_invarI[intro]:
  assumes "H_dom_invar H D\<^sub>f ary (Field (ufa_\<alpha> ufa))"
      and "H_ran_invar H (Field (ufa_\<alpha> ufa))"
  shows "egg_invar (D\<^sub>f, ary, ufa, H)"
  using assms unfolding egg_invar_def by fastforce

end (* end of theory Base *)
