theory AbstractEgg
  imports
    RawEgg
begin

(* TODO: Below lifted definitions and transferred lemmas are not complete yet, but can easily be
   added. When doing so, we intend to design a clean interface where information about the
   implementation of non-valid / undefined cases is not leaked / propagated to the abstract data
   type. That implies that most of the lemmas will be conditional; assuming the parameters are
   well-formed. *)

typedef 'a egg =
    "{egg :: 'a egg_tuple. egg_invar egg}"
proof -
  have "egg_invar ({}, (\<lambda>x. 0), (ufa_init 0), (\<lambda>x. None))"
    unfolding egg_invar_def_unfolded by fastforce
  then show ?thesis
    by blast
qed

section \<open>Lifting\<close>

setup_lifting type_definition_egg

subsection \<open>egg_init\<close>

lift_definition egg_init :: "'a egg" is init
  by transfer (simp add: init_def egg_invar_def_unfolded)

subsection \<open>egg_is_valid_nd\<close>

lift_definition egg_is_valid_nd :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> bool" is is_valid_nd .

lemma no_valid_nd_in_egg_init: "egg_is_valid_nd egg_init n = False"
  by transfer (rule no_valid_nd_in_init)

subsection \<open>egg_is_canonical_nd\<close>

lift_definition egg_is_canonical_nd :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> bool" is is_canonical_nd .

lemma egg_canonical_nd_is_valid_nd[simp]: "egg_is_canonical_nd egg n \<Longrightarrow> egg_is_valid_nd egg n"
  by transfer (rule canonical_nd_is_valid_nd)

lemma no_canonical_nd_in_egg_init: "\<not> egg_is_canonical_nd egg_init n"
  using no_valid_nd_in_egg_init egg_canonical_nd_is_valid_nd by blast

subsection \<open>egg_canonicalize\<close>

lift_definition egg_canonicalize :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> 'a eNode" is canonicalize .

lemma egg_valid_canonicalized_node_is_canonical :
  "egg_is_valid_nd egg n \<Longrightarrow> egg_is_canonical_nd egg (egg_canonicalize egg n)"
  by transfer (rule valid_canonicalized_node_is_canonical)

lemma egg_canoncicalize_canoncial_node_is_id :
  "egg_is_canonical_nd egg n \<Longrightarrow> egg_canonicalize egg n = n"
  by transfer (rule canoncicalize_canoncial_node_is_id)

lemma egg_canonicalize_is_idempotent:
  assumes "egg_is_valid_nd egg n"
  shows "egg_canonicalize egg (egg_canonicalize egg n) = egg_canonicalize egg n"
  using assms egg_canoncicalize_canoncial_node_is_id egg_valid_canonicalized_node_is_canonical
  by blast

lemma egg_valid_canonicalized_node_is_valid:
  "egg_is_valid_nd egg n \<Longrightarrow> egg_is_valid_nd egg (egg_canonicalize egg n)"
  by transfer (rule valid_canonicalized_node_is_valid)

subsection \<open>egg_lookup\<close>

lift_definition egg_lookup :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> eId option" is lookup .

lemma egg_lookup_on_init_is_none: "egg_lookup egg_init n = None"
  by transfer (rule lookup_on_init_is_none)

lemma egg_lookup_is_egg_lookup_on_canonicalized_node:
  "egg_is_valid_nd egg n \<Longrightarrow> egg_lookup egg (egg_canonicalize egg n) = egg_lookup egg n"
  by transfer (rule lookup_is_lookup_on_canonicalized_node)

subsection \<open>egg_is_valid_candidate\<close>

lift_definition egg_is_valid_candidate :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> bool" is is_valid_candidate .

lemma egg_valid_nd_is_valid_candidate : "egg_is_valid_nd egg n \<Longrightarrow> egg_is_valid_candidate egg n"
  by transfer (rule valid_nd_is_valid_candidate)

subsection \<open>egg_add\<close>

lift_definition egg_add :: "'a egg \<Rightarrow> 'a eNode \<Rightarrow> eId option \<times> 'a egg" is add
  by (auto split: pred_prod_split simp: add_preserves_egg_invar)

subsection \<open>egg_eq_class\<close>

lift_definition egg_eq_class :: "'a egg \<Rightarrow> eId \<Rightarrow> 'a eNode set" is eq_class .

lemma egg_eq_class_of_egg_init_empty: "egg_eq_class egg_init a = {}"
  by transfer (rule eq_class_of_init_empty)

end (* end of theory AbstractEgg *)
