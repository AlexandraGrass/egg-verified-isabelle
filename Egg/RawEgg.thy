theory RawEgg
  imports
    Base
begin

subsection \<open>init\<close>

definition init :: "'a egg_tuple" where
  "init = ({}, \<lambda>f. 0, ufa_init 0, \<lambda>n. None)"
declare init_def[simp]

subsection \<open>is_valid_nd\<close>

definition is_valid_nd :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> bool" where
  "is_valid_nd egg n = valid_eNode (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg) n"
declare is_valid_nd_def[simp]

lemma is_valid_nd_I[intro]:
  assumes "valid_eNode (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg) n"
  shows "is_valid_nd egg n"
  using assms by force

lemma is_valid_nd_E[elim]:
  assumes "is_valid_nd egg n"
  obtains "valid_eNode (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg) n"
  using assms by simp

lemma no_valid_nd_in_init: "is_valid_nd init n = False"
  by simp

subsection \<open>is_canonical_nd\<close>

definition is_canonical_nd :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> bool" where
  "is_canonical_nd egg n = (
    if is_valid_nd egg n
    then list_all (\<lambda>a. ufa_rep_of (U\<^sub>p egg) a = a) (as\<^sub>p n)
    else False)"  (* undefined case – or not? Because a canonical nd is basically just a valid nd *)
declare is_canonical_nd_def[simp]    (* and some extra requirement. Does imo not leak too much. *)

(* Write intro rule? *)

lemma canonical_nd_is_valid_nd[simp]: "is_canonical_nd egg n \<Longrightarrow> is_valid_nd egg n"
  by (auto split: if_splits)

lemma no_canonical_nd_in_init: "\<not> is_canonical_nd init n"
  using no_valid_nd_in_init canonical_nd_is_valid_nd by blast

subsection \<open>has_only_valid_children\<close>

definition has_only_valid_children :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> bool" where
  "has_only_valid_children egg n = list_all (\<lambda>a. a \<in> D\<^sub>a\<^sub>p egg) (as\<^sub>p n)"
declare has_only_valid_children_def[simp]

lemma valid_nd_has_only_valid_children[simp]: "is_valid_nd egg n \<Longrightarrow> has_only_valid_children egg n"
  by force

subsection \<open>canonicalize\<close>

definition canonicalize :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> 'a eNode" where
  "canonicalize egg n = (
    if has_only_valid_children egg n
    then nd (f\<^sub>p n) (map (ufa_rep_of (U\<^sub>p egg)) (as\<^sub>p n))
    else undefined)"  (* undefined case – should if case require valid_candidate? *)
declare canonicalize_def[simp]

lemma
  assumes "has_only_valid_children egg n"
      and "n' = canonicalize egg n" (* maybe this needs to be switched as well... *)
    shows canonicalized_f_remains_unchanged: "f\<^sub>p n' = f\<^sub>p n"
      and number_of_canonicalized_children_remains_unchanged: "length (as\<^sub>p n') = length (as\<^sub>p n)"
  using assms by simp+

lemma valid_canonicalized_node_is_canonical :
  "is_valid_nd egg n \<Longrightarrow> is_canonical_nd egg (canonicalize egg n)"
  by (auto simp: Ball_set[symmetric])

lemma canoncicalize_canoncial_node_is_id :
  "is_canonical_nd egg n \<Longrightarrow> canonicalize egg n = n"
  by (auto simp: list.map_cong_pred split: if_splits)

lemma canonicalize_is_idempotent:
  assumes "is_valid_nd egg n"
  shows "canonicalize egg (canonicalize egg n) = canonicalize egg n"
  using assms canoncicalize_canoncial_node_is_id valid_canonicalized_node_is_canonical
  by blast

lemma valid_canonicalized_node_is_valid:
  "is_valid_nd egg n \<Longrightarrow> is_valid_nd egg (canonicalize egg n)"
  by auto

subsection \<open>are_canonequivalent\<close>

definition are_canonequivalent :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> 'a eNode \<Rightarrow> bool"
  where "are_canonequivalent egg n\<^sub>1 n\<^sub>2 \<equiv>
      has_only_valid_children egg n\<^sub>1 \<and> has_only_valid_children egg n\<^sub>2 \<and>
      canonicalize egg n\<^sub>1 = canonicalize egg n\<^sub>2"
declare are_canonequivalent_def[simp]

lemma are_canonequivalent_I[intro]:
  assumes "has_only_valid_children egg n\<^sub>1"
      and "has_only_valid_children egg n\<^sub>2"
      and "canonicalize egg n\<^sub>1 = canonicalize egg n\<^sub>2"
  shows "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
  using assms by auto

lemma are_canonequivalent_E[elim]:
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
  obtains "has_only_valid_children egg n\<^sub>1"
      and "has_only_valid_children egg n\<^sub>2"
      and "canonicalize egg n\<^sub>1 = canonicalize egg n\<^sub>2"
  using assms by simp+

lemma canoequivalence_is_sym: "are_canonequivalent egg n\<^sub>1 n\<^sub>2 \<Longrightarrow> are_canonequivalent egg n\<^sub>2 n\<^sub>1"
  by auto

lemma
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
    shows are_canonequivalent_implies_same_fun_sym: "f\<^sub>p n\<^sub>1 = f\<^sub>p n\<^sub>2"
      and are_canonequivalent_implies_same_fun_arity: "length (as\<^sub>p n\<^sub>1) = length (as\<^sub>p n\<^sub>2)"
  using assms number_of_canonicalized_children_remains_unchanged
  by fastforce+

lemma node_and_its_repr_are_canonequivalent:
  assumes "has_only_valid_children egg n"
  shows "are_canonequivalent egg n (canonicalize egg n)"
  using assms by force

lemma validity_of_node_extends_to_all_canonequivalent:
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
    shows "is_valid_nd egg n\<^sub>1 \<longleftrightarrow> is_valid_nd egg n\<^sub>2"
  using are_canonequivalent_implies_same_fun_arity[OF assms] assms
  by fastforce

lemma repr_of_canonequivalent_is_unique_left:
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
      and "is_canonical_nd egg n\<^sub>1"
    shows "canonicalize egg n\<^sub>2 = n\<^sub>1"
  by (metis are_canonequivalent_def assms(1,2) canoncicalize_canoncial_node_is_id)

lemma repr_of_canonequivalent_is_unique_right:
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
      and "is_canonical_nd egg n\<^sub>2"
    shows "canonicalize egg n\<^sub>1 = n\<^sub>2"
    by (metis are_canonequivalent_def assms(1,2) canoncicalize_canoncial_node_is_id)

subsection \<open>lookup\<close>

definition lookup :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> eId option" where
  "lookup egg n = (H\<^sub>p egg) (canonicalize egg n)"
declare lookup_def[simp]

(*
lemma lookup_success_only_on_valid_nds:
  "lookup egg n = Some a \<Longrightarrow> is_valid_nd egg n"

Dies because the following lemma does also not hold true anymore:

lemma is_valid_canonicalized_nd_implies_is_valid_nd:
  "is_valid_nd egg (canonicalize egg n) \<Longrightarrow> is_valid_nd egg n"
*)

lemma lookup_on_init_is_none: "lookup init n = None"
  by simp (* So looking up sth undefined is fine?! *)

lemma lookup_is_lookup_on_canonicalized_node:
  "is_valid_nd egg n \<Longrightarrow> lookup egg (canonicalize egg n) = lookup egg n"
  by auto

lemma lookup_of_canonequivalent_is_same:
  assumes "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
  shows "lookup egg n\<^sub>1 = lookup egg n\<^sub>2"
  using assms by auto

subsection \<open>Equivalence over e-nodes\<close>

definition \<alpha> :: "'a egg_tuple \<Rightarrow> 'a eNode rel" where
  "\<alpha> egg \<equiv> {(n\<^sub>1, n\<^sub>2). \<exists>a b. is_valid_nd egg n\<^sub>1 \<and> lookup egg n\<^sub>1 = Some a \<and>
                            is_valid_nd egg n\<^sub>2 \<and> lookup egg n\<^sub>2 = Some b \<and>
                            (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)}"
(* has_only_valid_children egg n would suffice – do I want that? *)

lemma Field_\<alpha>[simp]:
  shows "n \<in> Field (\<alpha> egg) \<longleftrightarrow> (\<exists>a. is_valid_nd egg n \<and> lookup egg n = Some a \<and> a \<in> D\<^sub>a\<^sub>p egg)"
proof -
  have "(n, n) \<in> \<alpha> egg \<longleftrightarrow> (\<exists>a. is_valid_nd egg n \<and> lookup egg n = Some a \<and> a \<in> D\<^sub>a\<^sub>p egg)"
  proof
    assume "(n, n) \<in> \<alpha> egg"
    thus "\<exists>a. is_valid_nd egg n \<and> lookup egg n = Some a \<and> a \<in> D\<^sub>a\<^sub>p egg"
      by (auto simp: \<alpha>_def Field_iff)
  next
    assume assm: "\<exists>a. is_valid_nd egg n \<and> lookup egg n = Some a \<and> a \<in> D\<^sub>a\<^sub>p egg"
    obtain a where "lookup egg n = Some a" and "a \<in> D\<^sub>a\<^sub>p egg"
      using assm by force
    hence  "(a,a) \<in> ufa_\<alpha> (U\<^sub>p egg)"
      using ufa_rep_of_eq_iff_in_ufa_\<alpha> by blast
    show "(n, n) \<in> \<alpha> egg"
      unfolding \<alpha>_def
      using assm \<open>lookup egg n = Some a\<close> \<open>(a,a) \<in> ufa_\<alpha> (U\<^sub>p egg)\<close>
      by blast
  qed

  thus ?thesis
    by (auto simp: Field_iff \<alpha>_def)
qed

lemma Field_\<alpha>_if_egg_invar[simp]:
  assumes "egg_invar egg"
      and "has_only_valid_children egg n"
  shows "n \<in> Field (\<alpha> egg) \<longleftrightarrow> canonicalize egg n \<in> dom (H\<^sub>p egg)"
proof -
  have "(n, n) \<in> \<alpha> egg \<longleftrightarrow> canonicalize egg n \<in> dom (H\<^sub>p egg)"
  proof
    assume "(n, n) \<in> \<alpha> egg"
    thus "canonicalize egg n \<in> dom (H\<^sub>p egg)"
      by (auto simp: assms(2) \<alpha>_def)
  next
    assume assm: "canonicalize egg n \<in> dom (H\<^sub>p egg)"
    hence "is_valid_nd egg (canonicalize egg n)"
      using assms[unfolded egg_invar_def H_dom_invar_def] by blast
    hence "is_valid_nd egg n" using assms(2) by simp
    obtain a where a_def: "lookup egg n = Some a"
      using assm by force
    have "(a,a) \<in> ufa_\<alpha> (U\<^sub>p egg)"
      using assms[unfolded egg_invar_def H_ran_invar_def] a_def ufa_rep_of_eq_iff_in_ufa_\<alpha>
      by (auto intro!: ranI)
    show "(n, n) \<in> \<alpha> egg"
      unfolding \<alpha>_def
      using \<open>is_valid_nd egg n\<close> \<open>lookup egg n = Some a\<close> \<open>(a,a) \<in> ufa_\<alpha> (U\<^sub>p egg)\<close>
      by blast
  qed

  thus ?thesis
    by (auto simp: Field_iff \<alpha>_def)
qed

lemma in_\<alpha>I[intro]:
  assumes "is_valid_nd egg n\<^sub>1" "is_valid_nd egg n\<^sub>2"
          "\<exists>a b. lookup egg n\<^sub>1 = Some a \<and> lookup egg n\<^sub>2 = Some b \<and> (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
  using assms unfolding \<alpha>_def by blast

lemma in_\<alpha>E[elim]:
  assumes "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
  obtains "is_valid_nd egg n\<^sub>1" "is_valid_nd egg n\<^sub>2"
          "\<exists>a b. lookup egg n\<^sub>1 = Some a \<and> lookup egg n\<^sub>2 = Some b \<and> (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
  using assms unfolding \<alpha>_def by fast

lemma trans_\<alpha>: "(x, y) \<in> \<alpha> egg \<Longrightarrow> (y, z) \<in> \<alpha> egg \<Longrightarrow> (x, z) \<in> \<alpha> egg"
proof
  assume xy_in_\<alpha>: "(x, y) \<in> \<alpha> egg" and yz_in_\<alpha>: "(y, z) \<in> \<alpha> egg"
  thus "is_valid_nd egg x" and "is_valid_nd egg z"
    by auto

  obtain a where a_def: "lookup egg x = Some a"
    using \<open>(x, y) \<in> \<alpha> egg\<close> by blast
  obtain id\<^sub>y where id\<^sub>y_def: "lookup egg y = Some id\<^sub>y"
    using \<open>(x, y) \<in> \<alpha> egg\<close> by blast
  obtain b where b_def: "lookup egg z = Some b"
    using \<open>(y, z) \<in> \<alpha> egg\<close> by blast

  have "(a, id\<^sub>y) \<in> ufa_\<alpha> (U\<^sub>p egg)" and "(id\<^sub>y, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    using a_def id\<^sub>y_def b_def xy_in_\<alpha> yz_in_\<alpha> by fastforce+
  hence "(a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    using part_equiv_trans[OF part_equiv_ufa_\<alpha>] by fast

  show "\<exists>a b. lookup egg x = Some a \<and> lookup egg z = Some b \<and> (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    using \<open>lookup egg x = Some a\<close> \<open>lookup egg z = Some b\<close> \<open>(a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)\<close>
    by fast
qed

lemma sym_\<alpha>: "(x, y) \<in> \<alpha> egg \<Longrightarrow> (y, x) \<in> \<alpha> egg"
  using part_equiv_sym[OF part_equiv_ufa_\<alpha>]
  by (auto elim!: in_\<alpha>E)

lemma part_equiv_\<alpha>: "part_equiv (\<alpha> egg)"
  by (auto intro: part_equivI symI sym_\<alpha> transI trans_\<alpha>)

lemma
  assumes "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
  shows canonicalized_nd_is_in_same_rel_\<alpha>_left: "(canonicalize egg n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
    and canonicalized_nd_is_in_same_rel_\<alpha>_right: "(n\<^sub>1, canonicalize egg n\<^sub>2) \<in> \<alpha> egg"
  using assms by fastforce+

lemma nds_with_valid_children_are_in_same_rel_\<alpha>_as_their_canonical_repr_left:
  assumes "has_only_valid_children egg n\<^sub>1"
      and "(canonicalize egg n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
  using assms by fastforce

lemma nds_with_valid_children_are_in_same_rel_\<alpha>_as_their_canonical_repr_right:
  assumes "has_only_valid_children egg n\<^sub>2"
      and "(n\<^sub>1, canonicalize egg n\<^sub>2) \<in> \<alpha> egg"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
  using assms by fastforce

lemma valid_canonequivalent_nodes_are_in_\<alpha>:
  assumes "is_valid_nd egg n\<^sub>1"
      and "are_canonequivalent egg n\<^sub>1 n\<^sub>2"
      and "lookup egg n\<^sub>1 = Some id\<^sub>1"
      and "id\<^sub>1 \<in> D\<^sub>a\<^sub>p egg"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
proof
  show "is_valid_nd egg n\<^sub>1" and "is_valid_nd egg n\<^sub>2"
    using assms(1,2) validity_of_node_extends_to_all_canonequivalent
    by blast+

  have "lookup egg n\<^sub>1 = Some id\<^sub>1" and "lookup egg n\<^sub>2 = Some id\<^sub>1"
    using assms(3) lookup_of_canonequivalent_is_same[OF assms(2)] by auto
  moreover have "(id\<^sub>1, id\<^sub>1) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    using assms(4) by (auto intro!: ufa_\<alpha>I)
  ultimately show "\<exists>a b. lookup egg n\<^sub>1 = Some a \<and> lookup egg n\<^sub>2 = Some b \<and> (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    by blast
qed

lemma successful_lookup_implies_node_reflexive_in_\<alpha>:
  assumes "is_valid_nd egg n"
      and "lookup egg n = Some id\<^sub>l"
      and "id\<^sub>l \<in> D\<^sub>a\<^sub>p egg"
    shows "(n, n) \<in> \<alpha> egg"
  using assms by (auto intro!: ufa_\<alpha>I)

(* TODO: HOL/EquivRelations
- defines congruence!
- defines quotient types
- talks about lifting *)

subsection \<open>D_n as the domain of nodes considered by the e-graph\<close>

abbreviation D\<^sub>n :: "'a egg_tuple \<Rightarrow> 'a eNode set" where
  "D\<^sub>n egg \<equiv> Field (\<alpha> egg)"

lemma no_nodes_in_Field_\<alpha>_init: "D\<^sub>n init = {}"
  by fastforce

lemma in_Field_\<alpha>_init_implies_valid: "n \<in> D\<^sub>n egg \<Longrightarrow> is_valid_nd egg n"
  by force

lemma equiv_Field_\<alpha>_\<alpha>: "equiv (D\<^sub>n egg) (\<alpha> egg)"
proof (rule equivI)
  show "\<alpha> egg \<subseteq> D\<^sub>n egg \<times> D\<^sub>n egg"
    using Restr_Field by (auto simp: Int_lower2 )
  show "Refl (\<alpha> egg)"
    by (meson Field_\<alpha> in_\<alpha>I equiv_Field_ufa_\<alpha>_ufa_\<alpha> equiv_def refl_on_def)
qed (auto intro: part_equivI symI sym_\<alpha> transI trans_\<alpha>)

(* Might be interesting to have the finiteness as part of the invar? *)
lemma "finite (D\<^sub>n egg)"
  unfolding \<alpha>_def using finite_Field_ufa_\<alpha> oops

lemma canonicalize_in_Field_\<alpha>I[simp, intro]:
  assumes "n \<in> D\<^sub>n egg"
  shows "canonicalize egg n \<in> D\<^sub>n egg"
  using assms by auto

lemma lookup_in_Field_ufa_\<alpha>I[simp, intro]:
  assumes "n \<in> D\<^sub>n egg"
  shows "the (lookup egg n) \<in> D\<^sub>a\<^sub>p egg"
  using assms by auto

lemma successful_lookup_implies_node_in_Field_\<alpha>:
  assumes "is_valid_nd egg n"
      and "lookup egg n = Some id\<^sub>l"
      and "id\<^sub>l \<in> D\<^sub>a\<^sub>p egg"
    shows "n \<in> D\<^sub>n egg"
  using successful_lookup_implies_node_reflexive_in_\<alpha>[OF assms(1-3)]
  by (auto simp: Field_iff)

subsection \<open>is_valid_candidate\<close>

(* How to handle cases where f is already in D\<^sub>f, but with a different arity?
   \<rightarrow> introduce a predicate is_valid_candidate that checks whether f and its arity agree with D\<^sub>f
      and ary, and checks that ids are valid!
   This definition does not allow nodes to refer to themselves (which actually makes sense). *)
definition is_valid_candidate :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> bool" where
  "is_valid_candidate egg n \<equiv>
    has_only_valid_children egg n \<and> (f\<^sub>p n \<in> D\<^sub>f\<^sub>p egg \<longrightarrow> (ary\<^sub>p egg) (f\<^sub>p n) = length (as\<^sub>p n))"
declare is_valid_candidate_def[simp]

lemma valid_candidate_becomes_valid_nd_if:
  assumes "is_valid_candidate egg n"
      and "D\<^sub>f' = insert (f\<^sub>p n) (D\<^sub>f\<^sub>p egg)"
      and "ary' = (ary\<^sub>p egg)(f\<^sub>p n := length (as\<^sub>p n))"
    shows "is_valid_nd (D\<^sub>f', ary', U\<^sub>p egg, H\<^sub>p egg) n"
  using assms by force

lemma valid_nd_is_valid_candidate[simp]: "is_valid_nd egg n \<Longrightarrow> is_valid_candidate egg n"
  by fastforce

lemma canonicalized_valid_candidate_is_valid_nd_implies_nd_is_valid:
  assumes "is_valid_candidate egg n"
      and "is_valid_nd egg (canonicalize egg n)"
    shows "is_valid_nd egg n"
  using assms by simp

subsection \<open>add\<close>

declare lookup_def[simp del]

definition add :: "'a egg_tuple \<Rightarrow> 'a eNode \<Rightarrow> eId option \<times> 'a egg_tuple" where
  "add egg n = (
    if \<not> is_valid_candidate egg n then (None, egg)
    else
      let id = lookup egg n in
      case id of
        None \<Rightarrow> let D\<^sub>f' = insert (f\<^sub>p n) (D\<^sub>f\<^sub>p egg);
                    ary' = (ary\<^sub>p egg)(f\<^sub>p n := length (as\<^sub>p n));
                    n\<^sub>c = canonicalize (D\<^sub>f', ary', U\<^sub>p egg, H\<^sub>p egg) n;
                    (id', ufa') = ufa_extend (U\<^sub>p egg);
                    H' = (H\<^sub>p egg)(n\<^sub>c \<mapsto> id') in
                (Some id', D\<^sub>f', ary', ufa', H')
      | Some id' \<Rightarrow> (Some id', egg))"

(* TODO: direction of equalities should be chosen as simp rules.
   That means for a "let x = a in foo" there should be the rule "a = x"!
   let definitions do the opposite: *)
thm add_def[simplified Let_def]

lemma add_cases:
  assumes "add egg n = (id', egg')"
  obtains (Not_Valid)
        "\<not> is_valid_candidate egg n"
    and "(id', egg') = (None, egg)"   (* TODO: Once again, this case should be undefined *)
  | (Already_Contained) id\<^sub>l
  where "is_valid_candidate egg n"
    and "lookup egg n = Some id\<^sub>l"
    and "Some id\<^sub>l = id'"
    and "egg' = egg"
  | (Newly_Added) D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H'
  where "is_valid_candidate egg n"
    and "lookup egg n = None"
    and "D\<^sub>f' = insert (f\<^sub>p n) (D\<^sub>f\<^sub>p egg)"
    and "ary' = (ary\<^sub>p egg)(f\<^sub>p n := length (as\<^sub>p n))"
    and "n\<^sub>c = canonicalize (D\<^sub>f', ary', U\<^sub>p egg, H\<^sub>p egg) n"
    and "(id\<^sub>e, ufa') = ufa_extend (U\<^sub>p egg)"
    and "H' = (H\<^sub>p egg)(n\<^sub>c \<mapsto> id\<^sub>e)"
    and "id' = Some id\<^sub>e"
    and "egg' = (D\<^sub>f', ary', ufa', H')"
proof(cases "is_valid_candidate egg n" rule: case_split[case_names Valid Invalid])
  case Valid
  obtain idOpt where idOpt_def: "lookup egg n = idOpt" by blast
  then show ?thesis
  proof(cases idOpt rule: option.exhaust[case_names New_Node Contained])
    case New_Node
    obtain D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H'
      where D\<^sub>f'_def: "D\<^sub>f' = insert (f\<^sub>p n) (D\<^sub>f\<^sub>p egg)"
        and ary'_def: "ary' = (ary\<^sub>p egg)(f\<^sub>p n := length (as\<^sub>p n))"
        and n\<^sub>c_def: "n\<^sub>c = canonicalize (D\<^sub>f', ary', U\<^sub>p egg, H\<^sub>p egg) n"
        and extension_def: "(id\<^sub>e, ufa') = ufa_extend (U\<^sub>p egg)"
        and H'_def: "H' = (H\<^sub>p egg)(n\<^sub>c \<mapsto> id\<^sub>e)"
      by (metis old.prod.exhaust)
    note obtain_defs = D\<^sub>f'_def ary'_def[simplified] n\<^sub>c_def extension_def[simplified] H'_def

    have lkp_None: "lookup egg n = None"
      using New_Node idOpt_def by argo

    have "id' = Some id\<^sub>e" and "egg' = (D\<^sub>f', ary', ufa', H')"
      using assms
      by (auto simp: add_def Valid lkp_None obtain_defs(1,2,4,5)[symmetric] n\<^sub>c_def H'_def
               simp del: is_valid_candidate_def)

    thus ?thesis
      using Newly_Added[OF Valid lkp_None] obtain_defs length_map by simp
  next
    case (Contained idH)
    have "add egg n = (Some idH, egg)"
      using Already_Contained Valid Contained
      by (simp add: idOpt_def add_def)
    thus ?thesis
      using Already_Contained Valid Contained assms
      thm Already_Contained that(2) (* TIL: these are the same facts! *)
      by (simp add: idOpt_def)
  qed
next
  case Invalid
  then show ?thesis using that(1) assms unfolding add_def by argo
qed

declare add_def[simp]

lemma add_preserves_H_dom_invar:
  assumes "H_dom_invar (H\<^sub>p egg) (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg)"
      and "add egg n = (id', egg')"
    shows "H_dom_invar (H\<^sub>p egg') (D\<^sub>f\<^sub>p egg') (ary\<^sub>p egg') (D\<^sub>a\<^sub>p egg')"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')

  note valid_candidate = Newly_Added(1)
  note valid_node = valid_candidate_becomes_valid_nd_if[OF valid_candidate Newly_Added(3,4)]
  hence only_valid_children: "has_only_valid_children (D\<^sub>f', ary', U\<^sub>p egg, H\<^sub>p egg) n" by force

  have as'_def: "as\<^sub>p n\<^sub>c = map (ufa_rep_of (U\<^sub>p egg)) (as\<^sub>p n)"
    using  Newly_Added(5) only_valid_children by simp

  note canonicalize_preserves_validity =
    canonicalized_f_remains_unchanged[OF only_valid_children Newly_Added(5)]
    number_of_canonicalized_children_remains_unchanged[OF only_valid_children Newly_Added(5)]
    canonicalized_id_list_elements_in_Field_ufa_\<alpha>I[OF _ only_valid_children[simplified],
                                                   of "U\<^sub>p egg", folded as'_def, simplified]

  have valid_n\<^sub>c: \<open>is_valid_nd egg' n\<^sub>c\<close>
    using valid_node canonicalize_preserves_validity ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)]
    by (simp add: Ball_set[symmetric] Newly_Added(9))

  have valid_nds_remain_valid:
      "m \<in> dom (H\<^sub>p egg) \<Longrightarrow> is_valid_nd egg' m" for m
  proof -
    fix m
    assume "m \<in> dom (H\<^sub>p egg)"
    hence valid_old: "is_valid_nd egg m"
      using assms(1)[unfolded H_dom_invar_def] by simp
    show "is_valid_nd egg' m"
      using valid_old ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)] Newly_Added(1,3,4,9)
      by (auto simp: Ball_set[symmetric])
  qed

  show ?thesis
    unfolding H_dom_invar_def
    using valid_n\<^sub>c valid_nds_remain_valid Newly_Added(7,9)
    by auto
qed  (use assms in auto)

lemma add_preserves_H_ran_invar:
  assumes "H_ran_invar (H\<^sub>p egg) (D\<^sub>a\<^sub>p egg)"
      and "add egg n = (id', egg')"
    shows "H_ran_invar (H\<^sub>p egg') (D\<^sub>a\<^sub>p egg')"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  have ran_H_in_Field: "a \<in> ran (H\<^sub>p egg) \<Longrightarrow> a \<in> D\<^sub>a\<^sub>p egg" for a
    using assms(1)[simplified H_ran_invar_def] by blast
  have a_ran_H: "a \<in> ran H' \<Longrightarrow> a \<noteq> the id' \<Longrightarrow> a \<in> ran (H\<^sub>p egg)" for a
    using Newly_Added(7,8) by (auto simp: ran_def split: if_splits)
  have H'_ran_invar: "a \<in> ran H' \<Longrightarrow> a \<in> Field (ufa_\<alpha> ufa')" for a
    by (cases "a = the id'")
       (use Newly_Added(8) ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)]
            a_ran_H[THEN ran_H_in_Field] in auto)
  thus ?thesis
    by (force simp: H_ran_invar_def Newly_Added(9))
qed (use assms in auto)

lemma add_preserves_egg_invar:
  assumes "egg_invar egg"
      and "add egg n = (a, egg')"
    shows "egg_invar egg'"
  using assms(1,2) add_preserves_H_ran_invar add_preserves_H_dom_invar egg_invar_def
  by blast

lemma add_node_already_contained_is_nop:
  assumes "is_valid_candidate egg n"
      and "lookup egg n = Some id\<^sub>l"
      and "add egg n = (id', egg')"
    shows "id' = Some id\<^sub>l" and "egg' = egg"
  using assms by fastforce+

lemma add_preserves_validity:
  assumes "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
      and "is_valid_nd egg n'"
    shows "is_valid_nd egg' n'"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')

  have "length (as\<^sub>p n') = ary' (f\<^sub>p n')"
    using Newly_Added(4) assms(1,3)
    by (cases "f\<^sub>p n' = f\<^sub>p n") fastforce+

  thus ?thesis
    using Newly_Added(3,9) ufa_\<alpha>_ufa_extend_simp[OF Newly_Added(6)] assms(3)
    by (simp add: Ball_set_list_all[symmetric])
qed (use assms(1,3) in auto)

lemma children_of_added_node_with_valid_children_are_valid:
  assumes "has_only_valid_children egg n"
      and "add egg n = (id', egg')"
    shows "has_only_valid_children egg' n"
  using assms(2,1)
  by (cases rule: add_cases)
     (auto simp: ufa_extend_new_Field_ufa_\<alpha> intro: list.pred_mono_strong)

lemma add_valid_candidate_makes_node_valid:
  assumes "H_dom_invar (H\<^sub>p egg) (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg)"
      and "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
    shows "is_valid_nd egg' n"
  using assms(3)
proof (cases rule: add_cases)
  case (Already_Contained n\<^sub>l)
  have valid_canonicalized: "is_valid_nd egg (canonicalize egg n)"
    using assms(1) Already_Contained(2)
    unfolding H_dom_invar_def lookup_def by fast
  show ?thesis
    using canonicalized_valid_candidate_is_valid_nd_implies_nd_is_valid
            [OF Already_Contained(1) valid_canonicalized]
          Already_Contained(4)
    by fastforce
next
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  thus ?thesis
    by (auto simp: ufa_extend_new_Field_ufa_\<alpha> intro: list.pred_mono_strong)
qed (use assms in simp)

lemma add_does_not_change_canonicalization:
  assumes "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
      and "has_only_valid_children egg n'"
    shows "canonicalize egg' n' = canonicalize egg n'"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')

  have only_valid_children_egg': "has_only_valid_children egg' n'"
    using ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)] Newly_Added(9) assms(3)
    by (simp add: list.pred_mono_strong)

  obtain f' as' where n'_def: "n' = nd f' as'" by (cases n') blast
  obtain ufa where ufa_def: "U\<^sub>p egg = ufa" by blast

  have in_ufa': "a \<in> set as' \<Longrightarrow> a \<in> Field (ufa_\<alpha> ufa')" for a
    using ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)] assms(3)
    by (simp add: n'_def Ball_set_list_all[symmetric])

  have id\<^sub>e_notin_as: "id\<^sub>e \<notin> set as'"
    using assms(3) Newly_Added(6) n'_def
    by (auto simp: Ball_set_list_all[symmetric])

  have ufa_rep_of_remains_same:
      "a \<in> set as' \<Longrightarrow> ufa_rep_of ufa a = ufa_rep_of ufa' a" for a
    using ufa_extend_rep_of[OF Newly_Added(6) in_ufa'] id\<^sub>e_notin_as ufa_def
    by force

  show ?thesis
    by (simp only: canonicalize_def assms(3) only_valid_children_egg' ufa_def)
       (auto simp: Newly_Added(9) ufa_rep_of_remains_same id\<^sub>e_notin_as n'_def)
qed (use assms(1) in auto)

lemma add_results_in_identically_canonicalized_added_nd:
  assumes "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
    shows "canonicalize egg' n = canonicalize egg n"
  using assms(1) add_does_not_change_canonicalization[OF assms(1,2)]
  by simp

lemma add_does_not_change_canonequivalent:
  assumes "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
      and "has_only_valid_children egg n\<^sub>1"
      and "has_only_valid_children egg n\<^sub>2"
    shows "are_canonequivalent egg' n\<^sub>1 n\<^sub>2 \<longleftrightarrow> are_canonequivalent egg n\<^sub>1 n\<^sub>2"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')

  have only_valid_children_egg'_n: "has_only_valid_children egg' n\<^sub>1"
   and only_valid_children_egg'_n': "has_only_valid_children egg' n\<^sub>2"
    using ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)] Newly_Added(9) assms(3,4)
    by (auto simp: list.pred_mono_strong)

  moreover have "canonicalize egg' n\<^sub>1 = canonicalize egg' n\<^sub>2
             \<longleftrightarrow> canonicalize egg n\<^sub>1 = canonicalize egg n\<^sub>2"
    using add_does_not_change_canonicalization assms by metis

  ultimately show ?thesis
    using assms(3,4) by blast
qed (use assms(1) in auto)

lemma add_valid_candidate_makes_canonequivalent_nodes_valid:
  assumes "H_dom_invar (H\<^sub>p egg) (D\<^sub>f\<^sub>p egg) (ary\<^sub>p egg) (D\<^sub>a\<^sub>p egg)"
      and "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
      and "are_canonequivalent egg n n'"
    shows "is_valid_nd egg' n'"
  using assms(3)
proof (cases rule: add_cases)
  case (Already_Contained id\<^sub>l)
  show ?thesis
    using add_valid_candidate_makes_node_valid[OF assms(1-3)] Already_Contained(4)
          validity_of_node_extends_to_all_canonequivalent[OF assms(4)]
    by blast
next
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  obtain f' as' where n'_def: "n' = nd f' as'" by (cases n') blast

  have in_ufa': "a \<in> set as' \<Longrightarrow> a \<in> Field (ufa_\<alpha> ufa')" for a
    using ufa_extend_new_Field_ufa_\<alpha>[OF Newly_Added(6)] assms(4)
    by (simp add: n'_def Ball_set_list_all[symmetric])

  thus ?thesis
    using are_canonequivalent_implies_same_fun_sym[OF assms(4)]
          are_canonequivalent_implies_same_fun_arity[OF assms(4)]
          add_valid_candidate_makes_node_valid[OF assms(1-3), simplified]
    by (simp add: Newly_Added(9) n'_def Ball_set_list_all[symmetric])
qed (use assms(2) in auto)

lemma add_id_returned_is_lookup_id:
  assumes "is_valid_candidate egg n"
      and "add egg n = (Some id', egg')"
    shows "lookup egg' n = Some id'"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  note canonicalize_is_unchanged =
    add_results_in_identically_canonicalized_added_nd[OF Newly_Added(1) assms(2)]
  show ?thesis
    unfolding lookup_def canonicalize_is_unchanged
    using Newly_Added(5,7-9) by auto
qed (use assms(1) in auto)

lemma add_id_returned_is_lookup_id_of_canonequivalent_nds:
  assumes "is_valid_candidate egg n"
      and "add egg n = (Some id', egg')"
      and "are_canonequivalent egg n n'"
    shows "lookup egg' n' = Some id'"
  using assms add_does_not_change_canonequivalent add_id_returned_is_lookup_id
    lookup_of_canonequivalent_is_same
  by (metis are_canonequivalent_def)

lemma add_does_not_change_lookup_for_non_canonequivalent:
  assumes "is_valid_candidate egg n"
      and "add egg n = (id', egg')"
      and "has_only_valid_children egg n'"
      and "\<not> are_canonequivalent egg n n'"
    shows "lookup egg' n' = lookup egg n'"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')

  have "n\<^sub>c \<noteq> canonicalize egg n'"
    using Newly_Added(5) assms(1,3,4) by force

  thus ?thesis
    using add_does_not_change_canonicalization[OF assms(1-3)] Newly_Added(7,9)
    by (simp add: lookup_def)
qed (use assms(1) in auto)

lemma add_preserves_\<alpha>:
  assumes "is_valid_candidate egg n"
      and "add egg n = (Some id', egg')"
      and "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg'"
  using assms(2)
proof (cases rule: add_cases)
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  have ufa_\<alpha>_egg': "ufa_\<alpha> (U\<^sub>p egg') = insert (id\<^sub>e, id\<^sub>e) (ufa_\<alpha> (U\<^sub>p egg))"
    using ufa_\<alpha>_ufa_extend_simp[OF Newly_Added(6)] Newly_Added(9) by auto

  from assms(3) show ?thesis
    apply (elim in_\<alpha>E)
    apply (intro in_\<alpha>I)
    using add_preserves_validity[OF assms(1,2)] apply (blast, blast)
    by (metis (no_types, lifting) Newly_Added(2) insert_iff lookup_of_canonequivalent_is_same
        add_does_not_change_lookup_for_non_canonequivalent[OF assms(1,2)] option.distinct(1)
        ufa_\<alpha>_egg' valid_nd_has_only_valid_children)
qed (use assms(1,3) in auto)

lemma added_nd_and_canonequivalent_are_added_to_\<alpha>:
  assumes "egg_invar egg"
      and "is_valid_candidate egg n"
      and "add egg n = (Some id', egg')"
      and "are_canonequivalent egg n n\<^sub>1" and "are_canonequivalent egg n n\<^sub>2"
    shows "(n\<^sub>1, n\<^sub>2) \<in> \<alpha> egg'"
  using assms(3)
proof (cases rule: add_cases)
  case (Already_Contained id\<^sub>l)

  have "is_valid_nd egg n"
    using add_valid_candidate_makes_node_valid assms(1-3) egg_invar_def Already_Contained(4)
    by blast
  hence "(n,n) \<in> \<alpha> egg"
    using assms(1)[unfolded egg_invar_def H_ran_invar_def] Already_Contained(2)
    by (auto simp: lookup_def intro!: successful_lookup_implies_node_reflexive_in_\<alpha> ranI)

  thus ?thesis
    using Already_Contained(4) assms(4,5)
      lookup_of_canonequivalent_is_same validity_of_node_extends_to_all_canonequivalent
    by (metis (lifting) ext in_\<alpha>E in_\<alpha>I)
next
  case (Newly_Added D\<^sub>f' ary' n\<^sub>c id\<^sub>e ufa' H')
  have ufa_\<alpha>_egg': "ufa_\<alpha> (U\<^sub>p egg') = insert (id\<^sub>e, id\<^sub>e) (ufa_\<alpha> (U\<^sub>p egg))"
    using ufa_\<alpha>_ufa_extend_simp[OF Newly_Added(6)] Newly_Added(9) by auto
  note H_dom_invar_egg = conjunct1[OF assms(1)[unfolded egg_invar_def]]

  show ?thesis
    apply (intro in_\<alpha>I)
    using add_valid_candidate_makes_canonequivalent_nodes_valid[OF H_dom_invar_egg assms(2,3)]
          add_id_returned_is_lookup_id_of_canonequivalent_nds[OF assms(2,3)]
          ufa_\<alpha>_egg' Newly_Added(8) assms(4,5)
    by blast+
qed (use assms(1) in auto)

subsection \<open>merge\<close>

definition merge :: "'a egg_tuple \<Rightarrow> eId list \<Rightarrow> eId \<Rightarrow> eId
    \<Rightarrow> eId option \<times> eId list \<times> 'a egg_tuple" where
  "merge egg wl a b = (
    if a \<notin> D\<^sub>a\<^sub>p egg \<or> b \<notin> D\<^sub>a\<^sub>p egg then (None, wl, egg)
    else if (a, b) \<in> ufa_\<alpha> (U\<^sub>p egg) then (Some (ufa_rep_of (U\<^sub>p egg) b), wl, egg)
    else
      let ufa' = ufa_union (U\<^sub>p egg) a b in
      let id' = ufa_rep_of ufa' b in
      (Some id', wl @ [id'], D\<^sub>f\<^sub>p egg, ary\<^sub>p egg, ufa', H\<^sub>p egg))"

lemma merge_cases:
  assumes "merge egg wl a b = (id', wl', egg')"
  obtains (Not_Valid)
        "a \<notin> D\<^sub>a\<^sub>p egg \<or> b \<notin> D\<^sub>a\<^sub>p egg"
    and "id' = None"
    and "wl' = wl"   (* TODO: Once again, this case should be undefined *)
    and "egg' = egg"
  | (Already_Equivalent) id\<^sub>r
  where "(a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)"
    and "id\<^sub>r = ufa_rep_of (U\<^sub>p egg) b"
    and "id' = Some id\<^sub>r"
    and "wl' = wl"
    and "egg' = egg"
  | (Newly_Merged) ufa' id\<^sub>r
  where "a \<in> D\<^sub>a\<^sub>p egg"
    and "b \<in> D\<^sub>a\<^sub>p egg"
    and "(a, b) \<notin> ufa_\<alpha> (U\<^sub>p egg)"
    and "ufa' = ufa_union (U\<^sub>p egg) a b"
    and "id\<^sub>r = ufa_rep_of ufa' b"
    and "id' = Some id\<^sub>r"
    and "wl' = wl @ [id\<^sub>r]"
    and "egg' = (D\<^sub>f\<^sub>p egg, ary\<^sub>p egg, ufa', H\<^sub>p egg)"
proof(cases "(a, b) \<in> ufa_\<alpha> (U\<^sub>p egg)" rule: case_split[case_names In_\<alpha> Not_in_\<alpha>])
  case In_\<alpha>
  hence "a \<in> D\<^sub>a\<^sub>p egg \<and> b \<in> D\<^sub>a\<^sub>p egg" by (simp add: FieldI1 FieldI2)
  thus ?thesis using assms[unfolded merge_def] In_\<alpha> Already_Equivalent by fastforce
next
  case Not_in_\<alpha>
  then show ?thesis
  proof(cases "a \<in> D\<^sub>a\<^sub>p egg \<and> b \<in> D\<^sub>a\<^sub>p egg" rule: case_split[case_names Valid Invalid])
    case Valid
    then show ?thesis
      using assms[unfolded merge_def, simplified Let_def, symmetric] Not_in_\<alpha> Newly_Merged
      by fastforce
  next
    case Invalid
    then show ?thesis using assms[unfolded merge_def, symmetric] Not_Valid by auto
  qed
qed

declare merge_def[simplified Let_def, simp]

subsection \<open>eq_class\<close>

definition eq_class :: "'a egg_tuple \<Rightarrow> eId \<Rightarrow> 'a eNode set" where (* Synthesizing M *)
  "eq_class egg a = (
    case egg of (_, _, ufa, H) \<Rightarrow>
      if a \<in> Field (ufa_\<alpha> ufa)
      then {n \<in> dom H. ufa_rep_of ufa a = ufa_rep_of ufa (the (H n))}
      else {})"
declare eq_class_def[simp]

lemma eq_class_of_init_empty: "eq_class init a = {}"
  by auto

declare
  init_def[simp del]
  is_valid_nd_def[simp del]
  is_canonical_nd_def[simp del]
  canonicalize_def[simp del]
  (* lookup_def[simp del] *)
  is_valid_candidate_def[simp del]
  add_def[simp del]
  eq_class_def[simp del]

end (* end of theory RawEgg *)
