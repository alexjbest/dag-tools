import dag
import data.vector
import crawler
import tactic
import data.int.basic
import number_theory.quadratic_reciprocity
import topology.algebra.module
import topology.algebra.ordered.basic
import ring_theory.discrete_valuation_ring
import algebra.lie.classical
import all
import system.io
import init.meta.widget.tactic_component
import data.list.lex

local attribute [-instance] string_to_name
open tactic declaration environment io io.fs (put_str_ln close)

/-- These decls are special as they are magically defined in cpp and don't have a genuine lean file
    source to point to, also they can never not be imported. -/
def magic_homeless_decls := [`quot, `quot.mk, `quot.lift, `quot.ind]

/-- These are user attributes that we can use to check for imports not obvious from the final
    proof term, i.e.
    ```
    @[ext]
    structure blah := (n : ℕ)
    ```
    will produce a lemma `blah.ext` that doesn't contain any references to the file where the `ext`
    attribute is defined, nevertheless by looking up the place where the user attribute is defined
    we can track the dependency on that file.

    Putting every possible attribute in this list would be too slow so we restrict to a hand-crafted
    list we found useful.
    -/
def evidence_attrs : list name :=
-- [`_can_lift, `_ext_core, `_ext_lemma_core, `_localized, `_refl_lemma, `_simp.sizeof, `_simp_cache, `_simps_str, `_squeeze_loc, `algebra, `alias, `ancestor, `breakpoint, `class, `congr, `continuity, `derive, `derive_handle, `elab_as_eliminator, `elab_simple, `elab_strategy, `elab_with_expected_type, `elementwise, `ematch, `ematch_lhs, `equiv_rw_simp, `ext, `field_simps, `functor_norm, `ghost_simps, `higher_order, `hint_tactic, `hole_command, `inline, `instance, `integral_simps, `interactive, `intro, `inverse, `irreducible, `is_poly, `library_note, `linter, `main_declaration, `measurability, `mfld_simps, `mk_iff, `monad_norm, `mono, `monotonicity, `no_inst_pattern, `no_rsimp, `nolint, `nontriviality, `norm, `norm_cast, `norm_num, `notation_class, `obviously, `parity_simps, `parsing_only, `pattern, `pp_nodot, `pp_using_anonymous_constructor, `pre_smt, `protect_proj, `protected, `push_cast, `reassoc, `recursor, `reducibility, `reducible, `refl, `replaceable, `rewrite, `rsimp, `semireducible, `simp, `simps, `split_if_reduction, `subst, `sugar, `sugar_nat, `symm, `tactic_doc, `tidy, `to_additive, `to_additive_aux, `to_additive_ignore_args, `to_additive_relevant_arg, `to_additive_reorder, `trans, `transport_simps, `typevec, `unify, `user_attribute, `user_command, `user_notation, `vm_monitor, `vm_override, `wrapper_eq, `zify]
-- [`_ext_core, `_ext_lemma_core, `alias, `ancestor, `congr, `continuity, `elementwise, `ematch, `equiv_rw_simp, `ext, `field_simps, `functor_norm, `ghost_simps, `higher_order, `integral_simps, `interactive, `intro, `inverse, `irreducible, `is_poly, `library_note, `linter, `main_declaration, `measurability, `mfld_simps, `mk_iff, `monad_norm, `mono, `monotonicity, `no_inst_pattern, `no_rsimp, `nolint, `nontriviality, `norm, `norm_cast, `norm_num, `notation_class, `obviously, `parity_simps, `pattern, `pp_nodot, `protect_proj, `protected, `push_cast, `reassoc, `recursor, `reducibility, `reducible, `refl, `replaceable, `rewrite, `rsimp, `semireducible, `simp, `simps, `split_if_reduction, `subst, `symm, `tactic_doc, `tidy, `to_additive, `trans, `transport_simps, `unify, `user_attribute, `user_command, `zify]
[`ext,
 `simps,
 `continuity,
 `mono,
 `_localized, -- sadly this only makes files that depend on localized not remove, TODO localized still
 `nolint,
 `to_additive,
 `protect_proj,
 `linter,
 `higher_order, -- TODO double check
 `derive_handler, -- TODO double check
 `deriver, -- TODO double check
 `hint_tactic,
 `obviously,
 `ancestor,
 `norm_cast,
 `nontriviality,
 `mk_iff,
 `tidy
 ]
-- TODO map to get prios also
/-- get the attributes on a decl that tell us about necessary imports. -/
meta def get_decl_evidence_attrs (decna : name) : tactic $ list name :=
evidence_attrs.mfilter (λ ana, do (tactic.has_attribute ana decna >> return tt) <|> return ff)

/-- pre should have a slash at the end -/
def import_to_file (pre : string) (im : name) : string :=
pre ++ im.to_string_with_sep "/" ++ ".lean"-- TODO windows lol

section
open name
def name.remove_default : name → name
| (mk_string "default" p) := p
| p  := p
end

/-- A hackish way to get the `src` directory of any project.
  Requires as argument any declaration name `n` in that project, and `k`, the number of characters
  in the path of the file where `n` is declared not part of the `src` directory.
  Example: For `mathlib_dir_locator` this is the length of `tactic/project_dir.lean`, so `23`.
  Note: does not work in the file where `n` is declared. -/
meta def environment.get_project_dir (e : environment) (n : name) (k : ℕ) : string :=
(do
  s ← e.decl_olean n,
  return $ s.popn_back k).get_or_else sformat!"Hello! I'm {n} trapped in an error string, please let me out"

/-- A hackish way to get the `src` directory of mathlib. -/
meta def environment.get_mathlib_dir (e : environment) : string :=
e.get_project_dir `mathlib_dir_locator 23

/-- A hackish way to get the `src` directory of core. -/
meta def environment.get_core_dir (e : environment) : string :=
e.get_project_dir `nat 14

/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
meta def environment.is_in_mathlib (e : environment) (n : name) : bool :=
e.is_prefix_of_file e.get_mathlib_dir n


structure import_data : Type :=
(decl_name : name)
(file_name : name)
(file_pos : option pos)
(deps : list name)

lemma import_data.ext (d e : import_data) :
  d = e ↔ d.decl_name = e.decl_name ∧ d.file_name = e.file_name ∧ d.file_pos = e.file_pos ∧ d.deps = e.deps :=
begin
  split, { intro h, cases h, repeat { split, refl }, refl },
  cases d, cases e, dsimp, intro h,
  repeat { cases h with h' h, cases h' },
  cases h', congr,
end

-- attribute [derive inhabited] pos
meta instance : has_lt import_data := ⟨λ n m, n.decl_name < m.decl_name⟩
meta instance : decidable_eq import_data :=
begin
  intros d e, cases d, cases e,
  rw import_data.ext,
  dsimp,
  apply_instance,
end

meta instance : has_to_format import_data :=
  ⟨λ i, to_fmt i.decl_name
        ++ " : " ++ to_fmt i.file_name
        ++ " : " ++ to_fmt (i.file_pos.iget)
        ++ " : " ++ to_fmt (i.deps)
        ⟩

meta instance : has_to_string import_data :=
⟨λ b, to_string $ to_fmt b⟩

meta instance : has_to_tactic_format import_data :=
⟨λ b, return $ to_fmt b⟩

meta def get_attr_deps (n : name) : tactic (list name) :=
do
  ll ← get_decl_evidence_attrs n,
  list.mmap_filter (λ n, do (option.some <$> get_user_attribute_name n) <|> return none) ll
  -- o ←  ll.mmap_filter (λ ana, pure $ get_user_attribute_name ana),
  -- return o

/-- Given a declaration return a structure of its name, position, list of dependent decl names and
    filename. -/
meta def mk_data (env : environment) (file_to_import : string → name) (fname : name)
  (decl : declaration) : tactic import_data :=
let na := decl.to_name,
    po := env.decl_pos na
    --fname := file_to_import $ file_name $ env.decl_olean na
    in
  (λ attrd,
    { decl_name := na,
      file_name := fname,
      file_pos := po,
      deps := -- dont even consider quot and friends
        (list_items decl.type ++ list_items decl.value ++ attrd).erase_dup.diff magic_homeless_decls, }) <$>
  get_attr_deps na

#eval (λ inp : list nat, do l ← inp, guardb (l = 1), pure l) [1,2]
-- meta def aa (env : environment) (fname : name) (file_to_import : string → name) : list declaration → tactic (list import_data)
-- | (d :: l) :=
-- let fn_string := import_to_file env.get_mathlib_dir fname in
-- aa l >>= (
--   if (env.decl_olean d.to_name = fn_string) then
--  (do
--   of ← mk_data env file_to_import fname d,
--     ((::) of ))
--     else
--  id)
-- | [] := pure []
/-- Creates an import data tuple for every declaration in file `fname`. -/
meta def get_file_data (env : environment) (fname : name) (file_to_import : string → name) :
  tactic $ list import_data :=
let fn_string := import_to_file env.get_mathlib_dir fname in
-- env.get_decls.mmap_filter
-- aa env fname file_to_import env.get_decls
-- (λ decls : list declaration, do d ← decls,
--   guardb (env.decl_olean d.to_name = fn_string) >>
--   mk_data env file_to_import fname d,
--   skip
-- ) env.get_decls
  -- (λ d : declaration, env.decl_olean d.to_name = fn_string)).mmap
    -- (mk_data env file_to_import fname)
(env.get_decls.filter
  (λ d : declaration, env.decl_olean d.to_name = fn_string)).mmap
    (mk_data env file_to_import fname)

-- /-- Given a declaration return a structure of its name, position, list of dependent decl names and
--     filename. -/
-- meta def mk_data (env : environment) (file_to_import : string → name)
--   (decl : declaration) (na : name) : tactic import_data :=
-- let po := env.decl_pos na,
--     fname := file_to_import $ file_name $ env.decl_olean na in
--   (λ attrd,
--     { decl_name := na,
--       file_name := fname,
--       file_pos := po,
--       deps := (list_items decl.type ++ list_items decl.value ++ attrd).erase_dup, }) <$>
--   get_attr_deps env na

-- /-- Creates an import data tuple for every declaration in file `fname`. -/
-- meta def get_file_data (env : environment) (fname : name) (file_to_import : string → name) :
--   tactic $ list import_data :=
-- let fn_string := import_to_file env.get_mathlib_dir fname in
-- env.get_decls.mmap_filter (λ d, let na := d.to_name in if
--   env.decl_olean na = fn_string then
--     option.some <$> mk_data env file_to_import d na else none)

/-- Creates a dag of input data. -/
meta def mk_file_dag_of_file_data (fdata : list import_data) :
  dag import_data :=
-- let fdata := mk_file_data env fname file_to_import,
  -- let decl_names := fdata.map import_data.decl_name in
fdata.foldl
  (λ G id,
    id.deps.foldl
      (λ G2 dep,
        ((fdata.find (λ el : import_data, el.decl_name = dep)).map -- todo maybe replace with an rb_map
          (λ a, G2.insert_edge a id)).get_or_else G2)
      (G.insert_vertex id))
  (dag.mk _)

section rb_counter
open native
variables (T : Type)
meta def rb_counter := rb_map T ℕ
namespace rb_counter
variable {T}
meta def incr_by (t : T) (n : ℕ) (A : rb_counter T) : rb_counter T :=
rb_map.insert A t ((rb_map.zfind A t) + n)
meta def incr (t : T) (A : rb_counter T) : rb_counter T := A.incr_by t 1
meta def mk (key : Type) [has_lt key] [decidable_rel ((<) : key → key → Prop)] : rb_counter key :=
rb_map.mk _ _

meta instance [has_to_format T] : has_to_format (rb_counter T) := rb_map.has_to_format
meta instance [has_to_string T] : has_to_string (rb_counter T) := rb_map.has_to_string
end rb_counter
end rb_counter

open native

-- meta def dfs_all_paths' {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T] (d : dag T)
--   : T → (list (list T) × rb_set T) → (list (list T) × rb_set T)
-- -- vertex and stack, visited pair
-- | v stavis :=
--   (λ a : list (list T) × rb_set T, (a.fst.map ((::) v), a.snd))
--     ((d.find v).foldl
--       (λ stavis' w,
--         if stavis'.snd.contains w then
--           stavis'
--         else
--           dfs_all_paths' w stavis')
--       (stavis.fst, stavis.snd.insert v))
/-- Depth first search all paths. -/
meta def dfs_all_paths {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (tgt : T) : T → rb_lmap T (list T) → rb_lmap T (list T)
| v paths :=
  if paths.contains v then paths else
    let npaths := (d.find v).foldl (λ opaths de, dfs_all_paths de opaths) paths in
    rb_map.insert npaths v $ (d.find v).foldl (λ acc de,
      let dep_paths := (npaths.find de) in
      acc ++ dep_paths.map ((::) v)) []
    -- (d.find v).foldl (λ opaths de, rb_map.insert opaths v _) npaths
    -- rb_map.insert npaths v $ (npaths.find de).map ((::) v) _
    -- (d.find v).foldl (λ opa de,
    -- let npa :=
    --   if paths.contains de then opa else dfs_all_paths de opa in
    --     rb_map.insert npa v $ (npa.find de).map ((::) v)) paths
      -- else
      --   (dfs_all_paths de opa).map (λ p, v :: p)) paths
  -- let a := ((d.find v).foldl
      -- (λ (rea' : rb_map T (list T)) w, let n :=
      --   if rea'.contains w then
      --     rea'
      -- ()  else
      --     dfs_reach_table w rea' in
      --   n.insert v $ (((n.find v).get_or_else mk_rb_set).union $ (n.find w).get_or_else mk_rb_set))
      -- rea) in a.insert v $ ((a.find v).get_or_else mk_rb_set).insert v

meta def dag.all_paths {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (src tgt : T) : list (list T) :=
(dfs_all_paths d tgt src $ (mk_rb_map).insert tgt [[tgt]]).find src
-- #eval all_paths ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5), (5,6),(5,8),(8,7),(8,6), (5,19),(19,7), (6,7)]) 1 7

meta def dag.count_descendents {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (start : list T) : ℕ :=
d.dfs (λ _, nat.succ) 0 start

meta def dag.count_all_descendents {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (start : list T := d.vertices) : rb_counter T :=
d.dfs (λ v acc, acc.insert v $ 1 + ((d.find v).map $ λ de, acc.zfind de).sum) mk_rb_map start
-- #eval count_descendents (((dag.mk ℕ).insert_vertex 3).insert_edges [(1, 5), (4,5), (2,5)]) ([1,4,3])

open tactic

open native
meta def mk_file_dep_counts_basic (env : environment) (fname : name) (file_to_import : string → name)
  (fdata : list import_data) :
  rb_counter name :=
let G := mk_file_dag_of_file_data fdata,
    Gr := G.count_all_descendents in
(Gr.fold (rb_counter.mk _) (λ k d o, k.deps.foldl
  (λ o2 dep, let imp := file_to_import $ file_name $ env.decl_olean dep in
    if ¬ (`init).is_prefix_of imp then
      o2.incr_by imp d
    else o2) o)).erase fname

meta def remove_trail : list char → list char
| ['\n'] := []
| (a :: b) := a :: remove_trail b
| [] := []
meta def io.handle.get_line_as_string (f : handle) : io string :=
do g ← fs.get_line f, return $ (remove_trail g.to_list).as_string

meta def get_imports_aux : handle → bool → io (list name)
| f b :=
do
  eo ← io.fs.is_eof f,
  if eo then return []
  else do
    l ← f.get_line_as_string,
    let ls := l.split_on ' ',
    -- if ls.tail.head = "graph." hen return [] else -- stupid hack around reserved notation
    (if ls.head = "import" then
      do a ← get_imports_aux f tt,
        return ((((ls.tail.split_on_p (λ s, "--".is_prefix_of s)).head.filter (≠ "")).map
          name.from_string).map name.remove_default ++ a) -- space separated lists on imports (in core)
    else
      -- if we are either
      if (b ∧ l ≠ "\n") ∨ "/-!".is_prefix_of l then
        return []
      else
        get_imports_aux f b)

meta def get_imports (e : environment) (file : name) : io (list name) :=
do
  f ← mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read <|>
      mk_file_handle (import_to_file e.get_mathlib_dir $ file.append `default) io.mode.read <|>
      mk_file_handle (import_to_file e.get_core_dir file) io.mode.read <|>
      mk_file_handle (import_to_file e.get_core_dir $ file.append `default) io.mode.read,
  l ← get_imports_aux f ff,
  fs.close f,
  return l

meta def is_default (e : environment) (file : name) : io bool :=
do
  ((mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read >> return ff) <|>
      (mk_file_handle (import_to_file (e.get_core_dir) file) io.mode.read >> return ff) <|> return tt)

meta def file_is_in_mathlib (e : environment) (file : name) : io bool :=
do
  ((mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read >> return tt) <|>
      (mk_file_handle (import_to_file e.get_mathlib_dir $ file.append `default) io.mode.read >> return tt) <|> return ff)

meta def get_dag_aux (e : environment) : name → dag name → io (dag name)
| n d := do
if d.contains n then return d else do
  l ← get_imports e n,
  l.mfoldl (λ od im, do
    G ← get_dag_aux im od,
    return $ G.insert_edge n im) d

/-- get a dag of all file imports with edges
   the environment is used to find the location of files -/
meta def get_import_dag (e : environment) (files : list name) : io (dag name) :=
files.mfoldl (λ ol file, get_dag_aux e file ol) (dag.mk _)

open native
/-- pre should have a slash at the end -/
meta def mk_file_to_import (e : environment) : string → name :=
let mathlib_pre := e.get_mathlib_dir,
    core_pre := e.get_core_dir in
λ file,
let rest := (file.get_rest mathlib_pre).get_or_else $
            (file.get_rest core_pre).get_or_else
           sformat!"Hello, I'm {file} trapped in an error string, please let me out" in
  (name.from_components ((rest.popn_back 5).split_on '/')).remove_default

meta def mk_file_dep_counts (env : environment) (fname : name) (Gr : rb_map name (rb_set name))
  (fdata : list import_data) :
  rb_counter name :=
let file_to_import := mk_file_to_import env,
    dc := mk_file_dep_counts_basic env fname file_to_import fdata in
  -- io.put_str (to_fmt dc).to_string, -- another beautiful hack
  -- G ← get_import_dag env fname,
  (dc.fold dc
    (λ nam co acc, (Gr.ifind nam).fold acc (λ de acc', acc'.incr_by de $ dc.zfind nam))).erase fname
  -- return $ (Gr.fold dc (λ na ln odc, ln.fold odc (λ de odc', odc'.incr_by de ((dc.find na).get_or_else 0)))).erase fname

-- run_cmd (do
--   e ← get_env,
--   G ← unsafe_run_io $ get_import_dag e `algebra.group_power.lemmas,
--   trace (all_paths G `data.int.cast `data.equiv.basic),
  -- skip)
meta def get_minimal_imports (e : environment) (n : name) (G : dag name) (Gr := G.reachable_table)
  (fdata : list import_data) :
  rb_set name :=
  -- let n := `ring_theory.discrete_valuation_ring,
  -- let n := `algebra.lie.classical,
  let b := mk_file_dep_counts e n Gr fdata in
      G.minimal_vertices $ b.keys.filter (λ k, b.find k ≠ some 0)

meta def optimize_imports (e : environment) (nam : name) (G : dag name) (Gr := G.reachable_table)
  (fdata : list import_data) :
  name × list string × list string × ℕ × ℕ :=
  let new_imp := get_minimal_imports e nam G Gr fdata,
      old_imp := G.find nam in
  (nam,
   (old_imp.map name.to_string).qsort (λ a b, a < b : string → string → bool),
   (new_imp.keys.map to_string).qsort (λ a b, a < b : string → string → bool),
   G.count_descendents (old_imp : list name),
   G.count_descendents (new_imp.keys : list name))

/-- Convert the output of `optimize_imports` into a sed script for removing these imports. Note:
  * This clobbers import comments
  * Mac users should replace `sed` with `gsed` (via homebrew) in the script to ensure it works
  * This pipes to stdout by default, append `-i` after every `sed` to replace in-place
-/
def output_to_sed (o : name × list string × list string × ℕ × ℕ) : string :=
let ⟨na, ol, ne, oli, nei⟩ := o,
    fn := na.to_string_with_sep "/",
    -- https://unix.stackexchange.com/questions/342516/sed-remove-all-matches-in-the-file-and-insert-some-lines-where-the-first-match
    imps := "\\\n".intercalate $ ne.map (λ i, sformat!"import {i}") in
sformat!"# {oli} → {nei} {ol}\n" ++
(if oli = nei then "# only transitive imports removed\n" else "") ++
"sed '/^import /{x;//!c\\" ++ sformat!"
{imps}
d}' src/{fn}.lean\n"

set_option profiler true
run_cmd unsafe_run_io (do
  e ← run_tactic get_env,
  let L := [`data.sym.basic],
  -- let L := [`tactic.basic],
  -- let L := [`linear_algebra.affine_space.basic],
  -- let L := [`linear_algebra.matrix.determinant],
  fdata ← run_tactic $ get_file_data e L.head (mk_file_to_import e),
  -- print_ln fdata,
  G ← get_import_dag e L,
  -- print_ln (to_fmt G),
  -- let file_to_import := mk_file_to_import e,
  -- let G' := mk_file_dag e `algebra.group_with_zero.basic file_to_import,
  -- print_ln G'.keys,
  -- print_ln $to_fmt G,
  let Gr := G.reachable_table,
  let T := L.map (λ nam, optimize_imports e nam G Gr fdata),
  -- print_ln T,
  ((T.filter (λ R : name × list string × list string × ℕ × ℕ, R.2.2.1 ≠ R.2.1 ∧ R.2.2.2.2 ≠ 0)).map
    output_to_sed).mmap print_ln)

-- run_cmd silly `group_theory.free_abelian_group
-- run_cmd silly `algebra.module.linear_map -- quite successful
-- run_cmd silly `data.fin.basic
-- run_cmd silly `data.matrix.basic
-- run_cmd silly `data.polynomial.field_division
-- run_cmd silly `group_theory.perm.basic
-- run_cmd silly `group_theory.perm.sign
-- run_cmd silly `linear_algebra.coevaluation
-- run_cmd silly `linear_algebra.dimension
-- run_cmd silly `linear_algebra.eigenspace
-- run_cmd silly `linear_algebra.matrix.determinant
-- run_cmd silly `linear_algebra.matrix.transvection
-- run_cmd silly `algebra.group_power.identities
-- run_cmd silly `number_theory.number_field

-- (λ ana, do
--   ⟨b, prio⟩ ← tactic.has_attribute ana decna,
--   guardb b,
--   return (ana, prio))

open interaction_monad
open io io.fs native tactic
meta def main : io unit :=
do
  e ← run_tactic get_env,
  G ← get_import_dag e [`logic.relation],--[`algebra.char_p.quotient],
  print_ln G.keys,
  let Gr := G.reachable_table,
  print_ln sformat!"running on {G.keys.length} files",
  s ← run_tactic read,
  let res := G.keys.map_async_chunked (λ na, match
      (unsafe_run_io $ do
        b ← is_default e na, -- we skip default files
        b2 ← file_is_in_mathlib e na, -- we only work on mathlib itself (TODO allow other projects)
        guardb ((¬ b) ∧ b2) >>
        (do
        fdata ← run_tactic $ get_file_data e na (mk_file_to_import e),
        let T := optimize_imports e na G Gr fdata,
        if T.2.2.1 ≠ T.2.1 -- new imports not the same as old in any way
           ∧ T.2.2.2.2 ≠ 0 -- Any file that ends up with no imports is surely a default-style
                           -- special case, e.g. `tactic.basic`
        then
          return $ output_to_sed T
        else return "") <|> return "") s
      with
        | result.success w _ := w
        | result.exception msg _ _ :=
          "File splitter failed:\n" ++ msg.elim "(no message)" (λ msg, to_string $ msg ())
      end)
    64, -- chunk size
    print_ln $ "".intercalate res

run_cmd unsafe_run_io main
