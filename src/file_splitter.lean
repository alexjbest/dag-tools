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
  return $ s.popn_back k).get_or_else "Hello, I'm trapped in an error string, please let me out"

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

/-- Given a declaration return a structure of its name, position, list of dependent decl names and
    filename. -/
meta def mk_data (env : environment) (file_to_import : string → name) (decl : declaration) : import_data :=
let na := decl.to_name,
    po := env.decl_pos na,
    deps := (list_items decl.type ++ list_items decl.value).erase_dup,
    fname := file_to_import $ file_name $ env.decl_olean na in
  { decl_name := na,
    file_name := fname,
    file_pos := po,
    deps := deps, }

/-- Creates an import data tuple for every declaration in  file `fname`. -/
meta def mk_file_data (env : environment) (fname : name) (file_to_import : string → name) :
  list import_data :=
trace_val $let fn_string := trace "oog" trace_val $ import_to_file env.get_mathlib_dir fname in
(env.get_decls.filter
  (λ d : declaration, env.decl_olean d.to_name = fn_string)).map
    (mk_data env file_to_import)

/-- Creates a dag of input data. -/
meta def mk_file_dag (env : environment) (fname : name) (file_to_import : string → name) :
  dag import_data :=
let fdata := mk_file_data env fname file_to_import,
    decl_names := trace "o " trace_val $ fdata.map import_data.decl_name in
fdata.foldl
  (λ G id,
    id.deps.foldl
      (λ G2 dep, trace_val $ ((fdata.find (λ el : import_data, el.decl_name = dep)).map -- todo maybe replace with an rb_map
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
meta def mk_file_dep_counts_basic (env : environment) (fname : name) (file_to_import : string → name) :
  rb_counter name :=
let G := mk_file_dag env fname file_to_import,
    Gr := G.count_all_descendents in
(Gr.fold (rb_counter.mk _) (λ k d o, k.deps.foldl
  (λ o2 dep, --if env.is_in_mathlib dep then
      o2.incr_by (file_to_import $ file_name $ env.decl_olean dep) d
    -- else o2
    ) o)).erase fname

meta def io.handle.get_line_as_string (f : handle) : io string :=
do g ← fs.get_line f, return g.to_list.as_string

meta def get_imports_aux : handle → bool → io (list name)
| f b :=
do
  eo ← io.fs.is_eof f,
  if eo then return []
  else do
    l ← f.get_line_as_string,
    let ls := l.split (λ c, c.is_whitespace),
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
      mk_file_handle (import_to_file (e.get_core_dir) file) io.mode.read <|>
      mk_file_handle (import_to_file (e.get_core_dir) $ file.append `default) io.mode.read,
  l ← get_imports_aux f ff,
  fs.close f,
  return l

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
           "Hello, I'm trapped in an error string, please let me out" in
  (name.from_components ((rest.popn_back 5).split_on '/')).remove_default

meta def mk_file_dep_counts (env : environment) (fname : name) (Gr : rb_map name (rb_set name)) :
  rb_counter name :=
let file_to_import := mk_file_to_import env,
    dc := mk_file_dep_counts_basic env fname file_to_import in
    trace (to_string dc) $
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
meta def get_minimal_imports (e : environment) (n : name) (G : dag name) (Gr := G.reachable_table) :
  rb_set name :=
  -- let n := `ring_theory.discrete_valuation_ring,
  -- let n := `algebra.lie.classical,
  let b := mk_file_dep_counts e n Gr in
      G.minimal_vertices $ trace_val $ b.keys.filter (λ k, b.find k ≠ some 0)

section ignore
  def good_files : list name :=
  [
  `algebra.big_operators.enat,
  `algebra.big_operators.fin,
  `algebra.big_operators.finsupp,
  `algebra.big_operators.option,
  `algebra.char_p.quotient,
  `algebra.group_power.identities,
  `algebra.hierarchy_design,
  `algebra.order.pointwise,
  `algebraic_geometry.prime_spectrum.noetherian,
  `analysis.analytic.radius_liminf,
  `analysis.convex.complex,
  `analysis.hofer,
  `analysis.inner_product_space.conformal_linear_map,
  `category_theory.limits.constructions.binary_products,
  `category_theory.limits.constructions.weakly_initial,
  `category_theory.limits.shapes.concrete_category,
  `category_theory.linear,
  `category_theory.preadditive,
  `category_theory.products.bifunctor,
  `combinatorics.choose.bounds,
  `combinatorics.derangements.exponential,
  `data.buffer.parser,
  `data.fintype.fin,
  `data.int.absolute_value,
  `data.int.nat_prime,
  `data.list.prod_monoid,
  `data.nat.choose.vandermonde,
  `data.polynomial.cardinal,
  `data.real.pi.leibniz,
  `data.real.pointwise,
  `data.vector,
  `dynamics.fixed_points.topology,
  `field_theory.mv_polynomial,
  `linear_algebra,
  `linear_algebra.affine_space.basic,
  `linear_algebra.charpoly.to_matrix,
  `measure_theory.integral.divergence_theorem,
  `number_theory.basic,
  `number_theory.lucas_primality,
  `number_theory.sum_two_squares,
  `probability_theory.notation,
  `ring_theory.fintype,
  `system.io,
  `system.io_interface,
  `tactic.by_contra,
  `tactic.converter.apply_congr,
  `tactic.dec_trivial,
  `tactic.lean_core_docs,
  `tactic.linarith.lemmas,
  `tactic.noncomm_ring,
  `tactic.norm_swap,
  `tactic.nth_rewrite,
  `tactic.obviously,
  `tactic.rewrite_search.frontend,
  `tactic.show_term,
  `tactic.simp_rw,
  `tactic.simpa,
  `topology.category.CompHaus,
  `topology.category.Profinite,
  `topology.category.Top.epi_mono,
  `topology.uniform_space.complete_separated]
end ignore

meta def optimize_imports (e : environment) (nam : name) (G : dag name) (Gr := G.reachable_table) :
  name × list string × ℕ × ℕ :=
  let i := get_minimal_imports e nam G Gr,
      i2 := G.find nam in
  (nam, (i.keys.map to_string).qsort (λ a b, a < b : string → string → bool),
    G.count_descendents (i.keys : list name),
    -- i2 ++
    G.count_descendents (i2 : list name))

-- https://unix.stackexchange.com/questions/342516/sed-remove-all-matches-in-the-file-and-insert-some-lines-where-the-first-match
-- Note:
-- This clobbers import comments
-- Mac should use gsed
-- This pipes to stdout, use -i for in-place
def output_to_sed (o : name × list string × ℕ × ℕ) : string :=
let fn := o.1.to_string_with_sep "/",
    imps := "\\\n".intercalate $ o.2.1.map (λ i, sformat!"import {i}") in
"sed '/^import /{x;//!c\\" ++ sformat!"
{imps}
d}' src/{fn}.lean\n"

-- #eval trace_val $ output_to_sed (`a.b.c, "import ok
-- import hi", 0,0)
-- #exit

-- set_option profiler true
run_cmd unsafe_run_io (do
  e ← run_tactic get_env,
  let L := good_files.take 1,
  G ← get_import_dag e L,
  -- let file_to_import := mk_file_to_import e,
  -- let G' := mk_file_dag e `algebra.group_with_zero.basic file_to_import,
  -- print_ln G'.keys,
  -- print_ln $to_fmt G,
  let Gr := G.reachable_table,
  let nal :=[`init.util, `order.complete_boolean_algebra, `system.random, `init.meta.ac_tactics, `init.data.list.basic, `data.list.chain, `init.meta.async_tactic, `data.list.min_max, `tactic.cache, `data.nat.choose.basic, `data.multiset.erase_dup, `init.meta.well_founded_tactics, `init.funext, `data.nat.pairing, `init.meta.smt.interactive, `init.meta.format, `data.equiv.basic, `data.finset.prod, `tactic.show_term, `init.data.subtype.basic, `data.subtype, `init.data.unsigned.basic, `init.data.to_string, `tactic.tidy, `tactic.pretty_cases, `init.data.sum.basic, `order.rel_classes,
`tactic.monotonicity.interactive, `init.data.nat.bitwise, `tactic.push_neg, `init.meta.converter, `tactic.trunc_cases, `data.pfun, `tactic.lint.misc, `control.traversable.basic, `data.dlist.basic, `init.control.monad_fail, `init.meta.local_context, `init.meta.interactive, `data.pi, `init.meta.level, `data.rat.basic, `data.nat.enat, `init.data.list.instances, `data.set.bool, `tactic.replacer, `tactic.pi_instances, `algebra.group_power.lemmas, `data.part, `tactic.tauto,
`init.data.nat.div, `tactic.localized, `algebra.group_power.order, `algebra.group.inj_surj, `order.compare, `control.traversable.derive, `init.data.list.lemmas, `tactic.congr, `init.meta.options, `meta.expr, `data.int.cast, `init.meta.mk_has_sizeof_instance, `init.meta.smt.rsimp, `data.sigma.basic, `tactic.lint.basic, `init.control.except,
`data.set.lattice, `logic.relator, `init.meta.attribute, `init.meta.tagged_format, `data.list.of_fn, `tactic.generalize_proofs, `init.coe, `tactic.hint, `tactic.core, `init.data.subtype, `init.meta.converter.interactive, `init.meta.expr_address, `tactic.where,
`data.list.lex, `data.finset.fold, `order.boolean_algebra, `tactic.itauto, `tactic.dependencies, `tactic.binder_matching, `tactic.norm_cast, `init.meta.interaction_monad, `algebra.group_power.basic, `data.rat.cast, `order.preorder_hom, `init.algebra.functions, `algebra.group.prod, `init.meta.rec_util, `init.meta.comp_value_tactics,
`control.functor, `logic.basic, `init.meta.rewrite_tactic, `algebra.group.units, `algebra.group.to_additive, `init.meta.hole_command, `tactic.norm_num, `init.data.repr, `tactic.rewrite, `init.cc_lemmas, `data.list.prod_monoid,
`tactic.derive_inhabited, `tactic.ext, `data.list.erase_dup, `data.prod, `init.data.bool.basic, `tactic.obviously, `init.control.option, `init.meta.rb_map, `init.meta.lean.parser, `data.finset.basic, `tactic.interactive, `tactic.choose, `init.control.lawful, `init.meta.constructor_tactic,
`logic.function.conjugate, `init.data.setoid, `control.traversable.instances, `tactic.auto_cases, `algebra.order.sub, `data.bool, `tactic.simps, `data.vector.basic, `tactic.simp_command, `algebra.group.semiconj, `tactic.restate_axiom,
`init.control, `data.list.permutation, `tactic.mk_iff_of_inductive_prop, `init.control.state, `data.multiset.basic, `init.control.monad, `data.equiv.set, `data.mllist, `tactic.lift, `algebra.group.hom_instances, `init.propext, `data.pnat.basic, `data.option.defs,
`tactic.generalizes, `init.meta.exceptional, `init.meta.name, `data.multiset.pi, `data.list.defs, `data.set.function, `data.dlist, `data.set.basic, `init.algebra.classes, `tactic.protected, `data.finset.option, `control.traversable.lemmas, `data.list.nodup, `tactic.elide, `order.basic, `init.data.list, `tactic.lean_core_docs,
`init.data.list.qsort, `tactic.explode, `init.data.option.basic, `data.rbtree.init, `init.meta.smt.congruence_closure, `init.meta.smt, `data.nat.pow, `init.meta.task, `algebra.group_with_zero.basic, `algebra.regular.basic, `tactic.lint.simp, `control.basic, `data.nat.factorial.basic, `algebra.order.ring, `data.nat.basic, `order.directed, `tactic.fix_reflect_string, `init.control.alternative, `algebra.order.field, `order.rel_iso, `init.data.sigma.basic,
`init.control.functor, `tactic.nth_rewrite.congr, `data.multiset.powerset, `init.meta.mk_has_reflect_instance, `init.meta.contradiction_tactic, `control.traversable.equiv, `data.ulift, `init.meta, `init.meta.mk_dec_eq_instance, `init.control.lift, `data.equiv.nat, `init.meta.fun_info, `logic.function.iterate, `tactic.lint, `tactic.project_dir, `data.list.sublists, `tactic.lint.type_classes,
`data.equiv.encodable.basic, `data.rat.order, `algebra.char_zero, `data.equiv.mul_add, `tactic.basic, `meta.rb_map, `tactic.apply, `init.meta.mk_inhabited_instance, `init.data.nat, `data.finset.lattice, `init.meta.environment, `init.meta.interactive_base, `data.quot, `tactic.split_ifs,
`init.meta.has_reflect, `tactic.simp_rw, `algebra.big_operators.basic, `group_theory.perm.basic, `logic.nontrivial, `init.meta.backward, `init.function, `init.classical, `tactic.solve_by_elim, `init.meta.expr, `algebra.euclidean_domain, `data.list.perm, `tactic.converter.apply_congr, `order.bounded_lattice, `init.meta.type_context, `data.rat.meta_defs,
`algebra.group.defs, `init.meta.pexpr, `logic.function.basic, `init.core, `init.meta.smt.smt_tactic, `tactic.transform_decl, `tactic.dec_trivial, `tactic.monotonicity, `data.opposite, `tactic.rcases, `algebra.abs, `tactic.nth_rewrite.basic, `tactic.monotonicity.basic, `data.multiset.nodup, `init.data.string.basic,
`algebra.group.hom, `system.io_interface, `init.meta.match_tactic, `tactic.alias, `tactic.reserved_notation, `init.data.prod, `data.list.count, `init.data.fin.basic, `data.finset.powerset, `data.multiset.lattice, `init.data.fin.ops, `data.list.lattice, `order.bounds, `data.rbmap.basic, `init.control.combinators, `algebra.group.basic, `init.control.reader,
`tactic.squeeze, `data.multiset.range, `data.string.defs, `tactic.chain, `algebra.group_with_zero, `order.monotone, `init.data.quot, `data.fin.basic, `algebra.opposites, `algebra.covariant_and_contravariant, `init.data.nat.lemmas, `init.wf, `init.logic, `tactic.simp_result, `order.min_max, `data.buffer,
`tactic.rename_var, `logic.embedding, `tactic.converter.old_conv, `tactic.simpa, `tactic.algebra, `init.meta.relation_tactics, `init.meta.ref, `data.int.basic, `init.meta.congr_lemma, `algebra.group.type_tags, `data.list.range, `init.meta.simp_tactic, `init.meta.declaration,
`data.rbtree.default_lt, `init.meta.case_tag, `data.fintype.basic, `data.array.lemmas, `data.buffer.parser, `init.data.subtype.instances, `tactic.finish, `logic.unique, `order.lattice, `tactic.clear, `tactic.monotonicity.lemmas, `data.set.intervals.basic,
`control.traversable, `init.control.id, `algebra.field, `data.nat.gcd, `init.meta.module_info, `algebra.group.units_hom, `tactic.nth_rewrite, `init.meta.derive, `algebra.group.commute,
`init.meta.tactic, `tactic.delta_instance, `init.data.sigma.lex, `init.data.fin, `init.data.ordering.basic, `logic.is_empty, `data.set.pairwise, `data.list.forall2,
`init.meta.converter.conv, `init.meta.set_get_option_tactics, `meta.expr_lens, `tactic.suggest, `data.rel, `data.multiset.fold, `algebra.ring.basic, `data.list.join,
`control.applicative, `algebra.divisibility, `init.meta.occurrences, `algebra.group.with_one, `data.nat.cast, `algebra.group.pi, `init.meta.injection_tactic, `tactic.converter.interactive,
`data.list.big_operators, `algebra.order.monoid, `tactic.apply_fun, `order.order_dual, `data.nat.sqrt, `data.sym.basic, `logic.relation, `tactic.wlog, `algebra.order.group,
`tactic.interactive_expr, `group_theory.group_action.defs, `order.complete_lattice, `control.monad.basic, `tactic.find, `data.finset.pi, `algebra.order.monoid_lemmas, `init.meta.congr_tactic, `tactic.doc_commands, `init.meta.smt.ematch,
`data.int.char_zero, `data.multiset.finset_ops, `init.algebra.order, `init.data.char.basic, `data.vector, `init.meta.vm, `data.sum, `data.list.pairwise, `order.well_founded, `init.data.nat.basic, `algebra.invertible, `order.galois_connection, `data.list.basic, `data.option.basic, `algebra.group_power, `data.list.zip, `tactic.lint.frontend,
`system.io, `init.control.applicative, `tactic.unify_equations, `algebra.group_with_zero.defs],
  -- print_ln $ G.all_paths `algebra.big_operators.enat `algebra.euclidean_domain,
  print_ln $ G.all_paths `algebra.big_operators.basic `data.nat.enat,
  print_ln $ G.all_paths `data.nat.enat `tactic.norm_num,
  print_ln "mins",
  print_ln $ to_fmt $ G.minimal_vertices [`algebra.big_operators.basic, `data.nat.enat],
  print_ln $ to_fmt $ G.minimal_vertices nal,
  -- print $ to_fmt $ Gr.find `algebra.big_operators.enat
  -- print $ (Gr.ifind `n).to_list
  let T := L.map (λ nam, optimize_imports e nam G Gr),
  print T,
  (T.map output_to_sed).mmap print
)
  -- trace a
  -- let b := a.head,
  -- trace ((import_to_file e.get_mathlib_dir b)),
  -- trace (file_to_import e.get_mathlib_dir (import_to_file e.get_mathlib_dir b))

  -- io.print $ b.to_list.qsort (λ q w : name × ℕ, w.snd > q.snd),
  -- guardb (0 ∈ b.to_list.map (prod.snd)),
  -- G ← unsafe_run_io $ get_import_dag e n,
  -- let okimps := (G.find n).filter (λ de, ¬((de, 0) ∈ b.to_list)),
  -- trace okimps,
  -- trace $ G.vertices.filter (λ v, ¬ (v, 0) ∈ b.to_list)

  -- trace $ G.minimal_vertices (rb_set.of_list $ G.vertices.filter (λ v, ¬ (v, 0) ∈ b.to_list)),
  -- d← get_decl `vector.to_list_append,
  -- a ←  unsafe_run_io $ get_import_dag e $ file_to_import e.get_mathlib_dir (file_name (e.decl_olean `zmod.quadratic_reciprocity)),
  -- trace a,
  -- trace (all_paths a `algebra.algebra.basic `tactic.abel),
  -- trace (all_paths a `number_theory.quadratic_reciprocity `category_theory.whiskering),
  -- trace $ import_to_file e.get_mathlib_dir $ file_to_import e.get_mathlib_dir$file_name (e.decl_olean `zmod.quadratic_reciprocity),
  -- G ← unsafe_run_io $ get_import_dag e `data.int.basic,
  -- G.mfold () (λ na de _, do
  -- b ←  unsafe_run_io $ mk_file_dep_counts e na,
  -- if 0 ∈ b.to_list.map (prod.snd) then
  -- trace $ na.to_string ++ to_string b.to_list
  -- else
  -- skip
  -- ),
  -- b ←  unsafe_run_io $ mk_file_dep_counts e $ `algebra.algebra.basic,
  -- b ←  unsafe_run_io $ mk_file_dep_counts e $ file_to_import e.get_mathlib_dir (file_name (e.decl_olean `zmod.quadratic_reciprocity)),
  -- trace (list.qsort (λ q w : name × ℕ, w.snd < q.snd) b.to_list),
  -- trace $ mk_data e d,

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

-- run_cmd (do
--   e ← get_env,
--   let nam:=`tactic.basic,
--   -- f ← unsafe_run_io $ mk_file_handle (import_to_file e.get_mathlib_dir nam) io.mode.read,
--   trace $ unsafe_run_io $ get_import_dag e nam
--   -- trace a
--   -- let b := a.head,
--   -- trace ((import_to_file e.get_mathlib_dir b)),
--   -- trace (file_to_import e.get_mathlib_dir (import_to_file e.get_mathlib_dir b))
-- )


-- meta def main : tactic unit :=
-- do curr_env ← get_env,
--    h ← unsafe_run_io (mk_file_handle "data.yaml" mode.write),
--    let decls := curr_env.fold [] list.cons,
--    let filtered_decls := decls.filter
--      (λ x, not (to_name x).is_internal),
--    filtered_decls.mmap' (λ d,
--      do s ← (print_item_crawl curr_env d),
--         unsafe_run_io (do io.fs.put_str_ln h s,
--                           io.fs.flush h),
--         skip),
--    unsafe_run_io (close h),
--    skip
-- open io io.fs native tactic
-- meta def main : io unit :=
-- do
--   e ← run_tactic get_env,
--   -- b ← mk_file_dep_counts e `data.int.basic,
--   G ← get_import_dag e `all,
--   io.print "running on:\n",
--   io.print (to_fmt G.keys),
--   G.keys.mmap' (λ na, do
--     b ← mk_file_dep_counts e na,
--     -- io.print "hi",
--     io.print ("\n" ++ na.to_string ++" >>> \n" ++ to_string (b.to_list.qsort (λ q w : name × ℕ, w.snd < q.snd)) ++ "\n"),
--     guardb (¬ 0 ∈ b.to_list.map (prod.snd)) <|> (do
--       io.print "##### some zeroes\n",
--       io.print "ok and nok imps\n",
--       let okimps := (G.find na).filter (λ de, ¬((de, 0) ∈ b.to_list)),
--       io.print okimps,
--       let nokimps := (G.find na).filter (λ de, ((de, 0) ∈ b.to_list)),
--       io.print nokimps,
--       io.print "\nall rems\n",
--       io.print $ G.vertices.filter (λ v, ¬ (v, 0) ∈ b.to_list)
--       ))
-- run_cmd unsafe_run_io main
