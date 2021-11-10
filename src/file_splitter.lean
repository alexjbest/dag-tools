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
import data.list.lex

local attribute [-instance] string_to_name
open tactic declaration environment io io.fs (put_str_ln close)


/-- pre should have a slash at the end -/
def import_to_file (pre : string) (im : name) : string :=
pre ++ im.to_string_with_sep "/" ++ ".lean"-- TODO windows lol

/-- pre should have a slash at the end -/
def file_to_import (pre : string) (file : string) : name :=
name.from_components
((((string.get_rest file pre).get_or_else "Hello, I'm trapped in an error string, please let me out").split_on '.').head.split_on '/')

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

/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
meta def environment.is_in_mathlib (e : environment) (n : name) : bool :=
e.is_prefix_of_file e.get_mathlib_dir n


structure import_data : Type :=
(decl_name : name)
(file_name : string)
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
        -- ++ " : " ++ to_fmt (i.deps)
        ⟩

meta instance : has_to_tactic_format import_data :=
⟨λ b, return $ to_fmt b⟩

meta def mk_data (env : environment) (decl : declaration) : import_data :=
let na := decl.to_name,
    po := env.decl_pos na,
    deps := (list_items decl.type ++ list_items decl.value).erase_dup,
    fname := file_name (env.decl_olean na) in
  { decl_name := na,
    file_name := fname,
    file_pos := po,
    deps := deps, }

meta def mk_file_data (env : environment) (fname : name) : list import_data :=
(env.get_decls.filter
  (λ d : declaration, env.decl_olean d.to_name = import_to_file env.get_mathlib_dir fname)).map
    (mk_data env)

meta def mk_file_dag (env : environment) (fname : name) : dag import_data :=
let fdata := mk_file_data env fname,
    decl_names := fdata.map import_data.decl_name in
fdata.foldl (λ G id,
  id.deps.foldl (λ G2 dep, ((fdata.find (λ el : import_data, el.decl_name = dep)).map -- todo maybe replace with an rb_map
    (λ a, G2.insert_edge a id)).get_or_else G2) (G.insert_vertex id)
  ) (dag.mk _)

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
end rb_counter
end rb_counter
open tactic

meta def mk_file_dep_counts_basic (env : environment) (fname : name) : rb_counter name :=
let G := mk_file_dag env fname,
    Gr := G.reachable_table in
(Gr.fold (rb_counter.mk _) (λ k d o, k.deps.foldl
  (λ o2 dep, if env.is_in_mathlib dep then
      o2.incr_by (file_to_import env.get_mathlib_dir $ file_name $ env.decl_olean dep) d.size
    else o2) o)).erase fname


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
        return (((ls.tail.split_on_p (λ s, "--".is_prefix_of s)).head.filter (≠ "")).map name.from_string ++ a) -- space separated lists on imports (in core)
    else
      if (b ∧ l ≠ "\n") ∨ "/-!".is_prefix_of l then
        return []
      else
        get_imports_aux f b)

meta def get_imports (e : environment) (file : name) : io (list name) :=
do
  f ← mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read <|>
      mk_file_handle (import_to_file e.get_mathlib_dir $ file.append `default) io.mode.read <|>
      mk_file_handle (import_to_file (e.get_project_dir `nat 14) file) io.mode.read <|>
      mk_file_handle (import_to_file (e.get_project_dir `nat 14) $ file.append `default) io.mode.read,
  l ← get_imports_aux f ff,
  fs.close f,
  return l

meta def get_dag_aux (e : environment) : name → dag name → io (dag name)
| n d := do
if d.contains n then return d else do
a ← (get_imports e `data.int.basic),
  l ← get_imports e n,
  l.mfoldl (λ od im, do
    G ← get_dag_aux im od,
    return $ G.insert_edge n im) d

meta def get_import_dag (e : environment) (file : name) : io (dag name) :=
get_dag_aux e file (dag.mk _)

open native
meta def mk_file_dep_counts (env : environment) (fname : name) (Gr : rb_map name (rb_set name)) : io (rb_counter name) :=
do let dc := mk_file_dep_counts_basic env fname,
  -- io.put_str (to_fmt dc).to_string, -- another beautiful hack
  -- G ← get_import_dag env fname,
  -- let Gr := G.reachable_table,
  return $ (Gr.fold dc (λ na ln odc, ln.fold odc (λ de odc', odc'.incr_by de ((dc.find na).get_or_else 0)))).erase fname

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

meta def all_paths {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (src tgt : T) : list (list T) :=
(dfs_all_paths d tgt src $ (mk_rb_map).insert tgt [[tgt]]).find src
-- #eval all_paths ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5), (5,6),(5,8),(8,7),(8,6), (5,19),(19,7), (6,7)]) 1 7

meta def dag.count_descendents {T : Type*} [has_lt T] [decidable_rel ((<) : T → T → Prop)] [decidable_eq T]
  (d : dag T) (start : list T) : ℕ :=
d.dfs (λ _, nat.succ) 0 start
-- #eval count_descendents (((dag.mk ℕ).insert_vertex 3).insert_edges [(1, 5), (4,5), (2,5)]) ([1,4,3])
#check dag.count_descendents
-- run_cmd (do
--   e ← get_env,
--   G ← unsafe_run_io $ get_import_dag e `algebra.group_power.lemmas,
--   trace (all_paths G `data.int.cast `data.equiv.basic),
  -- skip)
meta def get_minimal_imports (e : environment) (n : name) (G : dag name) (Gr := G.reachable_table) :
  io (rb_set name) := do
  -- let n := `ring_theory.discrete_valuation_ring,
  -- let n := `algebra.lie.classical,
  b ← mk_file_dep_counts e n Gr,

  let mins := G.minimal_vertices $ b.keys.filter (λ k, b.find k ≠ some 0),
  return mins

run_cmd (do
  e ← get_env,
  let nam:=`number_theory.lucas_primality,
  -- f ← unsafe_run_io $ mk_file_handle (import_to_file e.get_mathlib_dir nam) io.mode.read,
  G ← unsafe_run_io $ get_import_dag e nam,
  i ← unsafe_run_io $ get_minimal_imports e nam G,
  trace $ "\n".intercalate $ i.keys.map (λ n, "import "++to_string n),
  trace $ G.count_descendents (i.keys : list name),
  i2 ← unsafe_run_io $ get_imports e nam,
  trace i2,
  tactic.trace $ G.count_descendents (i2 : list name)
  -- trace a
  -- let b := a.head,
  -- trace ((import_to_file e.get_mathlib_dir b)),
  -- trace (file_to_import e.get_mathlib_dir (import_to_file e.get_mathlib_dir b))
)

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
  -- trace a.reachable_table ,
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
open io io.fs native tactic
meta def main : io unit :=
do
  e ← run_tactic get_env,
  -- b ← mk_file_dep_counts e `data.int.basic,
  G ← get_import_dag e `all,
  io.print "running on:\n",
  io.print (to_fmt G.keys),
  G.keys.mmap' (λ na, do
    b ← mk_file_dep_counts e na,
    -- io.print "hi",
    io.print ("\n" ++ na.to_string ++" >>> \n" ++ to_string (b.to_list.qsort (λ q w : name × ℕ, w.snd < q.snd)) ++ "\n"),
    guardb (¬ 0 ∈ b.to_list.map (prod.snd)) <|> (do
      io.print "##### some zeroes\n",
      io.print "ok and nok imps\n",
      let okimps := (G.find na).filter (λ de, ¬((de, 0) ∈ b.to_list)),
      io.print okimps,
      let nokimps := (G.find na).filter (λ de, ((de, 0) ∈ b.to_list)),
      io.print nokimps,
      io.print "\nall rems\n",
      io.print $ G.vertices.filter (λ v, ¬ (v, 0) ∈ b.to_list)
      ))
-- run_cmd unsafe_run_io main
