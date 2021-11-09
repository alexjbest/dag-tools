import dag
import data.vector
import crawler
import tactic
import number_theory.quadratic_reciprocity
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
let name := decl.to_name,
    pos := (env.decl_pos name),
    deps := (list_items decl.type ++ list_items decl.value).erase_dup,
    fname := file_name (env.decl_olean name) in
  -- pos ← pos,
  { decl_name := name,
    file_name := fname,
    file_pos := pos,
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
Gr.fold (rb_counter.mk _) (λ k d o, k.deps.foldl
  (λ o2 dep, if env.is_in_mathlib dep then
      o2.incr_by (file_to_import env.get_mathlib_dir $ file_name $ env.decl_olean dep) d.size
    else o2) o)


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
    if ls.head = "import" then
      do a ← get_imports_aux f tt,
        return (name.from_string ls.tail.head :: a)
    else
      if b then
        return []
      else
        get_imports_aux f b

meta def get_imports (e : environment) (file : name) : io (list name) :=
do
  f ← mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read <|>
                      mk_file_handle (import_to_file e.get_mathlib_dir $ file.append `default) io.mode.read <|>
                      mk_file_handle (import_to_file (e.get_project_dir `nat 14) file) io.mode.read <|>
                      mk_file_handle (import_to_file (e.get_project_dir `nat 14) $ file.append `default) io.mode.read,
  get_imports_aux f ff

meta def get_dag_aux (e : environment) : name → dag name → io (dag name)
| n d := do
  l ← get_imports e n,
  l.mfoldl (λ od im, do
    G ← if od.contains im then return od else get_dag_aux im od,
    return $ G.insert_edge n im) d

meta def get_import_dag (e : environment) (file : name) : io (dag name) :=
get_dag_aux e file (dag.mk _)

meta def mk_file_dep_counts (env : environment) (fname : name) : io (rb_counter name) :=
do let dc := mk_file_dep_counts_basic env fname,
  G ← get_import_dag env fname,
  let Gr := G.reachable_table,
  return $ Gr.fold dc (λ na ln odc, ln.fold odc (λ de odc', odc'.incr_by de ((dc.find na).get_or_else 0)))

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
(d : dag T) (src tgt : T) :
  list (list T) :=
(dfs_all_paths d tgt src $ (mk_rb_map).insert tgt [[tgt]]).find src
-- #eval all_paths ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5), (5,6),(5,8),(8,7),(8,6), (5,19),(19,7), (6,7)]) 1 7


run_cmd (do
  e ← get_env,
  -- d← get_decl `vector.to_list_append,
  -- a ←  unsafe_run_io $ get_import_dag e $ file_to_import e.get_mathlib_dir (file_name (e.decl_olean `zmod.quadratic_reciprocity)),
  -- trace a,
  -- trace (all_paths a `algebra.algebra.basic `tactic.abel),
  -- trace (all_paths a `number_theory.quadratic_reciprocity `category_theory.whiskering),
  -- trace a.reachable_table ,
  -- trace $ import_to_file e.get_mathlib_dir $ file_to_import e.get_mathlib_dir$file_name (e.decl_olean `zmod.quadratic_reciprocity),
  G ← unsafe_run_io $ get_import_dag e `data.int.basic,
  G.mfold () (λ na de _, do
  b ←  unsafe_run_io $ mk_file_dep_counts e na,
  if 0 ∈ b.to_list.map (prod.snd) then
  trace $ na.to_string ++ to_string b.to_list
  else
  skip
  ),
  -- b ←  unsafe_run_io $ mk_file_dep_counts e $ `algebra.algebra.basic,
  -- b ←  unsafe_run_io $ mk_file_dep_counts e $ file_to_import e.get_mathlib_dir (file_name (e.decl_olean `zmod.quadratic_reciprocity)),
  -- trace (list.qsort (λ q w : name × ℕ, w.snd < q.snd) b.to_list),
  -- trace $ mk_data e d,
  skip
)

run_cmd (do
  e ← get_env,
  let nam:=`tactic.basic,
  -- f ← unsafe_run_io $ mk_file_handle (import_to_file e.get_mathlib_dir nam) io.mode.read,
  trace $ unsafe_run_io $ get_import_dag e nam
  -- trace a
  -- let b := a.head,
  -- trace ((import_to_file e.get_mathlib_dir b)),
  -- trace (file_to_import e.get_mathlib_dir (import_to_file e.get_mathlib_dir b))
)


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
