import dag
import data.vector
import crawler
import tactic
import number_theory.quadratic_reciprocity

open tactic declaration environment io io.fs (put_str_ln close)


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

meta def mk_file_data (env : environment) (fname : string) : list import_data :=
(env.get_decls.filter (λ d : declaration, env.decl_olean d.to_name = fname)).map (mk_data env)

meta def mk_file_dag (env : environment) (fname : string) : dag import_data :=
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

/-- A hackish way to get the `src` directory of any project.
  Requires as argument any declaration name `n` in that project, and `k`, the number of characters
  in the path of the file where `n` is declared not part of the `src` directory.
  Example: For `mathlib_dir_locator` this is the length of `tactic/project_dir.lean`, so `23`.
  Note: does not work in the file where `n` is declared. -/
meta def environment.get_project_dir (e : environment) (n : name) (k : ℕ) : option string :=
do
  s ← e.decl_olean n,
  return $ s.popn_back k

/-- A hackish way to get the `src` directory of mathlib. -/
meta def environment.get_mathlib_dir (e : environment) : string :=
(e.get_project_dir `mathlib_dir_locator 23).get_or_else "Hello, I'm trapped in an error string, please let me out"

/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
meta def environment.is_in_mathlib (e : environment) (n : name) : bool :=
e.is_prefix_of_file e.get_mathlib_dir n

open tactic
meta def mk_file_dep_counts (env : environment) (fname : string) : rb_counter string :=
let G := mk_file_dag env fname,
    Gr := G.reachable_table in
Gr.fold (rb_counter.mk _) (λ k d o, k.deps.foldl
  (λ o2 dep, if env.is_in_mathlib dep then o2.incr_by (file_name $ env.decl_olean dep) d.size else o2) o)


run_cmd (do
  e ← get_env,
  -- d← get_decl `vector.to_list_append,
  let a := mk_file_dag e (file_name (e.decl_olean `list.split_at)),
  trace a,
  -- trace a.reachable_table,
  trace $ mk_file_dep_counts e (file_name (e.decl_olean `zmod.quadratic_reciprocity)),
  -- trace $ mk_data e d,
  skip
)

meta def io.handle.get_line_as_string (f : handle) : tactic string :=
do g ← unsafe_run_io $ fs.get_line f, return g.to_list.as_string

meta def get_imports_aux : handle → bool → tactic (list name)
| f b :=
do
  eo ← unsafe_run_io $ io.fs.is_eof f,
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

/-- pre should have a slash at the end -/
def import_to_file (pre : string) (im : name) : string :=
pre ++ im.to_string_with_sep "/" ++ ".lean"-- TODO windows lol

/-- pre should have a slash at the end -/
def file_to_import (pre : string) (file : string) : name :=
".".intercalate
((((string.get_rest file pre).get_or_else "Hello, I'm trapped in an error string, please let me out").split_on '.').head.split_on '/')

meta def get_imports (file : name) : tactic (list name) :=
do e ← get_env,
  f ← unsafe_run_io $ mk_file_handle (import_to_file e.get_mathlib_dir file) io.mode.read,
  get_imports_aux f ff

meta def get_dag_aux : name → dag name → tactic (dag name)
| n d := do
  l ← get_imports n,
  l.mfoldl (λ od im, do G ← (get_dag_aux im od), return $ G.insert_edge n im) d

meta def get_dag (file : name) : tactic (dag name) :=
do e ← get_env,
  get_dag_aux file (dag.mk _)


run_cmd (do
  e ← get_env,
  let nam:=`data.list.defs,
  -- f ← unsafe_run_io $ mk_file_handle (import_to_file e.get_mathlib_dir nam) io.mode.read,
  trace $ get_dag nam
  -- trace a
  -- let b := a.head,
  -- trace ((import_to_file e.get_mathlib_dir b)),
  -- trace (file_to_import e.get_mathlib_dir (import_to_file e.get_mathlib_dir b))
)

meta def main : tactic unit :=
do curr_env ← get_env,
   h ← unsafe_run_io (mk_file_handle "data.yaml" mode.write),
   let decls := curr_env.fold [] list.cons,
   let filtered_decls := decls.filter
     (λ x, not (to_name x).is_internal),
   filtered_decls.mmap' (λ d,
     do s ← (print_item_crawl curr_env d),
        unsafe_run_io (do io.fs.put_str_ln h s,
                          io.fs.flush h),
        skip),
   unsafe_run_io (close h),
   skip
