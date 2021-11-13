import tactic.lint
import meta.rb_map
variables (T : Type)
meta def dag : Type := native.rb_lmap T T
-- TODO remove has_to_strings that were only needed for tracing

namespace dag
-- private meta def reflect_dag {X Y : Type} [has_reflect X] [has_reflect Y] : has_reflect (X × Y)
-- | ns := `(id %%(r.mkp `(prod.mk [ ns.1, ns.2]) : X × Y)
-- private meta def reflect_dag [has_reflect T] : has_reflect (dag T) | ns :=
--  expr.mk_app `(native.rb_map.of_list) (list.reflect ((native.rb_map.fold ns [] (λ a b o, (a, b) :: o)))
-- `(id %%(expr.mk_app `(Prop) $ ns.map (flip expr.const [])) : dag T)

meta def mk  [has_lt T] [decidable_rel ((<) : T → T → Prop)] : dag T := native.rb_lmap.mk T T
variable {T}
meta def insert_vertex (d : dag T) (a : T) : dag T :=
if ¬ native.rb_map.contains d a then
  native.rb_map.insert d a []
else
  d
meta def insert_vertices (d : dag T) (a : list T) : dag T := a.foldl insert_vertex d
meta def vertices : dag T → list T := native.rb_map.keys
meta def edges (d : dag T) : list (T × T) := native.rb_map.fold d []
  (λ v es old, old ++ es.map (λ x, (v, x)))
meta def num_edges (d : dag T) : ℕ := d.fold 0 (λ _ l o, o + l.length)

section dec_eq
variable [decidable_eq T]
meta def insert_edge (d : dag T) (v w : T) : dag T := if w ∈ d.find v then d else insert_vertex (native.rb_lmap.insert d v w) w
meta def insert_edges (d : dag T) (a : list (T × T)) : dag T := a.foldl (λ da ⟨v, w⟩, insert_edge da v w) d
meta def erase_all (d : dag T) (l : list T) : dag T := l.foldl (λ o v, native.rb_map.fold (native.rb_map.erase o v) (native.rb_map.erase o v) (λ w ll oll, native.rb_map.insert oll w (ll.erase v))) d
end dec_eq

section
variables [has_to_format T]
open format prod native.rb_map
private meta def format_key_data (k : T) (d : list T) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ "\"" ++ to_fmt k ++ "\""  ++ space ++ to_fmt "-> {" ++ space ++ to_fmt (",".intercalate $ d.map (λ a, "\""++(format.to_string $ to_fmt a) ++ "\"")) ++ space ++ "};" -- todo what symbol?

meta instance : has_to_format (dag T) :=
⟨λ m, group $ to_fmt "digraph D {" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ k d p, (fst p ++ format_key_data k d (snd p), ff)))) ++
              to_fmt "}"⟩
meta instance : has_repr (dag T) := ⟨λ s, (has_to_format.to_format s).to_string⟩
end


open native
/-- Inner loop of the dfs, this is called by dfs for any starting vertex, and recurses through the graph updating the
  accumulator `acc` as it progresses by applying the function `f`.
  The search is depth first so that
  ```
  (((dag.mk ℕ).insert_edges [(1, 2), (2,3)]).dfs_aux (λ a b, a) (λ _ _, id) 1 (0, mk_rb_set)).fst
  ```
  outputs 1 as the function `f = (λ a b, a)` updates the accumulator to the last seen vertex.

  The function `g pa ch` updates the accumulator when a parent vertex `pa` sees a child vertex `ch` that has been seen before.
  This happens when there are undirected cycles.
  The order in which descendents of a given vertex are visited depends on the order they were added in.
  ```
  (((dag.mk ℕ).insert_edges [(4,1),(4,3),(1, 2), (3,2)]).dfs_aux
    (λ _ acc, acc ++ "")
    (λ pa ch acc, acc ++ _root_.to_string (pa,ch) ++ " forms part of an (undirected) cycle!\n") 4 ("", mk_rb_set)).fst
  ```
 -/
meta def dfs_aux {α : Type} (d : dag T) (f : T → α → α) (g : T → T → α → α) : T → (α × rb_set T) → (α × rb_set T)
-- vertex and stack, visited pair
| v ⟨acc, seen⟩ :=
let res : α × rb_set T :=
  (d.find v).foldl
    (λ ⟨acc', seen'⟩ w,
      if seen'.contains w then
        ⟨g v w acc', seen'⟩
      else
        dfs_aux w (acc', seen'))
  (acc, seen.insert v) in
res.map (f v) id

variables [has_lt T] [decidable_rel ((<) : T → T → Prop)]

/-- Depth first search used for alles.
A very general version of dfs.
E.g.

```
#eval (((dag.mk ℕ).insert_edges [(1,2),(1,3),(2,4),(2,5), (3,6), (3,7)]).dfs
  (λ n acc, acc ++ to_string n)
  ""
```
 -/
meta def dfs {α : Type} (d : dag T) (f : T → α → α) (a : α) (start : list T := d.vertices) (g : T → T → α → α := λ _ _, id) : α :=
(start.foldl (λ (acc : α × rb_set T) v, if acc.2.contains v then acc else d.dfs_aux f g v acc) (a, mk_rb_map)).fst

-- #eval (((dag.mk ℕ).insert_edges [(9,7),(3,7),(4,3),(4,9)]).dfs_aux
--   (λ _ acc, acc ++ "")
--   (λ pa ch acc, acc ++ _root_.to_string (pa,ch) ++ " forms part of an (undirected) cycle!\n") 4 ("", mk_rb_set)).fst

-- TODO is this inefficient?
/-- Take the sub-graph of things reachable from `v` -/
meta def reachable (d : dag T) (v : T) : dag T :=
(d.dfs_aux (::) (λ _ _, id) v ([], mk_rb_map)).fst.foldl (λ ol w, rb_map.insert ol w $ d.find w) (dag.mk T)

meta def reachable_table (d : dag T) (vs : list T := d.vertices) : rb_map T (rb_set T) :=
d.dfs (λ v acc,
  (d.find v).foldl (λ acc' de, acc'.insert v $ (acc'.ifind v).union (acc'.ifind de)) acc)
  (d.fold mk_rb_map (λ v _ acc, acc.insert v $ rb_set.of_list [v]))
  vs

-- #eval (((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5), (5,6),(5,8),(8,7),(8,6), (6,7)])
--   .reachable_table.ifind 5).to_list

-- | [] c := c
-- | (n :: S) c := (d.find n).foldl
--   (λ old ins,
--     (native.rb_map.fold (reachable ins) old
--       (λ k d a, a.insert_edges (d.map (λ v, (k, v))))).insert_edge n ins)
--   ((dag.mk T).insert_vertex n)
/- Take the sub-graph of things reachable from a list of names-/
-- meta def reachable'_core (orig : dag T) : list T → native.rb_map T bool → dag T → dag T
-- | (h :: l) vis d := (orig.find h).foldl (λ o w, reachable'_core l vis d) (vis.insert h tt)
-- | [] _ d := d
-- meta def reachable' : list T → dag T → dag T :=
-- λ l d, reachable'_core l
  -- (d.fold (native.rb_map.mk _ _) (λ v _ o, o.insert v false)) d
-- λ n t,
--   (t.find n).foldl
--   (λ old ins,
--     (native.rb_map.fold (reachable ins t) old
--       (λ k d a, native.rb_map.insert a k d)).insert n ins)
--   (dag.mk T)
open native

/-- Return the list of minimal vertices in a dag -/
meta def minimal_vertices' (d : dag T) (start : list T := d.vertices) : rb_set T :=
let aux : rb_map T bool :=
d.dfs (λ v acc, if acc.contains v then acc else acc.insert v ff)
      (start.foldl (λ (acc : rb_map T bool) v, acc.insert v tt) mk_rb_map)
      start
      (λ v de acc, acc.insert de ff) in
start.foldl (λ acc v, if (aux.find v).get_or_else ff then acc.insert v else acc) mk_rb_set

meta def minimal_vertices (d : dag T) (start : list T := d.vertices) : rb_set T :=
d.dfs (λ v acc, (d.find v).foldl (λ acc' de, acc'.erase de) (acc.insert v)) mk_rb_set start

-- #eval (((dag.mk ℕ).insert_edges [(1,2), (1,3), (2,4), (3,4)]).minimal_vertices $ [2,4,3]).to_list
-- #eval (((dag.mk ℕ).insert_edges [(1,2), (2,3), (3,4), (4,5)]).minimal_vertices $ [2]).to_list
-- #eval (((dag.mk ℕ).insert_vertex 2).minimal_vertices $ [2]).to_list
-- #eval (((dag.mk ℕ).insert_edges [(1,2)]).minimal_vertices $ [1,2]).to_list

meta def merge_el [decidable_eq T] (S : list (list T)) :
  option (list T) → option (list T) → list (list T)
| none _ := S
| _ none := S
| (some u) (some v) := ((S.erase u).erase v).insert (u.union v)
meta def merge [decidable_eq T] (S : list (list T)) (u v : T) : list (list T) :=
merge_el S (S.find (λ s : list T, u ∈ s))
           (S.find (λ s : list T, v ∈ s))

/-- Return a topological sort of the DAG. -/
meta def topological_sort (d : dag T) (start : list T := d.vertices) : list T :=
d.dfs (::) [] start

variable [inhabited T]

meta def minimal_vertices_components_dfs [decidable_eq T] (d : dag T) (t : T) : T → rb_map T bool → rb_map T T
  → list (list T) → (rb_map T bool × rb_map T T × list (list T))
| v minimals visited components :=
    ((d.find v).foldl
      (λ ⟨mins, vis, fcomps⟩ w,
        let fcomps' := merge fcomps t w in
        if h : vis.contains w then
          -- TODO could replace with find_def w
          (mins.insert w ff, vis, merge fcomps' t (vis.ifind w))
        else
          minimal_vertices_components_dfs w (mins.insert w ff) vis fcomps')
      (minimals, visited.insert v t, components))

--#eval _root_.to_string (((((dag.mk ℕ).insert_vertex 3).insert_edge 2 1).insert_edge 2 3).minimal_vertices_components_dfs
  -- 2 2 ([1,2,3].foldl (λ o oo, o.insert oo tt) (rb_map.mk _ _))
  --     ([3].foldl (λ o oo, o.insert oo 3) (rb_map.mk _ _))
  --     ([1,2,3].foldl (λ o oo, o.insert ([oo])) ([]))
  --     )



/-- Return the list of minimal vertices in a dag -/
meta def minimal_vertices_with_components_aux [decidable_eq T] (d : dag T) (start : native.rb_set T) :
  native.rb_map T bool × native.rb_map T T × list (list T) :=
start.fold
  ((-- minimal vertices
    d.vertices.foldl (λ ol t, native.rb_map.insert ol t tt) (native.rb_map.mk T bool),
    -- visited
    rb_map.mk T T,
    -- components
    start.fold [] (λ t ol, [t] :: ol)) :
    native.rb_map T bool × native.rb_map T T × list (list T))
  (λ (v : T) (minsviscomp : native.rb_map T bool × native.rb_map T T × list (list T)),
  -- _root_.trace_val $
    if minsviscomp.2.1.contains v then -- already visited
      minsviscomp
    else
      minimal_vertices_components_dfs d v v minsviscomp.1 minsviscomp.2.1 minsviscomp.2.2)

meta def minimal_vertices_with_components [decidable_eq T] (d : dag T) (start : native.rb_set T) :
  rb_set T × list (list T) :=
(λ ans : native.rb_map T bool × native.rb_map T T × list (list T),
  ((ans.fst.fold mk_rb_set (λ w b ol, if b && start.contains w then ol.insert w else ol),
    ans.snd.snd) : rb_set T × list (list T)))
(minimal_vertices_with_components_aux d start)

--#eval to_string ((((dag.mk ℕ).insert_vertex 3).insert_edges [(1, 5), (3, 2), (4,5), (2,5)]).minimal_vertices_with_components_aux (rb_set.of_list [1,3,4])).2.2

  -- (native.rb_map.fold d
  --   (([] : list T), mk_rb_set)
  --   (λ v es stavis,
  --     if stavis.snd.contains v then
  --       stavis
  --     else
  --       d.dfs_aux (::) (λ _ _, id) v stavis)
  -- ).fst

-- meta def topological_sort' (d : dag T) [has_to_string T]:tactic unit :=
-- do
--   native.rb_map.mfold d
--     (([] : list T), d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk T bool))
--     (λ v es ⟨stack, vis⟩,
--       if (vis.find v).get_or_else ff then
--         do
--         tactic.trace "a",
--         tactic.trace $ to_string v,
--         tactic.trace $ to_string stack,
--         tactic.trace $ to_string vis,
--         return ⟨stack, vis⟩
--       else
--         do
--         tactic.trace "b",
--         tactic.trace $ to_string v,
--         return $ dfs d v stack vis),
--     return ()
-- #eval (λ d : dag _, (d.dfs 5 ([] : list _) (d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk _ bool))).fst) (((dag.mk ℕ).insert_vertices [0, 1, 2, 3, 4, 5]).insert_edges [(5, 2), (5,0),(4,0),(4,1),(2,3),(3,1)])
--#eval (((dag.mk ℕ).insert_vertices [0, 1, 2]).insert_edges [(0, 1), (2,1),(0,2)]).topological_sort
-- run_cmd (((dag.mk ℕ).insert_vertices [0, 1, 2]).insert_edges [(0, 1), (2,1),(0,2)]).topological_sort'

-- [id :linear_ordered_add_comm_group : [linear_ordered_cancel_add_comm_monoid, linear_order],
--  id :linear_order : [],
--  id :linear_ordered_cancel_add_comm_monoid : [linear_order]]
/-
Return the prefix of l up to and including the first element satisfying P
-/
def slice_up_to {α : Type*} (P : α → Prop) [decidable_pred P] : list α → list α
| [] := []
| (a :: l) := if P a then [a] else a :: slice_up_to l
--#eval slice_up_to (∈ [1,2,4]) [5,5,612,4,12,1]

/-
Is vertex w reachable from v in the dag d, given ts a topological sort of d.
-/
meta def is_reachable [has_to_string T] (d : dag T) (ts : list T) (v w : T) : bool :=
-- _root_.trace (_root_.to_string v) $
-- _root_.trace (_root_.to_string w) $
(d.reachable v).contains w
/-- are all vertices in `S` inside dag `d` with reachable table `dr` reachable from `v` -/
meta def all_reachable [has_to_string T] (d : dag T) (dr : rb_map T (rb_set T)) (v : T) (S : list T) : bool :=
-- _root_.trace (_root_.to_string v) $
-- _root_.trace (_root_.to_string S) $
-- _root_.trace (has_to_format.to_format dreach).to_string $
S.foldl (λ (ol : bool) (w : T), ol && ((dr.find v).get_or_else mk_rb_set).contains w) tt
-- TODO this is hilariously inefficient
--#eval ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5)]).is_reachable [] 3 3
/-- are all vertices in `S` inside dag `d` with topological sort `ts` reachable from `v` -/
meta def all_reachable' [has_to_string T] (d : dag T) (ts : list T) (v : T) (S : list T) : bool :=
-- _root_.trace (_root_.to_string v) $
-- _root_.trace (_root_.to_string S) $
let dreach := d.reachable v in
-- _root_.trace (has_to_format.to_format dreach).to_string $
S.foldl (λ (ol : bool) (w : T), ol && dreach.contains w) tt
-- TODO this is hilariously inefficient
--#eval ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5)]).is_reachable [] 3 3

meta def meet [decidable_eq T] [has_to_string T] (d : dag T) (ts : list T) (dr : rb_map T (rb_set T)) (S : list T) : T :=
-- trace (to_string ts)
((slice_up_to (∈ S) ts).reverse.find (λ v, d.all_reachable dr v S)).iget

meta def meet' [decidable_eq T] [has_to_string T] (d : dag T) (S : list T) : T := let ts := d.topological_sort in
-- trace (to_string ts)
((slice_up_to (∈ S) ts).reverse.find (λ v, d.all_reachable' ts v S)).iget

--#eval ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5),(7,1),(7,3)]).meet [3,1]
meta def meets_of_components [decidable_eq T] [has_to_string T] (d : dag T) (ts : list T) (dr : rb_map T (rb_set T)) (start : native.rb_set T) :
  native.rb_set T :=
rb_set.of_list $ (d.minimal_vertices_with_components start).snd.map (λ S, d.meet ts dr S)
meta def meets_of_components' [decidable_eq T] [has_to_string T] (d : dag T) (start : native.rb_set T) :
  native.rb_set T :=
rb_set.of_list $ (d.minimal_vertices_with_components start).snd.map (λ S, d.meet' S)
--#eval rb_set.to_list $ ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5),(7,1),(7,3),(7,6), (6,8)]).meets_of_components
  -- (rb_set.of_list [4,7])
--#eval ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5),(7,1),(7,3), (6,8)]).meet [8]
--#eval ((dag.mk ℕ).insert_edges [(1, 5), (3, 2), (4,5), (2,5),(7,1),(7,3), (6,8)]).reachable 8

end dag
