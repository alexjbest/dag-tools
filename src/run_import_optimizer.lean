import import_optimizer
import all
open dag
open interaction_monad
open io io.fs native tactic
meta def main : io unit :=
do
  e ← run_tactic get_env,
  G ← get_import_dag e [`data.int.basic],
  print_ln G.keys,
  let Gr := G.reachable_table,
  print_ln sformat!"running on {G.keys.length} files",
  s ← run_tactic read,
  -- this is the order we will traverse the dag so we can do lower imports first and parallelize too
  let dag_ord := G.ranks.to_list.reverse, --qsort (λ a b, prod.fst a < prod.fst b),
  print_ln dag_ord,
  -- let fdatas := rb_map.of_list $ G.keys.zip (G.keys.map_async_chunked (λ na,
  --   match (do
  --           b ← unsafe_run_io $ is_default e na, -- we skip default files
  --           b2 ← unsafe_run_io $ file_is_in_mathlib e na, -- we only work on mathlib itself (TODO allow other projects)
  --           guardb (b2 ∧ ¬ b) >>
  --   do l ← get_file_data e na,
  --     return $ rb_map.of_list $ l.map (λ t, (t.decl_name, t))) s
  --   with
  --     | result.success w _ := w
  --     | result.exception msg _ _ :=
  --       -- trace ("File splitter failed:\n" ++ msg.elim "(no message)" (λ msg, to_string $ msg ()))
  --       mk_rb_map
  --       end) 10),
  -- print_ln "fdata done",
  -- print_ln fdatas.size,
  -- print_ln "fdata done",
  let res := dag_ord.foldl (λ (acc : dag name × list string) (rankfiles : ℕ × list name),
    let
      files := rankfiles.snd,
      re := acc.1.reachable_table files,
      outs := files.map_async_chunked (λ na,
        match
          (unsafe_run_io $ do
          print_ln na,
            b ← is_default e na, -- we skip default files
            b2 ← file_is_in_mathlib e na, -- we only work on mathlib itself (TODO allow other projects)
            guardb (b2 ∧ ¬ b) >>
            (do
              fdata ← run_tactic $ get_file_data e na,

              let T := optimize_imports e na acc.1 re $
  rb_map.of_list $ fdata.map (λ t, (t.decl_name, t))
              , -- fdatas.ifind na,
              -- the original imports in the source files
              if -- (¬ tt) ∨ -- robust mode
                T.2.2 ≠ 0 -- Any file that ends up with no imports is surely a default-style
                                -- special case, e.g. `tactic.basic` so we ignore it
              then -- update the deps
                return $ some (⟨T.1, rb_set.of_list (G.find na),
                  rb_set.of_list $ (T.2.1 ∪ G.find na).filter $
                  -- TODO this should probably be an actual function
                    λ imp, T.2.1.foldl (λ acc min, acc || (re.ifind min).contains imp) ff = tt,
                  (Gr.find na).iget.sdiff (T.2.1.foldl (λ acc' v, acc'.union $ (re.find v).iget) mk_rb_set),
                  G.count_descendents $ G.find na,
                  T.2.2⟩ : name × rb_set name × rb_set name × rb_set name × ℕ × ℕ)
              else -- don't update the deps
                let old_imp := G.find na in
                return $ some (⟨T.1, rb_set.of_list old_imp, rb_set.of_list old_imp, rb_set.of_list [], G.count_descendents old_imp, G.count_descendents old_imp⟩ : name × rb_set name × rb_set name × rb_set name × ℕ × ℕ)
              ) <|> return none)
          s
        with
          | result.success w _ := w
          | result.exception msg _ _ :=
            trace ("File splitter failed:\n" ++ msg.elim "(no message)" (λ msg, to_string $ msg ()))
            none
       end)
       1 -- chunk size
    in (if tt then
        (outs.filter $
          λ op, option.is_some op = tt).foldl
        (λ oacc outp, let na := outp.iget.fst in
          rb_map.insert oacc na $ outp.iget.2.2.1.to_list) acc.1 -- update the recursive dag
      else

        acc.1, -- old version
     acc.2 ++ (outs.map (option.map output_to_sed)).map option.iget)) -- put all the outputs together
    (G, []),
  -- print_ln $ to_fmt G,
  -- print_ln $ to_fmt res.fst,
  print_ln $ "".intercalate res.snd

-- set_option profiler true
-- run_cmd unsafe_run_io main
