import data.real.basic
import number_theory.pell
import import_optimizer

-- https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/lemma.20distribution/near/212269963
-- see also https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/lemma.20distribution/near/212255452

lemma real_big : (3000 : ℝ) + 2 > 50 := by norm_num
lemma a :ℕ := 7
lemma b :ℕ := a

meta def expr.get_constants (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ s, match e' with
| expr.const nm _ := s.insert nm
| _ := s
end

meta def declaration.get_constants : declaration → name_set
| (declaration.ax nm _ tp) := tp.get_constants
| (declaration.cnst nm _ tp is_meta) := tp.get_constants
| (declaration.thm nm _ tp bd) := tp.get_constants.union bd.get.get_constants
| (declaration.defn nm _ tp bd _ is_meta) := tp.get_constants.union bd.get_constants

namespace tactic
open lean
open lean.parser
open interactive
open tactic
open widget
open widget_override.interactive_expression

meta def module_info_of_decl (n : name) : tactic module_info :=
do e ← get_env,
match e.decl_olean n with
| some s := return $ module_info.of_module_id s
| none := failed
end

meta def get_env_of (n : name) : tactic environment :=
do e ← get_env,
match e.decl_olean n with
| some s := return $ environment.for_decl_of_imported_module s n
| none := fail!"couldn't find {n}"
end

meta def test_names_at (ns : name_set) (tgt : name) : tactic bool :=
do e ← get_env_of tgt,
   return $ ns.fold tt $ λ nm b, b && e.contains nm
open native

meta def mk_file_to_import' (e : environment) : string → option name :=
let mathlib_pre := e.get_mathlib_dir,
    core_pre := e.get_core_dir in
λ file,
  ((file.get_rest mathlib_pre).orelse   -- take off the mathlib or core prefix
              $ file.get_rest core_pre).map (λ rest : string,
  (name.from_components -- create the name from the suffix
    ((rest.popn_back 5 -- remove the `.lean` suffix
      ).split_on '/')).remove_default)
meta def find_highest (tgt : name) : tactic (name × option name) :=
do
   trace "ok",
   d ← get_decl tgt,
   e ← get_env,

   trace "ok",
   dat ← mk_data e "" d,
   let files := dat.deps.map (λ n, module_info.of_module_id (e.decl_olean n).iget),
   trace "ok",
   let ftoi := mk_file_to_import' e,
  --  trace files,
  let global_fnames : rb_set name := e.get_decls.foldl (λ acc d, (((e.decl_olean d.to_name).bind ftoi).map acc.insert).get_or_else acc) mk_rb_set,
  let fnames : rb_set name := files.foldl (λ acc n, ((ftoi n.id).map acc.insert).get_or_else acc) mk_rb_set,
  --  trace fnames,
   dag ← unsafe_run_io $ get_import_dag e global_fnames.to_list,
  --  trace $ module_info.of_module_id "/",
  let dr := dag.reachable_table,
  -- trace dag,
  trace fnames,
  trace $ dag.minimal_vertices fnames.to_list,
  o ← dag.meet dag.topological_sort dr fnames.to_list,
  let of := import_to_file e.get_mathlib_dir o,
  let m := (dat.deps.filter (λ n, e.decl_olean n = of)).argmax (λ dep, ((e.decl_pos dep).map pos.line).iget),
  return (o, m)
  -- let cnsts := d.get_constants,
  -- cnsts.to_list.mfirst (λ nm,
  --   test_names_at (cnsts.erase nm) nm >>= guardb >> return nm) <|>
  -- fail "didn't find any highest decl"
  --  set_option pp.all true
  --  #check expr.const_name
-- run_cmd trace $ (find_highest ``b)
run_cmd trace $ (find_highest ``pell.xn)
run_cmd trace $ (find_highest ``pell.n_lt_a_pow)

meta def locate_decl (tgt : name) (posi : pos) : tactic unit :=
do file ← find_highest tgt,
   trace file,
   e ← get_env,
  --  let file := match e.decl_olean highest with
  --  | none := "the current file"
  --  | some s := (module_info.of_module_id s).id
  --  end,
   let tgtposi := ((file.2.bind e.decl_pos).map pos.line).iget + 1,
   let htm : html (unit) := h "a" [on_click (λ _, ()), attr.style [("cursor", "pointer")]]
    [(sformat!"{tgt} should be inserted in {file.fst} after line {tgtposi}" : string)],
   trace "oh",
   trace $ import_to_file e.get_mathlib_dir file.1,
   save_widget posi $
    component.ignore_action $
    component.with_effects (λ _ x,
      [widget.effect.reveal_position
        (import_to_file e.get_mathlib_dir file.1) $
        (file.2.bind e.decl_pos).get_or_else ⟨1, 0⟩]) $
      component.pure (λ _, [htm])
  --  trace!"{tgt} belongs in {file.1} after {file.1}" -- TODO
run_cmd trace $ (locate_decl ``pell.n_lt_a_pow $ pos.mk 1 1)

#check show_widget_cmd
reserve notation `#vind_home` -- TODO mve
@[user_command]
meta def find_home_cmd (x : interactive.parse $ tk "#vind_home") : lean.parser unit := do
  ⟨l, c⟩ ← cur_pos,
  na ← ident,
  locate_decl na ⟨l, c - 11⟩,
  pure ()
.

#vind_home pell.xn
#vind_home pell.n_lt_a_pow

end tactic


-- def recfn : ℕ → ℕ
-- | 0 := 0
-- | (n+1) := n


-- #check ``recfn
