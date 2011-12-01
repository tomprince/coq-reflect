(*i camlp4deps: "parsing/grammar.cma" i*)

open Libnames
open Coqlib
open Term
open Glob_term

let contrib_name = "Reflect"
let init_constant dir s () = gen_constant contrib_name dir s

let safe_init_constant md name () =
(*  check_required_library md;
  init_constant md name () *)
  find_reference contrib_name md name

let coq_datatypes_constant name =
    safe_init_constant ["Coq"; "Init"; "Datatypes"] name

let plugin_constant name =
    safe_init_constant ["term"] name

module Constants = struct
  let bool = safe_init_constant ["Coq"; "Datatypes"] "bool"
  let _true = coq_datatypes_constant "True"
  let _false = coq_datatypes_constant "False"
  let nat = coq_datatypes_constant "nat"
  let nat_O = coq_datatypes_constant "O"
  let nat_S = coq_datatypes_constant "S"
  let prod = coq_datatypes_constant "prod"
  let pair = coq_datatypes_constant "pair"
  let list = coq_datatypes_constant "list"
  let nil = coq_datatypes_constant "nil"
  let cons = coq_datatypes_constant "cons"

  let identifier = plugin_constant "identifier"
  let identifier_Ident = plugin_constant "Ident"
  let name = plugin_constant "name"
  let name_Name = plugin_constant "Name"
  let name_Anonymous = plugin_constant "Anonymous"
  let dir_path = plugin_constant "dir_path"
  let label = plugin_constant "label"
  let module_path = plugin_constant "module_path"
  let mp_file = plugin_constant "MPfile"
  let mp_dot = plugin_constant "MPdot"
  let kernel_name = plugin_constant "kernel_name"
  let mutual_inductive = plugin_constant "mutual_inductive"
  let inductive = plugin_constant "inductive"
  let universe = plugin_constant "universe"
  let metavariable = plugin_constant "metavariable"
  let existential_key = plugin_constant "existential_key"
  let sorts = plugin_constant "sorts"
  let prop = plugin_constant "KProp"
  let set = plugin_constant "KSet"
  let _type = plugin_constant "KType"
  let cast_kind = plugin_constant "cast_kind"
  let ck_VMcast = plugin_constant "VMcast"
  let ck_DEFAULTcast = plugin_constant "DEFAULTcast"
  let ck_REVERTcast = plugin_constant "REVERTcast"
  let case_info = plugin_constant "case_info"
  let build_case_info = plugin_constant "Build_case_info"
  let prec_declaration = plugin_constant "prec_declaration"
  let constr = plugin_constant "constr"
  let constr_Rel = plugin_constant "Rel"
  let constr_Var = plugin_constant "Var"
  let constr_Meta = plugin_constant "Meta"
  let constr_Evar = plugin_constant "Evar"
  let constr_Sort = plugin_constant "Sort"
  let constr_Cast = plugin_constant "Cast"
  let constr_Prod = plugin_constant "Prod"
  let constr_Lambda = plugin_constant "Lambda"
  let constr_Letin = plugin_constant "Letin"
  let constr_App = plugin_constant "App"
  let constr_Const = plugin_constant "Const"
  let constr_Case = plugin_constant "Case"
  let constr_Fix = plugin_constant "Fix"
  let constr_CoFix = plugin_constant "CoFix"
end

let dl = Util.dummy_loc

let to_coq_identifier id =
  GApp (dl, GRef (dl, Constants.identifier_Ident()), [ String_syntax.interp_string dl (Names.string_of_id id) ])

let to_coq_list t =
  let rec aux = function
    | [] -> GApp (dl, GRef (dl, Constants.nil()), [t])
    | x :: xs -> GApp (dl, GRef (dl, Constants.cons()), [t; x; aux xs])
  in aux

let to_coq_dir_path dp =
  to_coq_list (GRef (dl, Constants.identifier())) (List.map to_coq_identifier (Names.repr_dirpath dp))

let to_coq_module_path =
  let rec aux = function
    | Names.MPfile dp -> GApp (dl, GRef (dl, Constants.mp_file()), [to_coq_dir_path dp])
    | Names.MPbound _ -> raise (Util.UserError ("MPBound not implemented yet", Pp.str""))
    | Names.MPdot (mp, label) -> GApp (dl, GRef (dl, Constants.mp_dot()), [aux mp; to_coq_identifier (Names.id_of_label label)])
  in aux

let to_coq_tuple args =
  let rec aux = function
    | (t,x) :: [] -> (t,x)
    | (t,x) :: xs ->
      let (s, y) = aux xs in
      GApp (dl, GRef (dl, Constants.prod()),
	    [ s; t ]),
      GApp (dl, GRef (dl, Constants.pair()),
	    [ s ;t ; y ;x ])
  in snd (aux (List.rev args))

let to_coq_kn kn =
  match Names.repr_kn kn with
    | (mp, dp, label) ->
      to_coq_tuple
	[ GRef (dl, Constants.module_path()), to_coq_module_path mp
	; GRef (dl, Constants.dir_path()), to_coq_dir_path dp
	; GRef (dl, Constants.label()), to_coq_identifier (Names.id_of_label label)
	]

let to_coq_constant c =
  to_coq_tuple
    [ GRef (dl, Constants.kernel_name()), to_coq_kn (Names.user_con c)
    ; GRef (dl, Constants.kernel_name()), to_coq_kn (Names.canonical_con c)
    ]

let to_coq_constr c =
  match kind_of_term c with
    | Var id -> GApp (dl, GRef (dl, Constants.constr_Var()), [ to_coq_identifier id ])
    | Const c -> GApp (dl, GRef (dl, Constants.constr_Const()), [ to_coq_constant c ])
    | t -> GRef (dl, Constants.constr_Rel())

let glob_to_constr c =
  let (sigma, env) = Lemmas.get_current_context () in
  Constrintern.interp_constr sigma env (Constrextern.extern_glob_constr Names.Idset.empty c)

let to_coq_constr c = glob_to_constr (to_coq_constr c)

TACTIC EXTEND constr
[ "constr" constr(c) ] -> [ fun gl -> Tactics.letin_tac None Names.Anonymous (to_coq_constr c) None Tacticals.onConcl gl ]
END
