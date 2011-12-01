Require Import String ZArith.

(* kernel/names.ml *)
Inductive identifier := Ident : string -> identifier.
Inductive name := Name : identifier -> name | Anonymous : name.
Definition dir_path := list identifier.
Definition label := identifier.
Inductive module_path :=
  | MPfile : dir_path -> module_path
  | MPbound : Empty_set -> module_path (* not implemented *)
  | MPdot : module_path -> label -> module_path.
Definition kernel_name := (module_path * dir_path * label)%type.
Definition mutual_inductive := (kernel_name * kernel_name)%type.
Definition constant := (kernel_name * kernel_name)%type.
Definition inductive := (mutual_inductive * nat)%type.
Definition constructor := (inductive * nat)%type.

(* kernel/univ.ml *)
(* we keep a table of universes that have given to the user *)
Module Type t. Variable t: Type. End t.
Module Univ : t. Definition t := nat. End Univ.
Definition universe := Univ.t.
(* kernel/constr *)
Definition metavariable := nat.
Definition existential_key := nat.

Inductive sorts :=
  | KProp : sorts
  | KSet : sorts
  | KType : universe -> sorts.
Inductive cast_kind := VMcast | DEFAULTcast | REVERTcast.

Record case_info := {
  ci_ind : inductive;
  ci_npar : nat;
  ci_cstr_ndecls : list nat
}.

Definition prec_declaration constr := list constr.
Inductive constr :=
  | Rel : Z -> constr
  | Var : identifier -> constr
  | Meta : metavariable -> constr
  | Evar : existential_key -> list constr -> constr
  | Sort : sorts -> constr
  | Cast : constr -> cast_kind -> constr -> constr
  | Prod : name -> constr -> constr -> constr
  | Lambda : name -> constr -> constr -> constr
  | Letin : name -> constr -> constr -> constr -> constr
  | App : constr -> list constr -> constr
  | Const : constant -> constr
  | Ind : inductive -> constr
  | Constrct : constructor -> constr
  | Case : case_info -> constr -> constr -> list constr -> constr
  | Fix : list nat -> nat -> prec_declaration constr -> constr
  | CoFix : nat -> prec_declaration constr -> constr.

Declare ML Module "reflect".
