open Pretyping
open API
open Ltac_plugin   

DECLARE PLUGIN "myplug"

let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose Feedback.msg_info Pp.(str"myplug 1.0 at your service"))
  "myplug"
;;

open Glob_term
open Globnames
open Misctypes
open Evar_kinds
open Decl_kinds
open Names
open Proofview
open Pretyping
open Genarg
open Tacticals.New
open Stdarg

(* fun id : _ => _) *)

let underscore = CAst.make (GHole(GoalEvar, IntroAnonymous, None))
let lambda id = CAst.make (GLambda(Name id, Explicit, underscore, underscore))

let myintro id : unit tactic = Goal.nf_enter (fun g ->
  let env = Goal.env g in
  let concl = Goal.concl g in
  Refine.refine (fun sigma ->
       ise_pretype_gen (default_inference_flags false) env sigma empty_lvar
                       (OfType concl)
                       (lambda id)))
;;

let myintros ids = tclTHENLIST (List.map myintro ids)

TACTIC EXTEND myplug_intro
| [ "myintro" ident_list(ids) ] -> [ myintros ids ]
END

let myprint name =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef c ->
      begin match Global.body_of_constant c with
      | Some b -> Feedback.msg_info Pp.(Printer.pr_constr b)
      | None -> Feedback.msg_info Pp.(str "an axiom, nothing to print")
      end
  | _ -> CErrors.user_err ~hdr:"myplug" Pp.(str "not implemented")
;;

VERNAC COMMAND EXTEND Myplug_print CLASSIFIED AS QUERY
| [ "Myprint" global(name) ] -> [ myprint name ]
END


(* vim: set filetype=ocaml foldmethod=marker: *)
 
