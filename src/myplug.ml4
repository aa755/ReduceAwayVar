(* open Pretyping *)

(** In Coq trunk, use the API for plugins, a subset of all the interfaces of Coq. *)   
open API

(** To use tactics from the Ltac plugin *)   
open Ltac_plugin   

(** Plugin declaration, reflected in myplug.v's "Declare ML Module" *)   
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

(** Implementing a tactic looking for appearances of terms *)   
(* fun id : _ => _) *)

(** We build "constr_expr" terms and pass them to [refine], i.e. untyped surface syntax *)   
let underscore = CAst.make (GHole(GoalEvar, IntroAnonymous, None))
let lambda id = CAst.make (GLambda(Name id, Explicit, underscore, underscore))

(* (** We build an action in the tactic monad. See Proofview, Tactics.New and Tacticals.New
  modules for the basic actions and control structures. *)
let myintro id : unit tactic =
  (** In the monad, tactics are applied to multiple goals. To do the same in each goal, 
      we explicitely [enter] each of them. *)
  Goal.nf_enter (fun g ->
  (** Get the current goal's environment and conclusion *)      
  let env = Goal.env g in
  let concl = Goal.concl g in
  (** Use [refine] to give a partial proof term *)
  Refine.refine (fun sigma ->
      (** Here we call the typechecker to go from raw syntax to terms. *)
      ise_pretype_gen (default_inference_flags false)
                      (** env contains the global environment and local hypotheses *)
                      env
                      (** sigma contains the environment of existential variables and
                       universes *)
                      sigma
                      empty_lvar
                      (** Typing constraint for our lambda abstraction *)
                      (OfType concl)
                      (** The partial lambda term, holes will be turned into evars *)
                      (lambda id)))
;;

(** We apply the tactic in sequence when multiple identifiers are given. *)  
let myintros ids = tclTHENLIST (List.map myintro ids) 

(** Extend the grammar of tactics with a new entry for our [intros]. *)                 
TACTIC EXTEND myplug_intro
| [ "myintro" ident_list(ids) ] -> [ myintros ids ]
END *)

(** Command to print constant bodies associated to a global name *)
let myprint name =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  (* References can be constants, inductives, constructors or local variables,
     we only treat constants here. *)
  | ConstRef c ->
      begin match Global.body_of_constant c with
      | Some b ->
         (** Feedback is used to print information to various channels. *)
         Feedback.msg_info Pp.(Printer.pr_constr b)
      | None -> Feedback.msg_info Pp.(str "an axiom, nothing to print")
      end
  | _ ->
     (** Standard error reporting function *)
     CErrors.user_err ~hdr:"myplug" Pp.(str "not implemented")
;;

(** Extend the Vernacular grammar for our new command. 
    The CLASSIFIED clause is used by the STM to schedule the execution
    of this command when seen in a document. *)  
VERNAC COMMAND EXTEND Myplug_print
       CLASSIFIED AS QUERY
| [ "Myprint" global(name) ] -> [ myprint name ]
END
