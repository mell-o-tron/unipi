 
(**

This file contains a simple lambda calculus interpreter following the
definitions we used in class, on the first lambda calculus
lecture. You can uncomment the TESTS portions to see it run on some
examples. You can do `#use` on this file in the OCaml top-level to
call its functions directly, or just run `ocaml interp.ml` on the
command line (though doing so will not print anything except for tests
that explcitly call print).

**)

type id = string

type exp =
    Var of id
  | Lam of id * exp
  | App of exp * exp

(* generates a fresh variable name *)
let newvar =
  let x = ref 0 in
  fun () ->
    let c = !x in
    incr x;
    "v"^(string_of_int c)

(* computes the free (non-bound) variables in e *)
let rec fvs e =
  match e with
      Var x -> [x]
    | Lam (x,e) -> List.filter (fun y -> x <> y) (fvs e)
    | App (e1,e2) -> (fvs e1) @ (fvs e2)
;;

(*
(* TESTS *)
fvs (Var "x") = ["x"];;
fvs (Lam ("x",Var "y")) = ["y"];;
fvs (Lam ("x",Var "x")) = [];;
fvs (App (Lam ("x", Var "z"), Var "y")) = ["z"; "y"];;
*)

(* substitution: subst e y m means
  "substitute occurrences of variable y with m in the expression e" *)
let rec subst e y m =
  match e with
      Var x ->
	if y = x then m (* replace x with m *)
	else e (* variables don't match: leave x alone *)
    | App (e1,e2) -> App (subst e1 y m, subst e2 y m)
    | Lam (x,e) ->
      if y = x then (* don't substitute under the variable binder *)
	Lam(x,e)
      else if not (List.mem x (fvs m)) then (* no need to alpha convert *)
	Lam (x, subst e y m)
      else (* need to alpha convert *)
	let z = newvar() in (* assumed to be "fresh" *)
	let e' = subst e x (Var z) in (* replace x with z in e *)
	Lam (z,subst e' y m) (* substitute for y in the adjusted term, e' *)

(*
(* TESTS *)
let m1 =  (App (Var "x", Var "y"));;
let m2 = (App (Lam ("z",Var "z"), Var "w"));;
let m3 = (App (Lam ("z",Var "x"), Var "w"));;
let m4 = (App (App (Lam ("z",Var "z"), Lam ("x", Var "x")), Var "w"))

let m1_zforx = subst m1 "x" (Var "z");;
let m1_m2fory = subst m1 "y" m2
let m2_ughforz = subst m2 "z" (Var "ugh")
let m3_zforx = subst m3 "x" (Var "z")
let m1_m3fory = subst m1 "y" m3
*)

(* beta reduction. *)
let rec reduce e =
  match e with
      App (Lam (x,e), e2) -> subst e x e2 (* direct beta rule *)
    | App (e1,e2) ->
      let e1' = reduce e1 in (* try to reduce a term in the lhs *)
      if e1' != e1 then App(e1',e2)
      else App (e1,reduce e2) (* didn't work; try rhs *)
    | Lam (x,e) -> Lam (x, reduce e) (* reduce under the lambda (!) *)
    | _ -> e (* no opportunity to reduce *)

(*
(* TESTS *)
let m2red = reduce m2
let m3red = reduce m3
let m4red1 = reduce m4
let m4red2 = reduce m4red1
let m13sred = reduce m1_m3fory
*)

(* pretty printing *)

open Format;;

let ident = print_string;;
let kwd = print_string;;

let rec print_exp0 = function
  | Var s ->  ident s
  | lam -> open_hovbox 1; kwd "("; print_lambda lam; kwd ")"; close_box ()

and print_app = function
  | e -> open_hovbox 2; print_other_applications e; close_box ()

and print_other_applications f =
  match f with
  | App (f, arg) -> print_app f; print_space (); print_exp0 arg
  | f -> print_exp0 f

and print_lambda = function
  | Lam (s, lam) ->
      open_hovbox 1;
      kwd "\\"; ident s; kwd "."; print_space(); print_lambda lam;
      close_box()
  | e -> print_app e;;

(*
(* TESTS *)
print_lambda m1; print_newline ();;
print_lambda m2; print_newline ();;
*)
