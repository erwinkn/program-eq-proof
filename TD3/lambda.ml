(* --- 1. Implementing the lambda-calculus --- *)

(* 1.1 Lambda terms *)

type var = string;;

type t =
  | Var of var
  | App of t * t
  | Abs of var * t;;

(* UTF8 encoding of the lambda character
   https://stackoverflow.com/questions/33777404/how-to-create-the-lambda-char-in-ocaml *)
let lambda = "\xCE\xBB"

let rec to_string term = match term with
  | Var v -> v
  | App (t, u) -> "(" ^ (to_string t) ^ " " ^ (to_string u) ^ ")"
  | Abs (x, t) -> "(" ^ lambda ^ x ^ "." ^ (to_string t) ^ ")";;

(* Simple printing test *)
let () =
  print_endline (to_string (Abs ("x", App (Var "y", Var "x"))));
  print_endline (to_string (App (Abs ("x", Var "y"), Var "x")));;

(* 1.2 Free variables *)
let rec has_fv x term = match term with
  | Var v -> v = x
  | App (t, u) -> (has_fv x t) || (has_fv x u)
  | Abs (v, t) -> (v <> x) && (has_fv x t);;

let () =
  let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
  assert (has_fv "x" t);
  assert (not (has_fv "y" t));
  assert (has_fv "z" t);
  assert (not (has_fv "w" t));;


(* 1.3 Fresh variables *)
let n = ref 0;;
let fresh () =
  n := !n + 1;
  "x" ^ (string_of_int !n);;


(* 1.4 Substitution of x by u in t 
   sub needs to avoid capture of free variables in u
   when substituting in an abstraction *)
let rec sub x u t = match t with
  | Var v when v = x -> u
  | Var v -> t
  | App (t1, t2) -> App (sub x u t1, sub x u t2)
  | Abs (y, t2) when y = x -> t
  | Abs (y, t2) when has_fv y u ->
     let v = fresh () in
     let t3 = sub y (Var v) t2 in
     Abs (v , sub x u t3)
  | Abs (y, t2) -> Abs (y, sub x u t2);;

let () =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti);
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs("y", Var "y")));;
    

(* 1.5 Beta reduction *)
let rec red t = match t with
  | Var v -> None
  (* The case where a beta reduction step is applied *)
  | App (Abs (x, t), u) -> Some (sub x u t)
  | App (t, u) -> begin match red t with
                   | Some t1 -> Some (App (t1, u))
                   | _ -> begin match red u with
                          | Some t2 -> Some (App (t, t2))
                          | _ -> None
                          end
                   end
  | Abs (x, t) -> begin match red t with
                  | Some t2 -> Some (Abs (x, t2))
                  | _ -> None
                  end;;

(* Normalization (no checks against infinite reductions) *)
let rec normalize t = match red t with
  | None -> t
  | Some t2 -> normalize t2;;

(* Verbal beta reduction: prints the reduction step and keeps a counter *)
let reduction t =
  print_endline (to_string t);
  let rec red_aux t ctr = match red t with
    | None -> print_endline ((string_of_int ctr) ^ " reduction steps"); t
    | Some t2 -> print_endline("-> " ^ (to_string t2));
                 red_aux t2 (ctr+1)
  in red_aux t 0;;

let _ =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2));;


(* 1.6 Normal form equivalence *)
let eq t1 t2 =
  let rec eq_aux n1 n2 = match (n1, n2) with
    | (Var v1, Var v2) -> v1 = v2
    | (App (t1, u1), App (t2, u2)) -> (eq_aux t1 t2) && (eq_aux u1 u2)
    | (Abs (x1, t1), Abs (x2, t2)) -> (x1 = x2) && (eq_aux t1 t2)
    | _ -> false
  in eq_aux (normalize t1) (normalize t2);;

let () =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  assert (eq (App (id2, id2)) id2);;


(* 1.7 Proper beta-equivalence of lambda-terms *)

(* Alpha equivalence *)
let rec alpha t1 t2 = match (t1, t2) with
  | (Var v1, Var v2) -> v1 = v2
  | (App (t1, u1), App (t2, u2)) -> (alpha t1 t2) && (alpha u1 u2)
  | (Abs (x1, t1), Abs (x2, t2)) -> ((x1 = x2) && (alpha t1 t2))
                                    || (alpha t1 (sub x2 (Var x1) t2))
                                    || (alpha t2 (sub x1 (Var x2) t1))
  | _ -> false;;

let () =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y")));
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))));;

(* Full equivalence: 
   put in normal form and check alpha equivalence *)
let full_eq t1 t2 =
  alpha (reduction t1) (reduction t2);;

let () =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string t);
  assert (full_eq t (Abs ("z", Var "y")));;


(* --- 2. Computing in the lambda calculus --- *)

(* 2.1 & 2.2 Basics: identity, booleans *)
let id = Abs ("x", Var "x");;
let btrue = Abs ("x", Abs ("y", Var "x"));;
let bfalse = Abs ("x", Abs ("y", Var "y"));;

(* 2.3 Helper functions *)

(* Abstraction from a list of variables *)
let rec abss var_list t = match var_list with
  | [] -> t
  | h::r -> Abs (h, abss r t);;

(* Application of a list of terms / left-associative *)
let apps term_list = 
  List.fold_left (fun t1 t2 -> App (t1, t2)) (List.hd term_list) (List.tl term_list);;

let () =
  let t = Var "t" in
  assert (abss ["x"; "y"; "z"] t = Abs ("x", Abs ("y", Abs ("z", t))));;

let () =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [t; u; v; w] = App (App (App (t, u), v), w));;

(* 2.4 Conditional *)
let bif = abss ["p"; "a"; "b"] (apps [Var "p"; Var "a"; Var "b"]);;

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [bif; btrue; t; u]) t);
  assert (eq (apps [bif; bfalse; t; u]) u);;

(* 2.5 Church encoding of natural numbers *)
let nat n =
  let rec nat_aux n = match n with
    | 0 -> Var "x"
    | n -> App (Var "f", nat_aux (n-1))
  in Abs("f", Abs("x", nat_aux n));;

(* 2.6 Successor *)
let succ = abss ["n"; "f"; "x"] (App (Var "f", apps [Var "n"; Var "f"; Var "x"]));;

let () =
  assert (eq (apps [succ; nat 5]) (nat 6));;

(* 2.7 Addition *)
let add = abss ["m"; "n"; "f"; "x"] (apps [Var "m"; Var "f"; apps [Var "n"; Var "f"; Var "x"]]);;

let () =
  assert (eq (apps [add; nat 2; nat 3]) (nat 5));;

(* 2.8 Multiplication *)
let mul = abss ["m"; "n"; "f"] (App (Var "m", App(Var "n", Var "f")));;

let () =
  assert (eq (apps [mul; nat 3; nat 4]) (nat 12));;

(* 2.9 Is zero *)
let iszero = Abs ("n", App ( App (Var "n", Abs ("x", bfalse)), btrue));;

let () =
  assert (eq (apps [iszero; nat 5]) bfalse);
  assert (eq (apps [iszero; nat 0]) btrue);;

(* 2.10 Pairs *)
let pair = abss ["x"; "y"; "f"] (apps [Var "f"; Var "x"; Var "y"]);;
let fst = Abs("p", App(Var "p", btrue));;
let snd = Abs("p", App(Var "p", bfalse));;

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [fst; apps [pair; t; u]]) t);
  assert (eq (apps [snd; apps [pair; t; u]]) u);;


(* 2.11 Fibonacci *)

(* naive recursive implementation *)
let rec fib_naive = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib_naive (n-1) + fib_naive (n-2);;

let () = assert (fib_naive 10 = 55);;

(* fib_fun (Fn, Fn+1) returns (Fn+1, Fn+2) *)
let fib_fun f =
  let (f1, f2) = f in (f2, f1 + f2);;

(* Fibonacci: linear-time implementation *)
let fib n =
  let rec fib_aux ctr acc = match ctr with
    | 0 -> Stdlib.fst acc
    | n -> fib_aux (ctr-1) (fib_fun acc)
  in fib_aux n (0,1);;

let () = assert (fib 10 = 55);;


(* 2.12 Predecessor *)
let pred_fun =
  abss ["p"]
    (apps [pair;
          apps[snd; Var "p"];
          apps[succ; apps[snd; Var "p"]]
    ]);;

let () =
  assert (eq (apps [pred_fun; apps [pair; nat 1; nat 5]]) (apps [pair; nat 5; nat 6]));;

(* pred_fun applied n times to (p,q) outputs (q + n-1, q)
   By taking q = 0, we can deduce an expression for pred
   We take p = 0 to have the correct output for pred 0 *)
let pred =
  Abs("n", App (fst, App (App (Var "n", pred_fun), apps[pair; nat 0; nat 0])));;

let () =
  assert (eq (apps [pred; nat 11]) (nat 10));
  assert (eq (apps [pred; nat 0]) (nat 0));;

(* 2.13 Substraction *)
let sub =
  abss ["m"; "n"] (apps [Var "n"; pred; Var "m"]);;

let () =
  assert (eq (apps [sub; nat 14; nat 5]) (nat 9));;


(* 2.14 Factorial using fixpoint function *)
let rec fix f n = f (fix f) n;;
let fact_fun f n = match n with
  | 0 | 1 -> 1
  | n -> n * f (n-1);;

let fact n = fix fact_fun n;;

let () = assert (fact 5 = 120);;

(* 2.15 Y combinator *)
let fixpoint = Abs ("f", App (Abs ("x", apps[Var "f"; Var "x"; Var "x"]), Abs ("x", apps[Var "f"; Var "x"; Var "x"])));;

let _ =
  let t = Var "t" in
  (* let t = Abs("x", Var "x") in  <---  endless recursion *)
  reduction (apps [fixpoint; t]);;

(* 2.16 Factorial in lambda notation
 factorial = lambda_f. lambda_n.  (is zero n) (nat 1) (mul n (f n-1)) *)

(* DOES NOT WORK *)
let factorial_fun = abss ["f"; "n"] (apps[apps[iszero; Var "n"]; nat 1; apps[mul; Var "n"; apps[Var "f"; apps[pred; Var "n"]]]]);;
let factorial = apps[fixpoint; factorial_fun];;

(* let () = print_endline ("Factorial 3: " ^ to_string (normalize (App (factorial, nat 3))));
         print_endline (to_string (nat 3));; *)

(* --- 3. De Brujn indices --- *)

type dvar = int;;

type db =
  | DVar of dvar
  | DApp of db * db
  | DAbs of db;;

(* 3.1 Conversion
   Converts any classical lambda term [not necessarily closed]
   into its expression with De Bruijn indices *)
let of_term t =

  (* assign_value v fv var_list returns an index for the variable v
     bound variables have their corresponding index listed in var_list
     otherwise free variables can take the fv index *)
  let rec assign_value v fv = function
    | [] -> fv
    | (a,b)::q when a = v -> b
    | p::q -> assign_value v fv q
  in

  (* increments the index of all bound variables in the list *)
  let rec inc_all = function
    | [] -> []
    | (a, b)::q -> (a, b+1)::(inc_all q)
  in
  
  (* var_list contains a list of tuples matching variable names to their current De Bruijn index
     fv contains the next index we can attribute to a new free variable

     aux returns both the lambda term converted to its expression with De Brujn indices
     and the current index for new free variables which is used to propagate back results
     up the stack of recursive calls*)
  let rec aux fv var_list t = match t with
    | Var v -> begin match assign_value v fv var_list with
               | n when n = fv -> (DVar n, fv+1)
               | n -> (DVar n, fv)
               end
    | App (t1, t2) -> let (u1, fv1) = aux fv var_list t1 in
                      let (u2, fv2) = aux fv var_list t2 in
                      (DApp (u1, u2), fv1 + fv2 - fv)
    | Abs (x, t1) -> let (u1, fv1) = aux (fv+1) ((x, 0)::(inc_all var_list)) t1 in
                     (DAbs u1, fv1)
                     
  in let (result, _) = (aux 0 [] t)
     in result;;
                                   
let () =
  let t = Abs ("x", Abs ("y", App (App (Var "x", Abs ("z", Var "x")), Abs ("x", App (Var "x", Var "y"))))) in
  let t' = DAbs (DAbs (DApp (DApp (DVar 1, DAbs (DVar 2)), DAbs (DApp (DVar 0, DVar 1))))) in
  assert (of_term t = t');;

(* 3.2 Lifting *)
let rec lift n t = match t with
  | DVar v when v >= n -> DVar (v+1)
  | DVar _ -> t
  | DApp (t1, t2) -> DApp (lift n t1, lift n t2)
  | DAbs t1 -> DAbs (lift (n+1) t1);;

let () =
  let t = lift 0 (DAbs (DApp (DVar 0, DVar 1))) in
  let t' = DAbs (DApp (DVar 0, DVar 2)) in
  assert (t = t');;

(* 3.3 Unlifting *)

let unlift n = function
  | v when v > n -> (v-1)
  | v -> v;;

let () =
  assert (unlift 5 1 = 1);
  assert (unlift 5 4 = 4);
  assert (unlift 5 6 = 5);
  assert (unlift 5 9 = 8);;

(* 3.4 Substitution *)
(* Replaces variable x by term u in the term t *)
let rec sub x u t = match t with
  | DVar v when v = x -> u
  | DVar v -> DVar (unlift x v)
  | DApp (t1, t2) -> DApp (sub x u t1, sub x u t2)
  | DAbs t1 -> DAbs (sub (x+1) (lift 0 u) t1);;

(* 3.5 Normalization *)
let rec dred t = match t with
  | DVar _ -> None
  | DApp (DAbs t1, t2) -> Some (sub 0 t2 t1)
  | DApp (t1, t2) -> begin match dred t1 with
                     | None -> begin match dred t2 with
                               | None -> None
                               | Some u2 -> Some (DApp (t1, u2))
                               end
                     | Some u1 -> Some (DApp (u1, t2))
                     end
  | DAbs t1 -> match dred t1 with 
               | None -> None
               | Some u1 -> Some (DAbs u1);;

let rec dnormalize t = match dred t with
  | None -> t
  | Some t1 -> dnormalize t1;;

let () =
  let t = of_term (apps[add; nat 5; apps [mul; nat 4; nat 3]]) in
  let u = of_term (nat 17) in
  assert (dnormalize t = dnormalize u);;

