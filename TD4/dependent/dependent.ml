(* --- TD4/ 5. Dependent types --- *)

(* 5.1 Expressions *)
type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  (* forget about the constructors below at first *)
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr;;

(* 5.2 String representation *)
let rec to_string = function
  | Type -> "Type"
  | Var v -> v
  | App (t, u) -> "(" ^ (to_string t) ^ " " ^ (to_string u) ^ ")"
  | Abs (x, a, t) -> "(fun (" ^ x ^ ": " ^ (to_string a) ^ ") -> " ^ (to_string t) ^ ")"
  | Pi (x, a, b) -> "((" ^ x ^ " : " ^ (to_string a) ^ ") -> " ^ (to_string b) ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> "(S " ^ (to_string n) ^ ")"
  | Ind (p, z, s, n) -> "(Ind " ^ (to_string p) ^ " " ^ (to_string z) ^ " " ^ (to_string s) ^ " " ^ (to_string n) ^ ")"
  | Eq (t, u) -> "(Eq " ^ (to_string t) ^ " " ^ (to_string u) ^ ")"
  | Refl t -> "(Refl " ^ (to_string t) ^ ")"
  | J (p, r, x, y, e) -> "(J " ^ (to_string p) ^ " " ^ (to_string r) ^ " " ^  (to_string x) ^ " " ^ (to_string y) ^ " " ^ (to_string e) ^ ")";;

(* 5.3 Fresh variable names *)
let ctr = ref 0;;
let fresh_var () =
  ctr := !ctr + 1;
  "x" ^ (string_of_int !ctr);;

(* 5.4 Substitution *)

(* note: might be better to add check to see if a variable name
         is used by a free variable in a term *)
let rec has_fv x t = match t with
  | Var v when v = x -> true
  | Type | Z | Nat | Var _ -> false                      
  | App (t, u) -> has_fv x t || has_fv x u
  | Abs (y, a, t) -> has_fv x a || ((x<>y) && (has_fv x t))
  | Pi (y, a, b) -> has_fv x a || ((x<>y) && (has_fv x b))
  | S n -> has_fv x n
  | Ind (p, z, s, n) -> has_fv x p || has_fv x z || has_fv x s || has_fv x n
  | Eq (t, u) -> has_fv x t || has_fv x u
  | Refl t -> has_fv x t
  | J (p, r, x2, y, e) -> has_fv x p || has_fv x r || has_fv x x2 || has_fv x y || has_fv x e


let rec subst x u t = match t with
  | Var v when x = v -> u
  | App (t1, t2) -> App (subst x u t1, subst x u t2)
                  
  | Abs (y, a, t1) when x = y || has_fv y u ->
     let y2 = fresh_var () in
     let t2 = subst y (Var y2) t1 in
     Abs (y2, subst x u a, subst x u t2)
  | Abs (y, a, t) -> Abs (y, subst x u a, subst x u t)
                   
  | Pi (y, a, b) when x = y || has_fv y u -> 
     let y2 = fresh_var () in
     let b2 = subst y (Var y2) b in
     Pi (y2, subst x u a, subst x u b2)
  | Pi (y, a, b) -> Pi (y, subst x u a, subst x u b)
  | S n -> S (subst x u n)
  | Ind (p, z, s, n) -> Ind (subst x u p, subst x u z, subst x u s, subst x u n)
  | Eq (t1, t2) -> Eq (subst x u t1, subst x u t2)
  | Refl t -> Refl (subst x u t)
  | J (p, r, x2, y, e) -> J (subst x u p, subst x u r, subst x u x2, subst x u y, subst x u e)
  | _ -> t;;


(* 5.5 Contexts *)
type context = (var * (expr * expr option)) list;;

let string_of_context env =
  let format (v, (a, t)) = match t with
    | None -> v ^ " : " ^ (to_string a)
    | Some t -> v ^ " : " ^ (to_string a) ^ " = " ^ (to_string t)
  in String.concat " ; " (List.map format env);;

(* 5.6 Normalization *)
let rec normalize env = function
  | Type -> Type
  | Var v -> (try (match List.assoc v env with
                  | (_, Some t) -> normalize env t
                  | (_, None) -> Var v
                 )
              with Not_found -> Var v)
           
  | App (t, u) -> let t' = normalize env t in
                  (match t' with
                   | Abs (x, a, t) -> normalize env (subst x u t)
                   | _ -> App (t', normalize env u)
                  )
                
  | Abs (x, a, t) -> Abs (x, normalize env a, normalize ((x, (a, None))::env) t)
                     
  | Pi (x, a, b) -> Pi (x, normalize env a, normalize ((x, (a, None))::env) b)
                    
  | Nat -> Nat
  | Z -> Z
  | S n -> S (normalize env n)
  | Ind (p, z, s, n) ->
     (match normalize env n with
      | Z -> normalize env z
      | S n -> normalize env (App (App (s, n), Ind (p, z, s, n)))
      | x -> Ind (normalize env p, normalize env z, normalize env s, normalize env x)
     )
  | Eq (t, u) -> Eq (normalize env t, normalize env u)
  | Refl t -> Refl (normalize env t)
  | J (p, r, x, y, e) ->
     (match normalize env e with
      | Refl z when z = x && z = y -> App (r, x)
      | e' -> J (normalize env p, normalize env r, normalize env x, normalize env y, e')
     );;



let _ =
  assert ( (normalize [] (App (Abs ("x", Type, Var "x"), Var "y"))) = (Var "y"));;

(* 5.7 Alpha conversion *)
let rec alpha t1 t2 = match (t1, t2) with
  | Type, Type -> true
  | Var v1, Var v2 -> v1 = v2
  | App (t1, u1), App (t2, u2) -> (alpha t1 t2) && (alpha u1 u2)
  | Abs (x1, a1, t1), Abs (x2, a2, t2) ->
     (alpha a1 a2) && ( (x1 = x2) && (alpha t1 t2)
                        || (alpha t1 (subst x2 (Var x1) t2))
                        || (alpha t2 (subst x1 (Var x2) t1)) )
  | Pi (x1, a1, b1), Pi (x2, a2, b2) ->
     (alpha a1 a2) && ( (x1 = x2) && (alpha b1 b2)
                        || (alpha b1 (subst x2 (Var x1) b2))
                        || (alpha b2 (subst x1 (Var x2) b1)))
  | Nat, Nat -> true
  | Z, Z -> true
  | S n1, S n2 -> alpha n1 n2
  | Ind (p1, z1, s1, n1), Ind (p2, z2, s2, n2) ->
     alpha p1 p2 && alpha z1 z2 && alpha s1 s2 && alpha n1 n2
  | Refl t1, Refl t2 -> alpha t1 t2
  | Eq (t1, u1), Eq (t2, u2) -> alpha t1 t2 && alpha u1 u2
  | J (p1, r1, x1, y1, e1), J (p2, r2, x2, y2, e2) ->
     alpha p1 p2 && alpha r1 r2 && alpha x1 x2 && alpha y1 y2 && alpha e1 e2
  | _ -> false;;


(* 5.8 Conversion *)
let conv env t1 t2 =
  let t1' = normalize env t1 in
  let t2' = normalize env t2 in
  let _ = print_endline ("Comparing " ^ (to_string t1') ^ " and " ^ (to_string t2')) in
  alpha t1' t2';;

let _ =
  assert (conv [] (Pi ("x", Nat, Pi("y", Nat, Var "x"))) (Pi ("a", Nat, Pi ("b", Nat, Var "a"))));;

(* 5.9 Type inference *)
exception Type_error;;

let rec infer env = function
    
  (* --- Basic types --- *)
  | Type -> Type
  (* must have been defined previously *)
  | Var v -> (try fst (List.assoc v env)
              with Not_found -> raise Type_error
             )
  (* has to be the application of a function on an argument *)
  | App (t, u) -> (match infer env t with                      
                   | Pi (x, a, b) ->
                      (* u needs to be of type A *)
                      if conv env (infer env u) a then
                        subst x u b
                      else raise Type_error
                   | _ -> raise Type_error
                  )
  (* Check that A is a type and infer the type of B *)
  | Abs (x, a, t) -> if infer env a = Type then
                       let b = infer ((x, (a, None))::env) t in
                       Pi (x, a, b)
                     else raise Type_error
  | Pi (x, a, b) -> if infer env a = Type
                       && infer env b = Type
                    then Type
                    else raise Type_error
                  
  (* --- Natural numbers --- *)
  | Nat -> Type
  | Z -> Nat
  | S n -> if (infer env n) = Nat then Nat
           else raise Type_error
  (* - p is a predicate of type Nat => Type 
     - z is of type p Z 
     - s is of type Pi (n : Nat) -> (Pi (p : p n) -> p (S n))
     - n is of type Nat *)         
  | Ind (p, z, s, Z) ->
     if conv env (infer env z) (App (p, Z)) then
       infer env z
     else raise Type_error
  | Ind (p, z, s, n) ->
     (* note : the ordering ensures we do not call `conv` on any term that is not well typed *)
     if infer env n = Nat
        && conv env (infer env p) (Pi ("n", Nat, Type))
        && conv env (infer env z) (App (p, Z))
        && conv env (infer env s) (Pi ("n", Nat, Pi ("e", App (p, Var "n"), App (p, S (Var "n")))))
     then App (p, n)
     else raise Type_error

  (* --- Equality --- *)
  | Eq (_, _) -> Type
  | Refl t -> Eq (t, t)
  (* - p is of type Pi (x:A) -> Pi (y:A) -> Eq x y => Type 
     - r is of type Pi (x:A) -> p x x (Refl x)
     - x, y of type A
     - e is of type Eq (x, y)
     and returns a term of type (p x y e) *)
  | J (p, r, x, y, e) -> 
     let a = infer env x in
     if conv env (infer env y) a
        && conv env (infer env e) (Eq (x, y))
        && conv env (infer env p) (Pi ("x", a, Pi ("y", a, Pi ("e", Eq(Var "x", Var "y"), Type))))
        && conv env (infer env r) (Pi ("x", a, App(App(App(p, Var "x"), Var "x"), Refl (Var "x"))))
     then App(App(App(p, x), y), e)
     else raise Type_error
;;


(* 5.10 Type checking *)
let check env term typ =
  if not (conv env typ (infer env term)) then raise Type_error;;


(** Parsing of expressions. *)
let () = Printexc.record_backtrace true
       
exception Parse_error
        
let lexer = Genlex.make_lexer ["("; ","; ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"; "Nat"; "Z"; "S"; "Ind"; "Eq"; "Refl"; "J"]

          
let of_tk s =
  
  let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error in
  
  let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false in
  
  let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false in
  
  let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error in
  
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"] in
  
  let rec e () = abs ()
               
  and abs () =
    if peek_kwd s "Pi" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let b = e () in
        Pi (x, a, b)
      )
    else if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let t = e () in
        Abs (x, a, t)
      )
    else
      app ()
    
  and app () =
    let t = ref (arr ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
    
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else
      t
    
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
       let t = base () in
       S t
    | Genlex.Kwd "Ind" ->
       let p = base () in
       let z = base () in
       let ps = base () in
       let n = base () in
       Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
       let t = base () in
       let u = base () in
       Eq (t, u)
    | Genlex.Kwd "Refl" ->
       let t = base () in
       Refl t
    | Genlex.Kwd "J" ->
       let p = base () in
       let r = base () in
       let x = base () in
       let y = base () in
       let e = base () in
       J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
       let t = e () in
       must_kwd s ")";
       t
    | _ -> raise Parse_error
         
  in
  e ()
  
let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
         let x, sa = split ':' arg in
         let a = of_string sa in
         check !env a Type;
         env := (x,(a,None)) :: !env;
         print_endline (x^" assumed of type "^to_string a)
      | "define" ->
         let x, st = split '=' arg in
         let t = of_string st in
         let a = infer !env t in
         env := (x,(a,Some t)) :: !env;
         print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
         print_endline (string_of_context !env)
      | "type" ->
         let t = of_string arg in
         let a = infer !env t in
         print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
         let t, a = split '=' arg in
         let t = of_string t in
         let a = of_string a in
         check !env t a;
         print_endline "Ok."
      | "eval" ->
         let t = of_string arg in
         let _ = infer !env t in
         print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
 (* | e -> print_endline ("Error: "^Printexc.to_string e) *)
  done;
  print_endline "Bye."

    

