(* --- Type inference for a simply typed lambda-calculus --- *)

(* Type variables *)
type tvar = string

(* Term variables *)
type var = string

(* 1.1 Simple types *)         
type ty =
  | TVar of tvar
  | Arr of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
  | Nat

(* 1.2 Lambda terms *)
type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Case of tm * var * tm * var * tm
  | Left of tm * ty
  | Right of ty * tm
  | Unit
  | Absurd of tm * ty
  | Zero
  | Succ of tm
  | Rec of tm * tm * tm

(* 1.3 String representation *)
let rec string_of_ty t = match t with
  | TVar v -> v
  | Arr (t1, t2) -> "(" ^ (string_of_ty t1) ^ " => " ^ (string_of_ty t2) ^ ")"
  | And (t1, t2) -> "(" ^ (string_of_ty t1) ^ " /\\ " ^ (string_of_ty t2) ^ ")"
  | Or (t1, t2) -> "(" ^ (string_of_ty t1) ^ " \\/ " ^ (string_of_ty t2) ^ ")"
  | True -> "T"
  | False -> "_"
  | Nat -> "Nat";;

let _ =
  print_endline (string_of_ty (Arr (Arr (TVar "A", TVar "B"), Arr (TVar "A", TVar "C"))));;

let rec string_of_tm t = match t with
  | Var v -> v
  | App (t1, t2) -> "(" ^ (string_of_tm t1) ^ " " ^ (string_of_tm t2) ^ ")"
  | Abs (x, a, t1) ->
     "(fun (" ^ x ^ ": " ^ (string_of_ty a) ^ ") -> " ^ (string_of_tm t1) ^ ")"
  | Pair (t1, t2) -> "<" ^ (string_of_tm t1) ^ ", " ^ (string_of_tm t2) ^ ">"
  | Fst t1 -> "(fst " ^ (string_of_tm t1) ^ ")"
  | Snd t1 -> "(snd " ^ (string_of_tm t1) ^ ")"
  | Case (t, x, u, y, v) -> "(case " ^ (string_of_tm t) ^ " of " ^ x ^ " -> " ^ (string_of_tm u) ^ " | " ^ y ^ " -> " ^ (string_of_tm v) ^ ")"
  | Left (trm, typ) -> "left(" ^ (string_of_tm trm) ^ ", " ^ (string_of_ty typ) ^ ")"
  | Right (typ, trm) -> "right(" ^ (string_of_ty typ) ^ ", " ^ (string_of_tm trm) ^ ")"                     
  | Unit -> "()"
  | Absurd (t,a) -> "absurd(" ^ (string_of_tm t) ^ ", " ^ (string_of_ty a) ^ ")"
  | Zero -> "Z"
  | Succ n -> "S(" ^ (string_of_tm n) ^ ")"
  | Rec (n, z, s) -> "rec(" ^ (string_of_tm n) ^ ", " ^ (string_of_tm z) ^ ", " ^ (string_of_tm s) ^ ")";;

let _ =
  print_endline (
      string_of_tm (
          Abs ("f", Arr (TVar "A", TVar "B"),
               Abs ("x", TVar "A", App (Var "f", Var "x")))));;

(* 1.4 Type inference *)
type context = (string * ty) list

exception Type_error

let rec infer_type env t = match t with
  | Var v -> (try List.assoc v env
             with Not_found -> raise Type_error)
  | App (t1, t2) -> (match infer_type env t1 with
                    | Arr (a, b) -> (if infer_type env t2 = a then b
                                     else raise Type_error)
                    | _ -> raise Type_error)
  | Abs (x, a, t2) -> Arr (a, infer_type ((x,a)::env) t2)
  | Pair (t1, t2) -> And (infer_type env t1, infer_type env t2)
  | Fst t1 -> (match infer_type env t1 with
                 | And (a, b) -> a
                 | _ -> raise Type_error)
  | Snd t1 -> (match infer_type env t1 with
                 | And (a, b) -> b
                 | _ -> raise Type_error)
  | Case (t, x, u, y, v) ->
     (match infer_type env t with
      | Or (l, r) ->
         (match (infer_type ((x,l)::env) u, infer_type ((y,r)::env) v) with
          | (t1, t2) when t1 = t2 -> t1
          | _ -> raise Type_error)
      | _ -> raise Type_error)
  | Left (trm, typ) -> Or (infer_type env trm, typ)
  | Right (typ, trm) -> Or (typ, infer_type env trm)
  | Unit -> True
  | Absurd (t, a) -> (match infer_type env t with
                      | False -> a
                      | _ -> raise Type_error)
  | Zero -> Nat
  | Succ n -> (match infer_type env n with
               | Nat -> Nat
               | _ -> raise Type_error)
  | Rec (n, z, s) ->
     (match ((infer_type env n), (infer_type env z), (infer_type env s)) with
      | (Nat, t1, Arr(Arr(Nat, t2), t3)) 
      | (Nat, t1, Arr(Nat, Arr(t2, t3))) when t1 = t2 && t2 = t3 -> t1
      | _ -> raise Type_error);;

let _ =
  let term = Abs("f", Arr(TVar "A", TVar "B"),
                 Abs("g", Arr(TVar "B", TVar "C"),
                     Abs("x", TVar "A",
                         App(Var "g", App(Var "f", Var "x"))))) in
  print_endline ("Term: " ^ (string_of_tm term));
  print_endline ("Type: " ^ (string_of_ty (infer_type [] term)));;

let _ =
  let t1 = Abs("f", TVar "A", Var "x") in
  let t2 = Abs("f", TVar "A", Abs("x", TVar "B", App (Var "f", Var "x"))) in
  let t3 = Abs("f", Arr(TVar "A", TVar "B"), Abs("x", TVar "B", App(Var "f", Var "x"))) in
  let _ = try (let _ = infer_type [] t1 in ())
          with Type_error ->
            print_endline ("Type inference of t1: " ^ (string_of_tm t1) ^ " fails = OK") in
  let _ = try (let _ = infer_type [] t2 in ())
          with Type_error ->
            print_endline ("Type inference of t2: " ^ (string_of_tm t2) ^ " fails = OK") in
  let _ = try (let _ = infer_type [] t3 in ())
          with Type_error ->
            print_endline ("Type inference of t3: " ^ (string_of_tm t3) ^ " fails = OK") in
  ();;

(* 1.5 Type checking *)
let check_type trm typ =
  try (infer_type [] trm) = typ
  with Type_error -> false;;

let _ =
  assert (check_type (Abs("x", TVar "A", Var "x")) (Arr (TVar "A", TVar "A")));
  assert (not (check_type (Abs("x", TVar "A", Var "x")) (Arr (TVar "B", TVar "B"))));
  assert (not (check_type (Var "x") (TVar "A")));;

(* 1.6 Other connectives *)

(* Most of it has already been added to the types and functions defined previously.
   Here are the tests. *)

(* 1.7 Conjunction *)
let and_comm = Abs("x", And(TVar "A", TVar "B"), Pair(Snd (Var "x"), Fst (Var "x")));;
let _ =
  print_endline (string_of_ty (infer_type [] and_comm));;

(* 1.8. Truth *)
let trivial = Abs("f", Arr(True, TVar "A"), App(Var "f", Unit));;
let _ =
  print_endline (string_of_ty (infer_type [] trivial));;

(* 1.9 Disjunction *)
let or_comm = Abs("x", Or(TVar "A", TVar "B"), Case (Var "x", "y", Right(TVar "B", Var "y"), "z", Left(Var "z", TVar "A")));;
let _ =
  (* print_endline (string_of_tm or_comm); *)
  print_endline (string_of_ty (infer_type [] or_comm));;

(* 1.10 Falsity *)
let ex_falsum_quodlibet = Abs("x", And(TVar "A", Arr(TVar "A", False)),
                              Absurd (App (Snd (Var "x"), Fst (Var "x")), TVar "B"));;
let _ =
  print_endline (string_of_ty (infer_type [] ex_falsum_quodlibet));;

let () = Printexc.record_backtrace true
       
exception Parse_error
        
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
                                                                                 
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
                                                                                                                   
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
                                                                      
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
                                                                
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_"; "Nat"; "Z"; "S"; "rec"]

          
let ty_of_tk s =
  
  let rec ty () = arr ()
                
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Arr (a, arr ()) else a
    
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then And (a, prod ()) else a
    
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Or (a, sum ()) else a
    
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> TVar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
       let a = base () in
       Arr (a, False)
    | Genlex.Kwd "Nat" -> Nat
    | _ -> raise Parse_error
         
  in
  ty ()

  
let tm_of_tk s =
  
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  
  let ty () = ty_of_tk s in
  
  let rec tm () = app ()
                
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
    
  and abs () =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, x, u, y, v)
      )
    else
      base ()
    
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Fst t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Snd t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left (t, b)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Absurd (t, a)
    | Genlex.Kwd "Z" ->
       Zero
    | Genlex.Kwd "S" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Succ t
    | Genlex.Kwd "rec" ->
       must_kwd s "(";
       let n = tm () in
       must_kwd s ",";
       let z = tm () in
       must_kwd s ",";
       let f = tm () in
       must_kwd s ")";
       Rec (n, z, f)
    | _ -> raise Parse_error
         
  in
  tm ()
  
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))

let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l;;

let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
      "Z";
      "S(S(Z))";
      "rec(S(S(Z)),Z,fun (x : Nat) -> fun (y : A) -> x y)"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l;;


(* --- 2. Interactive prover --- *)

(* 2.1 String representation of contexts *)
let string_of_ctx env =
  String.concat " ; " (List.map (fun (x,t) -> x ^ ": " ^ (string_of_ty t)) env);;

let _ =
  print_endline(string_of_ctx [ ("x", Arr(TVar "A", TVar "B"));
                                ("y", And(TVar "A", TVar "B"));
                                ("Z", True)]);;

(* 2.2 Sequents *)
type sequent = context * ty

let string_of_seq s =
  let (env, t) = s in
  (string_of_ctx env) ^ " |- " ^ (string_of_ty t);;

(* 2.3. An interactive prover *)
let rec prove env a file =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a file in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  let () = output_string file (cmd ^ " " ^ arg ^ "\n") in
  match cmd with
  | "intro" ->
     (
       match a with
       | Arr (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b file in
            Abs (x, a, t)
       (* 2.7 Conjunctions *)
       | And (a, b) ->
          let t1 = prove env a file in
          let t2 = prove env b file in
          Pair (t1, t2)
       (* 2.8 Truth *)
       | True -> Unit
       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
     
  (* 2.4 Elimination of arrows *)
  | "elim" ->
     let f = tm_of_string arg in
     (match infer_type env f with
     | Arr (f1, f2) when f2 = a ->
        let t = prove env f1 file in
        App (f, t)
     | Arr (_, _) -> error "Not the right type."
     | Or (l, r) -> let t1 = prove ((arg ^ "1", l)::env) a file in
                    let t2 = prove ((arg ^ "2", r)::env) a file in
                    Case (f, arg ^ "1", t1, arg ^ "2", t2)
     (* 2.10 Falsity *)
     | False -> Absurd (f, a)
     | _ -> error "Need to provide an argument to elim.")

  (* 2.6 Double elimination of arrows *)
  | "cut" ->
     let b = ty_of_string arg in
     let t1 = prove env (Arr (b, a)) file in
     let t2 = prove env b file in
     App (t1, t2)

  (* 2.7 Conjunctions *)
  | "fst" ->
     let p = tm_of_string arg in
     (match infer_type env p with
      | And (t1, t2) -> if t1 <> a then error "Not the right type."
                        else (Fst p)
      | _ -> error "Can only be applied to a conjunction.")
  | "snd" ->
     let p = tm_of_string arg in
     (match infer_type env p with
      | And (t1, t2) -> if t2 <> a then error "Not the right type."
                        else (Snd p)
      | _ -> error "Can only be applied to a conjunction.")
     
  (* 2.8 Disjunctions *)
  | "left" ->
     (match a with
      | Or (a,b) -> let t = prove env a file in
                    Left(t, b)
      | _ -> error "Can only be applied to a disjunction.")
  | "right" ->
     (match a with
      | Or (a,b) -> let t = prove env b file in
                    Right  (a, t)
      | _ -> error "Can only be applied to a disjunction.")
    
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  
  (* 2.5 Proofs in files *)
  let file = open_out "temp.proof" in
  let t = prove [] a file in1
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";;





