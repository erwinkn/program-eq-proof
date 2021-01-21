(* --- 1. Simple method --- *)

(* 1.1 Formulas *)
type var = int;;

type formula =
  | Var of var
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | True | False;;

(* 1.2 Substitution 
    -> Replace `x` by `b` in `a` *)
let rec subst x b a = match a with
  | Var v when v = x -> b
  | And (f1, f2) -> And (subst x b f1, subst x b f2)
  | Or (f1, f2) -> Or (subst x b f1, subst x b f2)
  | Not f -> Not (subst x b f)
  | _ -> a;;

(* 1.3 Free variables *)

(* Slight change: we return None in case we didn't find any free variable *)
let rec free_var f = match f with
  | True | False -> None
  | Var v -> Some v
  | And (f1, f2) | Or (f1, f2) ->
     begin match free_var f1 with
     | Some v -> Some v
     | None ->
        begin match free_var f2 with
        | Some v -> Some v
        | None -> None
        end
     end
  | Not f -> free_var f;;

(* 1.4 Evaluation *)

exception Not_closed;;

let rec eval f = match f with
  | True -> true
  | False -> false
  | Var _ -> raise Not_closed
  | And (f1, f2) -> (eval f1) && (eval f2)
  | Or (f1, f2) -> (eval f1) || (eval f2)
  | Not f -> not (eval f);;

(* 1.5 Satisfiability *)

let sat f = 
  let rec build_fv_list acc f = match free_var f with
    | None -> acc
    | Some v -> build_fv_list (v::acc) (subst v True f) (* the truth value doesn't matter here *)
  in
  let rec sat_aux fv_list f = match fv_list with
    | [] -> eval f
    | v::q -> (sat_aux q (subst v True f)) || (sat_aux q (subst v False f))
  in sat_aux (build_fv_list [] f) f;;

let () =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let a = And (And(Or (x,y), Or (x',y)), Or (x',y')) in
  let b = And (And(Or (x,y), Or (x',y)), And(Or (x,y'), Or (x',y'))) in
  assert (sat a);
  assert (not (sat b));;


(* --- 2. DPLL --- *)

(* type var = int *)
type literal = bool * var (* false means negated *)
type clause = literal list
type cnf = clause list;;

(* 2.1 Operations on lists *)
let rec list_mem a = function
  | [] -> false
  | p::q when p = a -> true
  | _::q -> list_mem a q;;

let rec list_map f = function
  | [] -> []
  | p::q -> (f p)::(list_map f q);;

let rec list_filter pred = function
  | [] -> [] 
  | p::q when pred p -> p::(list_filter pred q)
  | _::q -> list_filter pred q;;

let () =
  assert (list_mem 2 [1;2;3]);
  assert (not (list_mem 5 [1;2;3]));
  assert (not (list_mem 1 []));;

let () =
  assert (list_map (fun x -> 2*x) [1;2;3] = [2;4;6]);
  assert (list_map (fun _ -> ()) [] = []);;

let () =
  let even x = x mod 2 = 0 in
  assert (list_filter even [1;2;3;4;6] = [2;4;6]);;

(* 2.2 Substitution *)
(* Substitute `x` by `bval` in `c`
   The case where we remove a clause is when it contains the literal x
   and the associated boolean value in the list is equal to bval *)
let rec subst_cnf x bval cnf = match cnf with
  | [] -> []
  | c::q when list_mem (bval, x) c -> subst_cnf x bval q
  | c::q when list_mem (not bval, x) c ->
     (list_filter ((fun x (b, v) -> v <> x) x) c)::(subst_cnf x bval q)
  | c::q -> c::(subst_cnf x bval q);;

(* 2.3 Simple satisfiability *)
(* We take the first free variable we find and split 
   by substituting it with true or false *)
let rec dpll_simple cnf = match cnf with
  | [] -> true
  | l when list_mem [] l -> false
  | c::q -> (dpll_simple (subst_cnf (snd (List.hd c)) true cnf))
            || (dpll_simple (subst_cnf (snd (List.hd c)) false cnf));;

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll_simple a);
  assert (not (dpll_simple b));;

(* 2.4 Unitary clauses *)
let rec unit cnf = match cnf with
  | [] -> None
  | ([x])::q -> Some x
  | c::q -> unit q;;

let () =
  let x = true, 0 in
  let y = true, 1 in
  let y'= false,1 in
  assert (unit [[x;y]; [x]; [y;y']] = Some x);;

(* 2.5 Pure literals *)
(* In this naive version we iterate through the proposition
   by considering each literal and checking all the clauses to see if it's pure.
   If it is, return it, otherwise eliminate all occurences of that literal
   and take the next one available.
   *)
let rec pure cnf = match cnf with
  | [] -> None
  | []::q -> pure q
  | c::q -> begin let (b,v) = List.hd c in
            match list_mem true (list_map (list_mem (not b, v)) cnf) with
            | false -> Some (b, v)
            | true -> pure (list_map (list_filter (fun (b2,v2) -> v2 <> v)) cnf) end;;

let () =
  let x = true, 0 in
  let x2 = false, 0 in
  let y = true, 1 in
  let y'= false,1 in
  assert (pure [[x;y]; [x]; [y;y']] = Some x);
  assert (pure [[x;y]; [x2]; [y;y']] = None);;

(* 2.6 DPLL algorithm *)
let dpll cnf =
  let rec unit_propagate cnf = match unit cnf with
    | None -> cnf
    | Some (b,v) -> unit_propagate (subst_cnf v b cnf)
  in
  let rec pure_assign cnf = match pure cnf with
    | None -> cnf
    | Some (b,v) -> pure_assign (subst_cnf v b cnf)
  in
  let rec dpll_aux cnf = match pure_assign (unit_propagate cnf) with
    | [] -> true
    | []::_ -> false
    | c::q -> let (b,v) = List.hd c in
       (dpll_aux (subst_cnf v true cnf)) || (dpll_aux (subst_cnf v false cnf))
  in dpll_aux cnf;;

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b));;

(* 2.7 MOM heuristics *)

(* Returns a list containing only the clauses of minimal length in cnf *)
let minimal_clauses cnf =
  let rec min_length curr_min cnf = match cnf with
    | [] -> curr_min
    | c::q -> let l = List.length c in
              if l < curr_min then min_length l q
              else min_length curr_min q
  in
  let rec aux length cnf = match cnf with
    | [] -> []
    | c::q when List.length c = length -> c::(aux length q)
    | _::q -> aux length q
  in aux (min_length (List.length (List.hd cnf)) cnf) cnf;;

(* Counts the number of occurrences of each variable in the cnf *)
let rec count var_tbl cnf = match cnf with
  | [] -> ()
  | []::q -> count var_tbl q
  | (hd::tl)::q -> begin let (b,v) = hd in
            try Hashtbl.replace var_tbl v (Hashtbl.find var_tbl v + 1)
            with Not_found -> Hashtbl.add var_tbl v 1;
            count var_tbl (tl::q)
                   end;;

(* For each variable, we have its number of occurrences in the clauses
   of minimal length. We just need to iterate on the variables to find
   the one with the maximal nb of occurrences. *)
let mom cnf =
  let cnf2 = minimal_clauses cnf in
  let var_tbl = Hashtbl.create (2 * (List.length cnf2)) in
  let _ = count var_tbl cnf2 in
  let f = fun key bind acc ->
    begin let (var, count) = acc in if bind > count then (key, bind) else acc end in
  fst (Hashtbl.fold f var_tbl (0, 0));;

(* DPLL using MOM heuristics for variable selection *)
let dpll_mom cnf =
  let rec unit_propagate cnf = match unit cnf with
    | None -> cnf
    | Some (b,v) -> unit_propagate (subst_cnf v b cnf)
  in
  let rec pure_assign cnf = match pure cnf with
    | None -> cnf
    | Some (b,v) -> pure_assign (subst_cnf v b cnf)
  in
  let rec dpll_aux cnf = match pure_assign (unit_propagate cnf) with
    | [] -> true
    | []::_ -> false
    | _ -> let v = mom cnf in
       (dpll_aux (subst_cnf v true cnf)) || (dpll_aux (subst_cnf v false cnf))
  in dpll_aux cnf;;

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll_mom a);
  assert (not (dpll_mom b));;


(* --- 3. Testing ---- *)

(* 3.1 CNF files *)
let parse f : cnf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c"::_ | "p"::_ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a,c) = function
    | "" -> (a,c)
    | "0" -> (c::a,[])
    | n ->
       let n = int_of_string n in
       let x = if n < 0 then (false,-n) else (true,n) in
       (a,x::c)
  in
  fst (List.fold_left aux ([],[]) f)

(* let () =
  (* print_endline Sys.argv.(1);
     assert (dpll (parse Sys.argv.(1)));
     print_endline ("Done solving " ^ Sys.argv.(1));; *)  
  let sat1 = "./sat/quinn.cnf" in
  let sat2 = "./sat/ii8a2.cnf" in
  (* let sat3 = "./sat/ais12.cnf" in *)
  let unsat1 = "./unsat/aim-50-1_6-no-1.cnf" in
  assert (dpll (parse sat1));
  print_endline ("Done solving " ^ sat1);
  assert (dpll (parse sat2));
  print_endline ("Done solving " ^ sat2);
  assert (not (dpll (parse unsat1)));
  print_endline ("Done confirming unsatisfiability of " ^ unsat1);;
  (* assert (dpll (parse sat3));
  print_endline ("Done solving " ^ sat3);; *)
 *)


  
(* 3.2 Sudoku solver
  
  Based on "Optimized CNF Encoding for Sudoku Puzzles" (Kwon, Jain - 2006) 
  https://www.cs.cmu.edu/~hjain/papers/sudoku-as-SAT.pdf *)
let var i j n : var =
  let i = i mod 9 in
  let j = j mod 9 in
  9*(9*i+j)+n;;

(* Modified version of List.init
   Builds the list [f low; f (low+1); ... ; f high] *)
let list_init low high f =
  let rec aux low high f acc = match low with
    | a when a > high -> acc
    | a -> aux (low+1) high f ((f low)::acc)
  in aux low high f []

(* Cell definiteness: at least one number in each cell 
   And{i in 0..8} And{j in 0..8} Or{n in 0..8} (var i j n) *)
let cell_d () =
  List.flatten( (* to flatten into a CNF *)
      list_init 0 8 (fun i ->
          list_init 0 8 (fun j ->
              list_init 0 8 (fun n -> (true, var i j n)))));;

(* Row uniqueness: each value appears once per row 
   And{i in 0..8} And{n in 0..8} And{c1 in 0..7} And{c2 in c1..8}
   (not (var i c1 n)) OR (not (var i c2 n)) *)
let row_u () =
  List.flatten
    (List.flatten
       (List.flatten
          (list_init 0 8 (fun i ->
               list_init 0 8 (fun n ->
                   list_init 0 7 (fun c1 ->
                       list_init (c1+1) 8 (fun c2 ->
                           [(false, var i c1 n) ; (false, var i c2 n)]
    )))))));;

(* Column uniqueness: each value appears once per column
   And{j in 0..8} And{n in 0..8} And{r1 in 0..7} And{r2 in c1..8}
   (not (var r1 j n)) OR (not (var r2 j n)) *)
let col_u () =
  List.flatten
    (List.flatten
       (List.flatten 
          (list_init 0 8 (fun j -> 
               list_init 0 8 (fun n ->
                   list_init 0 7 (fun r1 ->
                       list_init (r1+1) 8 (fun r2 ->
                           [(false, var r1 j n) ; (false, var r2 j n)]
    )))))));;

(* Block uniqueness: each value appears once per block 
   [not based on paper mentioned above]
   We first locate the block with `block_i` and `block_j`, 
   iterate for all possible values with `n`,
   go through the block with `r` and applying Euclidean division and modulo by 3
   and do the same for all cells after `r` in the block with help of `k`*)
let block_u () =
  List.flatten(
      List.flatten(
          List.flatten(
              List.flatten(
                  list_init 0 2 (fun block_i ->
                      list_init 0 2 (fun block_j ->
                          list_init 0 8 (fun n ->
                              list_init 0 7 (fun r ->
                                  list_init (r+1) 8 (fun k ->
                                      [(false, var (block_i * 3 + (r / 3)) (block_j * 3 + (r mod 3)) n) ;
                                       (false, var (block_i * 3 + (k / 3)) (block_j * 3 + (k mod 3)) n)]
    )))))))));;

(* Assigned values: the solution respects the game given in argument
   Simply add a unitary clause for each cell of the matrix that contains a value *)
let assigned matrix =
  let rec aux i j acc = match (i,j) with
    | (i,j) when i > 8 -> acc
    | (i,j) when j > 8 -> aux (i+1) 0 acc
    | (i,j) when matrix.(i).(j) <> 9 ->
       aux i (j+1) ( [ (true, var i j (matrix.(i).(j))) ]::acc )
    | (i,j) -> aux i (j+1) acc
  in aux 0 0 [];;

let simple_sudoku =
  [|[|9;9;7;9;8;2;4;9;9|];
    [|5;4;9;3;9;1;9;9;9|];
    [|9;1;0;9;7;9;2;9;9|];
    [|2;7;9;9;5;9;1;9;8|];
    [|9;6;9;9;9;9;9;0;9|];
    [|0;9;8;9;3;9;9;6;2|];
    [|9;9;4;9;0;9;6;2;9|];
    [|9;9;9;2;9;8;9;1;5|];
    [|9;9;5;7;1;9;0;9;9|]|];;

let medium_sudoku =
  [|[|9;1;9;7;4;3;9;9;9|];
    [|9;9;9;5;9;9;9;9;7|];
    [|9;0;9;9;9;9;9;9;8|];
    [|1;9;9;9;9;9;9;8;2|];
    [|9;6;4;2;9;7;5;1;9|];
    [|7;8;9;9;9;9;9;9;6|];
    [|3;9;9;9;9;9;9;5;9|];
    [|2;9;9;9;9;1;9;9;9|];
    [|9;9;9;6;5;0;9;3;9|]|];;

let hard_sudoku =
  [|[|9;9;9;9;4;9;8;9;9|];
    [|8;7;9;9;9;9;9;4;9|];
    [|9;3;4;6;9;9;2;9;9|];
    [|9;9;3;1;9;9;7;6;9|];
    [|9;9;9;0;9;3;9;9;9|];
    [|9;6;5;9;9;8;0;9;9|];
    [|9;9;7;9;9;0;5;2;9|];
    [|9;1;9;9;9;9;9;7;0|];
    [|9;9;6;9;2;9;9;9;9|]|];;

let sudoku pb =
  (cell_d ())@(row_u ())@(col_u ())@(block_u ())@(assigned pb);;

let _ =
  let a = sudoku simple_sudoku in
  let b = sudoku medium_sudoku in
  (* works but takes a long time 
  let c = sudoku hard_sudoku in *)
  assert (dpll a);
  assert (dpll b);;
(*  assert (dpll c);; *)

  
(* --- 4. CNF conversion --- *)
let rec cnf_aux bval f = match f with
  | Var v -> [[(bval, v)]]
  | Not f -> cnf_aux (not bval) f
           
  | And (f1, f2) ->
     if bval then  (cnf_aux true f1)@(cnf_aux true f2) 
     else cnf_aux true (Or (Not f1, Not f2))
    
  | Or (f1, f2) ->
     if not bval then cnf_aux true (And (Not f1, Not f2))
     
  (* [ [1] ; [2] ; ... ; [n] ] OR [ [n+1] ; ... ; [m] ]
   = [ [i] @ [j] ] for all i in {1, ..., n} and all j in {n+1, ..., m}
   We're assuming the two lists already are in CNF *)
     else let f1 = cnf_aux true f1 in
          let f2 = cnf_aux true f2 in
          let distrib c_list c = List.map (List.append c) c_list in
          List.concat (List.map (distrib f2) f1)
  | True -> []
  | False -> [[]];;

let _ =
  let prop = Or (Or (And (Var 1, Var 2), And (Var 3, Var 4)),
                 Or (And (Var 5, Var 6), And (Var 7, Var 8))) in
  cnf_aux true prop;; (* contains 16 = 2^4 clauses, as expected *)

