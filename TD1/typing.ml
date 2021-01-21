type prog =
  | Bool of bool
  | Int of int
  | Add of prog * prog
  | Lt of prog * prog
  | If of prog * prog * prog
  | Product of prog * prog
  | First of prog
  | Second of prog;;

let rec reduce p = match p with
  | Bool b -> None
  | Int n -> None
  | Add (Int n, Int m) -> Some (Int (n+m))
  | Add (Int n, m) -> begin match (reduce m) with
                      | Some p -> Some (Add (Int n, p))
                      | _ -> None
                      end
  | Add (n, m) ->  begin match (reduce n) with
                   | Some p -> Some (Add (p, m))
                   | _ -> None
                   end
  | Lt (Int n, Int m) -> if (n < m) then Some (Bool true)
                         else Some (Bool false)
  | Lt (Int n, m) -> begin match (reduce m) with
                     | Some p -> Some (Lt(Int n, p))
                     | _ -> None
                     end
  | Lt (n, m) -> begin match (reduce n) with
                 | Some p -> Some (Lt (p, m))
                 | _ -> None
                 end
  | If (Bool b, e1, e2) -> begin match b with
                           | true -> Some e1
                           | false -> Some e2
                           end
  | If (c, e1, e2) -> begin match reduce c with
                      | Some p -> Some (If (p, e1, e2))
                      | _ -> None
                      end
  | Product (p1, p2) -> begin match reduce p1 with
                        | None -> begin match reduce p2 with
                                  | None -> None
                                  | Some p -> Some (Product (p1, p))
                                  end
                        | Some p -> Some (Product (p, p2))
                        end
  | First p -> begin match p with
               | Product (p1, _) -> Some p1
               | _ -> None
               end
  | Second p -> begin match p with
                | Product (_, p2) -> Some p2
                | _ -> None
                end;;



let rec normalize p = match reduce p with
  | None -> p
  | Some q -> normalize q;;

let program = If(
                  Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4),
                  Bool false,
                  Int 5
                )
    in normalize program;;

type typ =
  | TBool
  | TInt
  | TProduct of typ * typ
  | TUnit;;

exception Type_error;;

let rec infer p = match p with
  | Int _ -> TInt
  | Bool _ -> TBool
  | Product (p1, p2) -> TProduct (infer p1, infer p2)
  | First p -> begin match infer p with
               | TProduct (t1, t2) -> t1
               | _ -> raise Type_error
               end
  | Second p -> begin match infer p with
                | TProduct (t1, t2) -> t2
                | _ -> raise Type_error
                end
  | Add (n, m) -> begin match (infer n, infer m) with
                 | (TInt, TInt) -> TInt
                 | _ -> raise Type_error
                 end
  | Lt (n, m) -> begin match (infer n, infer m) with
                 | (TInt, TInt) -> TBool
                 | _ -> raise Type_error
                 end
  | If (c, e1, e2) -> begin match (infer c) with
                      | TBool -> begin match (infer e1, infer e2) with
                                 | (TInt, TInt) -> TInt
                                 | (TBool, TBool) -> TBool
                                 | _ -> raise Type_error
                                 end
                      | _ -> raise Type_error
                      end


let typable p =
  try
    let _ = infer p in true
  with
  | Type_error -> false;;


let program1 = If(
                  Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4),
                  Int 4,
                  Int 5
                )
    in typable program1;;

let program2 = Add(Int 1, Bool false)
    in typable program2;;

let program3 = Product(Int 1, Bool false)
    in infer program3;;
