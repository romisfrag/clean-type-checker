open Sexplib


(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #require "sexplib";;
  #require "oUnit";;
  #use "lambda.ml";;
*)


type name =
  | Global of string 
  | Bound of int 
  | Quote of int


type inTm =
  | Ref of string
  | Hole_inTm of int
  | Abs of name * inTm
  | Inv of exTm
  | Pi of name * inTm * inTm 
  | Star
  | Zero
  | Succ of inTm
  | Nat
  | Pair of inTm * inTm 
  | Liste of inTm 
  | Nil
  | Cons of inTm * inTm 
  | Vec of inTm * inTm
  | DNil of inTm
  | DCons of inTm * inTm 
  | What of string
  | Id of inTm * inTm * inTm
  | Refl of inTm 				 
  | Bool
  | True 
  | False	
  | Sig of name * inTm * inTm 		 
and exTm = 
  | Hole_exTm of int 
  | Etiquette of string
  | Ann of inTm * inTm 
  | BVar of int 
  | FVar of name 
  | Appl of exTm * inTm
  | Iter of inTm * inTm * inTm * inTm  
  | Trans of inTm * inTm * inTm * inTm * inTm * inTm 
  | P0 of exTm
  | P1 of exTm 
  | DFold of inTm * inTm * inTm * inTm * inTm * inTm 
  | Fold of inTm * inTm * inTm * inTm * inTm 
  | Ifte of inTm * inTm * inTm * inTm 

 
type value = 
  | VLam of name * (value -> value)
  | VNeutral of neutral 
  | VStar 
  | VPi of name * value * (value -> value)
  | VSig of name * value * (value -> value)
  | VPair of value * value
  | VNat
  | VZero
  | VSucc of value
  | VBool
  | VTrue
  | VFalse
  | VVec of value * value 
  | VDNil of value
  | VDCons of value * value 
  | VListe of value 
  | VNil
  | VCons of value * value 
  | VId of value * value * value 
  | VRefl of value 
and neutral = 
  | NEtiquette of string
  | NFree of name 
  | NApp of neutral * value 
  | NIter of value * value * value * value
  | NIfte of value * value * value * value
  | NDFold of value * value * value * value * value * value 
  | NP0 of value
  | NP1 of value
  | NFold of value * value * value * value * value
  | NTrans of value * value * value * value * value * value  

let rec parse_term env t = 
      match t with   
      | Sexp.Atom "*" -> Star
      | Sexp.Atom "zero" -> Zero
      | Sexp.Atom "N" -> Nat 
      | Sexp.Atom "B" -> Bool 
      | Sexp.Atom "true" -> True
      | Sexp.Atom "false" -> False
      | Sexp.Atom "nil" -> 
	 Nil
      | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
	 Hole_inTm (int_of_string num)	 
      | Sexp.List [Sexp.Atom "ref";Sexp.Atom name] -> 
	 Ref(name)
      | Sexp.List [Sexp.Atom "?";Sexp.Atom a] -> What a
      | Sexp.List [Sexp.Atom "succ"; n] -> 
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "id";gA;a;b] -> 
	 Id((parse_term env gA),(parse_term env a),(parse_term env b))
      | Sexp.List[Sexp.Atom "refl";a] -> 
	 Refl(parse_term env a)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
	 Abs(Global(var),(parse_term (Global(var)::env) body))
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: Lambdainvalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           (List.map (fun x -> Global(x)) vars)
           (parse_term (List.append (List.rev ((List.map (fun x -> Global(x)) vars))) env) body)      
      | Sexp.List [Sexp.Atom "->"; s ; t ] -> 
	 Pi(Global("NO"),(parse_term env s),(parse_term (Global("NO") :: env) t))
      | Sexp.List [Sexp.Atom "pi"; Sexp.Atom var ; s ; t] -> 
	 Pi(Global(var),(parse_term env s),(parse_term (Global(var)::env) t))        
      | Sexp.List [Sexp.Atom "pi";Sexp.List vars; s; t] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser pi invalide variable") vars 
	 in 
	 List.fold_right
	   (fun var b -> Pi(var,(parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) s),b))
	   (List.map (fun x -> Global(x)) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) t)
      | Sexp.List [Sexp.Atom "sig"; Sexp.Atom var ;a;b] ->
	 Sig(Global(var),(parse_term env a),(parse_term (Global(var)::env) b))
      | Sexp.List [Sexp.Atom "sig"; Sexp.List vars;a;b] ->
	 let vars = List.map (function 
			       | Sexp.Atom v -> v 
			       | _ -> failwith "Parser sig invalide variable") vars
	 in 
	 List.fold_right 
	   (fun var b -> Sig(var,(parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) a),b))
	   (List.map (fun x -> Global(x)) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env ) t)
      | Sexp.List [a;Sexp.Atom ",";b] -> 
	 Pair((parse_term env a),(parse_term env b))
      | Sexp.List [Sexp.Atom "liste";alpha] -> 
	 Liste(parse_term env alpha)
      | Sexp.List [Sexp.Atom "cons"; a; xs] -> 
	 Cons((parse_term env a),(parse_term env xs))
      | Sexp.List [Sexp.Atom "vec";alpha; n] -> 
	 Vec((parse_term env alpha),(parse_term env n))
      | Sexp.List [Sexp.Atom "dnil";alpha] -> 
	 DNil(parse_term env alpha)
      | Sexp.List [Sexp.Atom "dcons";a;xs] -> 
	 DCons((parse_term env a),(parse_term env xs))
      | _ -> Inv(parse_exTm env t)
and parse_exTm env t = 
  let rec lookup_var env n v
    = match env with
    | [] -> FVar v
    | w :: env when v = w -> BVar n
    | _ :: env -> lookup_var env (n+1) v 
  in
  match t with 
  | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
     Hole_exTm (int_of_string num)
  | Sexp.List [Sexp.Atom "p0";x] ->
     P0(parse_exTm env x)
  | Sexp.List [Sexp.Atom "p1";x] ->
     P1(parse_exTm env x)
  | Sexp.List [Sexp.Atom reference] -> 
     Etiquette(reference)      
  | Sexp.List [Sexp.Atom "iter"; p ; n ; f ; z] ->
     Iter((parse_term env p),(parse_term env n),(parse_term env f),(parse_term env z))
  | Sexp.List [Sexp.Atom ":" ;x; t] -> 
     Ann((parse_term env x),(parse_term env t))
  | Sexp.List [Sexp.Atom "dfold";alpha;p;n;xs;f;a] -> 
     DFold((parse_term env alpha),(parse_term env p),(parse_term env n),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List [Sexp.Atom "trans"; gA;p;a;b;q;x] ->
     Trans((parse_term env gA),(parse_term env p),(parse_term env a),(parse_term env b),(parse_term env q),(parse_term env x))
  | Sexp.Atom v -> lookup_var env 0 (Global(v))
  | Sexp.List [Sexp.Atom "ifte"; p;c;tHen;eLse] ->
     Ifte((parse_term env p),(parse_term env c),(parse_term env tHen),(parse_term env eLse))
  | Sexp.List [Sexp.Atom "fold";a_t;alpha;xs;f;a] -> 
     Fold((parse_term env a_t),(parse_term env alpha),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List (f::args) -> 
     List.fold_left 
       (fun x y -> Appl(x, y))
       (parse_exTm env f)
       (List.map (parse_term env) args)
  | _ -> failwith "erreur de parsing" 

let read t = parse_term [] (Sexp.of_string t)

let rec pretty_print_inTm t l = 
  match t with 
  | Ref(name) -> "(ref " ^ name ^ ")"
  | Hole_inTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Abs(Global(str),x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm x (str :: l) ^ ")"
  | Abs(_,x) -> failwith "Pretty print Abs first arg must be a global"
  | Inv (x) ->  pretty_print_exTm x l
  | Pi (Global(str),s,t) -> "(pi " ^ str ^ " " ^ pretty_print_inTm s l ^ " " ^ pretty_print_inTm t (str :: l) ^ ")"
  | Pi (_,s,t) -> failwith "Pretty print Pi first arg must be a global"
  | Sig(Global(str),a,b) -> "(sig " ^ str ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b (str :: l) ^ ")"
  | Sig(_,a,b) -> failwith "Pretty print Sig first arg must be a global"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Bool -> "B"
  | True -> "true"
  | False -> "false"
  | Pair(a,b) -> "(" ^ pretty_print_inTm a l ^ " , " ^ pretty_print_inTm b l ^ ")"
  | Liste(alpha) -> "(liste " ^ pretty_print_inTm alpha l ^ ")"
  | Nil -> "nil"
  | Cons(a,xs) -> "(cons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | Vec(alpha,n) -> "(vec " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm n l ^ ")"
  | DNil(alpha) -> "(dnil " ^ pretty_print_inTm alpha l ^ ")"
  | DCons(a,xs) -> "(dcons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | What(s)-> "(? " ^ s ^ ")"
  | Id(bA,a,b) -> "(id " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b l ^ ")"
  | Refl(a) -> "(refl " ^ pretty_print_inTm a l ^ ")"
and pretty_print_exTm t l =
  match t with 
  | Hole_exTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Ann(x,y) ->  "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | BVar(x) -> begin 
      try List.nth l x with 
	| Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong list is to short BVar de " ^ string_of_int x) 
	| _ -> List.nth l x
    end
  | Etiquette(x) -> x
  | FVar (Global x) ->  x
  | FVar (Quote x) -> string_of_int x 
  | FVar (Bound x) -> string_of_int x
  | Appl(x,y) -> "(" ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm z l ^ ")"
  | Ifte(p,c,tHen,eLse) -> "(ifte " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm c l ^ " " ^ pretty_print_inTm tHen l ^ " " ^ pretty_print_inTm eLse l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
  |  DFold(alpha,p,n,xs,f,a) -> "(dfold " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm p l ^ " " ^pretty_print_inTm n l ^ 
				 " " ^ pretty_print_inTm xs l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm a l ^ ")"
  | Trans(bA,p,a,b,q,x) -> "(trans " ^ pretty_print_inTm bA l ^ " " ^pretty_print_inTm p l ^ " " ^pretty_print_inTm a l ^ " " ^
			     pretty_print_inTm b l ^ " " ^pretty_print_inTm q l ^ " " ^pretty_print_inTm x l ^ ")"
  | Fold(bA,alpha,xs,f,a) -> "(fold " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm xs l ^ "  " ^ pretty_print_inTm f l ^ " " ^
			 pretty_print_inTm a l ^ ")"


let rec substitution_inTm t tsub var = 
  match t with 
  | Ref(name) -> Ref(name)
  | Hole_inTm(x) -> Hole_inTm x
  | Inv x -> Inv(substitution_exTm x tsub var)
  | Abs(x,y) -> Abs(x,(substitution_inTm y tsub (var+1)))
  | Star -> Star
  | Pi(v,x,y) -> Pi(v,(substitution_inTm x tsub var),(substitution_inTm y tsub (var+1)))
  (*=End *)
  | Sig(x,a,b) -> Sig(x,(substitution_inTm a tsub var),(substitution_inTm b tsub (var+1)))
  | Zero -> Zero 
  | Succ n -> Succ(substitution_inTm n tsub var)
  | Nat -> Nat
  | Bool -> Bool
  | True -> True 
  | False -> False 
  | Pair(x,y) -> Pair((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Liste(alpha) -> Liste(substitution_inTm alpha tsub var)
  | Nil -> Nil
  | Cons(a,xs) -> Cons((substitution_inTm a tsub var),(substitution_inTm xs tsub var))
  | Vec(alpha,n) -> Vec((substitution_inTm alpha tsub var),(substitution_inTm n tsub var))
  | DNil(alpha) -> DNil(substitution_inTm alpha tsub var)
  | DCons(a,xs) -> DCons((substitution_inTm a tsub var),(substitution_inTm a tsub var))
  | What(a) -> What(a)
  | Id(gA,a,b) -> Id((substitution_inTm gA tsub var),(substitution_inTm a tsub var),(substitution_inTm b tsub var))
  | Refl(a) -> Refl(substitution_inTm a tsub var)
(*=substitution_exTm *)
and substitution_exTm  t tsub var = 
  match t with 
  | Hole_exTm(x) -> Hole_exTm x
  | FVar x -> FVar x
  | BVar x when x = var -> tsub
  | BVar x -> BVar x
  | Etiquette x -> Etiquette x 
  | Appl(x,y) -> Appl((substitution_exTm x tsub var),(substitution_inTm y tsub var))
  | Ann(x,y) -> Ann((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  (*=End *)
  | Iter(p,n,f,a) -> Iter((substitution_inTm p tsub var),(substitution_inTm n tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Ifte(p,c,tHen,eLse) -> Ifte((substitution_inTm p tsub var),(substitution_inTm c tsub var),(substitution_inTm tHen tsub var),(substitution_inTm eLse tsub var))
  | P0(x) -> P0(substitution_exTm x tsub var)
  | P1(x) -> P1(substitution_exTm x tsub var)
  | DFold(alpha,p,n,xs,f,a) -> DFold((substitution_inTm alpha tsub var),(substitution_inTm p tsub var),(substitution_inTm n tsub var),
				     (substitution_inTm xs tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Trans(gA,p,a,b,q,x) -> Trans((substitution_inTm gA tsub var),(substitution_inTm p tsub var),(substitution_inTm a tsub var),
				 (substitution_inTm b tsub var),(substitution_inTm q tsub var),(substitution_inTm x tsub var))
  | Fold(gA,alpha,xs,f,a) -> Fold((substitution_inTm gA tsub var),(substitution_inTm alpha tsub var),(substitution_inTm xs tsub var),(substitution_inTm f tsub var),
			    (substitution_inTm a tsub var))


let vfree n = VNeutral(NFree n)
  
let rec big_step_eval_inTm t envi = 
  match t with 
  | Ref(name) -> failwith "big_step_eval_inTm : you can't eval a ref (maybe i will change this later and call the function on it to put all 
			   the term at this place"
  | Hole_inTm x -> failwith "Big_step_eval : You can't eval a Hole" 
  | Inv(i) -> big_step_eval_exTm i envi
  | Abs(x,y) -> VLam(x,function arg -> (big_step_eval_inTm y (arg::envi)))
  | Star -> VStar
  | Pi (v,x,y) -> 
     VPi (v,(big_step_eval_inTm x envi),
	  (function arg -> (big_step_eval_inTm y (arg :: envi))))
  | Sig (x,a,b) -> 
     VSig (x,(big_step_eval_inTm a envi),
	   (function arg -> (big_step_eval_inTm b (arg :: envi))))
  | Nat -> VNat
  | Zero -> VZero
  | Succ(n) -> VSucc(big_step_eval_inTm n envi)
  | Bool -> VBool
  | True -> VTrue 
  | False -> VFalse 
  | Vec(alpha,n) -> VVec((big_step_eval_inTm alpha envi),(big_step_eval_inTm n envi))
  | DNil(alpha) -> VDNil(big_step_eval_inTm alpha envi)
  | DCons(a,xs) -> VDCons((big_step_eval_inTm a envi),(big_step_eval_inTm xs envi))
  | Id(gA,a,b) -> VId((big_step_eval_inTm gA envi),(big_step_eval_inTm a envi),(big_step_eval_inTm b envi))
  | Refl(a) -> VRefl(big_step_eval_inTm a envi)
  | Pair(x,y) -> VPair((big_step_eval_inTm x envi),(big_step_eval_inTm y envi))
  | Liste(a) -> VListe(big_step_eval_inTm a envi)
  | Nil -> VNil
  | Cons(xs,a) -> VCons((big_step_eval_inTm xs envi),(big_step_eval_inTm a envi))
  | What(a) -> failwith "do not put a hole in a type, it make no sense"  
and vapp v = 
  match v with 
  | ((VLam (x,f)),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "must not append"   
and vitter (p,n,f,a) =
  match n,f with
  | (VZero,VLam (name,fu)) -> a
  | (VSucc(x),VLam (name,fu)) -> vapp(fu n,(vitter (p,x,f,a)))
  | _ -> VNeutral(NIter(p,n,f,a))
and vdfold(alpha,p,n,xs,f,a) = 
  match xs,f,n with
  | (VDNil(alphi),VLam (name,fu),VZero) -> a
  | (VDCons(elem,y),VLam (name,fu),VSucc(ni)) -> vapp(vapp(vapp(fu n,xs),elem),vdfold(alpha,p,ni,y,f,a))
  | _ -> VNeutral(NDFold(alpha,p,n,xs,f,a))
and vifte(p,c,tHen,eLse) = 
  match c with 
  | VTrue -> tHen 
  | VFalse -> eLse 
  | _ -> VNeutral(NIfte(p,c,tHen,eLse))
and vfold(p,alpha,xs,f,a) = 
  match xs,f with 
  | (VNil,VLam (name,fu)) -> a 
  | (VCons(elem,suite),VLam (name,fu)) -> vapp(vapp((fu elem),xs),vfold(p,alpha,suite,f,a))
  | _ -> VNeutral(NFold(p,alpha,xs,f,a))
and big_step_eval_exTm t envi = 
  match t with
  | Hole_exTm x -> failwith "you can't eval a hole"
  | Ann(x,_) -> big_step_eval_inTm x envi 
  | FVar(v) -> vfree v 
  | BVar(v) -> List.nth envi v 
  | Etiquette x -> VNeutral(NEtiquette x) 		    
  | Appl(x,y) -> vapp((big_step_eval_exTm x envi),(big_step_eval_inTm y envi))    
  | Iter(p,n,f,a) -> vitter ((big_step_eval_inTm p envi),
			     (big_step_eval_inTm n envi),
			     (big_step_eval_inTm f envi),
			     (big_step_eval_inTm a envi))
  | Ifte(p,c,tHen,eLse) -> vifte((big_step_eval_inTm p envi),
				 (big_step_eval_inTm c envi),
				 (big_step_eval_inTm tHen envi),
				 (big_step_eval_inTm eLse envi))
  | P0(p) -> let eval_p = big_step_eval_exTm p envi in
     begin 
       match eval_p with 
       | VPair(x,y) -> x
       | _ -> VNeutral(NP0(eval_p))
     end 
  | P1(p) -> let eval_p = big_step_eval_exTm p envi in
     begin 
       match eval_p with 
       | VPair(x,y) -> y
       | _ -> VNeutral(NP1(eval_p))
     end        
  | DFold(alpha,p,n,xs,f,a) -> vdfold((big_step_eval_inTm alpha envi),(big_step_eval_inTm p envi),
				      (big_step_eval_inTm n envi),(big_step_eval_inTm xs envi),
				      (big_step_eval_inTm f envi),(big_step_eval_inTm a envi))				      
  | Fold(p,alpha,xs,f,a) -> vfold((big_step_eval_inTm p envi),(big_step_eval_inTm alpha envi),(big_step_eval_inTm xs envi),
				(big_step_eval_inTm f envi),(big_step_eval_inTm a envi))
  | _ -> failwith "il manque trans" 



let boundfree i n = 
  match n with 
  | Quote k -> BVar (i - k - 1)
  | x -> FVar x



let rec value_to_inTm i v =
  match v with 
  | VLam (name,f) -> value_to_inTm (i+1) (f (vfree(Quote i)))
  | VNeutral n -> Inv(neutral_to_exTm i n)
  | VPi(var,x,f) -> 
		  Pi(var,
		     (value_to_inTm i x),
		     (value_to_inTm (i+1) (f(vfree(Quote i)))))
  | VSig(var,x,f) -> 
		   Sig(var,
		       (value_to_inTm i x),
		       (value_to_inTm (i+1) (f(vfree(Quote i)))))
  | VPair(x,y) -> Pair((value_to_inTm i x),(value_to_inTm i y))
  | VStar -> Star
  | VNat -> Nat
  | VZero -> Zero
  | VSucc(n) -> Succ(value_to_inTm i n)
  | VBool -> Bool 
  | VTrue -> True 
  | VFalse -> False 
  | VVec(alpha,n) -> Vec((value_to_inTm i alpha),(value_to_inTm i n))
  | VDNil(alpha) -> DNil(value_to_inTm i alpha)
  | VDCons(a,xs) -> DCons((value_to_inTm i a),(value_to_inTm i xs)) 
  | VId(gA,a,b) -> Id((value_to_inTm i gA),(value_to_inTm i a),(value_to_inTm i b))
  | VRefl(a) -> Refl(value_to_inTm i a) 
  | VListe(a) -> Liste(value_to_inTm i a)
  | VNil -> Nil
  | VCons(a,xs) -> Cons((value_to_inTm i a),(value_to_inTm i xs)) 
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))
  | NDFold(alpha,p,n,xs,f,a) -> DFold((value_to_inTm i alpha),(value_to_inTm i p),(value_to_inTm i n),
				      (value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))
  | NIter(p,n,f,a) -> Iter((value_to_inTm i p),(value_to_inTm i n),(value_to_inTm i f),(value_to_inTm i a))
  | NIfte(p,c,tHen,eLse) -> Ifte((value_to_inTm i p),(value_to_inTm i c),(value_to_inTm i tHen),(value_to_inTm i eLse))
  | NTrans(gA,p,a,b,q,x) -> Trans((value_to_inTm i gA),(value_to_inTm i p),(value_to_inTm i a),
				  (value_to_inTm i b),(value_to_inTm i q),(value_to_inTm i x))
(* ici il faut trouver une solution plus élégante *)
  | NP0(x) -> P0(Ann((value_to_inTm i x),Star))
  | NEtiquette x-> Etiquette x
  | NP1(x) -> P1(Ann((value_to_inTm i x),Star))
  | NFold(p,alpha,xs,f,a) -> Fold((value_to_inTm i p),(value_to_inTm i alpha),(value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))

let rec equal_inTm t1 t2 = 
  match (t1,t2) with 
  | (Abs(_,x1),Abs(_,x2)) -> equal_inTm x1 x2
  | (Pi(_,x1,y1),Pi(_,x2,y2)) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Sig(_,x1,y1),Sig(_,x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Star,Star) -> true 
  | (Zero,Zero) -> true 
  | (Succ(n1),Succ(n2)) -> equal_inTm n1 n2
  | (Nat,Nat) -> true
  | (Bool,Bool) -> true 
  | (True,True) -> true 
  | (False,False) -> true 
  | (Inv(x1),Inv(x2)) -> equal_exTm x1 x2
  | (Pair(x1,y1),Pair(x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 
  | (What(a),What(b)) -> true
  | (Vec(x1,y1),Vec(x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2
  | (DNil x1,DNil x2) -> equal_inTm x1 x2 
  | (DCons(x1,y1),DCons(x2,y2)) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Id(x1,y1,z1),Id(x2,y2,z2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2
  | (Refl(a),Refl(b)) -> equal_inTm a b 
  | (Liste(a),Liste(b))-> equal_inTm a b
  | (Nil,Nil) -> true
  | (Cons(y1,z1),Cons(y2,z2)) -> equal_inTm y1 y2 && equal_inTm z1 z2				  
  | _ -> false 
and equal_exTm t1 t2 = 
  match (t1,t2) with 
  | (Ann(x1,y1),Ann(x2,y2)) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (BVar(x1),BVar(x2)) -> x1 = x2 
  | (FVar(x1),FVar(x2)) -> x1 = x2
  | (Appl(x1,y1),Appl(x2,y2)) -> equal_exTm x1 x2 && equal_inTm y1 y2 
  | (Iter(w1,x1,y1,z1),Iter(w2,x2,y2,z2)) -> 
     equal_inTm w1 w2 && equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2 
  | (Ifte(w1,x1,y1,z1),Ifte(w2,x2,y2,z2)) -> 
     equal_inTm w1 w2 && equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2 
  | (P0(x1),P0(x2)) -> equal_exTm x1 x2
  | (P1(x1),P1(x2)) -> equal_exTm x1 x2
  | (DFold(alpha1,p1,n1,xs1,f1,a1),DFold(alpha2,p2,n2,xs2,f2,a2)) -> equal_inTm alpha1 alpha2 && equal_inTm p1 p2 
								     && equal_inTm p1 p2 && equal_inTm n1 n2 
								     && equal_inTm xs1 xs2 && equal_inTm f1 f2 
								     && equal_inTm a1 a2 
  | (Fold(p1,alpha1,xs1,f1,a1),Fold(p2,alpha2,xs2,f2,a2)) -> 
     equal_inTm p1 p2 && equal_inTm alpha1 alpha2 && equal_inTm xs1 xs2 && 
       equal_inTm f1 f2 && equal_inTm a1 a2  
  | _ -> false


let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c


type result_synth_exTm = 
  | Ret of inTm 
  | Fail

let get_ret_synth t = 
  match t with 
  | Ret(x) -> x 
  | _ -> failwith "get_ret_synth : this is not supposed to append"

let rec check contexte inT ty = 
  match inT with
  | Ref(name) -> false
  | Hole_inTm x -> false
  | Abs(x,y) -> 
     begin  
       match ty with 
       | VPi(name,s,t) -> let freshVar = gensym () in 
		     check (((Global freshVar),s)::contexte) (substitution_inTm y (FVar(Global(freshVar))) 0) (t (vfree (Global freshVar)))
       | _ -> false
     end 
  | Inv(x) -> 
     let ret = synth contexte x in
     let bool = begin match synth contexte x with Ret(x) -> true | Fail -> false end in
     if equal_inTm (value_to_inTm 0 (ty)) (get_ret_synth ret) && bool
     then true
     else false
  | Star -> 
     begin 
      match ty with 
	| VStar -> true
	| _ -> false
     end
  | Pi (v,s,t) -> 
     begin 
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  let check_s = check contexte s VStar in 
		  let check_t = check (((Global freshVar),(big_step_eval_inTm s []))::contexte) 
				      (substitution_inTm t (FVar(Global(freshVar))) 0) VStar in
		  check_s && check_t
       | _ -> false
     end 
  |Sig(v,s,t) -> 
    begin 
      match ty with 
      | VStar -> let freshVar = gensym () in 
		 let check_s = check contexte s VStar in
		 let check_t = check (((Global freshVar),(big_step_eval_inTm s []))::contexte) 
				     (substitution_inTm t (FVar(Global(freshVar))) 0) VStar in
		 check_s && check_t
      | _ -> false
    end 
  | Nat -> 
     begin 
       match ty with
       | VStar -> true
       | _ -> false
     end 
  | Zero -> 
     begin 
       match ty with 
       | VNat -> true
       | _ -> false
     end
  | Succ(x) -> 
     begin 
       match ty with 
	 | VNat -> true
	 | _ -> false
     end 
  | Bool -> 
     begin 
       match ty with 
       | VStar -> true
       | _ -> false
     end 
  | True -> 
     begin 
       match ty with 
       | VBool -> true
       | _ -> false
     end 
  | False -> 
     begin 
       match ty with 
       | VBool -> true
       | _ -> false
     end 
  | Pair(x,y) -> 
     begin
       match ty with 
       | VSig(n,a,b) -> 
	  let check_x = check contexte x a  in
	  let check_y = check contexte y (b (big_step_eval_inTm x [])) in 
	  check_x && check_y 	  
       | _ -> false
     end 
  | Vec(alpha,n) -> 
     begin        
       match ty with 
       | VStar -> let check_alpha = check contexte alpha VStar in
		  let check_n = check contexte n VNat in 
		  check_alpha && check_n
       | _ -> false
     end
  | DNil(alpha) -> 
     begin
       match ty with
       | VVec(alpha_vec,VZero) -> equal_inTm (value_to_inTm 0 (big_step_eval_inTm alpha [])) 
					     (value_to_inTm 0 alpha_vec)
       | _ -> false
     end 
  | DCons(a,xs) -> 
     begin 
       match ty with 
       | VVec(alpha,VSucc(n)) -> let check_xs = check contexte xs (VVec(alpha,n)) in 
				 let check_a = check contexte a alpha in
				 check_xs && check_a
       | _ -> false
     end
  | What(a) -> true
  | Id(gA,a,b) -> let check_gA = check contexte gA VStar in 		  
		  let eval_gA = big_step_eval_inTm gA [] in 
		  let check_a = check contexte a eval_gA in 
		  let check_b = check contexte b eval_gA in 
		  check_gA && check_a && check_b
  | Refl(a) -> 
     begin
       match ty with 
       | VId(gA,ta,ba) -> let quote_ta = value_to_inTm 0 ta in 
			  let quote_ba = value_to_inTm 0 ba in
			  let check_gA = check contexte a gA in
			  equal_inTm a quote_ta && equal_inTm a quote_ba && check_gA
       | _ -> false
     end
  | Liste(alpha) -> 
     begin 
       match ty with 
       | VStar -> let check_alpha = check contexte alpha VStar in
		  check_alpha
       | _ -> false
     end
  | Nil -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> true
       | _ -> false
     end
  | Cons(a,xs) -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> let check_a = check contexte a alpha_liste in
				let check_xs = check contexte xs (VListe(alpha_liste)) in
				check_a && check_xs
       | _ -> false
     end 
and synth contexte exT =
  match exT with 
  | Hole_exTm x -> Fail
  | BVar x -> Fail
  | FVar x -> let typ = value_to_inTm 0 (List.assoc x contexte) in Ret(typ)
(*=End *)
  | Etiquette x -> Fail
  | P0(x) -> let synth_x = synth contexte x in 
	     begin
	       match synth_x with 
	       | Ret(x) -> begin
		   match big_step_eval_inTm x [] with 
		   | VSig(n,a,b) -> Ret(value_to_inTm 0 a) 
		   | _ -> Fail
		 end
	       | Fail -> Fail
	     end
  | P1(x) -> let synth_x = synth contexte x in 
	     begin
	       match synth_x with 
	       | Ret(r) -> begin
		   match big_step_eval_inTm r [] with 
		   | VSig(n,a,b) -> Ret(value_to_inTm 0 (b (big_step_eval_exTm (P0(x)) [])))
		   | _ -> Fail
		 end
	       | Fail -> Fail
	     end
  | Ann(x,t) -> let ret = check contexte t VStar in 
		let eval_t = big_step_eval_inTm t [] in
		let check_x = check contexte x eval_t in
		if ret && check_x then Ret(value_to_inTm 0 eval_t) else Fail
  | Appl(f,s) -> 
     let synth_f = synth contexte f in 
     begin 
       match synth_f with 
       | Ret(x) -> 
	  begin 
	    match big_step_eval_inTm x [] with 
	    | VPi(name,s_pi,fu) -> if check contexte s s_pi then Ret(value_to_inTm 0 (fu(big_step_eval_inTm s []))) else Fail
	    | _ -> Fail				   
	  end
       | Fail -> Fail 
     end
  | Iter(p,n,f,a) -> let big_p = big_step_eval_inTm p [] in
		     let big_n = big_step_eval_inTm n [] in 
		     let type_p = read "(pi x N *)" in 		     
 		     let check_p = check contexte p (big_step_eval_inTm type_p [])  in    
		     let check_n = check contexte n (big_step_eval_inTm (read "N") [])  in
		     let type_f = (Pi(Global("n"),Nat,Pi(Global("NO"),(Inv(Appl(Ann(p,type_p),Inv(BVar 0)))),(Inv(Appl(Ann(p,type_p),Succ(Inv(BVar 1)))))))) in 
		     let check_f = check contexte f (big_step_eval_inTm type_f []) in
		     let check_a = check contexte a (vapp(big_p,VZero))  in
		     if check_n && check_p && check_f && check_a then Ret(value_to_inTm 0 (vapp(big_p,big_n))) else Fail
  | Ifte(p,c,tHen,eLse) -> 
     let big_p = big_step_eval_inTm p [] in
     let big_c = big_step_eval_inTm c [] in 
     let check_p = check contexte p (big_step_eval_inTm (read "(-> B *)") []) in    
     let check_c = check contexte c (big_step_eval_inTm (read "B") []) in
     let check_tHen = check contexte tHen (vapp(big_p,VTrue)) in
     let check_eLse = check contexte eLse (vapp(big_p,VFalse)) in
     if check_p && check_c && check_tHen && check_eLse then Ret(value_to_inTm 0 (vapp(big_p,big_c))) else Fail
  | DFold(alpha,p,n,xs,f,a) -> let check_alpha = check contexte alpha VStar in
			       let type_p = (Pi(Global"n",Nat,(Pi(Global"xs",Vec(alpha,Inv(BVar 0)),Star)))) in 
			       let check_p = check contexte p (big_step_eval_inTm type_p []) in
			       let check_n = check contexte n VNat in			       
 			       let check_xs = check contexte xs (big_step_eval_inTm (Vec(alpha,n)) []) in 
  			       let check_f = check contexte f 
						   (big_step_eval_inTm 
						      (Pi(Global"n",Nat,
							  Pi(Global"xs",Vec(alpha,Inv(BVar 0)),
							     Pi(Global"a",alpha,
								Pi(Global"NO",Inv(Appl(Appl(Ann(p,type_p),n),xs)),
								   Inv(Appl(Appl(Ann(p,type_p),Succ(n)),DCons(a,xs)))))))) []) in 
			       let check_a = check contexte a (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),Zero),DNil(alpha)))) []) in 
			       let ret = big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),n),xs))) [] in
			       if check_alpha && check_p && check_n && check_xs && check_f && check_a 
			       then Ret(value_to_inTm 0 (ret))
			       else Fail
  | Trans(gA,p,a,b,q,x) -> let check_gA = check contexte gA VStar in
			   let check_a = check contexte a (big_step_eval_inTm gA []) in
			   let check_b = check contexte b (big_step_eval_inTm gA []) in
			   let check_q = check contexte q (big_step_eval_inTm (Id(gA,a,b)) [])in
			   let type_p = Pi(Global"a",gA,Pi(Global"b",gA,Pi(Global"NO",Id(gA,Inv(BVar 1),Inv(BVar 0)),Star))) in 
			   let check_p = check contexte p (big_step_eval_inTm type_p []) in
			   let check_x = check contexte x (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) []) in
			   let ret = (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) []) in
			   if check_gA && check_a && check_b && check_q && check_x && check_p
			   then Ret(value_to_inTm 0 (ret))
			   else Fail
  | Fold(p,alpha,xs,f,a) -> 
     let check_alpha = check contexte alpha VStar in 
     let type_p = Pi(Global"xs",Liste(alpha),Star) in 
     let check_p = check contexte p (big_step_eval_inTm type_p []) in 
     let check_xs = check contexte xs (big_step_eval_inTm (Liste(alpha)) []) in 
     let type_f = (Pi(Global"a",alpha,
		      Pi(Global"xs",Liste(alpha),			 
			 Pi(Global"NO",Inv(Appl(Ann(p,type_p),Liste(alpha))),
			    Inv(Appl(Ann(p,type_p),Cons(Inv(BVar 2),Inv(BVar 1)))))))) in		    
     let check_f = check contexte f (big_step_eval_inTm (type_f) []) in 
     let check_a = check contexte a (big_step_eval_inTm alpha []) in 
     let ret = (big_step_eval_inTm (Inv(Appl(Ann(p,type_p),xs))) []) in
     if check_alpha && check_p && check_f && check_a && check_xs
     then Ret(value_to_inTm 0 (ret))
     else Fail





