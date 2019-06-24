(*Progetto ocaml FILIPPO RENAI 530478*)

(*ide*)
type ide = string;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> 
if x = i then v 
else applyenv r x;;

(*espressione*)
type exp = 
Eint of int 
| Ebool of bool 
| Den of ide 
| Prod of exp * exp 
| Sum of exp * exp 
| Diff of exp * exp 
| Eq of exp * exp 
| Minus of exp 
| IsZero of exp 
| Or of exp * exp 
| And of exp * exp 
| Not of exp 
| Ifthenelse of exp * exp * exp  
| Let of ide * exp * exp 
| Fun of ide * exp  
| FunCall of exp * exp  
| Letrec of ide * exp * exp
(* espressioni aggiunti per il dizionario*)
| Estring of string
| Dict of mydic	(*creazione di un dizionario*)
| GetElem of exp * ide (*accedere a un elemento di un dizionario*)
| AddElem of exp * ide * exp (*aggiunta elemento ad un dizionario*)
| RmElem of exp * ide (*rimozione elemento ad un dizionario*)
| Clear of exp (*rimuovi tutti gli elementi di un dizionario*)
| ApplyOver of exp * exp (*applicare la funzione ad ogni elemento di un dizionario*)
and mydic = Empty | Item of (ide * exp) * mydic 

(*tipi esprimibili*)
type evT = 
Int of int 
| Bool of bool 
| Unbound 
| FunVal of evFun 
| RecFunVal of ide * evFun
(* tipi esprimibili aggiunti per il dizionario*)
| String of string
| Dictionary of dic
(* tipi esprimibili aggiunti per lo scope dinamico*)
|FunValD of evFunD
|RecFunValD of ide * evFunD
and dic = EmptyDic | Elem of (ide * evT) * dic
and evFun = ide * exp * evT env (*questa riga non aggiunta*)
(*Scope dinamico*)
and evFunD = ide * exp;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
"int" -> (match v with
Int(_) -> true 
|_ -> false)

| "bool" -> (match v with
Bool(_) -> true 
|_ -> false)
(*type checking aggiunti per il dizionario*)
| "Dictionary" -> (match v with
Dictionary(_) -> true 
|_ -> false)
| _ -> failwith("not a valid type");;

(*funzioni di supporto*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
then (match (x,y) with
(Int(n),Int(u)) -> Int(n*u)
| _-> failwith ("Type error"))
else failwith("Type error");;
let sum x y = if (typecheck "int" x) && (typecheck "int" y)
then (match (x,y) with
(Int(n),Int(u)) -> Int(n+u)
| _-> failwith ("Type error"))
else failwith("Type error");;
let diff x y = if (typecheck "int" x) && (typecheck "int" y)
then (match (x,y) with
(Int(n),Int(u)) -> Int(n-u)
| _-> failwith ("Type error"))
else failwith("Type error");;
let eq x y = if (typecheck "int" x) && (typecheck "int" y)
then (match (x,y) with
(Int(n),Int(u)) -> Bool(n=u)
| _-> failwith ("Type error"))
else failwith("Type error");;
let minus x = if (typecheck "int" x) 
then (match x with
Int(n) -> Int(-n)
| _-> failwith ("Type error"))
else failwith("Type error");;
let iszero x = if (typecheck "int" x)
then (match x with
Int(n) -> Bool(n=0)
| _-> failwith ("Type error"))
else failwith("Type error");;
let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
then (match (x,y) with
(Bool(b),Bool(e)) -> (Bool(b||e))
| _-> failwith ("Type error"))
else failwith("Type error");;
let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
then (match (x,y) with
(Bool(b),Bool(e)) -> Bool(b&&e)
| _-> failwith ("Type error"))
else failwith("Type error");;
let non x = if (typecheck "bool" x)
then (match x with
Bool(true)  -> Bool(false) 
| Bool(false) -> Bool(true)
| _-> failwith ("Type error"))
else failwith("Type error");;

(*aggiunta funzioni di supporto per il dizionario*)
let getelem (d:evT ) (id:ide) : evT = if(typecheck "Dictionary" d) 
then (
let rec f dE k = match dE with 
EmptyDic->failwith("element not in this Dictionary") 
| Elem((i, et), ds) -> if(i=k) then et
else f dE k
in match d with Dictionary di -> f di id )
else failwith("Type error");;

let addelem (d:evT ) (id:ide) (e:evT) : dic = if(typecheck "Dictionary" d) 
then (
let  f dE k e = match dE with 
resdic-> Elem((k,e),resdic)
in match d with Dictionary di -> f di id e)
else failwith("Type error");;

let rmelem (d:evT ) (id:ide) : dic = if(typecheck "Dictionary" d) 
then ( let rec f dE k  = match dE with 
EmptyDic->failwith("element not in this Dictionary") 
| Elem((i, et),ds) -> if(i=k) then ds
else Elem((i,et),f ds k)
in match d with 
Dictionary di -> f di id)
else failwith("Type error");;

(*funzione usata in ApplyOver usato per converire un evT in exp per usare la DunCall*)
let inExp (a : evT) = match a with
| Int q -> Eint q
| Bool q -> Ebool q
| String q -> Estring q
| _ -> failwith("evT non adatto");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
Eint n -> Int n 
| Ebool b -> Bool b 
| IsZero a -> iszero (eval a r) 
| Den i -> applyenv r i 
| Eq(a, b) -> eq (eval a r) (eval b r) 
| Prod(a, b) -> prod (eval a r) (eval b r) 
| Sum(a, b) -> sum (eval a r) (eval b r) 
| Diff(a, b) -> diff (eval a r) (eval b r) 
| Minus a -> minus (eval a r) 
| And(a, b) -> et (eval a r) (eval b r) 
| Or(a, b) -> vel (eval a r) (eval b r) 
| Not a -> non (eval a r) 
| Ifthenelse(a, b, c) -> 
(let g = (eval a r) in 
if (typecheck "bool" g)  then 
(if g = Bool(true) then (eval b r) 
else (eval c r))
else failwith ("nonboolean guard"))
| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
| Fun(i, a) -> FunVal(i, a, r) 
| FunCall(f, eArg) -> 
(let fClosure = (eval f r) in match fClosure with
FunVal(arg, fBody, fDecEnv) -> 
eval fBody (bind fDecEnv arg (eval eArg r)) 
| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
let aVal = (eval eArg r) in
let rEnv = (bind fDecEnv g fClosure) in
let aEnv = (bind rEnv arg aVal) in
eval fBody aEnv 
|_ -> failwith("non functional value")
)
| Letrec(f, funDef, letBody) -> 
(match funDef with
Fun(i, fBody) -> 
let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) 
in eval letBody r1 
| _ -> failwith("non functional def"))
(*aggiunta interprete per il dizionario*)
| Estring s -> String s
| Dict d -> let rec evalD d1 = match d1 with
Empty -> EmptyDic
| Item ((k,e),ds) -> Elem((k, eval e r), evalD ds)
in Dictionary (evalD d)
| GetElem(dic,k) -> getelem (eval dic r) k
| AddElem(dic,k,e)-> Dictionary(addelem (eval dic r) k (eval e r))
| RmElem(dic,k)-> Dictionary(rmelem (eval dic r) k)
| Clear dic -> (match (eval dic r) with 
Dictionary d -> Dictionary(EmptyDic)
|_ -> failwith("is not a dictionary"))
| ApplyOver(f,dic) -> 
let d = eval dic r in
(match d with
| Dictionary EmptyDic -> Dictionary EmptyDic 
| Dictionary(d1) ->
let rec fu d2 =
(match d2 with
EmptyDic -> EmptyDic
| Elem((k, e), ds) -> Elem(( k, eval (FunCall(f,inExp(e))) r ), fu ds)
)
in Dictionary(fu d1)
| _ -> failwith("not dictionary"));; 


(*------------------TEST---------------*)
let env0 = emptyenv Unbound;; (*ambiente vuoto*)

(*crea dizionario vuoto*)
let dic_vuoto = Dict(Empty);; 
eval dic_vuoto env0 ;; 

(*creazione di un dizionario con valorio*)
let dic = Dict(Item(("name", Estring("Giovanni")),
Item(("matricola", Eint(123456)),
Empty)));; 
eval dic env0 ;;

(*accedere a un elemento di un dizionario,con chiave presente*)
let get = GetElem(dic,"name");;
eval get env0;; 

(*aggiungere un elemento ad un dizionaro,con la sua relativa chiave*)
let add = AddElem(dic,"eta",Eint(22));;
eval add env0;;

(*eliminare un elemento dal dizionario*)
let rm = RmElem(dic,"matricola");;
eval rm env0;;
(*provo ad eliminare un elemento non presente*)
(*
let rm = RmElem(dic,"keyError");;
eval rm env0;;
*)

(*elimina tutti gli elementi di un dizionario*)
let cl = Clear(dic);;
eval cl env0;;

(*applicare la funzione ad ogni elemento di un dizionario*)
let dicA = Dict(Item(("key1", Eint(0)),
Item(("key2", Eint(1)),
Empty)));; 
let funz = Fun("y", Sum(Den "y", Eint(3)));; (*incrementa di tre l'argomento*)
let apply = ApplyOver(funz,dicA);;
eval apply env0;;
(*dizionari con elementi che non sono compatibili con la funzione*)
(*
let dicError = Dict(Item(("key1", Estring("error")),
Item(("key2", Eint(1)),
Empty)));;
let apply = ApplyOver(funz,dicError);;
eval apply env0;;
*)




(*----------------PARTE OPZIONALE------------------*)

let rec rt_eval (e : exp) (r : evT env) : evT = match e with
Eint n -> Int n 
| Ebool b -> Bool b 
| IsZero a -> iszero (rt_eval a r) 
| Den i -> applyenv r i
| Eq(a, b) -> eq (rt_eval a r) (rt_eval b r) 
| Prod(a, b) -> prod (rt_eval a r) (rt_eval b r) 
| Sum(a, b) -> sum (rt_eval a r) (rt_eval b r) 
| Diff(a, b) -> diff (rt_eval a r) (rt_eval b r) 
| Minus a -> minus (rt_eval a r) 
| And(a, b) -> et (rt_eval a r) (rt_eval b r) 
| Or(a, b) -> vel (rt_eval a r) (rt_eval b r) 
| Not a -> non (rt_eval a r) 
| Ifthenelse(a, b, c) -> 
(let g = (rt_eval a r) in 
if (typecheck "bool" g)  then 
(if g = Bool(true) then (rt_eval b r) 
else (rt_eval c r))
else failwith ("nonboolean guard"))
| Let(i, e1, e2) -> rt_eval e2 (bind r i (rt_eval e1 r))
| Fun(i, a) -> FunValD(i, a) 
| FunCall(f, eArg) -> 
(let fClosure = (rt_eval f r) in match fClosure with
FunValD(arg, fBody) -> 
rt_eval fBody (bind r arg (rt_eval eArg r)) 
| RecFunValD(g, (arg, fBody)) -> 
let aVal = (rt_eval eArg r) in
let rEnv = (bind r g fClosure) in
let aEnv = (bind rEnv arg aVal) in
rt_eval fBody aEnv 
|_ -> failwith("non functional value")
)
| Letrec(f, funDef, letBody) -> 
(match funDef with
Fun(i, fBody) -> 
let r1 = (bind r f (RecFunValD(f, (i, fBody)))) 
in rt_eval letBody r1 
| _ -> failwith("non functional def"))
(*espressioni del progetto*)
| Estring s -> String s
| Dict d -> let rec evalD d1 = match d1 with
Empty -> EmptyDic
| Item ((k,e),ds) -> Elem((k, eval e r), evalD ds)
in Dictionary (evalD d)
| GetElem(dic,k) -> getelem (rt_eval dic r) k
| AddElem(dic,k,e)-> Dictionary(addelem (rt_eval dic r) k (rt_eval e r))
| RmElem(dic,k)-> Dictionary(rmelem (rt_eval dic r) k)
| Clear dic -> (match (rt_eval dic r) with 
Dictionary d -> Dictionary(EmptyDic)
|_ -> failwith("is not a dictionary"))
| ApplyOver(f,dic) -> 
let d = rt_eval dic r in
(match d with
| Dictionary EmptyDic -> Dictionary EmptyDic 
| Dictionary(d1) ->
let rec fu d2 =
(match d2 with
EmptyDic -> EmptyDic
| Elem((k, e), ds) -> Elem(( k, rt_eval (FunCall(f,inExp(e))) r ), fu ds)
)
in Dictionary(fu d1)
| _ -> failwith("not dictionary"));; 

(*---------------TEST PARTE OPZIONALE---------------*)

let env0 = emptyenv Unbound;; (*ambiente vuoto*)

(*programma per il testing 

let n = 2;;

let g x = x+n;;

let f y = 
let n = y + 5 
in g (n*y) 

f 10;;

*)
let env0 = emptyenv Unbound;;

let funzione = Let("n",Eint 2,
Let("g",Fun("x",Sum(Den "x",Den "n")),
Let("f",
Fun("y",
Let("n",Sum(Den "y",Eint(5)),
FunCall(Den "g",Prod(Den "n",Den "y")))),
FunCall(Den "f",Eint(10)))));;

eval funzione env0;; (*scope statico -> valore atteso :152*)
rt_eval funzione env0;; (*scope dinamico -> valore atteso:165*)
