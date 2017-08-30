open Printf

(* Boolean formulas *)
type bool_formula = False | True | Atomb of string | And of bool_formula list | Or of bool_formula list | Not of bool_formula | Implies of bool_formula * bool_formula ;;

(* Symbolic accessibility relations *)
type acc_program = Assign of string * bool_formula | Set of string list  |   Test of bool_formula | Seq of acc_program list | Union of acc_program * acc_program | Inter of acc_program * acc_program | Converse of acc_program;;

(* Formulas of APAL/GAL (arbitrary public announcement logic/group announcement logic) *)
type agpal_formula = False | True | Atom of string | And of agpal_formula list | Or of agpal_formula list | Not of agpal_formula | Implies of agpal_formula * agpal_formula | Knows of acc_program * agpal_formula | Announcement of agpal_formula * agpal_formula | ArbitraryAnnouncement of agpal_formula | GroupAnnouncement of acc_program list * agpal_formula | NumberTrue of int * string list;;

(* Formulas of first-order logic. 
 Conventions: Predicate(p,x) for P(x); Existf(x,f) for forall x, f; Equalf(x,y) for (x = y)*)
type mfo_formula = Falsef | Truef |  Predicatef of string * string | Notf of mfo_formula | Andf of mfo_formula list | Orf of mfo_formula list | Impliesf of mfo_formula * mfo_formula | Equivalentf of mfo_formula * mfo_formula | Existsf of string * mfo_formula | Forallf of string * mfo_formula |  Equalf of string * string;;

(* input: a list l
   output: a list that contains the same element than in l, but each element only occuring once*)
let rec remove_duplicates l= match l with
| [] -> []
| h::t -> h::(remove_duplicates (List.filter (fun x -> x<>h) t))

(*
input: a Boolean agpal_formula f
output: a list of atoms (i.e.) atomic propositions appearing in f
*)
let extract_atoms_bool(f) =
    let rec  extract_atoms_rec(f) =
        match f with
            | Atomb(s) -> [s]
            | And(l) -> List.fold_left (fun x y -> x @ (extract_atoms_rec(y))) [] l
            | Or(l) -> List.fold_left (fun x y -> x @ (extract_atoms_rec(y))) [] l
            | Not(g) -> extract_atoms_rec(g)
            | Implies(g,h) -> (extract_atoms_rec(g))@(extract_atoms_rec(h))
            | _ -> []
    in remove_duplicates(extract_atoms_rec(f));;

(*
input: a symbolic accessibility relations p
output: a list of atoms (i.e.) atomic propositions appearing in p
*)
let extract_atoms_acc_program(p) =
    let rec extract_atoms_rec(p) =
    match p with
        | Assign(s,b) -> [s] @ extract_atoms_bool(b)
        | Set(l) -> l
        | Test(b) -> extract_atoms_bool(b)
        | Seq(l) -> List.fold_left (fun x y -> x @ (extract_atoms_rec(y))) [] l
        | Union(p1,p2) -> extract_atoms_rec(p1)@ extract_atoms_rec(p2)
        | Inter(p1,p2) -> extract_atoms_rec(p1)@ extract_atoms_rec(p2)
        | Converse(p1) -> extract_atoms_rec(p1)
    in remove_duplicates(extract_atoms_rec(p));;

(*
input: a APAL/GAL agpal_formula f
output: a list of atoms (i.e.) atomic propositions appearing in f
*)
let  extract_atoms(f) =
    let rec  extract_atoms_rec(f) =
        match f with
            | Atom(s) -> [s]
            | And(l) -> List.fold_left (fun x y -> x @ (extract_atoms_rec(y))) [] l
            | Or(l) -> List.fold_left (fun x y -> x @ (extract_atoms_rec(y))) [] l
            | Not(g) -> extract_atoms_rec(g)
            | Implies(g,h) -> (extract_atoms_rec(g))@(extract_atoms_rec(h))
            | Knows(_,g) -> extract_atoms_rec(g)
            | Announcement(g,h) -> (extract_atoms_rec(g))@(extract_atoms_rec(h))
            | ArbitraryAnnouncement(g) -> extract_atoms_rec(g)
            | GroupAnnouncement(_,g) -> extract_atoms_rec(g)
            | NumberTrue(_,l) -> l
            | _ -> []
    in remove_duplicates(extract_atoms_rec(f));;

(*
input: a Boolean agpal_formula f, a first-order variable x
output: the corresponding FO agpal_formula f(x)
*)
let rec bool_to_mfo(f,x) =
    match f with
        | Atomb(s) -> Predicatef(s,x)
        | And(l) -> Andf(List.map (fun g -> bool_to_mfo(g,x)) l)
        | Or(l) -> Orf(List.map (fun g -> bool_to_mfo(g,x)) l)
        | Not(g) -> Notf(bool_to_mfo(g,x))
        | Implies(g,h) -> Impliesf(bool_to_mfo(g,x),bool_to_mfo(h,x))
        | True -> Truef
        | False -> Falsef;;

(*
input: an integer i
output: a unique string of characters (to generate variables names later)
*)

let rec generate(i) =
  if (i < 26) then
     (String.make 1 (Char.chr (97+i)))
  else (generate(i/26))^(String.make 1 (Char.chr (97+(i mod 26))))

(* Generates names for variables *)
let generate_string(i) = "x"^generate(i);;

(* Generates names for predicates *)

let generate_string_predicate(i) = "s"^generate(i);;

(* Generates names for the counting atomic propositions *)

let generate_string_count(i,j) = "count"^generate(i)^string_of_int(j);;

(* Generates names for the atomic propositions in the muddy children problem. *)
let generate_string_muddy(i) = "m"^generate(i);;

(* Generates names for the atomic propositions in the russian cards problem. *)
let generate_string_russian(player,card) = generate(player)^generate(card);;


(*
input: a symbolic accessibility relation p, two first-order variables x, y, l_atoms ???, i???
output: the corresponding FO agpal_formula p(x,y)
*)
let rec acc_program_to_mfo(p,x,y,l_atoms,i) =
    match p with
    | Assign(s,b) -> let rec generate_program(l) = match l with | [] -> [] | hd::tl when (hd = s) -> generate_program(tl) | hd::tl -> (Equivalentf(Predicatef(hd,x),Predicatef(hd,y)))::generate_program(tl) in Andf((Equivalentf((bool_to_mfo(b,x)) , Predicatef(s,y)))::generate_program(l_atoms))
    | Set(l) -> let rec generate_program(l2) = match l2 with | [] -> [] | hd::tl when (List.mem hd l) -> generate_program(tl) | hd::tl -> (Equivalentf(Predicatef(hd,x),Predicatef(hd,y)))::generate_program(tl) in Andf(generate_program(l_atoms))
    | Test(b) -> Andf([Equalf(x,y);(bool_to_mfo(b,x))])
    | Seq(lp) -> let rec generate_seq(l,x,y,k) = match l with | [] -> failwith "acc_program_to_fo" | hd::[] -> acc_program_to_mfo(hd,x,y,l_atoms,k) | hd::tl -> let z = generate_string(k) in Existsf(z, Andf([acc_program_to_mfo(hd,x,z,l_atoms,(k+1));generate_seq(tl,z,y,(k+1))])) in generate_seq(lp,x,y,i)
    | Union(p1,p2) -> Orf([acc_program_to_mfo(p1,x,y,l_atoms,i);acc_program_to_mfo(p2,x,y,l_atoms,i)])
    | Inter(p1,p2) -> Andf([acc_program_to_mfo(p1,x,y,l_atoms,i);acc_program_to_mfo(p2,x,y,l_atoms,i)])
    | Converse(q) -> (acc_program_to_mfo(q,y,x,l_atoms,i));;


(*
input: a APAL/GAL formula f, a first-order variable x, ??
output: the corresponding FO agpal_formula
*)
let rec agpal_formula_to_mfo(f,x,s,l_atoms,i,j) =
    match f with
            | True -> (Truef,j)
            | False -> (Falsef,j)
            | Atom(s) -> (Predicatef(s,x),j)
            | And(l) -> let rec f_aux(l2,x2,s2,l_atoms,i2,j2) = match l2 with | [] -> ([],j) | hd::tl -> let (g2,j3) = agpal_formula_to_mfo(hd,x2,s2,l_atoms,i2,j2) in let (l3,j4) = f_aux(tl,x2,s2,l_atoms,i2,j3) in (g2::l3,j4) in  let (g,jj) = f_aux(l,x,s,l_atoms,i,j) in (Andf(g),jj)

            | Or(l) -> let rec f_aux(l2,x2,s2,l_atoms,i2,j2) = match l2 with | [] -> ([],j) | hd::tl -> let (g2,j3) = agpal_formula_to_mfo(hd,x2,s2,l_atoms,i2,j2) in let (l3,j4) = f_aux(tl,x2,s2,l_atoms,i2,j3) in (g2::l3,j4) in  let (g,jj) = f_aux(l,x,s,l_atoms,i,j) in (Orf(g),jj)
            | Not(g) -> let (h,j2) = agpal_formula_to_mfo(g,x,s,l_atoms,i,j) in (Notf(h),j2)
            | Implies(g,h) -> let (h1,j2) = agpal_formula_to_mfo(g,x,s,l_atoms,i,j) in
                               let (h2,j3) = agpal_formula_to_mfo(h,x,s,l_atoms,i,j2) in
(Impliesf(h1,h2),j3)
            | Knows(p,g) -> let y = generate_string(i) in let (h,j2) = agpal_formula_to_mfo(g,y,s,l_atoms,(i+1),j) in (Forallf(y, Impliesf(Andf([acc_program_to_mfo(p,x,y,l_atoms,(i+1));Predicatef(s,y)]),h)),j2)
            | ArbitraryAnnouncement(g) -> let ss = generate_string_predicate(j) in let (h,j2) = agpal_formula_to_mfo(g,x,ss,l_atoms,i,(j+1)) in let y = generate_string(i) in
                                    (Andf([Forallf(y,Impliesf(Predicatef(ss,y),Predicatef(s,y)));Predicatef(ss,x);h]),j2)

            | Announcement(g,h) -> let y = generate_string(i) in let (g2,j2) = agpal_formula_to_mfo(g,y,s,l_atoms,(i+1),j) in let ss = generate_string_predicate(j2) in let (h2,j3) = agpal_formula_to_mfo(h,x,ss,l_atoms,i,(j2+1)) in
                                    (Andf([Forallf(y,Equivalentf(Predicatef(ss,y),Andf([Predicatef(s,y);g2])));Predicatef(ss,x);h2]),j3)
            | GroupAnnouncement(l,g) -> let ss = generate_string_predicate(j) in let (h,j2) = agpal_formula_to_mfo(g,x,ss,l_atoms,i,(j+1)) in let y = generate_string(i) in

let rec f_aux(l2) = match l2 with | [] -> [] | hd::tl -> let x2 = generate_string(i) in let y = generate_string(i+1) in let z = generate_string(i+2) in (Forallf(x2,Impliesf(Forallf(y,Impliesf(acc_program_to_mfo(hd,x2,y,l_atoms,(i+3)), Existsf(z, Andf([acc_program_to_mfo(hd,z,y,l_atoms,(i+3));Predicatef(ss,z)]) )))    ,Predicatef(ss,x2))))::f_aux(tl) in

                                    (Andf([Forallf(y,Impliesf(Predicatef(ss,y),Predicatef(s,y)));Andf(f_aux(l));Predicatef(ss,x);h]),j2)
            | NumberTrue(i,l) -> let rec generate_props k l_false l_true l_rest =
                                    match k with
                                    | 0 -> [Andf((List.map (fun s -> Predicatef(s,x)) l_true)@(List.map (fun s -> Notf(Predicatef(s,x))) (l_false@l_rest)))]
                                    | _ when (List.length(l_rest) < k) -> failwith "generate_props"
                                    | _ when (List.length(l_rest) = k) -> [Andf((List.map (fun s -> Predicatef(s,x)) (l_true@l_rest))@(List.map (fun s -> Notf(Predicatef(s,x))) l_false))]
                                    | _ -> (generate_props (k-1) l_false ((List.hd(l_rest))::l_true) (List.tl(l_rest)))@(generate_props k ((List.hd(l_rest))::l_false) l_true (List.tl(l_rest)))
                                in (Orf(generate_props i [] [] l),j+1);;

(*
input: number of agents, number of muddy agents
output: a APAL/GAL formula of the situation
*)

let muddy_children_normal(nb_agents,nb_muddy) =

	let l = ref([]) in
	for i = 0 to (nb_muddy-1) do
		l := (Atom((generate_string_muddy(i))))::!l
	done;
	for i = (nb_muddy) to (nb_agents-1) do
		l := (Not(Atom((generate_string_muddy(i)))))::!l
	done;
	let ann_father = ref([]) in
	for i = 0 to (nb_agents-1) do
		ann_father := (Atom(generate_string_muddy(i)))::!ann_father
	done;
	let goal = ref([]) in
	for i = 0 to (nb_agents-1) do
		goal := (Or([Knows(Set([generate_string_muddy(i)]),Atom(generate_string_muddy(i)));Knows(Set([generate_string_muddy(i)]),Not(Atom(generate_string_muddy(i))))]))::!goal
	done;
    let ggoal = ref(Or(!goal)) in
    for i = 0 to (nb_muddy-1) do
        ggoal := Announcement(Not(Or(!goal)),!ggoal);
    done;
	l := (Announcement(Or(!ann_father), Or(!goal)))::!l;
	And(!l);;


let muddy_children_arbitrary(nb_agents,nb_muddy) =

	let l = ref([]) in
	for i = 0 to (nb_muddy-1) do
		l := (Atom((generate_string_muddy(i))))::!l
	done;
	for i = (nb_muddy) to (nb_agents-1) do
		l := (Not(Atom((generate_string_muddy(i)))))::!l
	done;
	let ann_father = ref([]) in
	for i = 0 to (nb_agents-1) do
		ann_father := (Atom(generate_string_muddy(i)))::!ann_father
	done;
	let goal = ref([]) in
	for i = 0 to (nb_agents-1) do
		goal := (Or([Knows(Set([generate_string_muddy(i)]),Atom(generate_string_muddy(i)));Knows(Set([generate_string_muddy(i)]),Not(Atom(generate_string_muddy(i))))]))::!goal
	done;
	l := (Announcement(Or(!ann_father), ArbitraryAnnouncement(And(!goal))))::!l;
	And(!l);;

let muddy_children_group(nb_agents,nb_muddy) =

	let l = ref([]) in
	for i = 0 to (nb_muddy-1) do
		l := (Atom((generate_string_muddy(i))))::!l
	done;
	for i = (nb_muddy) to (nb_agents-1) do
		l := (Not(Atom((generate_string_muddy(i)))))::!l
	done;
	let ann_father = ref([]) in
	for i = 0 to (nb_agents-1) do
		ann_father := (Atom(generate_string_muddy(i)))::!ann_father
	done;
	let goal = ref([]) in
    let l_acc_programs = ref([]) in
	for i = 0 to (nb_agents-1) do
        l_acc_programs := (Set([generate_string_muddy(i)]))::!l_acc_programs;
		goal := (Or([Knows(Set([generate_string_muddy(i)]),Atom(generate_string_muddy(i)));Knows(Set([generate_string_muddy(i)]),Not(Atom(generate_string_muddy(i))))]))::!goal
	done;
	l := (Announcement(Or(!ann_father), GroupAnnouncement(!l_acc_programs,And(!goal))))::!l;
	And(!l);;

let russian_cards_arbitrary(nb_a,nb_b,nb_c) =
    let l = ref([]) in
    for i = 0 to (nb_a-1) do
        l := (Atom(generate_string_russian(0,i)))::(Not(Atom(generate_string_russian(1,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        l := (Atom(generate_string_russian(1,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        l := (Atom(generate_string_russian(2,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(1,i))))::!l
    done;
    let ann_rules = ref([]) in
    let card_a = ref([]) in
    let card_b = ref([]) in
    let card_c = ref([]) in
    for i = 0 to (nb_a+nb_b+nb_c-1) do
       card_a := (generate_string_russian(0,i))::!card_a;
       card_b := (generate_string_russian(1,i))::!card_b;
       card_c := (generate_string_russian(2,i))::!card_c;
       ann_rules := (NumberTrue(1,[(generate_string_russian(0,i));(generate_string_russian(1,i));(generate_string_russian(2,i))]))::!ann_rules
    done;              
    ann_rules := (NumberTrue(nb_a,!card_a))::!ann_rules;
    ann_rules := (NumberTrue(nb_b,!card_b))::!ann_rules;
    ann_rules := (NumberTrue(nb_c,!card_c))::!ann_rules;
    let goal = ref([]) in
    for i = 0 to (nb_a-1) do
        goal := (Knows(Set(!card_a@ !card_c),Atom(generate_string_russian(0,i))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i)))))::!goal
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Atom(generate_string_russian(1,i))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(1,i))))::!goal
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i))))))::!goal
    done;
       l := Announcement(And(!ann_rules),ArbitraryAnnouncement(And(!goal)))::!l;
        And(!l);;

let russian_cards_group(nb_a,nb_b,nb_c) =
    let l = ref([]) in
    for i = 0 to (nb_a-1) do
        l := (Atom(generate_string_russian(0,i)))::(Not(Atom(generate_string_russian(1,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        l := (Atom(generate_string_russian(1,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        l := (Atom(generate_string_russian(2,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(1,i))))::!l
    done;
    let ann_rules = ref([]) in
    let card_a = ref([]) in
    let card_b = ref([]) in
    let card_c = ref([]) in
    for i = 0 to (nb_a+nb_b+nb_c-1) do
       card_a := (generate_string_russian(0,i))::!card_a;
       card_b := (generate_string_russian(1,i))::!card_b;
       card_c := (generate_string_russian(2,i))::!card_c;
       ann_rules := (NumberTrue(1,[(generate_string_russian(0,i));(generate_string_russian(1,i));(generate_string_russian(2,i))]))::!ann_rules
    done;              
    ann_rules := (NumberTrue(nb_a,!card_a))::!ann_rules;
    ann_rules := (NumberTrue(nb_b,!card_b))::!ann_rules;
    ann_rules := (NumberTrue(nb_c,!card_c))::!ann_rules;
    let goal = ref([]) in
    for i = 0 to (nb_a-1) do
        goal := (Knows(Set(!card_a@ !card_c),Atom(generate_string_russian(0,i))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i)))))::!goal
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Atom(generate_string_russian(1,i))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(1,i))))::!goal
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i)))))::!goal
    done;
       l := Announcement(And(!ann_rules),GroupAnnouncement([Set(!card_b@ !card_c)],GroupAnnouncement([Set(!card_a @ !card_c)],And(!goal))))::!l;
        And(!l);;

let russian_cards_group_one(nb_a,nb_b,nb_c) =
    let l = ref([]) in
    for i = 0 to (nb_a-1) do
        l := (Atom(generate_string_russian(0,i)))::(Not(Atom(generate_string_russian(1,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        l := (Atom(generate_string_russian(1,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(2,i))))::!l
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        l := (Atom(generate_string_russian(2,i)))::(Not(Atom(generate_string_russian(0,i))))::(Not(Atom(generate_string_russian(1,i))))::!l
    done;
    let ann_rules = ref([]) in
    let card_a = ref([]) in
    let card_b = ref([]) in
    let card_c = ref([]) in
    for i = 0 to (nb_a+nb_b+nb_c-1) do
       card_a := (generate_string_russian(0,i))::!card_a;
       card_b := (generate_string_russian(1,i))::!card_b;
       card_c := (generate_string_russian(2,i))::!card_c;
       ann_rules := (NumberTrue(1,[(generate_string_russian(0,i));(generate_string_russian(1,i));(generate_string_russian(2,i))]))::!ann_rules
    done;              
    ann_rules := (NumberTrue(nb_a,!card_a))::!ann_rules;
    ann_rules := (NumberTrue(nb_b,!card_b))::!ann_rules;
    ann_rules := (NumberTrue(nb_c,!card_c))::!ann_rules;
    let goal = ref([]) in
    for i = 0 to (nb_a-1) do
        goal := (Knows(Set(!card_a@ !card_c),Atom(generate_string_russian(0,i))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i)))))::!goal
    done;
    for i = nb_a to (nb_a+nb_b-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Atom(generate_string_russian(1,i))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Knows(Set(!card_a@ !card_b),Atom(generate_string_russian(1,i))))::!goal
    done;  
    for i = (nb_a+nb_b) to (nb_a+nb_b+nb_c-1) do
        goal := (Knows(Set(!card_a@ !card_c),Not(Atom(generate_string_russian(0,i)))))::(Knows(Set(!card_b@ !card_c),Not(Atom(generate_string_russian(1,i)))))::(Not(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(0,i))))))::(Knows(Set(!card_a@ !card_b),Not(Atom(generate_string_russian(1,i)))))::!goal
    done;
       l := Announcement(And(!ann_rules),GroupAnnouncement([Set(!card_b@ !card_c)],And(!goal)))::!l;
        And(!l);;

(*
input: a existential apal formula f
output: a string that represents the formula in the format of the prover tptp (TPTP) (using mfo_formula_to_tptp)
*)
let agpal_formula_to_tptp(f) =

    (*
    input: a FO formula
    output: a string that represents the F0 formula in the format of the prover tptp (TPTP)
    *)
    let rec mfo_formula_to_tptp(f) =
        match f with
        | Falsef -> "$false"
        | Truef -> "$true"
        | Predicatef(s,x) -> s^"("^String.uppercase(x)^")"
        | Notf(g) -> "(~"^(mfo_formula_to_tptp(g))^")"
        | Andf(l) -> let rec f_aux(l2) = match l2 with | [] -> failwith "f_aux" | hd::[] -> mfo_formula_to_tptp(hd) | hd::tl -> mfo_formula_to_tptp(hd)^" & "^f_aux(tl) in "("^f_aux(l)^")"
        | Orf(l) -> let rec f_aux(l2) = match l2 with | [] -> failwith "f_aux" | hd::[] -> mfo_formula_to_tptp(hd) | hd::tl -> mfo_formula_to_tptp(hd)^" | "^f_aux(tl) in "("^f_aux(l)^")"
        | Impliesf(g,h) -> "("^(mfo_formula_to_tptp(g))^" => "^(mfo_formula_to_tptp(h))^")"
        | Equivalentf(g,h) -> "("^(mfo_formula_to_tptp(g))^" <=> "^(mfo_formula_to_tptp(h))^")"
        | Equalf(x,y) -> "("^String.uppercase(x)^" = "^String.uppercase(y)^")"
        | Existsf(x,g) -> "( ?["^String.uppercase(x)^"] : "^mfo_formula_to_tptp(g)^")"
        | Forallf(x,g) -> "( !["^String.uppercase(x)^"] : "^mfo_formula_to_tptp(g)^")" in
    let l = extract_atoms(f) in
    let sol = ref("") in
    sol := !sol^"fof(fes,axiom,((";
    for i = 0 to (List.length(l)-2) do
        sol := !sol^(List.nth l i)^"(t) & ";
    done;
    sol := !sol^(List.nth l (List.length(l)-1))^"(t)))).\n" ;
     for i = 0 to (List.length(l)-1) do
        sol := !sol^"fof(funiv"^(List.nth l i)^",axiom,(![X] : (? [Y]: (("^(List.nth l i)^"(X) <=> ~"^(List.nth l i)^"(Y)) & ";
        for j = 0 to (List.length(l)-1) do
            if (i <> j) then begin
                sol := !sol^"("^(List.nth l j)^"(X) <=> "^(List.nth l j)^"(Y))";
                if ((j < (List.length(l)-2)) || ((i < (List.length(l)-1)) && (j < (List.length(l)-1)))) then begin
                    sol := !sol^" & ";
                end;
            end;
        done;
        sol := !sol^")))).\n";
    done;
    sol := !sol^"fof(fs,axiom,(![X] : s(X))).\n";
    let (hh,j) = agpal_formula_to_mfo(f,"x","s",l,0,0) in
    sol := !sol^"fof(ftoverify,axiom, (?[X]: "^(mfo_formula_to_tptp(hh))^")).\n";
    !sol;;

let () =
    match Sys.argv.(1) with
    | "muddy_normal" -> print_string (agpal_formula_to_tptp(muddy_children_normal(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)))))
    | "muddy_arbitrary" -> print_string (agpal_formula_to_tptp(muddy_children_arbitrary(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)))))
    | "muddy_group" -> print_string (agpal_formula_to_tptp(muddy_children_group(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)))))
    | "russian_arbitrary" -> print_string (agpal_formula_to_tptp(russian_cards_arbitrary(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)),int_of_string(Sys.argv.(4)))))
    | "russian_group" -> print_string (agpal_formula_to_tptp(russian_cards_group(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)),int_of_string(Sys.argv.(4)))))
    | "russian_group_one" -> print_string (agpal_formula_to_tptp(russian_cards_group_one(int_of_string(Sys.argv.(2)),int_of_string(Sys.argv.(3)),int_of_string(Sys.argv.(4)))))
    | _ -> failwith "unrecognized argument"
    ;;
