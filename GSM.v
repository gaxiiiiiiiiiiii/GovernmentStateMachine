From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Variable M R : finType.


Record state := mkState{
    member : {set M};
    role : {set R};
    assignment : R -> {set M};
    deliverator : R;
}.

Instance etaState : Settable state := 
    settable! mkState <member; role; assignment; deliverator>.


Inductive act  :=
    | assign : R -> M -> act
    | dismissal : R -> M -> act
    | add_mem : M -> act
    | del_mem : M -> act 
    | add_role : R -> act 
    | del_role : R -> act
    | propose : act -> act.

Variable deliverate : act -> state -> bool.


Fixpoint trans_  (a : act) (x : state)  :=
    match a with 
    | assign r m => 
        x <| assignment ::= fun f => fun r' => if r == r' then m |: f r' else f r' |>
    | dismissal r m => 
        x <| assignment ::= fun f => fun r' => if r == r' then f r' :\ m else f r' |> 
    | add_mem m => x <| member ::= fun X => m |: X|>
    | del_mem m => x <| member ::= fun X => X :\ m|>
    | add_role r => x <| role ::= fun X => r |: X|> 
    | del_role r => x <| role ::= fun X => X :\ r|>
    | propose a' => if deliverate a' x then trans_ a' x else x
    end.

Definition trans a x y := y = trans_ a x.

Inductive var :=
| existsDeliveration : var
| isAssigned : R -> M -> var
| isMember : M -> var.

Definition valuation (x : var) (s : state) : bool :=
    match x with 
    | existsDeliveration => deliverator s \in role s
    | isAssigned r m => m \in assignment s r
    | isMember m => m \in member s
    end.


Inductive form :=
    | Var : var -> form    
    | Top : form
    | Bot : form 
    | Not : form -> form 
    | And : form -> form -> form 
    | Or : form -> form -> form 
    | Imp : form -> form -> form
    | Box : act -> form -> form 
    | Dia : act -> form -> form 
    | AG : act -> form -> form 
    | EG : act -> form -> form.
    

Inductive step (a : act) : state -> state -> Prop :=
    | here s t : trans a s t -> step a s t
    | there b s t r : trans a s t -> step b t r -> step a s r.


Fixpoint eval (e : form) (s : state) : Prop :=
    match e with 
    | Var n => valuation n s
    | Top => True
    | Bot => False
    | Not e' => ~ eval e' s
    | And e1 e2 => eval e1 s /\ eval e2 s
    | Or e1 e2 => eval e1 s \/ eval e2 s
    | Imp e1 e2 => eval e1 s -> eval e2 s
    | Box a e' => forall s', trans a s s' -> eval e' s'
    | Dia a e' => exists s', trans a s s' /\ eval e' s'
    | AG a e' => forall s', step a s s' -> eval e' s'
    | EG a e' => exists s', eval e' s' /\ (forall t, step a s t -> step a t s' -> eval e' t)
    end.  


Notation "s |= e" := (eval e s)(at level 80).
Notation "⊤" := Top.
Notation "⊥" := Bot.
Notation "¬ e" := (Not e)(at level 10).
Notation "e1 ∧ e2" := (And e1 e2) (at level 30).
Notation "e1 ∨ e2" := (Or e1 e2) (at level 30).
Notation "[ a ] e" :=(Box a e)(at level 50).
Notation "< a > e" := (Dia a e) (at level 30).
Notation "e1 → e2" := (Imp e1 e2) (at level 20).


Definition AF a e := ¬ (EG a (¬ e)).

Section properties.
Variable (m : M) (r : R) (s : state).


(*
    任意の状態から任意の状態遷移を経ても、条件badを満たす状態にはならない
*)
Definition safety (bad : form) := 
    forall s a, s |= AG a (¬ bad).


(*
    任意の状態から任意の状態遷移を経ても、いずれ条件goodを満たす状態に至る
*)
Definition liveness (good : form) :=
    forall s a, s |= AF a good.


(*　
    任意の状態sにおいて、mが構成員であるならmがrに任命されている
     = mを罷免する事が出来ない
     = mが独裁的な地位についている？    
*)
Definition isDictator :=
    s |= Var (isMember m) → Var (isAssigned r m).
    

(*
    任意の状態において、罷免提案が提出された直後にも罷免が履行されない
     = 罷免提案が否決される
*)
Definition undismisalable :=   
    s |= [propose (dismissal r m)](Var (isAssigned r m)).




