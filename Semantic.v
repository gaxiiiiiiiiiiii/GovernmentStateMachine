Require Export GSM.


Set Implicit Arguments.
Unset Strict Implicit.

Inductive form :=
    | Var : var -> form    
    | Bot : form 
    | Imp : form -> form -> form
    | AX : act -> form -> form 
    | AG : act -> form -> form 
    | EG : act -> form -> form.

Definition Not A := Imp A Bot.
Definition Top := Not Bot.
Definition Or A B := Imp (Not A) B.
Definition And A B := Not (Imp A (Not B)).
Definition EX a A := Not (AX a (Not A)).
Definition AF a A := Not (EG a (Not A)).



Inductive step (a : act) : state -> state -> Prop :=
    | here s t : trans a s t -> step a s t
    | there b s t r : trans a s t -> step b t r -> step a s r.


Fixpoint eval (e : form) (s : state) : Prop :=
    match e with 
    | Var n => valuation n s
    | Bot => False
    | Imp e1 e2 => eval e1 s -> eval e2 s
    | AX a e' => forall s', trans a s s' -> eval e' s'
    | AG a e' => forall s', step a s s' -> eval e' s'
    | EG a e' => exists s', eval e' s' /\ (forall t, step a s t -> step a t s' -> eval e' t)
    end.  


Notation "s |= e" := (eval e s)(at level 80).
Notation "⊤" := Top.
Notation "⊥" := Bot.
Notation "¬ e" := (Not e)(at level 10).
Notation "e1 ∧ e2" := (And e1 e2) (at level 30).
Notation "e1 ∨ e2" := (Or e1 e2) (at level 30).
Notation "[ a ] e" :=(AX a e)(at level 25).
Notation "< a > e" := (EX a e) (at level 25).
Notation "e1 → e2" := (Imp e1 e2) (at level 20).







