Require Import ACTL.

Set Implicit Arguments.



Inductive state := State : bool -> bool -> bool  -> state.

Inductive action := switch | brake | park.

Inductive trans : state -> action -> state -> Prop :=
| T_switchOn : trans (State false true true) switch (State true true true)
| T_switchOff : trans (State true true true) switch (State false true true)
| T_brake e b p : trans (State b e p) brake (State e (negb b) p)
| T_park e b p : trans (State b e p) park (State e b (negb p)).



Inductive var := isOn | isBraked | isParked.

Definition valuation (v : var) (s : state) : Prop :=
match s with 
| State e b p =>
    match v with 
    | isOn => is_true e 
    | isBraked => is_true b 
    | isParked => is_true p 
    end 
end.

Notation Path := (path state action trans).
Notation Form := (form action var).
Notation Formr := (formr action var).
Check Path.

Check atom.


Notation IsOn := (atom _ _ isOn).
Notation IsBraked := (atom _ _ isBraked).
Notation IsParked := (atom _ _ isParked).

Check action_.

Notation Switch := (action_ _ switch).
Notation Brake := (action_ _ brake).
Notation Park := (action_ _ park).
Check sat.

Notation "|= f " := (forall s, sat state action trans var valuation f s).


Theorem switch_restriction : 
    |=  ((¬ IsOn ∧ IsBraked ∧ IsParked) → EX [Switch] IsOn).
Proof.
    intro.
    unfold sat; intros.
    inversion_clear H.
    inversion_clear H0.
    assert (s = State false true true).
    {
        destruct s.
        simpl in *.
        destruct b, b1, b0; auto;
        try match goal with 
        | [ H : ~ is_true true |- _] => contradiction H; unfold is_true; auto 
        | [H : is_true false |- _] => inversion H
        end. 
    }
    assert (trans s switch (State true true true))  by (rewrite H0; constructor).
    Check nilp.
    pose (p := nilp state action trans s switch (State true true true) H3).
    pose (r := Run state action trans s p).
    exists r; repeat split.
    apply until_here; simpl; auto.
    unfold r, nextStateOf; simpl.
    rewrite H0; simpl.








