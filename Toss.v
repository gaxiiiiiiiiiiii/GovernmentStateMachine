From mathcomp Require Export all_ssreflect.


(*****************)
(* subStateの種類 *)
(*****************)

(* type of subState *)
Variant toss :=
    | global    
    | police
    | judiciary
    | military 
    | media
    | education
    | registration
    | professional
    | facilitator.

Definition toss_seq : seq toss :=
    [:: global    
    ; police
    ; judiciary
    ; military 
    ; media
    ; education
    ; registration
    ; professional
    ; facilitator ].

Definition eqt (x y : toss) : bool :=
    match x, y with 
    | global, global => true
    | police, police => true
    | judiciary, judiciary => true
    | military, military  => true
    | media, media => true
    | education, education => true
    | registration, registration => true
    | professional, professional => true
    | facilitator, facilitator => true
    | _,_ => false 
    end.

Definition picklet (x : toss) : nat :=
    match x with 
    | global => 0
    | police => 1
    | judiciary => 2
    | military  => 3
    | media => 4
    | education => 5 
    | registration => 6
    | professional => 7
    | facilitator => 8 
    end.

Definition unpicklet (n : nat) : option toss :=
    match n with 
    | 0 => Some global 
    | 1 => Some police 
    | 2 => Some judiciary 
    | 3 => Some military  
    | 4 => Some media 
    | 5 => Some education  
    | 6 => Some registration 
    | 7 => Some professional 
    | 8 => Some facilitator  
    | _ => None
    end.

Definition findt (P : pred toss) (n : nat) : option toss :=
    match (unpicklet n) with
    | None => None
    | Some t' => if P t' then Some t' else None 
    end.


Tactic Notation "mkCompEq"  :=
    refine (EqMixin (compareP _)) => x y;
    unfold decidable; decide equality; apply eq_comparable.
Notation eqMixin := Equality.mixin_of.


Definition toss_eqMixin : eqMixin toss. Proof. mkCompEq. Qed.
Canonical Structure toss_eqType := Eval hnf in EqType toss toss_eqMixin.


Definition toss_choiceMixin : Choice.mixin_of toss.
Proof.
    eapply (@Choice.Mixin toss findt).
    {   
        move => P n t.
        pose (unpicklet n) as t'.
        rewrite /findt.
        destruct n => /=.
        +   remember (P global); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P police); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P judiciary); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P military); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P media); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P education); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P registration); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P professional); destruct b => H; inversion H; subst; auto.
        +   destruct n => /=.
            remember (P facilitator); destruct b => H; inversion H; subst; auto.
        +   move => H; inversion H.
    }
    {
        move => P [t Pt].
        destruct t; 
        [exists 0|exists 1|exists 2|exists 3| exists 4
        |exists 5|exists 6|exists 7|exists 8]; rewrite /findt => //=; rewrite Pt;
        rewrite /isSome => //.
    }
    {
        move => P Q H n.
        pose (unpicklet n) as t.
        destruct n; rewrite /findt => /=.
        +   move : (H global) => ->; case (Q global) => //.
        +   destruct n.
            move : (H police) => ->; case (Q police) => //.
        +   destruct n.
            move : (H judiciary) => ->; case (Q judiciary) => //.
        +   destruct n.
            move : (H military) => ->; case (Q military) => //.
        +   destruct n.
            move : (H media) => ->; case (Q media) => //.
        +   destruct n.
            move : (H education) => ->; case (Q education) => //.
        +   destruct n.
            move : (H registration) => ->; case (Q registration) => //.
        +   destruct n.
            move : (H professional) => ->; case (Q professional) => //.
        +   destruct n => //.
            move : (H facilitator) => ->; case (Q facilitator) => //.

    }
Qed.
Canonical toss_choiceType : choiceType := Eval hnf in ChoiceType toss toss_choiceMixin.

Axiom eqtE : eqt = eq_op.

Lemma toss_enumP :  (Finite.axiom toss_seq).
Proof. case; simpl; rewrite <- eqtE => //. Qed.

Definition toss_countMixin : Countable.mixin_of toss.
Proof.
    eapply (@Countable.Mixin toss picklet unpicklet).
    case => //.
Qed.
Canonical toss_countType : countType := Eval hnf in CountType toss toss_countMixin.

        

Definition toss_finMixin := Eval hnf in FinMixin toss_enumP.
Canonical toss_finType := Eval hnf in FinType toss toss_finMixin.







