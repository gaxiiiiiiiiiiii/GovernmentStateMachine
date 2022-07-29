Require Import ACTL.

Set Implicit Arguments.

Require Import Coq.Setoids.Setoid.



Inductive state := State : bool -> bool -> bool  -> state.

Inductive action := switch | brake | park | tau | isOn | isBraked | isParked.


Inductive trans : state -> action -> state -> Prop :=
    | Tr_SwitchOk e : trans (State e true true) switch (State (negb e) true true)
    | Tr_SwitchNG e b p : andb b p = false -> trans (State e b p) switch (State e b p)
    | Tr_Brake e b p : trans (State e b p) brake (State e (negb b) p)
    | Tr_Park e b p : trans (State e b p) park (State e b (negb p))
    | Tr_IsOn b p : trans (State true b p) isOn (State true b p)
    | Tr_IsBraked e p : trans (State e true p) isBraked (State e true p)
    | Tr_IsParked e b : trans (State e b true) isParked (State e b true)
    | Tr_tau s: trans s tau s.

Theorem tau_eq s s' : trans s tau s' <->  s = s'.
Proof.
    split; intro H.
    +   inversion H; subst; auto.
    +   subst; constructor.
Qed.       

Notation "s |= f" := (@sat state action trans f s)(at level 80).
Notation "|= f" := (forall s, s |= f)(at level 80).
Notation τ := (action_ tau).
Notation "< chi > f" := (E (⊤ [τ] U [chi] f))(at level 50, chi at level 5).
Notation "[ chi ] f" := (¬ <chi> ¬ f)(at level 50, chi at level 5).
Notation "'EX' f" := (<any> f)(at level 50).
Notation "'AX' f" := ([any] f)(at level 50).
Notation "'EF' f" := (f ∨ EF [any] f)(at level 50).
Notation "'AF' f" := (f ∨ AF [any] f)(at level 50).
Notation "'EG' f" := (¬ AF ¬ f)(at level 50).
Notation "'AG' f" := (¬ EF ¬ f)(at level 50).

Notation "f 'EU' f'" := (E (f U f'))(at level 50).


Notation Path := (@path state action trans).
Notation Form := (@form action).
Notation Formr := (@formr action).




Notation IsOn := (< (action_ isOn) > ⊤).
Notation IsBraked := (<(action_ isBraked)> ⊤).
Notation IsParked := (<(action_ isParked)> ⊤).

Notation Switch := (action_ switch).
Notation Brake := (action_ brake).
Notation Park := (action_ park).

Ltac  satisfy := unfold sat; fold (sat (trans := trans)).

Definition engineState s :=
    match s with 
    | State b _ _ => b 
    end.

Definition brakeState s :=
    match s with 
    | State _ b _ => b 
    end.

Definition parkState s := 
    match s with 
    | State _ _ b => b
    end.


Theorem IsOn_spec s :
    s |= IsOn <-> engineState s = true.
Proof.
    destruct s; simpl; split; satisfy; intro H.
    +   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; auto; subst.
        -   destruct r,p; simpl in *; subst; inversion t; auto.
        -   apply IHHU; symmetry; apply tau_eq; auto.
    +   subst.
        remember (State true b0 b1).
        assert (trans s isOn s) by (subst; constructor).
        exists (Run s (nilp s isOn s H)); repeat split.
        constructor; unfold sata; auto.
Qed.   

Theorem IsBraked_spec s :
    s |= IsBraked <-> brakeState s = true.
Proof.
    destruct s; simpl; split; satisfy; intro H.
    +   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; auto; subst.
        -   destruct r,p; simpl in *; subst; inversion t; auto.
        -   apply IHHU; symmetry; apply tau_eq; auto.
    +   subst.
        remember (State b true b1).
        assert (trans s isBraked s) by (subst; constructor).
        exists (Run s (nilp s isBraked s H)); repeat split.
        constructor; unfold sata; auto.
Qed.  

Theorem IsParked_spec s :
    s |= IsParked <-> parkState s = true.
Proof.
    destruct s; simpl; split; satisfy; intro H.
    +   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; auto; subst.
        -   destruct r,p; simpl in *; subst; inversion t; auto.
        -   apply IHHU; symmetry; apply tau_eq; auto.
    +   subst.
        remember (State b b0 true).
        assert (trans s isParked s) by (subst; constructor).
        exists (Run s (nilp s isParked s H)); repeat split.
        constructor; unfold sata; auto.
Qed.


    




Theorem switch_safe : 
    |= AG ((IsOn ∧ ¬ IsParked) → [Switch] IsOn).
Proof.
    satisfy; intros s F.
    induction F.
    +   apply imply_to_and in H.
        induction H as [[H H0] H1].
        apply IsOn_spec in H.
        rewrite (IsParked_spec s) in H0.
        assert (parkState s = false). 
            { destruct (parkState s); auto. contradiction H0; auto. } 
        clear H0.
        apply NNPP in H1.
        induction H1 as [r [Hr [_ HU]]].
        induction HU.
        -   apply H1; clear H1.
            destruct s; simpl in *; subst.
            destruct r, p; simpl in *; subst a s;
                inversion t; subst;
                remember (State true b0 false) as s;
                assert (trans s isOn s); try( subst; constructor );
                exists (Run s (nilp s isOn s H)); repeat split;
                constructor; unfold sata; auto.
        -   simpl in *; subst.
            apply IHHU. symmetry. apply tau_eq; auto.
    +   induction H as [r [Hr [_ HU]]]; subst.
        induction HU; auto.
        apply imply_to_and in H0.
        induction H0 as [[H0 H1] H2].
        apply IsOn_spec in H0.
        rewrite (IsParked_spec (nextState r)) in H1.
        assert (parkState (nextState r) = false).
            { destruct r, p, s', b1; auto; contradiction H1; auto. }
        clear H1.
        apply NNPP in H2.
        induction H2 as [r' [Hr' [_ HU']]].
        induction HU'.
        *   apply H2; clear H2.
            destruct r,p; simpl in *; subst;
            destruct r0; [destruct p| destruct p0]; simpl in *; subst;
            destruct s0; simpl in *; subst; inversion t0; subst;
                remember (State true b0 false) as s';
                assert (trans s' isOn s') as H0; try (subst; constructor);
                exists (Run s' (nilp s' isOn s' H0));
                repeat split; constructor; unfold sata; auto.
        *   apply IHHU'; simpl in *; subst.
            symmetry; apply tau_eq; auto.
Qed.





      
