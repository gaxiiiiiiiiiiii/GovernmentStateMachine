
Require Export Classical.
Require Import Coq.Setoids.Setoid.

Section Def.


Context {state action : Type} {trans : state -> action -> state -> Prop}
        {tau : action} {tau_eq : forall  s s', trans s tau s' <->  s = s'}.

     

(******************** path ********************)

CoInductive path : state -> Type :=
    | nilp s a s' : trans s a s' -> path s
    | consp s a s' : trans s a s' -> path s' -> path s.



Inductive run := Run s : path s -> run.

Definition headState (r : run) : state :=
    match r with Run s _ => s end.

Definition nextState (r : run) : state :=
    match r with 
    | Run s p => match p with 
        | nilp _ _ s' _ => s' 
        | consp _ _ s' _ _ => s' 
        end 
    end.





Definition pathOf (r : run) : match r with Run s _ => path s end :=
    match r with 
    | Run s p => p
    end.

Definition headAction (r : run) : action :=
    match r with 
    | Run _ p => match p with
        | nilp _ a _ _ => a
        | consp _ a _ _ _ => a 
        end 
    end.
 

(******************** action_formula ********************)



Inductive action_form :=
    | any : action_form 
    | action_ : action -> action_form
    | not_ : action_form -> action_form
    | and_ : action_form -> action_form -> action_form.

Definition non := not_ any .  

Fixpoint sata  (a : action) (chi : action_form) : Prop :=
    match chi with 
    | any => True 
    | action_ a' => a = a' 
    | not_ chi' => ~ sata a chi' 
    | and_ chi1 chi2 => sata a chi1 /\ sata a chi2
    end. 










(******************** ACTL ********************)

Inductive Until (f f' : state -> Prop) (chi chi' : action_form) : run -> Prop :=
    | until_here r : 
        sata (headAction r) chi' -> f' (nextState r) -> Until f f' chi chi' r
    | until_there s a s' H p: 
        sata a chi -> f s' -> Until f f' chi chi' (Run s' p) -> 
        Until f f' chi chi' (Run s (consp s a s' H p)).

Inductive form :=
    | top : form 
    | bot : form 
    | not : form -> form
    | and : form -> form -> form 
    | or : form -> form -> form 
    | imp : form -> form -> form
    | exist : formr -> form 
    | all : formr -> form

with formr :=
    | until : form -> form -> action_form -> action_form -> formr.




Scheme form_mut := Induction for form Sort Prop 
with formr_mut := Induction for formr Sort Prop.



Fixpoint sat (f : form) (s : state)  : Prop :=
    match f with 
    | top => True
    | bot => False
    | not f => ~ (sat f) s
    | and f1 f2 => sat f1 s /\ sat f2 s 
    | or f1 f2 => sat f1 s \/ sat f2 s
    | imp f1 f2 => sat f1 s -> sat f2 s 
    | exist f => exists r' , headState r' = s /\ satr f r'
    | all f => forall r', headState r' = s -> satr f r'
    end

with satr (f : formr) (r : run) : Prop :=
    match f with 
    | until f1 f2 chi chi' =>  sat f1 (headState r)  /\  Until (sat f1) (sat f2) chi chi' r
    end.

End Def.

(******************** derived operation ********************)


Notation "⊤" := top.
Notation "⊥" := bot.
Notation "¬ f" := (not f)(at level 10).
Notation "f ∧ f'" := (and f f')(at level 20).
Notation "f ∨ f'" := (or f f')(at level 20).
Notation "f → f'" := (imp f f')(at level 30).

Notation "f [ chi ]  'U'  [ chi' ] f'" := (until f f' chi chi')(at level 50).
Notation "f 'U' f'" := (f [any] U [any] f')(at level 50).
Notation "[ chi ]  'U'  [ chi' ] f'" := (⊤ [chi] U [chi'] f')(at level 50).

Notation "'E' p" := (exist p)(at level 50).
Notation "'A' p" := (all p)(at level 50).
Notation "'EX' [ chi ] f" := (E (⊤ [non] U [chi] f))(at level 50, chi at level 5).
Notation "'AX' [ chi ] f" := (A (⊤ [non] U [chi] f))(at level 50, chi at level 5).
Notation "'EF' [ chi ] f" := (E (⊤ [any] U [chi] f))(at level 50, chi at level 5).
Notation "'AF' [ chi ] f" := (A (⊤ [any] U [chi] f))(at level 50, chi at level 5).







Section theorems.

Context {state action : Set} {trans : state -> action -> state -> Prop}
        {tau : action} {tau_eq : forall  s s', trans s tau s' <->  s = s'}.


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

Notation "f 'EU' f'" := (f' ∨ (f ∧ (EX (E (f U f')))))(at level 50).
Notation "f 'AU' f'" := (f' ∨ (f ∧ (AX (A (f U f')))))(at level 50).
Notation "f 'EW' f'" := (¬ ((¬ f') AU ((¬ f) ∧ (¬ f'))))(at level 50).
Notation "f 'AW' f'" := (¬ ((¬ f') EU ((¬ f) ∧ (¬ f'))))(at level 50).


Theorem tau_refl s :
    trans s tau s.
Proof.
    apply tau_eq; auto.
Qed.   


Theorem dia_spec f s chi:
    s |= <chi> f <-> 
    exists a s', sata a chi /\ trans s a s' /\ s' |= f.
Proof.
    split.
    +   destruct f;
        try (
            intro H; induction H as [r [Hr [_ HU]]]; subst;
            induction HU; subst; simpl in *; subst; 
                try (destruct r, p; simpl in *; exists a, s'; repeat split; auto);
                assert (s = s') by (apply tau_eq; auto); subst s'; auto
        ).
        {
            intro H; induction H as [r [Hr [_ HU]]]; subst.
            induction HU; subst; simpl in *; subst. 
                try (induction H0; destruct r, p; simpl in *; exists a, s'; repeat split; auto).
                assert (s = s') by (apply tau_eq; auto); subst s'; auto.
        }               
    +   intro H; induction H as [a [s' [H_ [Ht Hf]]]].
        unfold sat; simpl.
        exists (Run s (nilp s a s' Ht)); repeat split; constructor; auto.
Qed.  




Theorem box_spec f s chi :  
    s |= [chi] f <->
    forall r : run (trans := trans),
        headState r = s ->
        sata (headAction r) chi -> 
        trans (headState r) (headAction r) (nextState r) -> 
        (nextState r) |= f.
Proof.
    split.
    +   destruct f;
            unfold sat; intros H r Hr Ha Ht;
            apply not_ex_all_not with (n := r) in H;
            apply not_and_or in H;
            induction H; try (case (H Hr)); subst;
            apply not_and_or in H;
            induction H; apply NNPP; intro F; apply H; auto; clear H;
            destruct r, p; simpl in *; constructor; simpl; auto.
    +   destruct f; auto;
            unfold sat; intros H F;
            induction F as [r [Hr [_ HU]]];
            induction HU; auto; simpl in *; subst;
                try (apply H1; clear H1; apply H; auto; destruct r, p; auto);
                try (assert (s = s') by (apply tau_eq; auto); subst s'; auto).
            apply (H r ); auto; destruct r, p; auto.
Qed.   

Inductive belong : run (trans := trans) -> state -> Prop :=
    | belong_here r s : headState r = s -> belong r s 
    | belong_next r s : nextState r = s -> belong r s 
    | belong_there s a s' H p s'': 
        belong (Run s' p) s'' -> belong (Run s (consp s a s' H p)) s''.

Theorem EF_spec f s :
    s |= EF f <-> 
        exists (r : run (trans := trans)) s', 
            headState r = s /\ belong r s' /\ s' |= f.
Proof.
    split; unfold sat; intro; fold (sat (trans := trans)) in *.
    +   induction H; auto.
        *   exists (Run s  (nilp s tau s (tau_refl s))), s; 
            repeat split; try constructor; auto.
        *   induction H as [r [Hr [_ HU]]]; subst.
            induction HU.
            -   exists r, (nextState r); repeat split; auto.
                destruct r, p; constructor 2; auto.
            -   simpl.
                induction IHHU as [r [s'' [Hr [Hs'' Hf]]]] .
                destruct r; simpl in *; subst s0.                
                exists (Run s (consp s a s' H p0)), s''; repeat split; auto.
                constructor 3; auto.
    +   induction H as [r [s' [Hr [Hs Hf]]]]; subst.
        induction Hs; subst; auto; right; simpl in *.
        -   exists r; repeat split.
            constructor; unfold sata; auto.
        -   apply IHHs in Hf.
            induction Hf; auto.
            *   exists (Run s (nilp s a s' H)); repeat split.
                constructor; try unfold sata; auto.
            *   induction H0 as [r [Hr [_ HU]]].
                destruct r; simpl in Hr; subst s0.
                exists (Run s (consp s a s' H p0)); repeat split.
                constructor 2; try unfold sata; auto.
Qed. 


Theorem AF_spec f s :
    s |= AF f <->
        (forall r, headState r = s ->
        (exists s', belong r s' /\ s' |= f)).
Proof.
    split; unfold sat; intro; fold (sat (trans := trans)) in *.
    +   intros r Hr.
        induction H.
        -   exists s; split; auto; constructor; auto.
        -   apply H in Hr; clear H.
            induction Hr as [_].
            induction H.
            *   exists (nextState r); split; auto.
                constructor 2; auto.
            *   induction IHUntil as [s'' [Hs'' Hf]].
                exists s''; split; auto.
                constructor 3; auto.
    +   specialize (H (Run s (nilp s tau s (tau_refl s))) (eq_refl s)).
        induction H as [s' [Hs Hf]].
        inversion Hs; subst; auto.
Qed.    

Theorem axiomK f f' :
    |= (AX (f → f')) → ((AX f) → (AX f')).
Proof.
    unfold sat; intros; fold (sat (trans := trans)) in *.
    intro F; induction F as [r [Hr [_ HU]]].
    induction HU.
    +   apply H0; exists r; repeat split; auto.
        constructor; try unfold sata; auto; intro F.
        apply H; exists r; repeat split; auto.
        constructor; try unfold sata; auto.
    +   simpl in *; subst s0 a.
        apply IHHU; symmetry; apply tau_eq; auto.
Qed.  

Theorem axiomAXEX f :
    |= (AX f) → (EX f).
Proof.
    unfold sat; intros s H; fold (sat (trans := trans)) in *.
    remember (Run s (nilp s tau s (tau_refl s))).
    apply not_ex_all_not with (n := r) in H.
    apply not_and_or in H.
    induction H; simpl in *.
    +   contradiction H; subst; auto.
    +   apply not_and_or in H; induction H; [apply NNPP; intro F; apply H; auto|].
        apply NNPP; intro F; apply H; constructor; unfold sata; auto; simpl.
        intro F_; apply F.
        exists r; subst; repeat split; constructor; unfold sata; auto.
Qed.        

Ltac  satisfy := unfold sat; fold (sat (trans := trans)).

Theorem axiomAX f :
    |= f -> |= AX f.
Proof.
    satisfy; intros H s F.
    induction F as [r [Hr [_ HU]]].
    induction HU; eauto; simpl in *; subst.
    apply IHHU; symmetry; apply tau_eq; auto.
Qed.



Theorem AU_ind f g h :
    |= g → h -> (|= f → ((AX h) → h)) -> |= (f AU g) → h.
Proof.
    satisfy; intros IH IH' s H.
    induction H; eauto.
    induction H.
    apply (IH' s H); clear IH'.
    intro F; apply H0; clear H0.
    induction F as [r [Hr [_ HU]]].    
    induction HU; simpl in *; subst.
    -   exists r; repeat split; auto.
        constructor; auto; intro F.
        specialize (F 
            (Run (nextState r) (nilp (nextState r) tau (nextState r) (tau_refl (nextState r))))
            (eq_refl (nextState r))
        ); simpl in F; induction F.
        inversion H3; simpl in *; auto.
    -   rewrite tau_eq in H0; symmetry in H0; auto.
Qed.  

Theorem EU_ind f g h :
    |= g → h -> (|= f → ((EX h) → h)) -> |= (f EU g) → h.
Proof.
Abort.
            
Theorem AU_intro f g :
    |= g →  (f AU g).
Proof.
    satisfy; intros s H; left; auto.
Qed.

End theorems.




