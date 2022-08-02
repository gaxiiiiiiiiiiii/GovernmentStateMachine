Require Import ACTL.
Require Import EDEN.
Require Import Coq.Setoids.Setoid.



Set Implicit Arguments.



Notation "s |= f" := (@sat State action Trans f s)(at level 80).
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

Notation Path := (@path State action Trans).
Notation Form := (@form action).
Notation Formr := (@formr action).

Notation Action_ := (@action_ action).
Notation Act_var := (@act_var Proposal).


(* 命題変数 *)
Notation HasNoBudget adm := (<(Action_ (Act_var (hasNoBudget adm)))> ⊤).
Notation HasNoComitee adm := (<(Action_ (Act_var (hasNoComitee adm)))> ⊤).
Notation HasNoTenureWoker adm := (<(Action_ (Act_var (hasNoTenureWoker adm)))> ⊤).
Notation HasNoMember adm := (<(Action_ (Act_var (hasNoMember adm)))> ⊤).
Notation IsBudgetRestricted adm := (<(Action_ (Act_var (isBudgetRestricted adm)))> ⊤).
Notation IsTransferRestricted adm := (<(Action_ (Act_var (isBudgetRestricted adm)))> ⊤).
Notation IsAssignmentRestrected adm adm' := (<(Action_ (Act_var (isAssignmentRestrected adm adm')))> ⊤).
Notation IsAdminControlRestricted adm := (<(Action_ (Act_var (isAdminControlRestricted adm)))> ⊤).
Notation IsAssigned adm ctz := (<(Action_ (Act_var (isAssigned adm ctz)))> ⊤).
Notation IsProposed adm prp := (<(Action_ (Act_var (isProposed adm prp)))> ⊤).
Notation IsTenureWorker adm ctz := (<(Action_ (Act_var (isTenureWorker adm ctz)))> ⊤).
Notation IsWithinExpiration adm ctz := (<(Action_ (Act_var (isWithinExpiration adm ctz)))> ⊤).


Notation Propose prp := (Action_ (act_proposal prp)).
Notation Withdraw adm n := (Propose (withdraw adm n)).
Notation Deposit adm n := (Propose (deposit adm n)).
Notation Transfer from to n := (Propose (transfer from to n)).
Notation AssignMember adm n := (Propose (assignMember adm n)).
Notation DismissalMember adm n := (Propose (dismissalMember adm n)).
Notation AssignTenureWorker adm n := (Propose (withdraw adm n)).
Notation DismissalTenureWorker adm n := (Propose (dismissalTenureWorker adm n)).
Notation GenAdmin adm n := (Propose (genAdmin adm n)).
Notation SlashAdmin adm n := (Propose (slashAdmin adm n)).

Notation Deliberate adm := (Action_ (act_deliberate adm)).


Definition ROOT := Adm 0.
Definition PROFESSIONALS := Adm 1.
Definition FACILITATORS := Adm 2.
Definition REGISTRATOR := Adm 3.
Definition POLICE := Adm 4.
(* Definition JUDICIARY := Adm 5.
Definition MILITARY := Adm 6.
Definition MEDIA := Adm 7.
Definition EDUCATION := Adm 8. *)


Definition IsAssignmentRestrectedStrict adm :=
    IsAssignmentRestrected adm ROOT ∧
    IsAssignmentRestrected adm PROFESSIONALS ∧
    IsAssignmentRestrected adm FACILITATORS ∧
    IsAssignmentRestrected adm POLICE.
    (* IsAssignmentRestrected adm JUDICIARY ∧
    IsAssignmentRestrected adm MILITARY ∧   
    IsAssignmentRestrected adm MEDIA ∧   
    IsAssignmentRestrected adm EDUCATION. *)





Definition ROOT_spec :=
    IsBudgetRestricted ROOT ∧
    HasNoTenureWoker ROOT ∧
    IsAssignmentRestrected ROOT ROOT.

    
Definition PROFESSIONAL_spec :=
    HasNoBudget PROFESSIONALS ∧
    HasNoComitee PROFESSIONALS ∧
    HasNoMember PROFESSIONALS.

Definition FACILITATORS_spec :=
    HasNoBudget FACILITATORS ∧
    HasNoComitee FACILITATORS ∧
    HasNoMember FACILITATORS.

    
Definition REGISTRATOR_spec :=
    IsBudgetRestricted REGISTRATOR ∧
    IsTransferRestricted REGISTRATOR ∧
    IsAdminControlRestricted REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR FACILITATORS ∧
    IsAssignmentRestrected REGISTRATOR REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR POLICE.

Definition POLICE_spec :=
    IsBudgetRestricted POLICE ∧
    IsTransferRestricted POLICE ∧
    IsAdminControlRestricted POLICE ∧
    IsAssignmentRestrected POLICE ROOT ∧
    IsAssignmentRestrected POLICE PROFESSIONALS ∧
    IsAssignmentRestrected POLICE FACILITATORS ∧
    IsAssignmentRestrected POLICE REGISTRATOR ∧
    IsAssignmentRestrected POLICE POLICE.


Definition SPEC :=
    ROOT_spec ∧ PROFESSIONAL_spec ∧ REGISTRATOR_spec ∧ POLICE_spec.

Ltac  satisfy := unfold sat; fold (sat (trans := Trans)).

Theorem tau_eq : forall  s s', Trans s tau s' <->  s = s'.
Proof.
    intros s s'; split; intro H; symmetry; auto.    
Qed.

Theorem IsAssignedUnfdold adm c s :
    s |= IsAssigned adm c  <-> 
        match Ssubstate s adm with 
        | None => False 
        | Some ss' => c \in SSmember ss'
        end.
Proof.
    split; satisfy; intro H.
    -   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; subst; auto; simpl in *.
        +   destruct r, p; simpl in *; subst;
                inversion t; subst; destruct s'; auto.
        +   apply IHHU; auto.
    -   remember (Ssubstate s adm) as ss.
        destruct ss.
        +   assert (Trans s (Act_var (isAssigned adm c)) s) as Ht.
            { constructor; simpl; destruct (Ssubstate s adm);
                inversion Heqss; subst; auto.
            }    
            Check path.

            exists (Run s (nilp s (Act_var (isAssigned adm c)) s Ht));
            repeat split; constructor; unfold sata; auto.
        +   inversion H.
Qed.

Theorem IsProposedUnfold adm prp s : 
            s |= IsProposed adm prp <->
                match Ssubstate s adm with 
                | None => False 
                | Some ss => match SScomitee ss with
                    | None => False 
                    | Some cmt => prp =  Dproposal cmt
                    end
                end.
Proof.
    split; satisfy; intro H.
    -   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; subst; auto; simpl in *.
        +   destruct r, p; simpl in *; subst;
                inversion t; subst; destruct s'; auto.
        +   apply IHHU; auto.
    -   remember (Ssubstate s adm) as ss.
        destruct ss.
        +   assert (Trans s (Act_var (isProposed adm prp)) s) as Ht.
            { constructor; simpl; destruct (Ssubstate s adm);
                inversion Heqss; subst; auto.
            }            
            exists (Run s (nilp s (Act_var (isProposed adm prp)) s Ht));
            repeat split; constructor; unfold sata; auto.
        +   inversion H.
Qed.            

            
Definition dismissible adm c :=
    (IsProposed ROOT (dismissalMember adm c)) ∧ ¬ [Deliberate ROOT] (IsAssigned adm c).

    
Definition deliberate_soundness adm c :=
    |= IsAssigned adm c → AF (dismissible adm c).