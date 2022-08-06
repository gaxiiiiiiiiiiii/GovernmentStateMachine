Require Import ACTL.
Require Import EDEN.
Require Import Coq.Setoids.Setoid.

  
Set Implicit Arguments.


Definition lts := Build_LTS State Action Trans tau Tau_eq.


Notation Path := (@path lts).
Notation Form := (@form lts).
Notation Formr := (@formr lts).
Notation Citizen := (citizen env).
Notation Admin := (admin env).
Notation Var := (var env).

Notation State := (@ACTL.state lts).
Notation Action_ := (@ACTL.action_ lts).
Notation Tau := (@ACTL.tau lts).
Notation Act_var := (@act_var env).


(* 命題変数 *)
Notation HasNoBudget adm := (<(Action_ (Act_var (hasNoBudget adm)))> ⊤).
Notation HasNoComitee adm := (<(Action_ (Act_var (hasNoComitee adm)))> ⊤).
Notation IsBudgetRestricted adm := (<(Action_ (Act_var (isBudgetRestricted adm)))> ⊤).
Notation IsTransferRestricted adm := (<(Action_ (Act_var (isBudgetRestricted adm)))> ⊤).
Notation IsAssignmentRestrected adm adm' := (<(Action_ (Act_var (isAssignmentRestrected adm adm')))> ⊤).
Notation IsAdminControlRestricted adm := (<(Action_ (Act_var (isadminControlRestricted adm)))> ⊤).
Notation IsAssigned adm ctz := (<(Action_ (Act_var (isAssigned adm ctz)))> ⊤).
Notation IsProposed adm prp := (<(Action_ (Act_var (isProposed adm prp)))> ⊤).



Notation Propose prp := (Action_ (act_propose prp)).
Notation Withdraw adm n := (Propose (withdraw adm n)).
Notation Deposit adm n := (Propose (deposit adm n)).
Notation Transfer from to n := (Propose (transfer from to n)).
Notation AssignMember adm n := (Propose (assign adm n)).
Notation DismissalMember adm n := (Propose (dismissal adm n)).
Notation AssignTenureWorker adm n := (Propose (withdraw adm n)).
Notation GenAdmin adm n := (Propose (genAdmin adm n)).
Notation SlashAdmin adm n := (Propose (slashAdmin adm n)).

Notation Deliberate adm := (Action_ (act_deliberate adm)).



Variable ROOT PROFESSIONALS FACILITATORS REGISTRATOR DUMMY : Admin.


Definition IsAssignmentRestrectedStrict adm :=
    IsAssignmentRestrected adm ROOT ∧
    IsAssignmentRestrected adm PROFESSIONALS ∧
    IsAssignmentRestrected adm FACILITATORS ∧
    IsAssignmentRestrected adm DUMMY.



Definition ROOT_spec :=
    IsBudgetRestricted ROOT ∧
    IsAssignmentRestrected ROOT ROOT.

    
Definition PROFESSIONAL_spec :=
    HasNoBudget PROFESSIONALS ∧
    HasNoComitee PROFESSIONALS.

Definition FACILITATORS_spec :=
    HasNoBudget FACILITATORS ∧
    HasNoComitee FACILITATORS.

    
Definition REGISTRATOR_spec :=
    IsBudgetRestricted REGISTRATOR ∧
    IsTransferRestricted REGISTRATOR ∧
    IsAdminControlRestricted REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR FACILITATORS ∧
    IsAssignmentRestrected REGISTRATOR REGISTRATOR ∧
    IsAssignmentRestrected REGISTRATOR DUMMY.

Definition DUMMY_spec :=
    IsBudgetRestricted DUMMY ∧
    IsTransferRestricted DUMMY ∧
    IsAdminControlRestricted DUMMY ∧
    IsAssignmentRestrected DUMMY ROOT ∧
    IsAssignmentRestrected DUMMY PROFESSIONALS ∧
    IsAssignmentRestrected DUMMY FACILITATORS ∧
    IsAssignmentRestrected DUMMY REGISTRATOR ∧
    IsAssignmentRestrected DUMMY DUMMY.


Definition SPEC :=
    ROOT_spec ∧ PROFESSIONAL_spec ∧ REGISTRATOR_spec ∧ DUMMY_spec.

Ltac  satisfy := unfold sat; fold (@sat lts).



Theorem IsAssignedUnfdold adm c s :
    s |= IsAssigned adm c  <-> 
        match s adm with 
        | None => False 
        | Some ss' => c \in memberSS ss'
        end.
Proof.
    split; satisfy; intro H.
    -   induction H as [r [Hr [_ HU]]].
        induction HU; simpl in *; subst; auto; simpl in *.
        +   destruct r, p; simpl in *; subst; inversion t; subst; simpl in *; auto.                
        +   apply IHHU; auto.
    -   remember (s adm) as ss.
        destruct ss.
        +   assert (Trans s (Act_var (isAssigned adm c)) s) as Ht.
            { constructor; simpl; destruct (s adm);
                inversion Heqss; subst; auto.
            }    
            exists (Run s (nilp s (Act_var (isAssigned adm c)) s Ht));
            repeat split; constructor; unfold sata; auto.
        +   inversion H.
Qed.


        

            
Definition dismissible adm c :=
    (IsProposed ROOT (dismissal adm c)) ∧ ¬ [Deliberate ROOT] (IsAssigned adm c).

    
Definition deliberate_soundness adm c :=
    |= IsAssigned adm c → AF (dismissible adm c).