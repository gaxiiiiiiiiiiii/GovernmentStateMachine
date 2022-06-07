Require Export Semantic.

(*************)
(* Notations *)
(*************)

(* type of substate *)
Notation GLOBAL := global.
Notation POLICE := police.
Notation JUDICIARY := judiciary.
Notation MILITARY := military.
Notation MEDIA := media.
Notation EDUCATION := education.
Notation REGISTRATION := registration.
Notation PROFESSIONAL := professional.
Notation FACILITATOR := facilitator.

(* 原子命題 *)
Notation HasNoBudget t := (Var (hasNoBudget t)).
Notation HasNoDeliberation t := (Var (hasNoDeliberation t)).
Notation HasNoTenuren t := (Var (hasNoTenuren t)).
Notation HasNoExpiration t := (Var (hasNoExpiration t)).

Notation ProhibitWithdraw  t := (Var (prohibitWithdraw t)).
Notation ProhibitDeposit t := (Var (prohibitDeposit t)).
Notation ProhibitAllocate t := (Var (prohibitAllocate t)).
Notation ProhibitAssign t := (Var (prohibitAssign t)).
Notation ProhibitDismissal t := (Var (prohibitDismissal t)).
Notation ProhibitSetTenure t := (Var (prohibitSetTenure t)).
Notation ProhibitSetExpiration t := (Var (prohibitSetExpiration t)).

Notation IsAssigned r m := (Var (isAssigned r m)).
Notation WithinExpiration r := (Var (withinExpiration r)).
Notation IsProposed adm a := (Var (isProposed adm a)).
Notation IsTenuren adm m := (Var (isTenuren adm m)).
Notation IsValidDeliberation := (Var isValidDeliberation).

(* アクション *)
Notation PROPOS := Apropose.
Notation DELIBERATE := Adeliberate.

(* 提案 *)
Notation ASSIGN := Passign.
Notation DISMISSAL := Pdismissal.
Notation WITHDRAW := Pwithdraw.
Notation DEPOSIT := Pdeposit.
Notation ALLOCATE := Pallocate.
Notation SET_TENURE := PsetTenure.
Notation SET_EXPIRATION := PsetExpiration.

(*****************)
(* specification *) 
(*****************)

(* professionalはmember以外の状態を持たない *)
Definition ProfessionalHasNoBudget :=
    AG (HasNoBudget PROFESSIONAL).
Definition ProfessionalHasNoDeliberation :=
    AG (HasNoDeliberation PROFESSIONAL).
Definition ProfessionalHasNoTenuren :=
    AG (HasNoTenuren PROFESSIONAL).
Definition ProfessionalHasNoExpiration :=
    AG (HasNoExpiration PROFESSIONAL).
Definition ProfessionalSpec :=
    ProfessionalHasNoBudget ∧ ProfessionalHasNoDeliberation ∧ 
    ProfessionalHasNoTenuren ∧ ProfessionalHasNoExpiration.

(* facilitatorはmember以外の状態を持たない *)
Definition FacilitatorHasNoBudget :=
    AG (HasNoBudget FACILITATOR).
Definition FacilitatorHasNoDeliberation :=
    AG (HasNoDeliberation FACILITATOR).
Definition FacilitatorHasNoTenuren :=
    AG (HasNoTenuren FACILITATOR).
Definition FacilitatorHasNoExpiration :=
    AG (HasNoExpiration FACILITATOR).
Definition FacilitatorSpec :=
    FacilitatorHasNoBudget ∧ FacilitatorHasNoDeliberation ∧ 
    FacilitatorHasNoTenuren ∧ FacilitatorHasNoExpiration.

(* globalのだけがallocateの提案をできる *)    
Definition PoliceIsProhibittedAllocate :=
    AG (ProhibitAllocate POLICE).
Definition JudiciaryIsProhibittedAllocate :=
    AG (ProhibitAllocate JUDICIARY).
Definition MilitaryIsProhibittedAllocate :=
    AG (ProhibitAllocate MILITARY).
Definition MediaIsProhibittedAllocate :=
    AG (ProhibitAllocate MEDIA).
Definition EducationIsProhibittedAllocate :=
    AG (ProhibitAllocate EDUCATION).
Definition RegistrationIsProhibittedAllocate :=
    AG (ProhibitAllocate REGISTRATION).
Definition AllocateSpec :=
    PoliceIsProhibittedAllocate ∧ JudiciaryIsProhibittedAllocate ∧
    MilitaryIsProhibittedAllocate ∧ MediaIsProhibittedAllocate ∧
    EducationIsProhibittedAllocate ∧ RegistrationIsProhibittedAllocate.


Definition SPEC :=
    ProfessionalHasNoBudget ∧ FacilitatorHasNoBudget ∧ AllocateSpec.    




(*******************)
(* 証明したい命題など *)
(*******************)


Section Proposition.

Variable (m : citizen) (adm : toss)  (s : state).


(* 任意の状態から任意の状態遷移を経ても、条件badを満たす状態にはならない *)
Definition safety (bad : form) := 
    s |= AG (¬ bad).


(* 任意の状態から任意の状態遷移を経ても、いずれ条件goodを満たす状態に至る *)
Definition liveness (good : form) :=
    s |= AF good.

 
(* 罷免が提案されている *)
Definition IsDissmissProposed adm m :=
    IsProposed global (DISMISSAL adm m).


(* 罷免提案が否決される *)
Definition RejectDismissal := 
    IsDissmissProposed adm m ∧ [DELIBERATE global] (IsAssigned adm m).

Definition IsDectator :=
    AG RejectDismissal.

(*  任期満了前の罷免提案は否決される *)    
Definition unndissmissibleBeforExpiation :=
    WithinExpiration adm → RejectDismissal.

End Proposition.

