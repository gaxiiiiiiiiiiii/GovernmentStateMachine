Require Export Semantic.

(*************)
(* Notations *)
(*************)

(* type of substate *)
Definition REGISTRATION := Admin 0.
Definition PROFESSIONAL := Admin 1.
Definition FACILITATOR := Admin 2.
Definition POLICE := Admin 3.
Definition JUDICIARY := Admin 4.
Definition MILITARY := Admin 5.
Definition MEDIA := Admin 6.
Definition EDUCATION := Admin 7.


(* 原子命題 *)
Definition HasNoBudget t := (Var (hasNoBudget t)).
Definition HasNoDeliberation t := (Var (hasNoDeliberation t)).
Definition HasNoTenureWoker t := (Var (hasNoTenureWoker t)).
Definition HasNoMember t := (Var (hasNoMember t)).

Definition TreasuryRestriction  t := (Var (treasuryRestriction t)).
Definition BudgetRestriction t := (Var (budgetRestriction t)).
Definition AllocateRestriction t := (Var (allocateRestriction t)).
Definition AssignRestriction t := (Var (assignRestriction t)).
Definition RegisrateRestriction t := (Var (regisrateRestriction t)).


Definition IsAssigned r m := (Var (isAssigned r m)).
Definition WithinExpiration r m := (Var (withinExpiration r m)).
Definition IsProposed adm a := (Var (isProposed adm a)).
Definition IsTenurenWorker adm m := (Var (isTenureWorker adm m)).
Definition IsValidDeliberation a p f:= (Var (isValidDeliberation a p f)).

(* アクション *)
Notation SPROPOSE := AsubPropose.
Notation SDELIBERATE := AsubDeliberate.
Notation GPROPOSE := AglobalPropose.
Notation GDELIBERATE := AglobalDeliberate.

(* 提案 *)
Notation ASSIGNM := PassignMember.
Notation DISMISSALM := PdismissalMember.
Notation ASSIGNTW := PassignTenureWorker.
Notation ADISMISSLATW := PdismissalTenureWorker.
Notation WITHDRAWT := PwithdrawTreasury.
Notation DEPOSITT := PdepositTreasury.
Notation WITHDRAWB := PwithdrawBudget.
Notation DEPOSETB := PdepositBudget.
Notation ALLOCATE := Pallocate.
Notation REGISRATE := Pregisrate.
Notation DEREGISRATE := Pderegisrate.

(*****************)
(* specification *) 
(*****************)

(* 人材プール *)

Definition hasOnlyTenureWoker adm :=
    HasNoBudget adm ∧ HasNoDeliberation adm ∧ HasNoMember adm.
Notation IsPool := hasOnlyTenureWoker.
Definition ProfessionalIsPool := IsPool PROFESSIONAL.
Definition FacilitatorIsPool := IsPool FACILITATOR.

Definition PoolSpec := ProfessionalIsPool ∧ FacilitatorIsPool.

(* global以外の行政の提案の制約 *)   

Definition LAR restriction :=
    restriction POLICE ∧
    restriction JUDICIARY ∧
    restriction MILITARY ∧
    restriction MEDIA ∧
    restriction EDUCATION ∧
    restriction REGISTRATION.
Definition TreasuryLAR := LAR TreasuryRestriction.
Definition AllocateLAR := LAR AllocateRestriction.
Definition BudgetLAR := LAR BudgetRestriction.
Definition AssignLAR := LAR AssignRestriction.

Definition LocalAdminSpec := 
    TreasuryLAR ∧ AllocateLAR ∧ BudgetLAR ∧ AssignLAR.


(* 市民登録・解除ができるのはREGISRATIONだけ *)
(* ※グローバルな熟議でも市民登録・解除の提案ができてしまうので、要修正 *)
Definition RegisrateSpec :=
    RegisrateRestriction POLICE ∧
    RegisrateRestriction JUDICIARY ∧
    RegisrateRestriction MILITARY ∧
    RegisrateRestriction MEDIA ∧
    RegisrateRestriction EDUCATION.

(* 行政の仕様全体 *)    
Definition SPEC :=
    AG (PoolSpec ∧ LocalAdminSpec ∧ RegisrateSpec).


(*******************)
(* 証明したい命題など *)
(*******************)


Section Proposition.

Variable (m : citizen) (adm : admin)  (s : state).


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



