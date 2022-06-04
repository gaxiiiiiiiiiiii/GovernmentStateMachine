Require Export Semantic.

(* 原子命題 *)
Notation IsAssigned r m := (Var (isAssigned r m)).
Notation WithinTerm r := (Var (withinTerm r)).
Notation IsProposed adm a := (Var (isProposed adm a)).
Notation HasTenuren adm := (Var (hasTenuren adm)).
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
Notation SET_TENURE := Pset_tenure.
Notation SET_EXPIRATION := Pset_expiration.

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
    WithinTerm adm → RejectDismissal.

End Proposition.

