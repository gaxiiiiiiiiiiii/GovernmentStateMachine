From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.
Require Export Nat.


Set Implicit Arguments.
Unset Strict Implicit.

(***************)
(* パラメータなど *)    
(***************)

Parameter citizen : finType.
Definition currency := nat.
Definition timestamp := nat.
Definition random := Type.

Parameter now : timestamp.
Parameter random_choice : forall A : Type, random -> A.
Definition randomC := random_choice citizen.
Definition randomSetC := random_choice {set citizen}.


(*******)
(* 役職 *)    
(*******)

Variant role :=
    | Professional
    | Facilitator.

Lemma eq_role_dec (s t : role) : { s = t} + { s <> t}.
Proof. decide equality; apply eq_comparable. Qed.
Definition role_eqMixin := EqMixin (compareP eq_role_dec).
Canonical Structure role_eqType := Eval hnf in @EqType role role_eqMixin.

(************)
(* アクション *)
(************)

Inductive proposal  :=
    | Passign : role -> citizen -> proposal
    | Pdismissal : role -> citizen -> proposal
    | Padd_mem :citizen -> proposal
    | Pdel_mem :citizen -> proposal 
    | Pwithdraw : currency -> proposal 
    | Pdeposit : currency -> proposal 
    | Pallocate : currency -> role -> proposal
    | Pset_expiration : role -> timestamp -> proposal.

Lemma eq_proposal_dec (s t : proposal) : { s = t} + { s <> t}.
Proof. decide equality; apply eq_comparable. Qed.
Definition proposal_eqMixin := EqMixin (compareP eq_proposal_dec).
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.

Inductive act :=
    | Apropose : proposal -> random -> random -> random -> act
    | Adeliberate.


(************)    
(* 状態と熟議 *)
(************)

Record deliberation := mkDlb{
    Dproposal : proposal;
    Dprofessional : citizen;
    Dfacilitator : citizen;
    Ddeliberator : {set citizen};
}.

Record state := mkState{
    Streasury : currency;    
    Smember : {set citizen};
    Sassignment : role -> {set citizen};
    Sbudget : role -> currency;
    Sexpiration : role -> timestamp;
    Sdeliberation : deliberation
}.

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Smember; Sassignment; Sbudget; Sexpiration; Sdeliberation >.


(**********)
(* 状態遷移 *)
(**********)

Parameter evalD : deliberation -> bool.  

Definition transv_  (a : proposal) (x : state)  :=
    match a with 
    | Passign r m => 
        x <| Sassignment ::= fun f => fun r' => if r == r' then m |: f r' else f r' |>
    | Pdismissal r m => 
        x <| Sassignment ::= fun f => fun r' => if r == r' then f r' :\ m else f r' |> 

    | Padd_mem m => x <| Smember ::= fun X => m |: X|>
    | Pdel_mem m => x <| Smember ::= fun X => X :\ m|>

    | Pwithdraw n => x <|Streasury ::= plus n|>    
    | Pdeposit n => x <|Streasury ::= minus n|>
    | Pallocate n r => x <|Streasury ::= minus n|> 
                        <|Sbudget ::= fun f => fun r' => if r == r' then f r + n else f r'|>

    | Pset_expiration r n => 
        x  <|Sbudget ::= fun f => fun r' => if r == r' then n else f r'|>                   
    end.

Definition trans_ (a : act) (x : state) :=
    match a with 
    | Apropose a' p_ f_ d_ => 
        x <| Sdeliberation := mkDlb a' (randomC p_) (randomC f_ ) (randomSetC d_) |>
    | Adeliberate => 
        if evalD (Sdeliberation x) then transv_ (Dproposal (Sdeliberation x)) x else x
    end.


Definition trans a x y := y = trans_ a x.

(***********)
(* 原子命題 *)
(***********)

Inductive var :=
    | isAssigned : role -> citizen -> var
    | isMember : citizen -> var
    | withinTerm : role -> var
    | isProposed : proposal -> var
    | isValidDeliberation.

Definition valuation (x : var) (s : state) : bool :=
    match x with 
    | isAssigned r m => m \in Sassignment s r
    | isMember m => m \in Smember s
    | withinTerm r => now <? Sexpiration s r 
    | isProposed a => a == Dproposal (Sdeliberation s)
    | isValidDeliberation => 
        (Dprofessional (Sdeliberation s) \in Sassignment s Professional) && 
        (Dfacilitator (Sdeliberation s) \in Sassignment s Facilitator) &&
        (Ddeliberator (Sdeliberation s) != set0)
    end.



