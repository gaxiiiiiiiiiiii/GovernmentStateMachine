From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.
Require Export Nat.

Set Implicit Arguments.
Unset Strict Implicit.

(********************)
(* メタ・アサンプション *)
(********************)

Parameter citizen : finType.
Definition currency := nat.
Definition timestamp := nat.
Definition random := Type.

Parameter now : timestamp.
Parameter random_choice : forall A : Type, random -> A.
Definition randomC := random_choice citizen.
Definition randomSetC := random_choice {set citizen}.



Variant admin :=
    | global    
    | police
    | judiciary
    | military 
    | media
    | education
    | registration
    | professional
    | facilitator.


(************)
(* アクション *)
(************)

Inductive proposal  :=
    | Passign : admin -> citizen -> proposal
    | Pdismissal : admin -> citizen -> proposal
    | Pwithdraw : currency -> proposal 
    | Pdeposit : currency -> proposal 
    | Pallocate : admin -> currency ->  proposal
    | Pset_tenure : admin -> citizen -> proposal
    | Pset_expiration : admin -> timestamp -> proposal.    


Inductive act :=
    | Apropose : admin -> proposal -> random -> random -> random -> act
    | Adeliberate : admin -> act.


(************)    
(* 状態と熟議 *)
(************)



Record deliberation := mkDlb{
    Dproposal : proposal;
    Dprofessional : citizen;
    Dfacilitator : citizen;
    Ddeliberator : {set citizen};    
}.



Record subState := mkSubState{
    SSbudget : currency;
    SStenure : option citizen;
    SSterm : timestamp;
    SSmember : {set citizen};
    SSdeliberation : option deliberation
}.


Record state := mkState{
    Streasury : currency;    
    Sadmin : admin -> subState;    
}.

(*********************)
(* updatable recortd *)
(*********************)


Instance etaSubState : Settable subState := 
    settable! mkSubState 
        < SSbudget; SStenure; SSterm; SSmember; SSdeliberation>.

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Sadmin >.




(**************************)
(* eqType's instantiation *)
(**************************)

Tactic Notation "mkCompEq"  :=
    refine (EqMixin (compareP _)) => x y;
    unfold decidable; decide equality; apply eq_comparable.

Definition eqMixin := Equality.mixin_of.

Definition admin_eqMixin : eqMixin admin. Proof. mkCompEq. Qed.
Canonical Structure admin_eqType := Eval hnf in @EqType admin admin_eqMixin.

Definition proposal_eqMixin : eqMixin proposal. Proof. mkCompEq. Qed.
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.


Definition deliberation_eqMixin  : eqMixin deliberation. Proof. mkCompEq. Qed.
Canonical Structure deliberation_eqType := Eval hnf in @EqType deliberation deliberation_eqMixin.        

Definition subState_eqMixin : eqMixin subState. Proof. mkCompEq. Qed.
Canonical Structure subState_eqType := Eval hnf in @EqType subState subState_eqMixin.


(**********)
(* 状態遷移 *)
(**********)

Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then r else f d'.
Notation "a ↦ b" := (subst a b)(at level 10).

Parameter evalD : deliberation -> bool.  

Definition transv_  (a : proposal) (x : state)  :=
    match a with     
    | Pwithdraw n => x <|Streasury ::= plus n|>    
    | Pdeposit n => x <|Streasury ::= minus n|>
    | Passign a m => 
        let ss := Sadmin x a in 
        let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
        x <| Sadmin ::= a ↦ ss'|>
    | Pdismissal a m => 
        let ss := Sadmin x a in 
        let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
        x <| Sadmin ::= a ↦ ss'|>
    | Pallocate a n => 
        let ss := Sadmin x a in 
        let ss' := ss <| SSbudget ::= fun n' => n + n' |> in
        x <| Sadmin ::= a ↦ ss'|>
    | Pset_tenure a m => 
        let ss := Sadmin x a in 
        let ss' := ss <| SStenure := Some m |> in
        x <| Sadmin ::= a ↦ ss'|>
    | Pset_expiration a n =>
        let ss := Sadmin x a in 
        let ss' := ss <| SSterm := n |> in
        x <| Sadmin ::= a ↦ ss'|>
    end.


Definition trans_ (a : act) (x : state) :=
    match a with 
    | Apropose adm a' p_ f_ d_ => 
        let ss := Sadmin x adm in         
        let ss' := ss <|SSdeliberation := Some (mkDlb a' (randomC p_) (randomC f_ ) (randomSetC d_))|> in 
        x <| Sadmin ::= adm ↦ ss'|>
    | Adeliberate adm => 
        let ss := Sadmin x adm in
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            if evalD dlb then transv_ (Dproposal dlb) x else x
        | None => x
        end
    end.


Definition trans a x y := y = trans_ a x.

(***********)
(* 原子命題 *)
(***********)

Inductive var :=
    | isAssigned : admin -> citizen -> var
    | withinTerm : admin -> var
    | isProposed : admin -> proposal -> var
    | hasTenuren : admin -> var
    | isTenuren : admin -> citizen -> var
    | isValidDeliberation : admin -> var.




Definition valuation (x : var) (s : state) : bool :=
    match x with     
    | isAssigned a m => 
        let ss := Sadmin s a in 
        let mem := SSmember ss in         
        m \in mem
    | withinTerm a => 
        let ss := Sadmin s a in 
        let n := SSterm ss in
        now <? n
    | isProposed adm a => 
        let ss := Sadmin s adm in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            a == Dproposal dlb
        | None => false
        end
    | isValidDeliberation a => 
        let ss := Sadmin s a in 
        let ps := SSmember (Sadmin s professional) in 
        let fs := SSmember (Sadmin s facilitator) in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            (Dprofessional dlb \in ps) && 
            (Dfacilitator dlb \in fs) &&
            (Ddeliberator dlb != set0)
        | None => false
        end        
    | hasTenuren a => 
        let ss := Sadmin s a in 
        let m := SStenure ss in 
        match m with 
        | Some _ => true 
        | _ => false 
        end
    | isTenuren a m  =>
        let ss := Sadmin s a in 
        let m' := SStenure ss in 
        match m' with 
        | Some m'' => m'' == m 
        | _ => false
        end
    end.



