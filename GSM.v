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


(************)
(* アクション *)
(************)

Inductive proposal  :=
    | Pwithdraw : currency -> proposal 
    | Pdeposit : currency -> proposal 
    | Pallocate : toss -> currency ->  proposal
    | Passign : toss -> citizen -> proposal
    | Pdismissal : toss -> citizen -> proposal    
    | Pset_tenure : toss -> citizen -> proposal
    | Pset_expiration : toss -> timestamp -> proposal.    


Inductive act :=
    | Apropose : toss -> proposal -> random -> random -> random -> act
    | Adeliberate : toss -> act.


(************)    
(* 状態と熟議 *)
(************)



Record deliberation := mkDlb{
    Dproposal : proposal;
    Dprofessional : citizen;
    Dfacilitator : citizen;
    Ddeliberator : {set citizen};
}.

Record subState := mkSubState {
    SSbudget : currency;
    SSmember : {set citizen};
    SSdeliberation : option deliberation;
    SStenure : option citizen;
    SSexpiration : option timestamp;
}.


Record state := mkState{
    Streasury : currency;    
    Stoss : toss -> subState;    
}.

(*********************)
(* updatable recortd *)
(*********************)



Instance etaSubState : Settable subState :=
    settable! mkSubState <SSbudget; SSmember; SSdeliberation; SStenure; SSexpiration>.        

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Stoss >.




(**************************)
(* eqType's instantiation *)
(**************************)

Tactic Notation "mkCompEq"  :=
    refine (EqMixin (compareP _)) => x y;
    unfold decidable; decide equality; apply eq_comparable.

Definition eqMixin := Equality.mixin_of.

Definition toss_eqMixin : eqMixin toss. Proof. mkCompEq. Qed.
Canonical Structure toss_eqType := Eval hnf in @EqType toss toss_eqMixin.

Definition proposal_eqMixin : eqMixin proposal. Proof. mkCompEq. Qed.
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.


Definition deliberation_eqMixin  : eqMixin deliberation. Proof. mkCompEq. Qed.
Canonical Structure deliberation_eqType := Eval hnf in @EqType deliberation deliberation_eqMixin.        

Definition subState_eqMixin : eqMixin subState. Proof. 
    refine (EqMixin (compareP _)) => x y.
    unfold decidable; decide equality; try unfold timestamp; apply eq_comparable.
Qed.
Canonical Structure subState_eqType := Eval hnf in @EqType subState subState_eqMixin.

(***********************)
(* subType of subState *)
(***********************)

Definition condP ss :=
    (SSdeliberation ss == None) &&
    (SStenure ss == None) && 
    (SSexpiration ss == None).


(**********)
(* 状態遷移 *)
(**********)


Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then r else f d'.
Notation "a ↦ b" := (subst a b)(at level 10).

Lemma subst_lemma {dom ran : finType} (f : dom -> ran) (d : dom) (r : ran) :
    let f' := subst d r f in f' d = r.
Proof. rewrite /subst eq_refl => // Qed.




Parameter evalD : deliberation -> bool.  

Definition transv_  (a : proposal) (x : state)  :=
    match a with     
    | Pwithdraw n => x <|Streasury ::= plus n|>    
    | Pdeposit n => x <|Streasury ::= minus n|>
    | Pallocate a n => 
        let ss := Stoss x a in 
        let ss' := ss <| SSbudget ::= fun n' => n + n' |> in
        x <| Stoss ::= a ↦ ss'|>
    | Passign a m => 
        let ss := Stoss x a in 
        let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
        x <| Stoss ::= a ↦ ss'|>
    | Pdismissal a m => 
        let ss := Stoss x a in 
        let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
        x <| Stoss ::= a ↦ ss'|>
    
    | Pset_tenure a m => 
        let ss := Stoss x a in 
        let ss' := ss <| SStenure := Some m |> in
        x <| Stoss ::= a ↦ ss'|>
    | Pset_expiration a n =>
        let ss := Stoss x a in 
        let ss' := ss <| SSexpiration := Some n |> in
        x <| Stoss ::= a ↦ ss'|>
    end.


Definition trans_ (a : act) (x : state) :=
    match a with 
    | Apropose adm a' p_ f_ d_ => 
        let ss := Stoss x adm in         
        let ss' := ss <|SSdeliberation := Some (mkDlb a' (randomC p_) (randomC f_ ) (randomSetC d_))|> in 
        x <| Stoss ::= adm ↦ ss'|>
    | Adeliberate adm => 
        let ss := Stoss x adm in
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
    | hasNoBudget : toss -> var
    | hasNoDeliberation : toss -> var
    | hasNoTenuren : toss -> var    
    | hasNoExpiration : toss -> var

    | isAssigned : toss -> citizen -> var
    | isProposed : toss -> proposal -> var 
    | isTenuren : toss -> citizen -> var
    | withinExpiration : toss -> var  
    | isValidDeliberation : toss -> var.




Definition valuation (x : var) (s : state) : bool :=
    match x with
    | hasNoBudget t => let ss := Stoss s t in SSbudget ss == 0
    | hasNoDeliberation t => let ss := Stoss s t in SSdeliberation ss == None
    | hasNoTenuren t => let ss := Stoss s t in SStenure ss == None 
    | hasNoExpiration t => let ss := Stoss s t in SSexpiration ss == None 

    | isAssigned a m => 
        let ss := Stoss s a in 
        let mem := SSmember ss in         
        m \in mem
    | isProposed adm a => 
        let ss := Stoss s adm in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            a == Dproposal dlb
        | None => false
        end
    | withinExpiration a => 
        let ss := Stoss s a in 
        let n := SSexpiration ss in
        now <? n
    | isValidDeliberation a => 
        let ss := Stoss s a in 
        let ps := SSmember (Stoss s professional) in 
        let fs := SSmember (Stoss s facilitator) in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            (Dprofessional dlb \in ps) && 
            (Dfacilitator dlb \in fs) &&
            (Ddeliberator dlb != set0)
        | None => false
        end           
    | isTenuren a m  =>
        let ss := Stoss s a in 
        let m' := SStenure ss in 
        match m' with 
        | Some m'' => m'' == m 
        | _ => false
        end
    end.



