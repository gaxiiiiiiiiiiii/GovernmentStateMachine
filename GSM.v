From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.
Require Import Currency Toss Timestamp.


Set Implicit Arguments.
Unset Strict Implicit.

(********************)
(* メタ・アサンプション *)
(********************)

Parameter citizen : finType.
Parameter limit : nat.
Definition random := Type.


Parameter now : timestamp.
Parameter random_choice : forall A : Type, random -> A.
Definition randomC := random_choice citizen.
Definition randomSetC := random_choice {set citizen}.





(************)
(* アクション *)
(************)

Inductive proposal  :=
    | Pwithdraw : currency -> proposal 
    | Pdeposit : currency -> proposal 
    | Pallocate : toss -> currency ->  proposal
    | Passign : toss -> citizen -> proposal
    | Pdismissal : toss -> citizen -> proposal    
    | PsetTenure : toss -> citizen -> proposal
    | PsetExpiration : toss -> timestamp -> proposal.    


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
    Ssubstate : toss -> subState;    
}.

(*********************)
(* updatable recortd *)
(*********************)

Instance etaSubState : Settable subState :=
    settable! mkSubState <SSbudget; SSmember; SSdeliberation; SStenure; SSexpiration>.        

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Ssubstate >.


(**************************)
(* eqType's instantiation *)
(**************************)


Definition proposal_eqMixin : eqMixin proposal. Proof. mkCompEq. Qed.
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.


Definition deliberation_eqMixin  : eqMixin deliberation. Proof. mkCompEq. Qed.
Canonical Structure deliberation_eqType := Eval hnf in @EqType deliberation deliberation_eqMixin.        

Definition subState_eqMixin : eqMixin subState. Proof. 
    refine (EqMixin (compareP _)) => x y.
    unfold decidable; decide equality; try unfold timestamp; apply eq_comparable.
Qed.
Canonical Structure subState_eqType := Eval hnf in @EqType subState subState_eqMixin.



(**********)
(* 状態遷移 *)
(**********)


Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then r else f d'.
Notation "a ↦ b" := (subst a b)(at level 10).


Lemma subst_lemma {dom ran : finType} (f : dom -> ran) (d : dom) (r : ran) :
    let f' := subst d r f in f' d = r.
Proof. rewrite /subst eq_refl => //. Qed.


Parameter evalD : deliberation -> bool.  

Definition transv_  (a : proposal) (x : state)  :=
    match a with     
    | Pwithdraw n => x <|Streasury ::= addc n|>    
    | Pdeposit n => x <|Streasury ::= subc n|>
    | Pallocate a n => 
        let ss := Ssubstate x a in 
        let ss' := ss <| SSbudget ::= fun n' => addc n n' |> in
        x <| Ssubstate ::= a ↦ ss'|>
    | Passign a m => 
        let ss := Ssubstate x a in 
        let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
        x <| Ssubstate ::= a ↦ ss'|>
    | Pdismissal a m => 
        let ss := Ssubstate x a in 
        let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
        x <| Ssubstate ::= a ↦ ss'|>
    
    | PsetTenure a m => 
        let ss := Ssubstate x a in 
        let ss' := ss <| SStenure := Some m |> in
        x <| Ssubstate ::= a ↦ ss'|>
    | PsetExpiration a n =>
        let ss := Ssubstate x a in 
        let ss' := ss <| SSexpiration := Some n |> in
        x <| Ssubstate ::= a ↦ ss'|>
    end.


Definition trans_ (a : act) (x : state) :=
    match a with 
    | Apropose adm a' p_ f_ d_ => 
        let ss := Ssubstate x adm in         
        let ss' := ss <|SSdeliberation := Some (mkDlb a' (randomC p_) (randomC f_ ) (randomSetC d_))|> in 
        x <| Ssubstate ::= adm ↦ ss'|>
    | Adeliberate adm => 
        let ss := Ssubstate x adm in
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

    | restrictWithdraw  : toss -> var
    | restrictDeposit : toss -> var
    | restrictAllocate : toss -> var
    | restrictAssign : toss -> var
    | restrictDismissal : toss -> var
    | restrictSetTenure : toss -> var
    | restrictSetExpiration : toss -> var

    | isAssigned : toss -> citizen -> var
    | isProposed : toss -> proposal -> var 
    | isTenuren : toss -> citizen -> var
    | withinExpiration : toss -> var  
    | isValidDeliberation : toss -> var.






Definition valuation (x : var) (s : state) : bool :=
    match x with
    | hasNoBudget t => let ss := Ssubstate s t in SSbudget ss == noCurr
    | hasNoDeliberation t => let ss := Ssubstate s t in SSdeliberation ss == None
    | hasNoTenuren t => let ss := Ssubstate s t in SStenure ss == None 
    | hasNoExpiration t => let ss := Ssubstate s t in SSexpiration ss == None 

    | restrictWithdraw  t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists n , (Pwithdraw n == prp)]
        end

    | restrictDeposit t  =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists n , (Pdeposit n == prp)]
        end
    | restrictAllocate t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists n, [exists t', (Pallocate t' n == prp)]]
        end
    | restrictAssign t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists m, [exists t', (Passign t' m == prp)]]
        end
    | restrictDismissal t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists m, [exists t', (Pdismissal t' m == prp)]]
        end
    | restrictSetTenure t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists m, [exists t', (PsetTenure t' m == prp)]]
        end
    | restrictSetExpiration t =>
        let dlb := SSdeliberation (Ssubstate s t) in 
        match dlb with 
        | None => true 
        | Some dlb' => let prp := Dproposal dlb' in 
            ~~ [exists m, [exists t', (PsetExpiration t' m == prp)]]
        end
    
    | isAssigned a m => 
        let ss := Ssubstate s a in 
        let mem := SSmember ss in         
        m \in mem
    | isProposed adm a => 
        let ss := Ssubstate s adm in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            a == Dproposal dlb
        | None => false
        end
    | withinExpiration a => 
        let ss := Ssubstate s a in 
        let n := SSexpiration ss in
        now < n
    | isValidDeliberation a => 
        let ss := Ssubstate s a in 
        let ps := SSmember (Ssubstate s professional) in 
        let fs := SSmember (Ssubstate s facilitator) in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            (Dprofessional dlb \in ps) && 
            (Dfacilitator dlb \in fs) &&
            (Ddeliberator dlb != set0)
        | None => false
        end           
    | isTenuren a m  =>
        let ss := Ssubstate s a in 
        let m' := SStenure ss in 
        match m' with 
        | Some m'' => m'' == m 
        | _ => false
        end
        
    end.



