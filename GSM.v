From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section GSM.

(******************** 前提 ********************)

(* finTypeのtimestamp *)
Context {limit_time' : nat}.
Definition limit_time := limit_time' + 1.
Definition timestamp := ordinal limit_time.
Context {now : timestamp}.

(* 各行政機関を表す変数 *)
Inductive admin := Adm of nat.

(* 通貨 *)
Inductive currency := Curr of nat.

Definition plusc (x y : currency) :=
    match x, y with 
    | Curr x_, Curr y_ => Curr (x_ + y_)
    end.
    
Definition minusc (x y : currency) :=
    match x, y with 
    | Curr x_, Curr y_ => Curr (x_ - y_)
    end.   


(* 市民 *)
Context {citizen : finType}.

(* 乱数 *)
Definition random := Type.

(* 乱数と集合をとり、ランダムに要素を抽出する関数 *)
Context {random_choice : forall {T : finType}, {set T} -> random -> T}.
Axiom random_choice_axiom : forall (T : finType) r (A : {set T}), 
    random_choice A r \in A.

(* 乱数と集合をとり、任意の大きさの部分集合を返す関数 *)
(* この公理は、#|A| < n の時に矛盾が生じるので要修正 *)
Context {random_choice_set : forall {T : finType} (A : {set T}),random -> nat -> {set T}}.
Axiom random_choice_set_axiom : forall {T : finType} r (A : {set T}) n,
    let B := @random_choice_set T A r n in 
    (B \subset A) && (#|B| == n).

Context {proposal : Type}.
Context {var : Type}.
Context {prop_dec : forall x y : proposal, {x = y} + {x <> y}}.

(******************** アクション・状態 ********************)

Inductive action :=
    | act_proposal : admin -> proposal -> random -> random -> random -> nat -> action
    | act_deliberate : admin -> action
    | act_var : var -> action
    | tau : action.


    Record comitee := mkDlb{
    Dproposal : proposal;
    Dprofessional : citizen;
    Dfacilitator : citizen;
    Ddeliberator : {set citizen};
}.

Record subState := mkSubState {
    SSbudget : currency;
    SSmember : {set citizen};
    SScomitee : option comitee;
    SStenureWorker : {set citizen * timestamp};
}.

Definition empty_subState := mkSubState (Curr 0) set0 None set0.


Record state := mkState{
    Scomitee : option comitee;
    Ssubstate : admin -> option subState
}.


(******************** インスタンス化 ********************)


Instance etaSubState : Settable subState :=
    settable! mkSubState <SSbudget; SSmember; SScomitee; SStenureWorker>.        

Instance etaState : Settable state := 
    settable! mkState 
        < Scomitee;Ssubstate >.


Coercion nat_of_admin a := let : Adm n := a in n.
Canonical admin_subType  := [newType for nat_of_admin ].
Definition admin_eqMixin := Eval hnf in [eqMixin of admin by <:].
Canonical admin_eqType := Eval hnf in EqType admin admin_eqMixin.

(******************** 状態遷移 ********************)


Context {evalD : comitee -> bool}.
Context {transp : state -> proposal -> state}.
Context {valuation : state -> var -> Prop}.

Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then Some r else (f d').

Notation "t ↦ b" := (subst t b)(at level 10).


Definition trans s a s' : Prop :=
    match a with 
    | act_proposal adm prop p_ f_ d_ n => 
        let ss := Ssubstate s adm in
        match ss with 
            | None =>  s = s'
            | Some ss' =>  
                let mem := SSmember ss' in 
                let p := random_choice mem p_ in 
                let f := random_choice mem f_ in 
                let d := random_choice_set mem d_ n in 
                let ss'' := ss' <|SScomitee := Some (mkDlb prop p f d)|> in 
                s' = s <| Ssubstate ::= adm ↦ ss''|>
            end

    | act_deliberate adm =>
        let ss := Ssubstate s adm in
        match ss with 
        | None => s = s'
        | Some ss => 
            let dlb_ := SScomitee ss in
            match dlb_ with 
            | Some dlb =>                 
                if evalD dlb 
                    then  s' = transp s (Dproposal dlb) 
                    else  s = s'
            | None => s = s'
            end 
        end
    | act_var p => valuation s p /\ s = s'    
    | tau => s = s'
    end.
    End GSM.
