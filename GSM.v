From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export finset fintype ssrbool eqtype ssrnat fintype ssreflect.


Set Implicit Arguments.
Unset Strict Implicit.


Definition currency := nat.

Record ENV := {
    citizen : finType;
    admin : finType;
    proposal : Type;
    var : Type;
    
}.

    
Section action.


Context {env : ENV}.

Notation citizen := (citizen env).
Notation admin := (admin env).
Notation proposal := (proposal env).
Notation var := (var env).

Variant action :=
    | act_propose : admin -> proposal -> {set citizen} -> action
    | act_deliberate : admin -> action
    | act_var : var -> action
    | tau : action.

Record comitee := Comitee {
    proposalC : proposal;
    memberC : {set citizen};
}.


Record substate := Substate {
    budgetSS : currency;
    memberSS : {set citizen};
    comiteeSS : option comitee;
}.
    
Definition state := admin -> option substate.            
        
Definition empty_subState := Substate 0 set0 None.

#[local] Instance EtaSubtate : Settable substate :=
    settable! Substate  <budgetSS; memberSS; comiteeSS>.



Record Eval := {
    deliberate : comitee -> state -> bool;
    transp : state -> proposal -> state;
    valuation : state -> var -> Prop;
}.

Section Eval.

Context {eval : Eval}.

Notation Deliberate := (deliberate eval).
Notation Transp := (transp eval).
Notation Valuation := (valuation eval).

Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then Some r else (f d').

Notation "t ↦ b" := (subst t b)(at level 10).



Definition trans s a s' : Prop :=
    match a with 
    | act_propose adm prp cmt => 
        let ss := s adm in
        match ss with 
            | None =>  s = s'
            | Some ss' =>  
                let ss'' := ss' <|comiteeSS := Some (Comitee prp cmt)|> in 
                s' = (adm ↦ ss'') s
            end
    | act_deliberate adm => 
        let ss := s adm in
        match ss with 
            | None =>  s = s'
            | Some ss' =>  
                match comiteeSS ss' with 
                | None => s = s' 
                | Some cmt =>  
                    if (memberC cmt) \subset (memberSS ss')
                        then if Deliberate cmt s
                            then s' = Transp s (proposalC cmt)
                            else s = s'
                        else s = s'
                end
            end
    | act_var p => Valuation s p /\ s = s'    
    | tau => s = s'
    end.

End Eval.
End action.


