From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export finset fintype ssrbool eqtype ssrnat fintype ssreflect.



Set Implicit Arguments.
Unset Strict Implicit.

Section GSM.


(******************** アクション・状態 ********************)


Definition currency := nat.
Context {citizen : finType}.
Context {admin : finType}.
Context {proposal : Type}.
Context {var : Type}.

Variant action :=
    | act_deliberate : admin -> proposal -> {set citizen} -> action
    | act_var : var -> action
    | tau : action.

Record substate := Substate {
    budget : currency;
    member : {set citizen};
}.

Definition state := admin -> option substate.            

Definition empty_subState := Substate 0 set0.



(******************** 状態遷移 ********************)


Context {deliberate : proposal -> {set citizen} -> bool}.
Context {transp : state -> proposal -> state}.
Context {valuation : state -> var -> Prop}.

Definition trans s a s' : Prop :=
    match a with 
    | act_deliberate adm prp cmt => 
        let ss := s adm in
        match ss with 
            | None =>  s = s'
            | Some ss' =>  
                let mem := member ss' in 
                if cmt \subset mem 
                    then if deliberate prp cmt
                        then s' = transp s prp
                        else s = s'
                    else s = s'
            end
    | act_var p => valuation s p /\ s = s'    
    | tau => s = s'
    end.

End GSM.


