Require Export GSM.
From mathcomp Require Import all_ssreflect.

Context {limit_time' : nat}.
Context {Now : @timestamp limit_time'}.
Context {Citizen : finType}.
Context {random_choice : forall {T : finType}, {set T} -> random -> T}.
Context {random_choice_set : forall {T : finType} (A : {set T}),random -> nat -> {set T}}.


Notation Timestamp := (@timestamp limit_time').
Notation Admin := admin.


Inductive Proposal  : Type :=
    (* 国庫・予算の入出金 *)
    | withdraw : Admin -> currency -> Proposal 
    | deposit : Admin -> currency -> Proposal 
    | transfer : Admin -> Admin -> currency -> Proposal
    (* 役職への任免・罷免 *)
    | assignMember : Admin -> Citizen -> Proposal
    | dismissalMember : Admin -> Citizen -> Proposal    
    | assignTenureWorker : Admin -> Citizen -> Timestamp -> Proposal    
    | dismissalTenureWorker : Admin -> Citizen -> Proposal
    (* 行政の追加・削除 *)
    | genAdmin : Admin -> Proposal 
    | slashAdmin : Admin -> Proposal.

Inductive Var :=
    (* substaeの持ち得る状態についての制約 *)
    | hasNoBudget : Admin -> Var
    | hasNoComitee : Admin -> Var
    | hasNoTenureWoker : Admin -> Var
    | hasNoMember : Admin -> Var
    (* 行政機関が熟議できる提案の制約 *)
    | isBudgetRestricted : Admin -> Var
    | isTransferRestricted : Admin -> Var
    | isAssignmentRestrected : Admin -> Admin -> Var
    | isAdminControlRestricted : Admin -> Var
    (* その他 *)
    | isAssigned : Admin -> Citizen -> Var
    | isProposed : Admin -> Proposal -> Var 
    | isTenureWorker : Admin -> Citizen -> Var
    | isWithinExpiration : Admin -> Citizen-> Var.

 Context {prop_dec : forall x y : Proposal, {x = y} + {x <> y}}.   
  
Notation Comitee := (@comitee Citizen Proposal).
Notation Substate := (@subState limit_time' Citizen Proposal).
Notation State := (@state limit_time' Citizen Proposal).
Context {evalD : Comitee -> bool}.

#[local] Instance EtaSubtate : Settable subState :=
    settable! @mkSubState limit_time' Citizen Proposal
        <SSbudget; SSmember; SScomitee; SStenureWorker>.        

#[local] Instance EtaState : Settable state := 
    settable! @mkState limit_time' Citizen Proposal 
        <Scomitee; Ssubstate >.


Notation "t ↦ b" := (subst t b)(at level 10).

Fixpoint findExpiration_ (p : seq (Citizen * Timestamp)) (c : Citizen) : option Timestamp :=
    match p with 
    | [::] => None
    | (m,n) :: p' => if c == m then Some n else findExpiration_ p' c 
    end.

Definition findExpiration (p : {set Citizen * Timestamp}) (c : Citizen) : option Timestamp :=
    findExpiration_ (enum p) c.




Definition transp  (x : State) (p : Proposal) : state :=
    match p with 
    | withdraw t n => 
        match Ssubstate x t with
        | None => x 
        | Some ss => 
            let ss' := ss <|SSbudget ::= minusc n|> in 
            x <| Ssubstate ::= t ↦ ss'|>  
        end 
    | deposit t n => 
        match Ssubstate x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <|SSbudget ::= plusc n|> in 
            x <| Ssubstate ::= t ↦ ss'|>  
        end
    
    | transfer from to n => 
            let ss_from := Ssubstate x from in 
            let ss_to := Ssubstate x to in 
            match ss_from, ss_to with 
            | Some ss_from, Some ss_to => 
                let ss_from' := ss_from <|SSbudget ::= minusc n|> in 
                let ss_to' := ss_to <|SSbudget ::= plusc n|> in 
                x <| Ssubstate ::= from ↦ ss_from'|> <|Ssubstate ::= to ↦ ss_to'|>
            | _,_ => x
            end


   
    | assignMember t m => 
        match Ssubstate x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
            x <| Ssubstate ::= t ↦ ss'|>   
        end  
    | dismissalMember t m => 
        match Ssubstate x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
            x <| Ssubstate ::= t ↦ ss'|>
        end


    | assignTenureWorker t m n =>        
        match Ssubstate x t with
        | None => x 
        | Some ss =>  
            let tws := SStenureWorker ss in 
            x  <| Ssubstate ::= t ↦ (ss <|SStenureWorker := (m,n) |: tws|>) |>
        end

    | dismissalTenureWorker t m => 
        match Ssubstate x t with
        | None => x 
        | Some ss =>  
            let tws := SStenureWorker ss in 
            let n := findExpiration tws m in 
            match n with 
            | None => x 
            | Some n' => x <| Ssubstate ::= t ↦ (ss <|SStenureWorker := tws :\ (m,n')|>) |>
            end
        end
    | genAdmin t => 
        match Ssubstate x t with
        | None => x <|Ssubstate ::= t ↦ empty_subState|>
        | Some _ => x        
        end
    | slashAdmin t =>
        match Ssubstate x t with
        | None => x 
        | Some _ => x <|Ssubstate ::= fun f => fun t' => if t' == t then None else f t'|>
        end
    end.




Definition valuation (s : State) (x : Var) : Prop :=
    match x with
    | hasNoBudget t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => True
        | Some ss => SSbudget ss = Curr 0
        end 
    | hasNoComitee t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => True
        | Some ss => SScomitee ss = None
        end
    | hasNoTenureWoker t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => True
        | Some ss => SStenureWorker ss = set0
        end
    | hasNoMember t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => True
        | Some ss => SSmember ss = set0
        end

    | isBudgetRestricted t =>
            let ss := Ssubstate s t in
            match ss with 
            | None => True 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | withdraw t' _ => t = t' 
                    | deposit t'  _ => t = t'
                    | _ => True
                    end
                end
            end
    
    | isTransferRestricted t =>
            let ss := Ssubstate s t in
            match ss with 
            | None => True 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | transfer t' _ _ => t = t'  
                    | _ => True
                    end
                end
            end            

    | isAssignmentRestrected t t'=> 
        let ss := Ssubstate s t in
            match ss with 
            | None => True 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | assignMember  t'' _ => t' <> t''
                    | dismissalMember  t'' _ => t' <> t''
                    | assignTenureWorker  t'' _ _ => t' <> t''
                    | dismissalTenureWorker  t'' _ => t' <> t''
                    | _ => True
                    end
                end
            end

    | isAdminControlRestricted t => 
        let ss := Ssubstate s t in
            match ss with 
            | None => True 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | genAdmin _ => False
                    | slashAdmin _ => False
                    | _ => True
                    end
                end
            end
    
    | isAssigned a m => 
        let ss := Ssubstate s a in
        match ss with 
        | None => False
        | Some ss =>
            let mem := SSmember ss in         
            m \in mem
        end

    | isProposed adm a => 
        let ss := Ssubstate s adm in
        match ss with 
        | None => False
        | Some ss =>
            let dlb_ := SScomitee ss in
            match dlb_ with 
            | Some  dlb =>  
                a = Dproposal dlb
            | None => False
            end
        end 

    | isTenureWorker t m  =>
        let ss := Ssubstate s t in
        match ss with 
        | None => False
        | Some ss =>
            let tws := SStenureWorker ss in 
            let n := findExpiration tws m in
            match n with 
            | Some _ => True 
            | _ => False
            end
        end

    | isWithinExpiration t m => 
        let ss := Ssubstate s t in
        match ss with 
        | None => False
        | Some ss =>
            let tws := SStenureWorker ss in 
            let tw := findExpiration tws m in
            match tw with 
            | None => False 
            | Some n => Now < n 
            end 
        end 
    end.


Notation Trans := (@trans limit_time' Citizen random_choice random_choice_set Proposal Var evalD transp valuation).
Notation Actioin := (@action Proposal Var).



















