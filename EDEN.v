Require Export GSM.

Context {citizen : finType}.
Context {admin : finType}.


Inductive Proposal  : Type :=
    (* 国庫・予算の入出金 *)
    | withdraw : admin -> currency -> Proposal 
    | deposit : admin -> currency -> Proposal 
    | transfer : admin -> admin -> currency -> Proposal
    (* 役職への任免・罷免 *)
    | assign : admin ->  citizen -> Proposal
    | dismissal : admin ->  citizen -> Proposal    
    (* 行政の追加・削除 *)
    | genAdmin : admin -> Proposal 
    | slashAdmin : admin -> Proposal.

Inductive Var :=
    (* substaeの持ち得る状態についての制約 *)
    | hasNoBudget : admin -> Var
    | hasNoComitee : admin -> Var
    (* 行政機関が熟議できる提案の制約 *)
    | isBudgetRestricted : admin -> Var
    | isTransferRestricted : admin -> Var
    | isAssignmentRestrected : admin -> admin -> Var
    | isadminControlRestricted : admin -> Var
    (* その他 *)
    | isAssigned : admin ->  citizen -> Var
    | isProposed : admin -> Proposal -> Var.

Definition env := Build_ENV  citizen admin Proposal Var.







#[local] Instance EtaSubtate : Settable substate :=
    settable! @Substate env <budgetSS; memberSS; comiteeSS>.
    
    
Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then Some r else (f d').

Notation "t ↦ b" := (subst t b)(at level 10).

Notation State := (@state env).
Notation Substate := (@substate env).
Notation Comitee := (@comitee env).
Notation Action := (@action env).





Definition Transp  (x : State) (p : Proposal) : State :=
    match p with 
    | withdraw t n => 
        match x t with
        | None => x 
        | Some ss => 
            let ss' := ss <|budgetSS ::= minus n|> in 
            (t ↦ ss') x 
        end 
    | deposit t n => 
        match x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <|budgetSS ::= plus n|> in 
            (t ↦ ss') x 
        end
    
    | transfer from to n => 
            let ss_from := x from in 
            let ss_to := x to in 
            match ss_from, ss_to with 
            | Some ss_from, Some ss_to => 
                let ss_from' := ss_from <|budgetSS ::= minus n|> in 
                let ss_to' := ss_to <|budgetSS ::= plus n|> in
                (from ↦ ss_from'  ((to ↦ ss_to') x))
            | _,_ => x
            end
   
    | assign t m => 
        match x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <| memberSS ::= fun mem => m |: mem |> in
            (t ↦ ss') x  
        end  
    | dismissal t m => 
        match x t with
        | None => x 
        | Some ss =>  
            let ss' := ss <| memberSS ::= fun mem => mem :\ m |> in
            (t ↦ ss') x
        end


  
    | genAdmin t => 
        match x t with
        | None => t ↦ empty_subState x
        | Some _ => x        
        end
    | slashAdmin t =>
        match x t with
        | None => x 
        | Some _ => fun t' => if t == t' then None else x t'
        end
    end.




Definition Valuation (s : State) (x : Var) : Prop :=
    match x with
    | hasNoBudget t => 
        match s t with 
        | None => True
        | Some ss => budgetSS ss =  0
        end 




    | hasNoComitee t =>
        match s t with 
        | None => True 
        | Some ss => 
            match comiteeSS ss with 
            | None => True 
            | _ => False 
            end 
        end
    

    | isBudgetRestricted t =>
            match s t with 
            | None => True 
            | Some ss =>
                match (comiteeSS ss) with 
                | None => True 
                | Some cmt => 
                    match (proposalC cmt) with 
                    | withdraw t' _ => t = t' 
                    | deposit t'  _ => t = t'
                    | _ => True
                    end
                end
            end
    
    | isTransferRestricted t =>
            match s t with 
            | None => True 
            | Some ss => 
                match (comiteeSS ss) with 
                | None => True 
                | Some dlb' => let prp := proposalC dlb' in
                    match prp with 
                    | transfer t' _ _ => t = t'  
                    | _ => True
                    end
                end
            end            

    | isAssignmentRestrected t t'=> 
        match s t with 
            | None => True 
            | Some ss => let dlb := comiteeSS ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := proposalC dlb' in
                    match prp with 
                    | assign  t'' _ => t' <> t''
                    | dismissal  t'' _ => t' <> t''
                    | _ => True
                    end
                end
            end

    | isadminControlRestricted t => 
        match s t with 
            | None => True 
            | Some ss => let dlb := comiteeSS ss
                in match dlb with 
                | None => True 
                | Some dlb' => let prp := proposalC dlb' in
                    match prp with 
                    | genAdmin _ => False
                    | slashAdmin _ => False
                    | _ => True
                    end
                end
            end
    
    | isAssigned a m => 
        match s a with 
        | None => False
        | Some ss =>
            let mem := memberSS ss in         
            m \in mem
        end

    | isProposed adm a => 
        match s adm with 
        | None => False
        | Some ss =>
            let dlb_ := comiteeSS ss in
            match dlb_ with 
            | Some  dlb =>  
                a = proposalC dlb
            | None => False
            end
        end 


    end.




Context {Deliberate : Comitee -> State -> bool}.
Definition eval := Build_Eval Deliberate  Transp Valuation.
Notation Trans := (@trans env eval).
Notation deliberate := (@deliberate env eval).
Notation transp := (@transp env eval).
Notation valuation := (@valuation env eval).

Theorem Tau_eq (s s': State) :
    Trans s tau s' <-> s = s'. 
Proof.
    simpl; split; auto.
Qed.  