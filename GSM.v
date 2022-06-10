


From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(********************)
(* メタ・アサンプション *)
(********************)


(* finTypeのtimestamp *)
Parameter limit_time' : nat.
Definition limit_time := limit_time' + 1.
Definition timestamp := ordinal limit_time.
Parameter now : timestamp.

(* 各行政機関を表す変数 *)
Inductive admin := Admin of nat.

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
Parameter citizen : finType.


(* 乱数 *)
Definition random := Type.

(* 乱数と集合をとり、ランダムに要素を抽出する関数 *)
Parameter random_choice : forall {T : finType}, {set T} -> random -> T.
Axiom random_choice_axiom : forall (T : finType) r (A : {set T}), 
    random_choice A r \in A.

(* 乱数と集合をとり、任意の大きさの部分集合を返す関数 *)
(* この公理は、#|A| < n の時に矛盾が生じるので要修正 *)
Parameter random_choice_set : forall {T : finType} (A : {set T}),random -> nat -> {set T}.
Axiom random_choice_set_axiom : forall {T : finType} r (A : {set T}) n,
    let B := @random_choice_set T A r n in 
    (B \subset A) && (#|B| == n).




(************)
(* アクション *)
(************)

Inductive proposal  :=
    (* 国庫・予算の入出金 *)
    | PwithdrawTreasury : currency -> proposal
    | PdepositTreasury : currency -> proposal
    | PwithdrawBudget : admin -> currency -> proposal 
    | PdepositBudget : admin -> currency -> proposal 
    | Pallocate : admin -> currency -> proposal
    (* 役職への任免・罷免 *)
    | PassignMember : admin -> citizen -> proposal
    | PdismissalMember : admin -> citizen -> proposal    
    | PassignTenureWorker : admin -> citizen -> timestamp -> proposal    
    | PdismissalTenureWorker : admin -> citizen -> proposal
    (* 市民登録・解除 *)
    | Pregister : citizen -> proposal
    | Pderegister : citizen -> proposal
    (* 行政の追加・削除 *)
    | PgenAdmin : admin -> proposal 
    | PslashAdmin : admin -> proposal.



Inductive act :=
    | AsubPropose : admin -> proposal -> random -> random -> random -> nat -> act
    | AglobalPropose : proposal -> random -> random -> random -> nat -> act
    | AsubDeliberate : admin -> act
    | AglobalDeliberate : act.



(************) 
(* 状態と熟議 *)
(************)

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
    Streasury : currency;
    Smember : {set citizen};
    Scomitee : option comitee;
    Ssubstate : admin -> option subState
}.

(*************************************)
(* updatable recortd's instantiation *)
(*************************************)

Instance etaSubState : Settable subState :=
    settable! mkSubState <SSbudget; SSmember; SScomitee; SStenureWorker>.        

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Smember; Scomitee;Ssubstate >.


(**************************)
(* eqType's instantiation *)
(**************************)

Coercion nat_of_admin a := let : Admin n := a in n.
Canonical admin_subType  := [newType for nat_of_admin ].
Definition admin_eqMixin := Eval hnf in [eqMixin of admin by <:].
Canonical admin_eqType := Eval hnf in EqType admin admin_eqMixin.

Coercion nat_of_currency a := let : Curr n := a in n.
Canonical currency_subType  := [newType for nat_of_currency ].
Definition currency_eqMixin := Eval hnf in [eqMixin of currency by <:].
Canonical currency_eqType := Eval hnf in EqType currency currency_eqMixin.

Tactic Notation "mkCompEq"  :=
    refine (EqMixin (compareP _)) => x y;
    unfold decidable; decide equality; apply eq_comparable.
Notation eqMixin := Equality.mixin_of.


Definition proposal_eqMixin : eqMixin proposal. Proof. mkCompEq. Qed.
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.


Definition comitee_eqMixin  : eqMixin comitee. Proof. mkCompEq. Qed.
Canonical Structure comitee_eqType := Eval hnf in @EqType comitee comitee_eqMixin.        

Definition subState_eqMixin : eqMixin subState. Proof. 
    refine (EqMixin (compareP _)) => x y.
    unfold decidable; decide equality; apply eq_comparable.
Qed.
Canonical Structure subState_eqType := Eval hnf in @EqType subState subState_eqMixin.



(**********)
(* 状態遷移 *)
(**********)


Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then Some r else (f d').
Notation "t ↦ b" := (subst t b)(at level 10).


Lemma subst_lemma {dom ran : finType} (f : dom -> option ran) (d : dom) (r : ran) :
    let f' := subst d r f in f' d = Some r.
Proof. rewrite /subst eq_refl => //. Qed.

Fixpoint findExpiration_ (p : seq (citizen * timestamp)) (c : citizen) : option timestamp :=
    match p with 
    | [::] => None
    | (m,n) :: p' => if c == m then Some n else findExpiration_ p' c 
    end.

Definition findExpiration (p : {set citizen * timestamp}) (c : citizen) : option timestamp :=
    findExpiration_ (enum p) c.


Parameter evalD : comitee -> bool.  


Definition transv_  (p : proposal) (x : state)  :=
    match p with 
    | PwithdrawTreasury n => x <| Streasury ::= minusc n|>
    | PdepositTreasury n => x <| Streasury ::= plusc n|>
    | PwithdrawBudget t n => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss => 
            let ss' := ss <|SSbudget ::= minusc n|> in 
            x <| Ssubstate ::= t ↦ ss'|>  
        end 
    | PdepositBudget t n => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let ss' := ss <|SSbudget ::= plusc n|> in 
            x <| Ssubstate ::= t ↦ ss'|>  
        end    
    | Pallocate t n => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let ss' := ss <|SSbudget ::= minusc n|> in 
            x  <| Ssubstate ::= t ↦ ss'|> <| Streasury ::= minusc n|>
        end
   
    | PassignMember t m => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
            x <| Ssubstate ::= t ↦ ss'|>   
        end  
    | PdismissalMember t m => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
            x <| Ssubstate ::= t ↦ ss'|>
        end
    | PassignTenureWorker t m n =>
        let tw := (m,n) in 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let tws := SStenureWorker ss in 
            x  <| Ssubstate ::= t ↦ (ss <|SStenureWorker := tw |: tws|>) |>
        end

    | PdismissalTenureWorker t m => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some ss =>  
            let tws := SStenureWorker ss in 
            let n := findExpiration tws m in 
            match n with 
            | None => x 
            | Some n' => x <| Ssubstate ::= t ↦ (ss <|SStenureWorker := tws :\ (m,n')|>) |>
            end
        end
    | Pregister m => x <| Smember ::= fun mem => m |: mem|>
    | Pderegister m => x <| Smember ::= fun mem => mem :\ m|>
    | PgenAdmin t => 
        let ss := Ssubstate x t in 
        match ss with 
        | None => x <|Ssubstate ::= t ↦ empty_subState|>
        | Some _ => x        
        end
    | PslashAdmin t =>
        let ss := Ssubstate x t in 
        match ss with 
        | None => x 
        | Some _ => x <|Ssubstate ::= fun f => fun t' => if t' == t then None else f t'|>
        end

    end.




Definition trans_ (a : act) (x : state) :=
    match a with 
    | AsubPropose adm a' p_ f_ d_ n => 
        let ss := Ssubstate x adm in  
        match ss with 
        | None => x 
        | Some ss =>  
            let mem := SSmember ss in 
            let p := random_choice mem p_ in 
            let f := random_choice mem f_ in 
            let d := random_choice_set mem d_ n in 
            let ss' := ss <|SScomitee := Some (mkDlb a' p f d)|> in 
            x <| Ssubstate ::= adm ↦ ss'|>
        end

    | AsubDeliberate adm => 
        let ss := Ssubstate x adm in
        match ss with 
        | None => x 
        | Some ss => 
            let dlb_ := SScomitee ss in
            match dlb_ with 
            | Some dlb =>  
                if evalD dlb then transv_ (Dproposal dlb) x else x
            | None => x
            end
        end

    | AglobalPropose a' p_ f_ d_ n =>
        let mem := Smember x in
        let p := random_choice mem p_ in 
        let f := random_choice mem f_ in 
        let d := random_choice_set mem d_ n in 
        x <|Scomitee := Some (mkDlb a' p f d)|>

    | AglobalDeliberate => 
        let dlb := Scomitee x in 
        match dlb with 
        | None => x 
        | Some dlb_ => 
            if evalD dlb_ then transv_ (Dproposal dlb_) x else x 
        end
    end.

Definition trans a x y := y = trans_ a x.

(***********)
(* 原子命題 *)
(***********)

Inductive var :=
    (* substaeの状態の制限 *)
    | hasNoBudget : admin -> var
    | hasNoComitee : admin -> var
    | hasNoTenureWoker : admin -> var
    | hasNoMember : admin -> var
    (* 行政機関が熟議できる提案の制限 *)
    | treasuryRestriction : admin -> var 
    | budgetRestriction : admin -> var
    | allocateRestriction : admin -> var
    | assignRestriction : admin -> var
    | registerRestriction : admin -> var
    | adminControlRestriction : admin -> var
    (* globalStateに課す制約 *)
    (* より汎用的に表現できるようにしたいけど、
    ひとまずregisterとbudgetについての制約 *)
    | globalRestriction : var

    | isAssigned : admin -> citizen -> var
    | isProposed : admin -> proposal -> var 
    | isTenureWorker : admin -> citizen -> var
    | withinExpiration : admin -> citizen-> var  
    | isValidComitee : admin -> admin -> admin -> var.

Locate "<?".



Definition valuation (x : var) (s : state) : bool :=
    match x with
    | hasNoBudget t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss => SSbudget ss == Curr 0
        end 
    | hasNoComitee t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss => SScomitee ss == None
        end
    | hasNoTenureWoker t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss => SStenureWorker ss == set0
        end
    | hasNoMember t => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss => SSmember ss == set0
        end
    | treasuryRestriction t =>
            let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | PwithdrawTreasury  _ => false 
                    | PdepositTreasury _ => false  
                    | _ => false
                    end
                end
            end
    | budgetRestriction t =>
            let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | PwithdrawBudget t' _ => t == t' 
                    | PdepositBudget t'  _ => t == t'  
                    | _ => true
                    end
                end
            end
    | allocateRestriction t =>
            let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | Pallocate _ _ => false
                    | _ => true
                    end
                end
            end
    | assignRestriction t => 
        let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | PassignMember  _ _ => false
                    | PdismissalMember  _ _ => false
                    | PassignTenureWorker  _ _ _ => false
                    | PdismissalTenureWorker  _ _ => false
                    | _ => true
                    end
                end
            end
    | registerRestriction t => 
        let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | Pregister _ => false
                    | Pderegister _ => false
                    | _ => true
                    end
                end
            end
    | adminControlRestriction t => 
        let ss := Ssubstate s t in
            match ss with 
            | None => true 
            | Some ss => let dlb := SScomitee ss
                in match dlb with 
                | None => true 
                | Some dlb' => let prp := Dproposal dlb' in
                    match prp with 
                    | PgenAdmin _ => false
                    | PslashAdmin _ => false
                    | _ => true
                    end
                end
            end
    | globalRestriction =>
        let dlb := Scomitee s in
        match dlb with 
        | None => true 
        | Some dlb => let prp := Dproposal dlb in 
            match prp with 
            | Pregister  _ => false 
            | Pderegister _ => false 
            | PwithdrawBudget _ _ => false 
            | PdepositBudget  _ _ => false
            | _ => true 
            end 
        end
    
    
    | isAssigned a m => 
        let ss := Ssubstate s a in
        match ss with 
        | None => true
        | Some ss =>
            let mem := SSmember ss in         
            m \in mem
        end
    | isProposed adm a => 
        let ss := Ssubstate s adm in
        match ss with 
        | None => true
        | Some ss =>
            let dlb_ := SScomitee ss in
            match dlb_ with 
            | Some  dlb =>  
                a == Dproposal dlb
            | None => false
            end
        end 
    | isTenureWorker t m  =>
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss =>
            let tws := SStenureWorker ss in 
            let n := findExpiration tws m in
            match n with 
            | Some _ => true 
            | _ => false
            end
        end
    | withinExpiration t m => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss =>
            let tws := SStenureWorker ss in 
            let tw := findExpiration tws m in
            match tw with 
            | None => false 
            | Some n => now < n 
            end 
        end
    | isValidComitee t ps fs => 
        let ss := Ssubstate s t in
        match ss with 
        | None => true
        | Some ss =>
            let ssp := Ssubstate s ps in 
            let ssf := Ssubstate s fs in 
            match ssp, ssf with 
            | Some ssp, Some ssf => 
                let pf := SStenureWorker ssp in 
                let fc := SStenureWorker ssf in 
                let dlb_ := SScomitee ss in
                match dlb_ with 
                | Some  dlb =>  
                    [exists n,  (Dprofessional dlb, n) \in pf] && 
                    [exists n, (Dfacilitator dlb, n) \in fc] &&
                    (Ddeliberator dlb != set0)
                | None => false
                end     
            | _ , _ => false 
            end 
        end     
    end.
