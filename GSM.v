From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
From mathcomp Require Export all_ssreflect.
Require Export Currency Administration Timestamp.



Set Implicit Arguments.
Unset Strict Implicit.

(********************)
(* メタ・アサンプション *)
(********************)


(* 市民 *)
Parameter citizen : finType.

(* 現在時刻を返す関数 *)
Parameter now : timestamp.

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
    | PasignTenureWorker : admin -> citizen -> timestamp -> proposal    
    | PdismissalTenureWorker : admin -> citizen -> proposal
    (* 市民登録・解除 *)
    | Pregisrate : citizen -> proposal
    | Pderegisrate : citizen -> proposal.



Inductive act :=
    | AsubPropose : admin -> proposal -> random -> random -> random -> nat -> act
    | AglobalPropose : proposal -> random -> random -> random -> nat -> act
    | AsubDeliberate : admin -> act
    | AglobalDeliberate : act.



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
    SStenureWorker : {set citizen * timestamp};
}.


Record state := mkState{
    Streasury : currency;
    Smember : {set citizen};
    Sdeliberation : option deliberation;
    Ssubstate : admin -> subState
}.

(*************************************)
(* updatable recortd's instantiation *)
(*************************************)

Instance etaSubState : Settable subState :=
    settable! mkSubState <SSbudget; SSmember; SSdeliberation; SStenureWorker>.        

Instance etaState : Settable state := 
    settable! mkState 
        < Streasury; Smember; Sdeliberation;Ssubstate >.


(**************************)
(* eqType's instantiation *)
(**************************)

Tactic Notation "mkCompEq"  :=
    refine (EqMixin (compareP _)) => x y;
    unfold decidable; decide equality; apply eq_comparable.
Notation eqMixin := Equality.mixin_of.


Definition proposal_eqMixin : eqMixin proposal. Proof. mkCompEq. Qed.
Canonical Structure proposal_eqType := Eval hnf in @EqType proposal proposal_eqMixin.


Definition deliberation_eqMixin  : eqMixin deliberation. Proof. mkCompEq. Qed.
Canonical Structure deliberation_eqType := Eval hnf in @EqType deliberation deliberation_eqMixin.        

Definition subState_eqMixin : eqMixin subState. Proof. 
    refine (EqMixin (compareP _)) => x y.
    unfold decidable; decide equality; apply eq_comparable.
Qed.
Canonical Structure subState_eqType := Eval hnf in @EqType subState subState_eqMixin.



(**********)
(* 状態遷移 *)
(**********)


Definition subst {dom : eqType} {ran} (d : dom) (r : ran) := 
    fun f => fun d' =>  if d == d' then r else f d'.
Notation "t ↦ b" := (subst t b)(at level 10).


Lemma subst_lemma {dom ran : finType} (f : dom -> ran) (d : dom) (r : ran) :
    let f' := subst d r f in f' d = r.
Proof. rewrite /subst eq_refl => //. Qed.

Fixpoint findExpiration_ (p : seq (citizen * timestamp)) (c : citizen) : option timestamp :=
    match p with 
    | [::] => None
    | (m,n) :: p' => if c == m then Some n else findExpiration_ p' c 
    end.

Definition findExpiration (p : {set citizen * timestamp}) (c : citizen) : option timestamp :=
    findExpiration_ (enum p) c.


Parameter evalD : deliberation -> bool.  


Definition transv_  (p : proposal) (x : state)  :=
    match p with 
    | PwithdrawTreasury n => x <| Streasury ::= subc n|>
    | PdepositTreasury n => x <| Streasury ::= addc n|>
    | PwithdrawBudget t n => 
        let ss := Ssubstate x t in 
        let ss' := ss <|SSbudget ::= subc n|> in 
        x <| Ssubstate ::= t ↦ ss'|>   
    | PdepositBudget t n => 
        let ss := Ssubstate x t in 
        let ss' := ss <|SSbudget ::= addc n|> in 
        x <| Ssubstate ::= t ↦ ss'|>      
    | Pallocate t n => 
        let ss := Ssubstate x t in 
        let ss' := ss <|SSbudget ::= subc n|> in 
        x  <| Ssubstate ::= t ↦ ss'|> <| Streasury ::= subc n|>
   
    | PassignMember t m => 
        let ss := Ssubstate x t in 
        let ss' := ss <| SSmember ::= fun mem => m |: mem |> in
        x <| Ssubstate ::= t ↦ ss'|>     
    | PdismissalMember t m => 
        let ss := Ssubstate x t in 
        let ss' := ss <| SSmember ::= fun mem => mem :\ m |> in
        x <| Ssubstate ::= t ↦ ss'|>
    | PasignTenureWorker t m n =>
        let tw := (m,n) in 
        let ss := Ssubstate x t in 
        let tws := SStenureWorker ss in 
        x  <| Ssubstate ::= t ↦ (ss <|SStenureWorker := tw |: tws|>) |>

    | PdismissalTenureWorker t m => 
        let ss := Ssubstate x t in 
        let tws := SStenureWorker ss in 
        let n := findExpiration tws m in 
        match n with 
        | None => x 
        | Some n' => x <| Ssubstate ::= t ↦ (ss <|SStenureWorker := tws :\ (m,n')|>) |>
        end
    | Pregisrate m => x <| Smember ::= fun mem => m |: mem|>
    | Pderegisrate m => x <| Smember ::= fun mem => mem :\ m|>
    end.




Definition trans_ (a : act) (x : state) :=
    match a with 
    | AsubPropose adm a' p_ f_ d_ n => 
        let ss := Ssubstate x adm in   
        let mem := SSmember ss in 
        let p := random_choice mem p_ in 
        let f := random_choice mem f_ in 
        let d := random_choice_set mem d_ n in 
        let ss' := ss <|SSdeliberation := Some (mkDlb a' p f d)|> in 
        x <| Ssubstate ::= adm ↦ ss'|>

    | AsubDeliberate adm => 
        let ss := Ssubstate x adm in
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some dlb =>  
            if evalD dlb then transv_ (Dproposal dlb) x else x
        | None => x
        end

    | AglobalPropose a' p_ f_ d_ n =>
        let mem := Smember x in
        let p := random_choice mem p_ in 
        let f := random_choice mem f_ in 
        let d := random_choice_set mem d_ n in 
        x <|Sdeliberation := Some (mkDlb a' p f d)|>

    | AglobalDeliberate => 
        let dlb := Sdeliberation x in 
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
    | hasNoDeliberation : admin -> var
    | hasNoTenureWoker : admin -> var
    (* 熟議できる提案の制限 *)
    | treasuryRestriction : admin -> var 
    | budgetRestriction : admin -> var
    | allocateRestriction : admin -> var
    | assignRestriction : admin -> var
    | regisrateRestriction : admin -> var

    | isAssigned : admin -> citizen -> var
    | isProposed : admin -> proposal -> var 
    | isTenureWorker : admin -> citizen -> var
    | withinExpiration : admin -> citizen-> var  
    | isValidDeliberation : admin -> admin -> admin -> var.



Definition valuation (x : var) (s : state) : bool :=
    match x with
    | hasNoBudget t => let ss := Ssubstate s t in SSbudget ss == noCurr
    | hasNoDeliberation t => let ss := Ssubstate s t in SSdeliberation ss == None
    | hasNoTenureWoker t => let ss := Ssubstate s t in SStenureWorker ss == set0
    | treasuryRestriction t =>
            let dlb := SSdeliberation (Ssubstate s t) 
            in match dlb with 
            | None => true 
            | Some dlb' => let prp := Dproposal dlb' in
                match prp with 
                | PwithdrawTreasury  _ => false 
                | PdepositTreasury _ => false  
                | _ => false
                end
            end
    | budgetRestriction t =>
            let dlb := SSdeliberation (Ssubstate s t) 
            in match dlb with 
            | None => true 
            | Some dlb' => let prp := Dproposal dlb' in
                match prp with 
                | PwithdrawBudget t' _ => t == t' 
                | PdepositBudget t'  _ => t == t'  
                | _ => true
                end
            end
    | allocateRestriction t =>
            let dlb := SSdeliberation (Ssubstate s t) 
            in match dlb with 
            | None => true 
            | Some dlb' => let prp := Dproposal dlb' in
                match prp with 
                | Pallocate _ _ => false
                | _ => true
                end
            end
    | assignRestriction t => 
        let dlb := SSdeliberation (Ssubstate s t) 
            in match dlb with 
            | None => true 
            | Some dlb' => let prp := Dproposal dlb' in
                match prp with 
                | PassignMember  _ _ => false
                | PdismissalMember  _ _ => false
                | PasignTenureWorker  _ _ _ => false
                | PdismissalTenureWorker  _ _ => false
                | _ => true
                end
            end
    | regisrateRestriction t => 
        let dlb := SSdeliberation (Ssubstate s t) 
            in match dlb with 
            | None => true 
            | Some dlb' => let prp := Dproposal dlb' in
                match prp with 
                | Pregisrate _ => false
                | Pderegisrate _ => false
                | _ => true
                end
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
    | isTenureWorker t m  =>
        let ss := Ssubstate s t in 
        let tws := SStenureWorker ss in 
        let n := findExpiration tws m in
        match n with 
        | Some _ => true 
        | _ => false
        end
    | withinExpiration t m => 
        let ss := Ssubstate s t in 
        let tws := SStenureWorker ss in 
        let tw := findExpiration tws m in
        match tw with 
        | None => false 
        | Some n => now < n 
        end 
    | isValidDeliberation a ps fs => 
        let ss := Ssubstate s a in 
        let pf := SSmember (Ssubstate s ps) in 
        let fc := SSmember (Ssubstate s fs) in 
        let dlb_ := SSdeliberation ss in
        match dlb_ with 
        | Some  dlb =>  
            (Dprofessional dlb \in pf) && 
            (Dfacilitator dlb \in fc) &&
            (Ddeliberator dlb != set0)
        | None => false
        end           
    end.



