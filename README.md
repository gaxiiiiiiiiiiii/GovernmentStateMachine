# 概要
このプロジェクトは、熟議民主制による政体をCoqにより形式化し、その性質を証明する事を目的としている。また、政体の諸性質を証明可能な命題として表現する為に、様相論理を用いている。


# 論理体系
様相論理とは、一般的な命題論理を拡張して、状態遷移の表現も可能にした論理体系の総称である。本プロジェクトでは様相論理のうち、PDL（propositional Dynamic logic）とCTL(computational tree logic）のシンタックスを用いており、それらの前提となる状態機械としてLTS（labeled transition system）を採用している。
## LTS
LTSとは、アクションによりラベル付けされた、状態遷移を意味する二項関係の集合である。アクションの集合Aと状態の集合Sが与えられた時、`→ ⊆ S × A × S`となる集合→を、LTSとする。すなわち、`a ∈ A` と `s,s’ ∈ S`に対して、`(s, a, s’) ∈ →` となる時、状態sがアクションaにより状態s’に遷移し得る事を意味する。
以下、PDLとCTLにおける状態遷移は、LTSによって定義されているものとする。
## PDL
PDLとは、一般的な命題論理に必然性・可能性を意味する演算子を加えた論理体系である。アクション`a ∈ A`と論理命題Pに対して、`[a]P`と`<a>P`がそれぞれ必然性と可能性を表す。各命題の直感的な意味は以下の通りである。
```
状態sにおいて[a]Pが成り立つ事は、
sからaを行使した後のいかなる状態でもPが成り立つ事を意味する。
```
```
状態sにおいて<a>Pが成り立つ事は、
sからaを行使した後でもPが成り立つ状態が存在する。
```
## CTL
CTLとは、一般的な命題論理を拡張し、状態遷移を木構造とみなした時のパスの特性を表現可能にした論理体系である。本プロジェクトでは、演算子`AG`と`AF`を主に使うので、その直感的な意味をここに記す。
```
状態sにおいてAG Pが成り立つ事は、
sから始まるいかなる状態遷移のパス上でPが成り立つ事を意味する。
```
```
状態sにおいてEF Pが成り立つ事は、
sから始まって且つ最終的にPが成り立つ状態遷移のパスが存在する事を意味する。
```

# GSM
熟議民主制の政体を形式化したLTSをGMS（Government State Machine）と呼ぶ。グローバルステートが各行政機関を状態として持つ入れ子構造となっている。アクションは提案と熟議の実行のみであり、熟議で可決された提案のみが状態遷移を起こす。また、comiteeを引数に取りboolを返す関数の存在を仮定して、それに熟議の採否を担わせている。

各行政は変数にて識別できるのみで、GMSだけでは特定の行政（例えば市民登録を担う機関）を表現できない。そこで、命題変数を用いて各行政個別に制約を課せる仕様となっている。

# state

```Coq
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
```

## state
政体全体を表す状態。グローバルステート。
+ Streasury
    
    国庫。

+ Smember
    
    市民。
+ Scomitee

    熟議。提案がなされていない場合、Noneを返す。    
+ Ssubstate

    行政。adminは各行政機関（substate）を表す変数である。変数への割り当てがない場合、Noneを返す。

## substate
各行政機関を表す状態。
+ SSbudget

    予算。
+ SSmember

    行政の構成員。
+ comitee

     熟議。提案がなされていない場合、Noneを返す。
+ SStenureWorker

    任期付きの役職。該当する役職がない場合、空集合を返す。
## comitee
熟議を表す状態
+ Dproposal

    提案内容。
+ Dprofessional

    専門家。特定のtenureWorkerから選出されるよう、命題変数で制約を課す想定。
+ Dfacilitator

    ファシリテーター。特定のtenureWorkerから選出されるよう、命題変数で制約を課す想定。    
    
+ Ddeliberator

    熟議を行う審議員

# act
PDLの必然性・可能性命題の引数となるアクション。具体的な状態遷移は、transv_とtrans_にて定義されている。
```Coq
Inductive proposal  :=
    | PwithdrawTreasury : currency -> proposal
    | PdepositTreasury : currency -> proposal
    | PwithdrawBudget : admin -> currency -> proposal 
    | PdepositBudget : admin -> currency -> proposal 
    | Pallocate : admin -> currency -> proposal
    | PassignMember : admin -> citizen -> proposal
    | PdismissalMember : admin -> citizen -> proposal    
    | PassignTenureWorker : admin -> citizen -> timestamp -> proposal    
    | PdismissalTenureWorker : admin -> citizen -> proposal
    | Pregister : citizen -> proposal
    | Pderegister : citizen -> proposal
    | PgenAdmin : admin -> proposal 
    | PslashAdmin : admin -> proposal.



Inductive act :=
    | AglobalPropose : proposal -> random -> random -> random -> nat -> act    
    | AglobalDeliberate : act
    | AsubPropose : admin -> proposal -> random -> random -> random -> nat -> act
    | AsubDeliberate : admin -> act.
```
## proposal
stateの状態遷移についての提案
+ PwithdrawTreasury n

    国庫にcurrencyをnだけ入金する
+ PdepositTreasury n

    国庫からcurrencyをnだけ引き出す
+ PwithdrawBudget a n

    行政aの予算に、currencyをnだけ預ける
+ PdepositBudget

    行政aの予算から、currencyをnだけ引き出す
+ Pallocate a n 

    国庫から行政aに、currencyをnだけ分配する
+ PassignMember a m 

    市民mを行政aの構成員に任命する
+ PdismissalMember a m 

    市民mを行政mの構成員から罷免する
+ PassignTenureWorker a m t 

    市民mを行政aのTenureWokerに任期をtとして任命する
+ PdismissalTenureWorker a m

    市民mを行政mのTenureWokerから罷免する
+ Pregister m 

    市民mを政体の構成員として登録する
+ Pderegister m 

    市民mを政体の構成員から外す
+ PgenAdmin a 

    行政aを登録する。実際的には、stateの関数Ssubstateにおいて、変数aがSome empty_sbustateを返すように実装している。
+ PslashAdmin a

    行政aを削除する。実際的には、stateの関数Ssubstateにおいて、変数aがNoneを返すように実装している。

## act
直接stateに働きかけるアクション
+ AglobalPropose : proposal -> random -> random -> random -> nat -> act    

    グローバルステートへの提案。提案内容と、専門家・ファシリテーター・審議員を選出する為の乱数、及び審議員の人数を引数に取る。
+ AglobalDeliberate : act

    グローバルステートの熟議の実行
+ AsubPropose

    各行政機関への提案。提案先の行政、提案内容、専門家・ファシリテーター・審議員を選出する為の乱数、及び審議員の人数を引数に取る。
+ AsubDeliberate

    行政機関での熟議の実行

# var
上述の論理体系において、論理式を構成する最小単位。書く状態の性質を表現する命題変数である。具体的な真偽判定はvaluationで定義されている。
```Coq
Inductive var :=
    | hasNoBudget : admin -> var
    | hasNoComitee : admin -> var
    | hasNoTenureWoker : admin -> var
    | hasNoMember : admin -> var
    | treasuryRestriction : admin -> var 
    | budgetRestriction : admin -> var
    | allocateRestriction : admin -> var
    | assignRestriction : admin -> var
    | registerRestriction : admin -> var
    | adminControlRestriction : admin -> var
    | globalRestriction : var
    | isAssigned : admin -> citizen -> var
    | isProposed : admin -> proposal -> var 
    | isTenureWorker : admin -> citizen -> var
    | withinExpiration : admin -> citizen-> var  
    | isValidComitee : admin -> admin -> admin -> var.
```
+ hasNoBudget　a

    行政aが予算を持たない
+ hasNoComitee　a

    行政aがcomiteeを持たない
+ hasNoTenureWoker　a

    行政aがTenureWorkerを持たない
+ hasNoMember　a

    行政aが構成員を持たない
+ treasuryRestriction 　a

    行政aが、国庫に対しての入出金の提案ができない
+ budgetRestriction　a

    行政aが、自身の予算に対しての入出金の提案しかできない
+ allocateRestriction　a

    行政aが、予算分配の提案をできない。
+ assignRestriction　a

    行政aが、行政の構成員の任命・罷免提案をできない。
+ registerRestriction　a

    行政aが、市民登録・解除の提案をできない。
+ adminControlRestriction　a

    行政aが、新な行政の追加・既存行政の削除の提案をできない。
+ globalRestriction

    グローバルステートで熟議できる提案についての制約
+ isAssigned　a m

    市民mが行政aの構成員である
+ isProposed

    行政aに提案pが提出されている
+ isTenureWorker a m 

    市民mが行政aのTenureWorkerである
+ withinExpiration

    市民mが行政mのtenureWorkerで任期内である










   