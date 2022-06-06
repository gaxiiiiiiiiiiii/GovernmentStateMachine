From mathcomp Require Export all_ssreflect.
Require Import Lia.
Parameter limit' : nat.
Definition limit := limit' .+1.

Variant currency :=
    Currency m : m < limit -> currency.

Coercion nat_of_curr c := let : Currency m _ := c in m.

Canonical currency_subType := [subType for nat_of_curr].
Definition currency_eqMixin := Eval hnf in [eqMixin of currency by <:].
Canonical currency_eqType := Eval hnf in EqType currency currency_eqMixin.
Definition currency_choiceMixin := [choiceMixin of currency by <:].
Canonical currency_choiceType :=
  Eval hnf in ChoiceType currency currency_choiceMixin.
Definition currency_countMixin := [countMixin of currency by <:].
Canonical currency_countType := Eval hnf in CountType currency currency_countMixin.
Canonical currency_subCountType := [subCountType of currency].

Lemma ltn_curr (i : currency) : i < limit.
Proof. destruct i => //=. Qed.

Lemma curr_inj : injective nat_of_curr.
Proof. exact: val_inj. Qed.


Definition curr_enum : seq currency := pmap insub (iota 0 limit).

Lemma val_curr_enum : map val curr_enum = iota 0 limit.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma curr_enum_uniq : uniq curr_enum.
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_curr_enum i : i \in curr_enum.
Proof. by rewrite -(mem_map curr_inj) val_curr_enum mem_iota ltn_curr. Qed.

Definition currency_finMixin :=
  Eval hnf in UniqFinMixin curr_enum_uniq mem_curr_enum.
Canonical currency_finType := Eval hnf in FinType currency currency_finMixin.
Canonical currency_subFinType := Eval hnf in [subFinType of currency].

Definition add_(x y : nat) : nat :=
    if x + y < limit then x + y else limit'.

Definition addc (x y : currency) : currency.
    refine (Currency (add_ x y) _).
    rewrite /add_.
    remember  (x + y < limit).    
    destruct b => //=.
Qed.    

Definition subc (x y : currency): currency.
    refine (Currency (x - y) _).
    induction x, y; simpl in *.
    induction m0 => //=.
    +   rewrite subn0 => //.
    +   have : m < m0 + limit.
        {
            rewrite <- ltn_psubLR => //=.
            apply IHm0.
            apply ltn_trans with m0.+1 => //=.
        }
        rewrite ltn_psubLR => //= H.
        have : m0.+1 + limit = (m0 + limit).+1.
        {
            induction m0 => //=.
        }
        move => ->.
        apply ltn_trans with (m0 +limit) => //.
Qed.    