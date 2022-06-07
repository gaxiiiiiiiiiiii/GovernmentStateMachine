From mathcomp Require Export all_ssreflect.
Parameter limit' : nat.
Definition limit := limit' .+1.

Variant timestamp :=
    Currency m : m < limit -> timestamp.

Coercion nat_of_curr c := let : Currency m _ := c in m.

Canonical timestamp_subType := [subType for nat_of_curr].
Definition timestamp_eqMixin := Eval hnf in [eqMixin of timestamp by <:].
Canonical timestamp_eqType := Eval hnf in EqType timestamp timestamp_eqMixin.
Definition timestamp_choiceMixin := [choiceMixin of timestamp by <:].
Canonical timestamp_choiceType :=
  Eval hnf in ChoiceType timestamp timestamp_choiceMixin.
Definition timestamp_countMixin := [countMixin of timestamp by <:].
Canonical timestamp_countType := Eval hnf in CountType timestamp timestamp_countMixin.
Canonical timestamp_subCountType := [subCountType of timestamp].

Lemma ltn_curr (i : timestamp) : i < limit.
Proof. destruct i => //=. Qed.

Lemma curr_inj : injective nat_of_curr.
Proof. exact: val_inj. Qed.


Definition curr_enum : seq timestamp := pmap insub (iota 0 limit).

Lemma val_curr_enum : map val curr_enum = iota 0 limit.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma curr_enum_uniq : uniq curr_enum.
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_curr_enum i : i \in curr_enum.
Proof. by rewrite -(mem_map curr_inj) val_curr_enum mem_iota ltn_curr. Qed.

Definition timestamp_finMixin :=
  Eval hnf in UniqFinMixin curr_enum_uniq mem_curr_enum.
Canonical timestamp_finType := Eval hnf in FinType timestamp timestamp_finMixin.
Canonical timestamp_subFinType := Eval hnf in [subFinType of timestamp].

