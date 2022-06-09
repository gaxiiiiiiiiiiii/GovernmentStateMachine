From mathcomp Require Export all_ssreflect.


(*****************)
(* subStateの種類 *)
(*****************)


Definition limita' := 2 ^ 15.
Definition limita := limita' .+1.

Variant admin :=
    Admin m : m < limita -> admin.

Coercion nat_of_curr c := let : Admin m _ := c in m.

Canonical admin_subType := [subType for nat_of_curr].
Definition admin_eqMixin := Eval hnf in [eqMixin of admin by <:].
Canonical admin_eqType := Eval hnf in EqType admin admin_eqMixin.
Definition admin_choiceMixin := [choiceMixin of admin by <:].
Canonical admin_choiceType :=
  Eval hnf in ChoiceType admin admin_choiceMixin.
Definition admin_countMixin := [countMixin of admin by <:].
Canonical admin_countType := Eval hnf in CountType admin admin_countMixin.
Canonical admin_subCountType := [subCountType of admin].

Lemma ltn_curr (i : admin) : i < limita.
Proof. destruct i => //=. Qed.

Lemma curr_inj : injective nat_of_curr.
Proof. exact: val_inj. Qed.


Definition curr_enum : seq admin := pmap insub (iota 0 limita).

Lemma val_curr_enum : map val curr_enum = iota 0 limita.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma curr_enum_uniq : uniq curr_enum.
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_curr_enum i : i \in curr_enum.
Proof. by rewrite -(mem_map curr_inj) val_curr_enum mem_iota ltn_curr. Qed.

Definition admin_finMixin :=
  Eval hnf in UniqFinMixin curr_enum_uniq mem_curr_enum.
Canonical admin_finType := Eval hnf in FinType admin admin_finMixin.
Canonical admin_subFinType := Eval hnf in [subFinType of admin].



(* Definition global       : admin. refine (Admin 0 _) => //. Qed.
Definition police       : admin. refine (Admin 1 _) => //. Qed.
Definition judiciary    : admin. refine (Admin 2 _) => //. Qed.
Definition military     : admin. refine (Admin 3 _) => //. Qed.
Definition regisrator   : admin. refine (Admin 4 _) => //. Qed.
Definition professional : admin. refine (Admin 5 _) => //. Qed.
Definition facilitator  : admin. refine (Admin 6 _) => //. Qed. *)

