From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MathStructures.


Module PCMDef.

Record mixin_of (T : Type) := Mixin {
  valid_op : T -> bool;
  join_op : T -> T -> T;
  unit_op : T;
  _ : commutative join_op;
  _ : associative join_op;
  _ : left_id unit_op join_op;
  _ : forall x y, valid_op (join_op x y) -> valid_op x;
  _ : valid_op unit_op
}.

Check valid_op.

Lemma r_unit T (pcm: mixin_of T) (t: T) : (join_op pcm t (unit_op pcm)) = t.
Proof.
case: pcm => _ join unit Hc _ Hlu _ _ /=.
by rewrite Hc Hlu.
Qed.

Section Packing.
Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.

Local Coercion type : pack_type >-> Sortclass.

Variable cT: pack_type.

Definition pcm_struct : mixin_of cT :=
  let: Pack _ c := cT return mixin_of cT in c.

Definition valid := valid_op pcm_struct.
Definition join := join_op pcm_struct.
Definition unit := unit_op pcm_struct.
End Packing.

Module Exports.
Notation pcm := pack_type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@Pack T m).
Notation "x \+ y" := (join x y) (at level 43, left associativity).
Notation valid := valid.
Notation Unit := unit.
Coercion type : pack_type >-> Sortclass.

Section PCMLemmas.
Variable U : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof.
by case: U x y => tp [v j z Cj *]; apply Cj.
Qed.

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof.
by case: U x y z => tp [v j z Cj Aj *]; apply: Aj.
Qed.

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof.
by rewrite -2!joinA (joinC y z).
Qed.
(* case: U x y z => t [v j z Cj Aj *] /=.
rewrite /join => /=.
rewrite -2!Aj.
Abort. *)

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof.
by rewrite (joinC y z) joinA joinC.
Qed.

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof.
case: U x y => tp [v j z Cj Aj Li V Vi] x y. 
by apply: V.
Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof.
rewrite (joinC x y); by apply validL.
Qed.

Lemma unitL (x : U) : (@Unit U) \+ x = x.
Proof.
case: U x => tp [v j z Cj Aj Li V Vi] x.
by apply Li.
Qed.

Lemma unitR (x : U) : x \+ (@Unit U) = x.
Proof.
rewrite joinC. by apply unitL.
Qed.

Lemma valid_unit : valid (@Unit U).
Proof.
case: U => tp [v j z Cj Aj Li V Vi].
by apply Vi.
Qed.

End PCMLemmas.
End Exports.
End PCMDef.

Export PCMDef.Exports.


Module CancelPCM.
Record mixin_of (U : pcm) := Mixin {
  _ : forall a b c: U, valid (a \+ b) -> a \+ b = a \+ c -> b = c
}.

Structure pack_type : Type := Pack {pcmT : pcm; _ : mixin_of pcmT}.
Module Exports.
Notation cancel_pcm := pack_type.
Notation CancelPCMMixin := Mixin.
Notation CancelPCM T m:= (@Pack T m).

Coercion pcmT : pack_type >-> pcm.
Lemma cancel (U: cancel_pcm) (x y z: U):
  valid (x \+ y) -> x \+ y = x \+ z -> y = z.
Proof.
by case: U x y z => Up [Hc] x y z; apply: Hc.
Qed.

End Exports.
End CancelPCM.

Export CancelPCM.Exports.

Lemma cancelC (U: cancel_pcm) (x y z : U) :
  valid (y \+ x \+ z) -> y \+ x = x \+ z -> y = z.
Proof.
by move/validL; rewrite ![y \+ _]joinC; apply: cancel.
Qed.



Definition natPCMMixin :=
  PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).

Definition NatPCM := PCM nat natPCMMixin.

Canonical natPCM := PCM nat natPCMMixin.
Print Canonical Projections.


Lemma add_perm (a b c : nat) : a \+ (b \+ c) = a \+ (c \+ b).
Proof. by rewrite (joinC b c). Qed.

Lemma cancelNat : forall a b c: nat, true -> a + b = a + c -> b = c.
Proof.
move => a b c; elim: a=>// n /(_ is_true_true) Hn _ H.
apply: Hn. by rewrite !addSn in H; move/eq_add_S: H.
Qed.

Definition cancelNatPCMMixin := CancelPCMMixin cancelNat.
Canonical cancelNatPCM := CancelPCM natPCM cancelNatPCMMixin.



Section PCMExamples.
Variables a b c: nat.
Goal a \+ (b \+ c) = c \+ (b \+ a).
Proof.
by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
Qed.


Goal c \+ a = a \+ b -> c = b.
Proof.
rewrite [c \+ _]joinC. by apply cancel.
Qed.

Lemma addn_join (x y: nat): x + y = x \+ y.
Proof. by []. Qed.
End PCMExamples.

End MathStructures.




Module Poset.
Record posetMixin (T : Type) := PosetMixin {
  rel_op : T -> T -> bool;
  _ : reflexive rel_op;
  _ : transitive rel_op;
  _ : antisymmetric rel_op;
}.
Structure poset : Type := Poset {type : Type; _ : posetMixin type}.
Local Coercion type : poset >-> Sortclass.

Section Packing.
Variable P: poset.
Definition pcm_struct : posetMixin P :=
  let: Poset _ c := P return posetMixin P in c.
Definition op := rel_op pcm_struct.
End Packing.

Notation "a \< b" := (op a b) (at level 43, left associativity).

Lemma poset_refl: forall (P: poset) (x: P), x \< x.
Proof. case => a [op rop top aop] x. apply: rop. Qed.

Lemma poset_asym: forall (P: poset) (x y: P), (x \< y) && (y \< x) -> x = y.
Proof. case => a [op rop top aop] x y. apply: aop. Qed.

Print transitive.
Lemma poset_trans: forall (P: poset) (x y z: P), x \< y -> y \< z -> x \< z.
Proof. case => a [op rop top aop] x y z. apply: top. Qed.
End Poset.



Import Poset.

Definition natPosetMixin := PosetMixin leqnn leq_trans anti_leq.
Definition NatPoset := Poset natPosetMixin.
Canonical natPCM := NatPoset.

Lemma tst_nat_poset_refl (x: nat): x \< x.
Proof. apply: poset_refl. Qed.

