(* Signs and sets of signs *)
Inductive sign: Type :=
  Neg : sign
| Zero : sign
| Pos : sign
.

Definition eq := (@eq sign).

Definition compare l r: comparison :=
  match l, r with
    Neg, Neg => Eq
  | Neg, _ => Lt
  | Zero, Neg => Gt
  | Zero, Zero => Eq
  | Zero, Pos => Lt
  | Pos, Pos => Eq
  | Pos, _ => Gt
  end.

Definition lt l r: Prop := (compare l r) = Lt.

Lemma sign_compare_eq: forall x y, compare x y = Eq -> x = y.
case x, y; simpl compare;
intros H; try reflexivity; try discriminate H.
Qed.

Lemma sign_compare_lt: forall x y, compare x y = Lt -> lt x y.
intros.
unfold lt.
exact H.
Qed.

Lemma sign_compare_gt: forall x y, compare x y = Gt -> lt y x.
unfold lt.
case x, y; simpl compare; intros H; try reflexivity; try discriminate H.
Qed.



Require Import MSets.
Require Import Decidable.


Module SignOTWL <: OrderedTypeWithLeibniz.
Definition t := sign.
Definition eq := eq.
Instance eq_equiv : Equivalence eq.
Proof.
split;
unfold Reflexive; unfold Symmetric; unfold Transitive.
reflexivity.
intros.
rewrite H.
reflexivity.
intros.
rewrite H.
rewrite H0.
reflexivity.
Qed.
Definition lt := lt.
Instance lt_strorder: StrictOrder lt.
Proof.
split;
unfold Irreflexive; unfold Reflexive; unfold complement; unfold Transitive;
unfold lt; unfold Top.lt.
intros x.
case x; simpl compare;
intros H; discriminate H.
case x, y, z; simpl compare;
intros H1 H2; try discriminate H1; try discriminate H2; try reflexivity.
Qed.
Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
split;
rewrite H; rewrite H0;
intros Hlt; exact Hlt.
Qed.
Definition compare := compare.
Lemma compare_spec: forall x y, CompSpec eq lt x y (compare x y).
intros.
unfold CompSpec.
case_eq (compare x y);
constructor.
apply sign_compare_eq.
exact H.
apply sign_compare_lt.
exact H.
apply sign_compare_gt.
exact H.
Qed.
Lemma eq_dec: forall x y:sign, {eq x y} + {~ eq x y}.
case x, y;
try (left; reflexivity); try (right; discriminate).
Qed.
Lemma eq_leibniz: forall x y: sign, (eq x y) -> x = y.
intros.
exact H.
Qed.
End SignOTWL.

Module SignSet := MakeWithLeibniz SignOTWL.
Module SignSetFacts := MSetFacts.WFacts SignSet.
Module SignSetProps := MSetProperties.WProperties SignSet.

Definition signset := SignSet.t.

Require Import List.

Fixpoint fromList l : signset :=
  match l with
    nil => SignSet.empty
  | (h :: t) => SignSet.add h (fromList t)
  end.

Definition AllSigns := fromList (Neg :: Zero :: Pos :: nil).

Lemma in_allsigns: forall x, SignSet.In x AllSigns.
intros.
unfold AllSigns; simpl.
case x; intuition.
Qed.


Lemma exists_in_singleton: forall s, exists t, SignSet.In t (SignSet.singleton s).
intros.
exists s.
apply SignSetProps.Dec.F.singleton_2.
reflexivity.
Qed.

Require Import ZArith.
Open Scope Z_scope.

Require Import Ensembles.

Definition sign_of (n:Z) : signset :=
  match Z.compare n 0 with
    Eq => SignSet.singleton Zero
  | Lt => SignSet.singleton Neg
  | Gt => SignSet.singleton Pos
  end.


Definition alpha P s : Prop := exists n, P n /\ SignSet.In s (sign_of n).

Definition gamma P n : Prop := exists s, P s /\ SignSet.In s (sign_of n).

Lemma alpha_monotone: forall (P Q: Ensemble Z), (forall n, P n -> Q n) -> (forall s, (alpha P) s -> (alpha Q) s).
intros P Q HPnQn.
unfold alpha.
intros s [n [HPn Hsalpha]].
exists n.
split.
apply HPnQn in HPn.
exact HPn.
exact Hsalpha.
Qed.

Lemma gamma_monotone: forall (P Q : Ensemble sign), (forall s, P s -> Q s) -> (forall n, (gamma P) n -> (gamma Q) n).
intros P Q HPsQs.
unfold gamma.
intros n [s [HPs Hsalpha]].
exists s.
auto.
Qed.

Lemma sign_in_alpha: forall n P, P n -> exists s, SignSet.In s (sign_of n).
intros.
unfold sign_of.
case_eq n; simpl; intros; apply exists_in_singleton.
Qed.

Lemma gamma_alpha: forall (P: Ensemble Z) n, P n -> (gamma (alpha P)) n.
intros P n HPn.
unfold alpha; unfold gamma.
assert (HPn_has_sign := HPn).
apply sign_in_alpha in HPn_has_sign.
destruct HPn_has_sign as [s Hsalpha].
exists s.
split.
exists n.
split.
exact HPn.
exact Hsalpha.
exact Hsalpha.
Qed.


Lemma sign_of_produces_singleton: forall s t n, SignSet.In s (sign_of n) -> SignSet.In t (sign_of n) -> eq s t.
intros s t n Hsalpha Htalpha.
case_eq n;
intros; rename H into Hn;
rewrite Hn in Hsalpha; rewrite Hn in Htalpha;
unfold sign_of in Hsalpha; unfold sign_of in Htalpha;
simpl in Hsalpha; simpl in Htalpha;
apply SignSetProps.Dec.F.singleton_1 in Hsalpha;
apply SignSetProps.Dec.F.singleton_1 in Htalpha;
rewrite <- Htalpha;
rewrite <- Hsalpha;
reflexivity.
Qed.


Lemma alpha_gamma: forall P s, (alpha (gamma P)) s -> P s.
intros P s.
unfold alpha; unfold gamma.
intros [n [[t [Htp Htalpha]] Hsalpha]].
case_eq n;
intros; rename H into Hn;
rewrite Hn in Hsalpha; unfold sign_of in Hsalpha; simpl in Hsalpha;
rewrite Hn in Htalpha; unfold sign_of in Htalpha; simpl in Htalpha;
apply SignSetProps.Dec.F.singleton_1 in Hsalpha;
apply SignSetProps.Dec.F.singleton_1 in Htalpha;
rewrite <- Htalpha in Htp;
rewrite <- Hsalpha;
exact Htp.
Qed.


Definition set_plus P Q x : Prop := exists n m, P n /\ Q m /\ n + m = x.

Lemma sum_in_plus: forall n m (P Q: Z -> Prop), P n -> Q m -> (set_plus P Q) (n + m).
intros n m.
unfold set_plus.
exists n.
exists m.
repeat split.
exact H.
exact H0.
Qed.


Definition sign_plus (n: sign) (m: sign) : SignSet.t :=
  match n, m with
    Neg,  Neg  => SignSet.singleton Neg
  | Neg,  Zero => SignSet.singleton Neg
  | Neg,  Pos  => AllSigns
  | Zero, Neg  => SignSet.singleton Neg
  | Zero, Zero => SignSet.singleton Zero
  | Zero, Pos  => SignSet.singleton Pos
  | Pos,  Neg  => AllSigns
  | Pos,  Zero => SignSet.singleton Pos
  | Pos,  Pos  => SignSet.singleton Pos
  end.


Fixpoint sign_plus_aux (n: sign) (m: sign) (g: nat) {struct g}: SignSet.t :=
  match n, m, g with
    Neg, Pos, _ => AllSigns
  | Neg, _, _ => SignSet.singleton Neg
  | Zero, Zero, _ => SignSet.singleton Zero
  | _, Pos, _ => SignSet.singleton Pos
  | _, _, (S g) => sign_plus_aux m n g
  | _, _, _ => SignSet.empty
  end.

Definition sign_plus_2 n m := sign_plus_aux n m 1.

Lemma sign_plus_equal: forall n m, sign_plus n m = sign_plus_2 n m.
intros.
unfold sign_plus; unfold sign_plus_2; unfold sign_plus_aux.
case n, m; reflexivity.
Qed.

Definition signs_plus_fin (n:SignSet.t) (m:SignSet.t) : SignSet.t :=
  let elts := list_prod (SignSet.elements n) (SignSet.elements m)
  in let alphas :=  map (prod_curry sign_plus) elts
  in fold_left SignSet.union alphas SignSet.empty.

(*
Compute a_plus_fin (fromList (Neg::Zero::nil)) (fromList (Zero::nil)).
*)



Lemma alpha_aux_p: forall n m, SignSet.Subset (sign_of (n + m)) (signs_plus_fin (sign_of n) (sign_of m)).
intros.
unfold SignSet.Subset.
case_eq n; case_eq m; 
unfold sign_of; unfold signs_plus_fin; simpl; intros;
try (apply SignSetProps.Dec.F.union_3; exact H1);
apply in_allsigns.
Qed.




Definition signset_plus P Q s : Prop := exists n m, P n /\ Q m /\ SignSet.In s (sign_plus n m).



Lemma signset_plus_sound: forall s (P Q: Ensemble Z), (alpha (set_plus P Q)) s -> (signset_plus (alpha P) (alpha Q)) s.
intros s P Q.
unfold alpha; unfold signset_plus.
intros [x [Hsp Hsign_x]].
unfold set_plus in Hsp.
destruct Hsp as [n [m [HPn [HQm Hplus]]]].
rewrite <- Hplus in Hsign_x.

assert (HPn_has_sign := HPn).
apply sign_in_alpha in HPn_has_sign.
destruct HPn_has_sign as [t HPn_has_sign].
exists t.

assert (HQm_has_sign := HQm).
apply sign_in_alpha in HQm_has_sign.
destruct HQm_has_sign as [u HQm_has_sign].
exists u.

split.
exists n.
split.
exact HPn.
exact HPn_has_sign.

split.
exists m.
split.
exact HQm.
exact HQm_has_sign.

case_eq m; case_eq n;
intros until 2; rename H into Hn; rename H0 into Hm;

rewrite Hn in HPn_has_sign;
unfold sign_of in HPn_has_sign;
simpl in HPn_has_sign;
apply SignSetProps.Dec.F.singleton_1 in HPn_has_sign;
apply SignSet.E.eq_leibniz in HPn_has_sign;

rewrite Hm in HQm_has_sign;
unfold sign_of in HQm_has_sign;
simpl in HQm_has_sign;
apply SignSetProps.Dec.F.singleton_1 in HQm_has_sign;
apply SignSet.E.eq_leibniz in HQm_has_sign;

rewrite <- HPn_has_sign;
rewrite <- HQm_has_sign;
unfold sign_plus;

rewrite Hn in Hsign_x;
rewrite Hm in Hsign_x;
unfold sign_of in Hsign_x;
simpl in Hsign_x;

try exact Hsign_x;
try apply in_allsigns.
Qed.

