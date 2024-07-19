Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall Types.Sigma.
Require Import WildCat.Core WildCat.Equiv WildCat.Monoidal WildCat.Bifunctor.
Require Import WildCat.NatTrans.
Require Import Algebra.Groups.Group Algebra.Groups.QuotientGroup.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Biproduct.
Require Import Algebra.AbGroups.AbHom Algebra.AbGroups.FreeAbelianGroup.
Require Import Algebra.AbGroups.Abelianization Algebra Algebra.Groups.FreeGroup.
Require Import Colimits.Quotient.
Require Import Spaces.List.Core Spaces.Int.
Require Import AbGroups.Z.
Require Import Truncations.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * Tensor Product of Abelian Groups *)

(** ** Construction *)

(** We define the tensor product of abelian groups as a quotient of the free abelian group on pairs of elements of the two groups by the subgroup generated by the biadditive pairs. *)

(** Here we define the subgroup of biadditive pairs in two steps *)
Definition family_biadditive_pairs {A B : AbGroup}
  : FreeAbGroup (A * B) -> Type.
Proof.
  intros x.
  refine ((exists (a1 a2 : A) (b : B), _) + exists (a : A) (b1 b2 : B), _)%type. 
  - refine (_ - (_ + _) = x).
    1-3: apply freeabgroup_in.
    + exact (a1 + a2, b).
    + exact (a1, b).
    + exact (a2, b).
  - refine (_ - (_ + _) = x).
    1-3: apply freeabgroup_in.
    + exact (a, b1 + b2).
    + exact (a, b1).
    + exact (a, b2).
Defined.

Definition subgroup_biadditive_pairs {A B : AbGroup}
  : Subgroup (FreeAbGroup (A * B))
  := subgroup_generated family_biadditive_pairs.

(** The tensor product [ab_tensor_prod A B] of two abelian groups [A] and [B] is defined to ba a quotient of the free abelian group on pairs of elements [A * B] by the subgroup of biadditive pairs. *)
Definition ab_tensor_prod (A B : AbGroup) : AbGroup
  := QuotientAbGroup (FreeAbGroup (A * B)) subgroup_biadditive_pairs.

Arguments ab_tensor_prod A B : simpl never.

(** The tensor product of [A] and [B] contains formal combinations of pairs of elements from [A] and [B]. We denote these pairs as simple tensors and name them [tensor]. *)
Definition tensor {A B : AbGroup} : A -> B -> ab_tensor_prod A B
  := fun a b => grp_quotient_map (freeabgroup_in (a, b)).

(** ** Properties of tensors *)

(** The characterizing property of simple tensors are that they are bilinear in their arguments. *)

(** A [tensor] of a sum distributes over the sum on the left. *) 
Definition tensor_dist_l {A B : AbGroup} (a : A) (b b' : B)
  : tensor a (b + b') = tensor a b + tensor a b'.
Proof.
  apply qglue, tr.
  apply sgt_inv'.
  rewrite ab_neg_op.
  rewrite grp_inv_inv.
  apply sgt_in.
  right.
  by exists a, b, b'.
Defined.

(** A [tensor] of a sum distributes over the sum on the right. *)
Definition tensor_dist_r {A B : AbGroup} (a a' : A) (b : B)
  : tensor (a + a') b = tensor a b + tensor a' b.
Proof.
  apply qglue, tr.
  apply sgt_inv'.
  rewrite ab_neg_op.
  rewrite grp_inv_inv.
  apply sgt_in.
  left.
  by exists a, a', b.
Defined.

(** Tensoring on the left is a group homomorphism. *)
Definition grp_homo_tensor_l {A B : AbGroup} (a : A)
  : B $-> ab_tensor_prod A B.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun b => tensor a b).
  - intros b b'.
    nrapply tensor_dist_l.
Defined. 

(** Tensoring on the right is a group homomorphism. *)
Definition grp_homo_tensor_r {A B : AbGroup} (b : B)
  : A $-> ab_tensor_prod A B.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun a => tensor a b).
  - intros a a'.
    nrapply tensor_dist_r.
Defined.

(** Tensors preserve negation in the left argument. *)
Definition tensor_neg_l {A B : AbGroup} (a : A) (b : B)
  : tensor (-a) b = - tensor a b.
Proof.
  change (grp_homo_tensor_r b (-a) = - tensor a b).
  by rewrite grp_homo_inv.
Defined.

(** Tensors preserve negation in the right argument. *)
Definition tensor_neg_r {A B : AbGroup} (a : A) (b : B)
  : tensor a (-b) = - tensor a b.
Proof.
  change (grp_homo_tensor_l a (-b) = - tensor a b).
  by rewrite grp_homo_inv.
Defined.

(** Tensoring by zero on the left is zero. *)
Definition tensor_zero_l {A B : AbGroup} (b : B)
  : tensor (A:=A) 0 b = 0.
Proof.
  change (grp_homo_tensor_r (A:=A) b 0 = 0).
  nrapply grp_homo_unit.
Defined.

(** Tensoring by zero on the right is zero. *)
Definition tensor_zero_r {A B : AbGroup} (a : A)
  : tensor (B:=B) a 0 = 0.
Proof.
  change (grp_homo_tensor_l (B:=B) a 0 = 0).
  nrapply grp_homo_unit.
Defined.

(** The [tensor] map is bilinear and therefore can be written in a curried form using the internal abelian group hom. *)
Definition grp_homo_tensor `{Funext} {A B : AbGroup}
  : A $-> ab_hom B (ab_tensor_prod A B). 
Proof.
  snrapply Build_GroupHomomorphism.
  - intros a.
    snrapply Build_GroupHomomorphism.
    + exact (tensor a).
    + nrapply tensor_dist_l.
  - intros a a'.
    apply equiv_path_grouphomomorphism.
    intros b.
    nrapply tensor_dist_r.
Defined.

(** ** Induction principles *)

(** Here we write down some induction principles to help us prove lemmas about the tensor product. Some of these are quite specialised but are patterns that appear often in practice. *) 

(** Our main recursion principle states that in order to build a homomorphism out of the tensor product, it is sufficient to provide a map out of the direct product which is bilinear, that is, a map that preserves addition in both arguments of the product. *)

(** We separate out the proof of this part, so we can make it opaque. *)
Definition ab_tensor_prod_rec_helper {A B C : AbGroup}
  (f : A -> B -> C)
  (l : forall a b b', f a (b + b') = f a b + f a b')
  (r : forall a a' b, f (a + a') b = f a b + f a' b)
  (x : FreeAbGroup (A * B)) (insg : subgroup_biadditive_pairs x)
  : grp_homo_abel_rec (FreeGroup_rec (A * B) C (uncurry f)) x = mon_unit.
Proof.
  strip_truncations.
  induction insg as
    [ x [ [ a [ a' [ b p ] ] ] | [ a [ b [ b' p ] ] ] ]
    |
    | ? ? ? H1 ? H2 ].
  - destruct p.
    rewrite grp_homo_op.
    rewrite grp_homo_inv.
    apply grp_moveL_1M^-1%equiv.
    exact (r a a' b).
  - destruct p.
    rewrite grp_homo_op.
    rewrite grp_homo_inv.
    apply grp_moveL_1M^-1%equiv.
    exact (l a b b').
  - nrapply grp_homo_unit.
  - rewrite grp_homo_op, grp_homo_inv.
    apply grp_moveL_1M^-1.
    exact(H1 @ H2^).
Defined.

Opaque ab_tensor_prod_rec_helper.

Definition ab_tensor_prod_rec {A B C : AbGroup}
  (f : A -> B -> C)
  (l : forall a b b', f a (b + b') = f a b + f a b')
  (r : forall a a' b, f (a + a') b = f a b + f a' b) 
  : ab_tensor_prod A B $-> C.
Proof.
  unfold ab_tensor_prod.
  snrapply grp_quotient_rec.
  - snrapply grp_homo_abel_rec.
    snrapply FreeGroup_rec.
    exact (uncurry f).
  - unfold normalsubgroup_subgroup.
    apply ab_tensor_prod_rec_helper; assumption.
Defined.

(** We give an induction principle for an hprop-valued type family [P].  It may be surprising at first that we only require [P] to hold for the simple tensors [tensor a b] and be closed under addition.  It automatically follows that [P 0] holds (since [tensor 0 0 = 0]) and that [P] is closed under negation (since [tensor -a b = - tensor a b]). This induction principle says that the simple tensors generate the tensor product as a semigroup. *)
Definition ab_tensor_prod_ind_hprop {A B : AbGroup}
  (P : ab_tensor_prod A B -> Type)
  {H : forall x, IsHProp (P x)}
  (Hin : forall a b, P (tensor a b))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  unfold ab_tensor_prod.
  srapply grp_quotient_ind_hprop.
  srapply Abel_ind_hprop; cbn beta.
  srapply FreeGroup_ind_hprop'; intros w; cbn beta.
  induction w.
  - exact (transport P (tensor_zero_l 0) (Hin 0 0)).
  - destruct a as [[a b]|[a b]].
    + change (P (grp_quotient_map (abel_unit (freegroup_in (a, b) + freegroup_eta w)))).
      (* Both [rewrite]s are [reflexivity], but the [Defined] is slow if [change] is used instead. *)
      rewrite 2 grp_homo_op.
      apply Hop; trivial.
      apply Hin.
    + change (P (grp_quotient_map (abel_unit (- freegroup_in (a, b) + freegroup_eta w)))).
      (* The [rewrite]s on the next two lines are all reflexivity. *)
      rewrite 2 grp_homo_op.
      rewrite 2 grp_homo_inv.
      apply Hop; trivial.
      rewrite <- tensor_neg_l.
      apply Hin.
Defined.

(** As a commonly occuring special case of the above induction principle, we have the case when the predicate in question is showing that two group homomorphisms out of the tensor product are homotopic. In order to do this, it suffices to show it only for simple tensors. The homotopy is closed under addition, so we don't need to hypothesise anything else. *)
Definition ab_tensor_prod_ind_homotopy {A B G : AbGroup}
  {f f' : ab_tensor_prod A B $-> G}
  (H : forall a b, f (tensor a b) = f' (tensor a b))
  : f $== f'.
Proof.
  rapply ab_tensor_prod_ind_hprop.
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** As an even more specialised case, we occasionally have the second homomorphism being a sum of abelian group homomorphisms. In those cases, it is easier to use this specialised lemma. *)
Definition ab_tensor_prod_ind_homotopy_plus {A B G : AbGroup}
  {f f' f'' : ab_tensor_prod A B $-> G}
  (H : forall a b, f (tensor a b) = f' (tensor a b) + f'' (tensor a b))
  : forall x, f x = f' x + f'' x
  := ab_tensor_prod_ind_homotopy (f':=ab_homo_add f' f'') H.

(** Here we give an induction principle for a triple tensor, a.k.a a dependent trilinear function. *)
Definition ab_tensor_prod_ind_hprop_triple {A B C : AbGroup}
  (P : ab_tensor_prod A (ab_tensor_prod B C) -> Type)
  (H : forall x, IsHProp (P x))
  (Hin : forall a b c, P (tensor a (tensor b c)))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  rapply (ab_tensor_prod_ind_hprop P).
  - intros a.
    rapply (ab_tensor_prod_ind_hprop (fun x => P (tensor _ x))).
    + nrapply Hin.
    + intros x y Hx Hy.
      rewrite tensor_dist_l.
      by apply Hop.
  - exact Hop.
Defined.

(** Similar to before, we specialise the triple tensor induction principle for proving homotopies of trilinear functions. *)
Definition ab_tensor_prod_ind_homotopy_triple {A B C G : AbGroup}
  {f f' : ab_tensor_prod A (ab_tensor_prod B C) $-> G}
  (H : forall a b c, f (tensor a (tensor b c)) = f' (tensor a (tensor b c)))
  : f $== f'.
Proof.
  rapply ab_tensor_prod_ind_hprop_triple.
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** As explained for the bilinear and trilinear cases, we also derive an induction principle for quadruple tensors giving us dependent quadrilinear maps. *) 
Definition ab_tensor_prod_ind_hprop_quad {A B C D : AbGroup}
  (P : ab_tensor_prod A (ab_tensor_prod B (ab_tensor_prod C D)) -> Type)
  (H : forall x, IsHProp (P x))
  (Hin : forall a b c d, P (tensor a (tensor b (tensor c d))))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  rapply (ab_tensor_prod_ind_hprop P).
  - intros a.
    rapply (ab_tensor_prod_ind_hprop_triple (fun x => P (tensor _ x))).
    + nrapply Hin.
    + intros x y Hx Hy.
      rewrite tensor_dist_l.
      by apply Hop.
  - exact Hop.
Defined.

(** To construct a homotopy between quadrilinear maps we need only check equality for the quadruple simple tensors. *)
Definition ab_tensor_prod_ind_homotopy_quad {A B C D G : AbGroup}
  {f f' : ab_tensor_prod A (ab_tensor_prod B (ab_tensor_prod C D)) $-> G}
  (H : forall a b c d, f (tensor a (tensor b (tensor c d)))
    = f' (tensor a (tensor b (tensor c d))))
  : f $== f'.
Proof.
  rapply (ab_tensor_prod_ind_hprop_quad (fun _ => _)).
  - exact H.
  - intros x y; apply grp_homo_op_agree.
Defined.

(** ** Universal Property of the Tensor Product *)

(** A function of two variables is biadditive if it preserves the operation in each variable. *)
Class IsBiadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C} (f : A -> B -> C) := {
  isbiadditive_l :: forall b, IsSemiGroupPreserving (flip f b);
  isbiadditive_r :: forall a, IsSemiGroupPreserving (f a);  
}.

Definition issig_IsBiadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  (f : A -> B -> C)
  : _ <~> IsBiadditive f
  := ltac:(issig).

(** The truncation level of the [IsBiadditive f] predicate is determined by the truncation level of the codomain. This will almost always be a hset. *)
Global Instance istrunc_isbiadditive `{Funext}
  {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  (f : A -> B -> C) n `{IsTrunc n.+1 C}
  : IsTrunc n (IsBiadditive f).
Proof.
  nrapply istrunc_equiv_istrunc.
  1: rapply issig_IsBiadditive.
  unfold IsSemiGroupPreserving.
  exact _.
Defined.

(** The simple tensor map is biadditive. *)
Global Instance isbiadditive_tensor (A B : AbGroup)
  : IsBiadditive (@tensor A B) := {|
  isbiadditive_l := fun b a a' => tensor_dist_r a a' b;
  isbiadditive_r := tensor_dist_l;
|}.

(** The type of biadditive maps. *)
Record Biadditive (A B C : Type) `{SgOp A, SgOp B, SgOp C} := {
  biadditive_fun :> A -> B -> C;
  biadditive_isbiadditive :: IsBiadditive biadditive_fun;
}.

Definition issig_Biadditive {A B C : Type} `{SgOp A, SgOp B, SgOp C}
  : _ <~> Biadditive A B C
  := ltac:(issig).

(** The universal property of the tensor product is that biadditive maps between abelian groups are in one-to-one corresondance with maps out of the tensor product. In this sense, the tensor product is the most perfect object describing biadditive maps between two abelian groups. *)
Definition equiv_ab_tensor_prod_rec `{Funext} (A B C : AbGroup)
  : Biadditive A B C <~> (ab_tensor_prod A B $-> C).
Proof.
  snrapply equiv_adjointify.
  - intros [f [l r]].
    exact (ab_tensor_prod_rec f r (fun a a' b => l b a a')).
  - intros f.
    exists (fun x y => f (tensor x y)).
    snrapply Build_IsBiadditive.
    + intros b a a'; simpl.
      lhs nrapply (ap f).
      1: nrapply tensor_dist_r.
      nrapply grp_homo_op.
    + intros a a' b; simpl.
      lhs nrapply (ap f).
      1: nrapply tensor_dist_l.
      nrapply grp_homo_op.
  - intros f.
    snrapply equiv_path_grouphomomorphism.
    snrapply ab_tensor_prod_ind_homotopy.
    intros a b; simpl.
    reflexivity.
  - intros [f [l r]].
    snrapply (equiv_ap_inv' issig_Biadditive).
    rapply path_sigma_hprop; simpl.
    reflexivity.
Defined.

(** ** Functoriality of the Tensor Product *)

(** The tensor product produces a bifunctor and we will later show that it gives a symmetric monoidal structure on the category of abelian groups. *)

(** Given a pair of maps, we can produce a homomorphism between the pairwise tensor products of the domains and codomains. *) 
Definition functor_ab_tensor_prod {A B A' B' : AbGroup}
  (f : A $-> A') (g : B $-> B')
  : ab_tensor_prod A B $-> ab_tensor_prod A' B'.
Proof.
  snrapply ab_tensor_prod_rec.
  - intros a b.
    exact (tensor (f a) (g b)).
  - intros a b b'; hnf.
    rewrite grp_homo_op.
    by rewrite tensor_dist_l.
  - intros a a' b; hnf.
    rewrite grp_homo_op.
    by rewrite tensor_dist_r.
Defined.

(** 2-functoriality of the tensor product. *)
Definition functor2_ab_tensor_prod {A B A' B' : AbGroup}
  {f f' : A $-> A'} (p : f $== f') {g g' : B $-> B'} (q : g $== g')
  : functor_ab_tensor_prod f g $== functor_ab_tensor_prod f' g'.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  exact (ap011 tensor (p _) (q _)).
Defined.

(** The tensor product functor preserves identity morphisms. *)
Definition functor_ab_tensor_prod_id (A B : AbGroup)
  : functor_ab_tensor_prod (Id A) (Id B) $== Id (ab_tensor_prod A B).
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  reflexivity.
Defined.

(** The tensor product functor preserves composition. *)
Definition functor_ab_tensor_prod_compose {A B C A' B' C' : AbGroup}
  (f : A $-> B) (g : B $-> C) (f' : A' $-> B') (g' : B' $-> C')
  : functor_ab_tensor_prod (g $o f) (g' $o f')
    $== functor_ab_tensor_prod g g' $o functor_ab_tensor_prod f f'.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  intros a b; simpl.
  reflexivity.
Defined.

(** The tensor product functor is a 0-bifunctor. *)
Global Instance is0bifunctor_ab_tensor_prod : Is0Bifunctor ab_tensor_prod.
Proof.
  rapply Build_Is0Bifunctor'.
  snrapply Build_Is0Functor.
  intros [A B] [A' B'] [f g].
  exact (functor_ab_tensor_prod f g).
Defined.

(** The tensor product functor is a bifunctor. *)
Global Instance is1bifunctor_ab_tensor_prod : Is1Bifunctor ab_tensor_prod.
Proof.
  rapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros AB A'B' fg f'g' [p q].
    exact (functor2_ab_tensor_prod p q).
  - intros [A B].
    exact (functor_ab_tensor_prod_id A B).
  - intros AA' BB' CC' [f g] [f' g'].
    exact (functor_ab_tensor_prod_compose f f' g g').
Defined.

(** ** Symmetry of the Tensor Product *)

(** The tensor product is symmetric in that the order in which we take the tensor shouldn't matter upto isomorphism. *)

(** We can define a swap map which swaps the order of simple tensors. *)
Definition ab_tensor_swap {A B} : ab_tensor_prod A B $-> ab_tensor_prod B A.
Proof.
  snrapply ab_tensor_prod_rec. 
  - exact (flip tensor).
  - intros a b b'.
    apply tensor_dist_r.
  - intros a a' b.
    apply tensor_dist_l.
Defined.

(** [ab_tensor_swap] is involutive. *)
Definition ab_tensor_swap_swap {A B}
  : ab_tensor_swap $o @ab_tensor_swap A B $== Id _. 
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  reflexivity.
Defined. 

(** [ab_tensor_swap] is natural in both arguments. This means that it also acts on tensor functors. *)
Definition ab_tensor_swap_natural {A B A' B'} (f : A $-> A') (g : B $-> B')
  : ab_tensor_swap $o functor_ab_tensor_prod f g
    $== functor_ab_tensor_prod g f $o ab_tensor_swap.
Proof.
  snrapply ab_tensor_prod_ind_homotopy.
  simpl. (* This speeds up the [reflexivity] and the [Defined]. *)
  reflexivity.
Defined.

(** The data of swap together gives us a symmetric braiding on the category of abelian groups. We will later show it is a full symmetric monoidal category. *)
Global Instance symmetricbraiding_ab_tensor_prod : SymmetricBraiding ab_tensor_prod.
Proof.
  snrapply Build_SymmetricBraiding.
  - snrapply Build_NatTrans.
    + intro; exact ab_tensor_swap.
    + snrapply Build_Is1Natural.
      intros; nrapply ab_tensor_swap_natural.
  - intros; nrapply ab_tensor_swap_swap.
Defined. 

(** ** Twisting Triple Tensors *)

(** In order to construct the symmetric monoidal category, we will use what is termed the "Twist construction" in Monoidal.v. This simplifies the data of a symmetric monoidal category by constructing it from simpler parts. For instance, instead of having to prove full associativity [(A ⊗ B) ⊗ C $-> A ⊗ (B ⊗ C)], we can provide a twist map [A ⊗ (B ⊗ C) $-> B ⊗ (A ⊗ C)] and use the symmetric braiding we have so far to prove associativity. *)

(** In order to be more efficient whilst unfolding definitions, we break up the definition of a twist map into its components. *)

Local Definition ab_tensor_prod_twist_map {A B C : AbGroup}
  : A -> ab_tensor_prod B C -> ab_tensor_prod B (ab_tensor_prod A C).
Proof.
  intros a.
  snrapply ab_tensor_prod_rec.
  - intros b c.
    exact (tensor b (tensor a c)).
  - intros b c c'; hnf.
    lhs nrapply ap.
    1: nrapply tensor_dist_l.
    nrapply tensor_dist_l.
  - intros b b' c; hnf.
    nrapply tensor_dist_r.
Defined.

Arguments ab_tensor_prod_twist_map {A B C} _ _ /.

Local Definition ab_tensor_prod_twist_map_additive_r {A B C : AbGroup}
  (a : A) (b b' : ab_tensor_prod B C)
  : ab_tensor_prod_twist_map a (b + b')
    = ab_tensor_prod_twist_map a b + ab_tensor_prod_twist_map a b'.
Proof.
  intros; nrapply grp_homo_op.
Defined.

Local Definition ab_tensor_prod_twist_map_additive_l {A B C : AbGroup}
  (a a' : A) (b : ab_tensor_prod B C)
  : ab_tensor_prod_twist_map (a + a') b
    = ab_tensor_prod_twist_map a b + ab_tensor_prod_twist_map a' b.
Proof.  
  revert b.
  nrapply ab_tensor_prod_ind_homotopy_plus.
  intros b c.
  change (tensor b (tensor (a + a') c)
    = tensor b (tensor a c) + tensor b (tensor a' c)). 
  rhs_V nrapply tensor_dist_l.
  nrapply (ap (tensor b)).
  nrapply tensor_dist_r.
Defined.

(** Given a triple tensor product, we have a twist map which permutes the first two components. *)
Definition ab_tensor_prod_twist {A B C}
  : ab_tensor_prod A (ab_tensor_prod B C) $-> ab_tensor_prod B (ab_tensor_prod A C).
Proof.
  snrapply ab_tensor_prod_rec.
  - exact ab_tensor_prod_twist_map. 
  - exact ab_tensor_prod_twist_map_additive_r.
  - exact ab_tensor_prod_twist_map_additive_l.
Defined.

(** The twist map is involutive. *)
Definition ab_tensor_prod_twist_twist {A B C}
  : ab_tensor_prod_twist $o @ab_tensor_prod_twist A B C $== Id _.
Proof.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  reflexivity.
Defined.

(** The twist map is natural in all 3 arguments. This means that the twist map acts on the triple tensor functor in the same way. *)
Definition ab_tensor_prod_twist_natural {A B C A' B' C'}
  (f : A $-> A') (g : B $-> B') (h : C $-> C')
  : ab_tensor_prod_twist $o fmap11 ab_tensor_prod f (fmap11 ab_tensor_prod g h)
    $== fmap11 ab_tensor_prod g (fmap11 ab_tensor_prod f h) $o ab_tensor_prod_twist.
Proof.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros a b c.
  (* This [change] speeds up the [reflexivity].  [simpl] produces a goal that looks the same, but is still slow. *)
  change (tensor (g b) (tensor (f a) (h c)) = tensor (g b) (tensor (f a) (h c))).
  reflexivity.
Defined.

(** ** Unitality of [abgroup_Z] *)

(** In the symmetric monoidal structure on abelian groups, [abgroup_Z] is the unit. We show that tensoring with [abgroup_Z] on the right is isomorphic to the original group. *)

(** First we characterise the action of integers via [grp_pow] and their interaction on tensors. This is just a generalisation of the distributivity laws for tensors. *)

(** Multiplication in the first factor can be factored out. *)
Definition tensor_ab_mul_l {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor (ab_mul z a) b = ab_mul z (tensor a b)
  := ab_mul_natural (grp_homo_tensor_r b) z a.

(** Multiplication in the second factor can be factored out. *)
Definition tensor_ab_mul_r {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor a (ab_mul z b) = ab_mul z (tensor a b)
  := ab_mul_natural (grp_homo_tensor_l a) z b.

(** Multiplication can be transferred from one factor to the other. The tensor product of [R]-modules will include this as an extra axiom, but here we have [Z]-modules and we can prove it. *)
Definition tensor_ab_mul {A B : AbGroup} (z : Int) (a : A) (b : B)
  : tensor (ab_mul z a) b = tensor a (ab_mul z b).
Proof.
  rhs nrapply tensor_ab_mul_r.
  nrapply tensor_ab_mul_l.
Defined.

(** [abgroup_Z] is a right identity for the tensor product. *) 
Definition ab_tensor_prod_Z_r {A}
  : ab_tensor_prod A abgroup_Z $<~> A.
Proof.
  (** Checking that the inverse map is a homomorphism is easier. *)
  symmetry.
  snrapply Build_GroupIsomorphism.
  - nrapply grp_homo_tensor_r.
    exact 1%int.
  - snrapply isequiv_adjointify.
    + snrapply ab_tensor_prod_rec.
      * exact grp_pow_homo.
      * intros a z z'; cbn beta.
        nrapply grp_homo_op.
      * intros a a' z; cbn beta.
        apply (grp_homo_op (ab_mul z)).
    + hnf.
      change (forall x : ?A, (grp_homo_map ?f) ((grp_homo_map ?g) x) = x)
        with (f $o g $== Id _).
      snrapply ab_tensor_prod_ind_homotopy.
      intros a z.
      change (tensor (B:=abgroup_Z) (grp_pow a z) 1%int = tensor a z).
      lhs nrapply tensor_ab_mul.
      nrapply ap.
      lhs nrapply abgroup_Z_ab_mul.
      apply int_mul_1_r.
    + exact grp_unit_r.
Defined.

(** We have a right unitor for the tensor product given by unit [abgroup_Z]. Naturality of [ab_tensor_prod_Z_r] is straightforward to prove. *)
Global Instance rightunitor_ab_tensor_prod
  : RightUnitor ab_tensor_prod abgroup_Z.
Proof.
  snrapply Build_NatEquiv.
  - intros A.
    apply ab_tensor_prod_Z_r.
  - snrapply Build_Is1Natural.
    intros A A' f.
    snrapply ab_tensor_prod_ind_homotopy.
    intros a z.
    change (grp_pow (f a) z = f (grp_pow a z)).
    exact (grp_pow_natural _ _ _)^.
Defined.

(** Since we have symmetry of the tensor product, we get left unitality for free. *)
Global Instance left_unitor_ab_tensor_prod
  : LeftUnitor ab_tensor_prod abgroup_Z.
Proof.
  rapply left_unitor_twist.
Defined.

(** ** Symmetric Monoidal Structure of Tensor Product *)

(** Using the twist construction we can derive an associator for the tensor product. In other words, we have associativity of the tensor product of abelian groups natural in each factor. *)
Global Instance associator_ab_tensor_prod : Associator ab_tensor_prod.
Proof.
  srapply associator_twist.
  - exact @ab_tensor_prod_twist.
  - intros; nrapply ab_tensor_prod_twist_twist.
  - intros; nrapply ab_tensor_prod_twist_natural.
Defined.

(** The triangle identity is straightforward to prove using the custom induction principles we proved earlier. *)
Global Instance triangle_ab_tensor_prod
  : TriangleIdentity ab_tensor_prod abgroup_Z.
Proof.
  snrapply triangle_twist.
  intros A B.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros a b z.
  exact (tensor_ab_mul _ _ _)^.
Defined.

(** The hexagon identity is also straighforward to prove. We simply have to reduce all the involved functions on the simple tensors using our custom triple tensor induction principle. *)
Global Instance hexagon_ab_tensor_prod : HexagonIdentity ab_tensor_prod.
Proof.
  snrapply hexagon_twist.
  intros A B C.
  snrapply ab_tensor_prod_ind_homotopy_triple.
  intros b a c.
  change (tensor c (tensor a b) = tensor c (tensor a b)).
  reflexivity.
Defined.

(** Finally, we can prove the pentagon identity using the quadruple tensor induction principle. As we did before, the work only involves reducing the involved functions on the simple tensor redexes. *)
Global Instance pentagon_ab_tensor_prod : PentagonIdentity ab_tensor_prod.
Proof.
  snrapply pentagon_twist.
  intros A B C D.
  snrapply ab_tensor_prod_ind_homotopy_quad.
  intros a b c d.
  change (tensor c (tensor d (tensor a b)) = tensor c (tensor d (tensor a b))). 
  reflexivity.
Defined.

(** We therefore have all the data of a monoidal category. *)
Global Instance ismonoidal_ab_tensor_prod
  : IsMonoidal AbGroup ab_tensor_prod abgroup_Z
  := {}.

(** And furthermore, all the data of a symmetric monoidal category. *)
Global Instance issymmmetricmonoidal_ab_tensor_prod
  : IsSymmetricMonoidal AbGroup ab_tensor_prod abgroup_Z
  := {}.

(** TODO: Show that the category of abelian groups is symmetric closed and therefore we have adjoint pair with the tesnor and internal hom. This should allow us to prove lemmas such as tensors distributing over coproducts. *)
