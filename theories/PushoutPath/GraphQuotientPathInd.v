Require Import Types.
Require Import Basics.
Require Import Colimits.GraphQuotient.
Require Import WildCat.

(** This file proves the induction principle for path spaces of coequalizers. This follows the paper PATH SPACES OF HIGHER INDUCTIVE TYPES
IN HOMOTOPY TYPE THEORY by Kraus and von Raumer. Their formalization can be found at https://gitlab.com/fplab/freealgstr. In the [FamilyCat] section we will define the categories [C] and [D] as described by this paper. [C] will be denoted [ptd_family_with_relations], and [D] will be denoted [ptd_family_graphquotient]. Since our final goal relies on the flattening lemma, we will currently assume univalence throughout the entire section. *)

Section FamilyCat.
  Context `{Univalence} {A : Type} (a0 : A) (R : A -> A -> Type).

  (** [ptd_family_with_relations] represents the wild category of pointed type families that respect the relation. That is, if there is a term [r : R b c], then there is an equivalence [K b <~> K c]. *)

  Definition ptd_family_with_relations : Type 
    := {K : A -> Type & K a0 * forall b c : A, R b c -> K b <~> K c}.

  (** Accessor functions for [ptd_family_with_relations]. *)

  (** First projection *)
  Definition K_ : ptd_family_with_relations -> A -> Type := pr1.

  (** Second projection *)
  Definition r_ (Kre : ptd_family_with_relations) : K_ Kre a0 := fst (pr2 Kre).

  (** Third projection *)  
  Definition e_ (Kre : ptd_family_with_relations) {b c : A} 
    : R b c -> (K_ Kre) b <~> (K_ Kre) c := snd (pr2 Kre) b c.

  (** The arrows in this category are given by another triple. The first component is a collection of functions betwen the fibers of the type families. The second component is the assertion that this collection of functions respects the base point. The third component asserts that this collection is natural. *)

  Instance isgraph_ptd_family_with_relations : IsGraph ptd_family_with_relations.
  Proof.
    snrapply Build_IsGraph.
    intros Kre Kre'.
    exact {f : forall b : A, K_ Kre b -> K_ Kre' b 
      & (f a0 (r_ Kre) = r_ Kre') 
      * forall b c : A, forall s : R b c, 
        ((e_ Kre') s) o (f b) == (f c) o (e_ Kre) s}.
  Defined.

  (** Accessor functions for the homs of [ptd_family_with_relations]. *)

  (** first projection *)
  Definition f_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre') (b : A)
    : K_ Kre b -> K_ Kre' b := pr1 f b.

  (** Second projection *)
  Definition d_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre')
    : f_ f a0 (r_ Kre) = r_ Kre' := fst (pr2 f).

  (** Third projection *)
  Definition gamma_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre') 
    {b c : A} (s : R b c) : (e_ Kre' s) o (f_ f b) == (f_ f c) o (e_ Kre s)
    := snd (pr2 f) b c s.

  (** [ptd_family_with_relations] defines a 1-category with morphism extensionality. *)

  Instance is01cat_ptd_family_with_relations : Is01Cat ptd_family_with_relations.
  Proof.
    snrapply Build_Is01Cat.
    - intro Kre.
      srefine (_ ; _).
      + intro a. exact idmap.
      + srefine (_ , _).
        * reflexivity.
        * intros b c s k. reflexivity.
    - intros Kre1 Kre2 Kre3 g f.
      srefine (_ ; _).
      + intro a. exact ((f_ g a) o (f_ f a)).
      + srefine (_ , _).
        * simpl. exact ((ap (f_ g a0) (d_ f)) @ d_ g).
        * intros b c s k.
          lhs nrapply (gamma_ g s).
          nrapply (ap (f_ g c) (gamma_ f s k)).
  Defined.

  (* I don't think these are the 2-cells that I want. At some point I'm forced to use funext. Switching these cells out with some homtopies sounds smarter, but I'm not so sure how this is done, as I need transports as well. *)
  Instance is2graph_ptd_family_with_relations : Is2Graph ptd_family_with_relations.
  Proof.
    intros Kre Kre'.
    snrapply Build_IsGraph.
    intros f g. exact (f = g).
  Defined.

  Instance is1cat_ptd_family_with_relations : Is1Cat ptd_family_with_relations.
  Proof.
    snrapply Build_Is1Cat'.
    - intros Kre Kre'.
      snrapply Build_Is01Cat.
      + intros f. reflexivity.
      + intros f g h p q. exact (q @ p).
    - intros Kre Kre'.
      snrapply Build_Is0Gpd.
      + intros f g p. exact p^.
    - intros Kre Kre' Kre'' f.
      snrapply Build_Is0Functor.
      + intros g h []. reflexivity.
    - intros Kre Kre' Kre'' f.
      snrapply Build_Is0Functor.
      + intros g h []. reflexivity.
    - intros Kre Kre' Kre'' Kre''' f g h.
      snrapply path_sigma.
      + reflexivity.
      + unfold transport. 
        snrapply path_prod.
        * cbn.
          lhs snrapply concat_p_pp.
          apply (ap (fun x => x @ d_ h)).
          lhs snrapply (ap_compose (f_ g a0) _ _ @@ 1).
          snrapply (ap_pp _ _ _)^.
        * cbn.
          (* I don't like this *)
          apply apD10^-1. intro b.
          apply apD10^-1. intro c.
          apply apD10^-1. intro s.
          apply apD10^-1. intro k.
          lhs_V nrapply concat_p_pp.
          apply (ap (fun x => _ @ x)).
          lhs nrapply (1 @@ ap_compose _ _ _).
          nrapply (ap_pp _ _ _)^.
    - intros Kre Kre' f.
      snrapply path_sigma.
      + reflexivity.
      + unfold transport.
        snrapply path_prod.
        * cbn.
          lhs nrapply concat_p1.
          nrapply ap_idmap.
        * cbn.
          (* I don't like this *)
          apply apD10^-1. intro b.
          apply apD10^-1. intro c.
          apply apD10^-1. intro s.
          apply apD10^-1. intro k.
          lhs nrapply concat_1p.
          nrapply ap_idmap.
    - intros Kre Kre' f.
      snrapply path_sigma.
      + reflexivity.
      + unfold transport.
        snrapply path_prod.
        * cbn.
          nrapply concat_1p.
        * cbn.
          (* I don't like this *)
          apply apD10^-1. intro b.
          apply apD10^-1. intro c.
          apply apD10^-1. intro s.
          apply apD10^-1. intro k.
          nrapply concat_p1.
  Defined.

  (** Since the 2-cells are defined to be paths, we trivially have morphism extensionality, and the 1-category is strong. *)

  (* It would still be nice if this could be true with a better choice of paths. Since I'm assuming univalence, maybe a homotopy version of the above could work out nicely. *)
  Instance hasmorext_ptd_family_with_relations : HasMorExt ptd_family_with_relations.
  Proof.
    snrapply Build_HasMorExt.
    intros Kre Kre' f g.
    snrapply (Build_IsEquiv _ _ _ idmap).
    all: intros []; reflexivity.
  Defined.

  (** [ptd_family_graphquotient] represents the wild category of pointed type families over the [GraphQuotient R]. *)

  Definition ptd_family_graphquotient : Type
    := {L : GraphQuotient R -> Type & L (gq a0)}.

  (** Accessor functions fpr [ptd_family_graphquotient]. *)

  (** First projection *)
  Definition L_ : ptd_family_graphquotient -> GraphQuotient R -> Type := pr1.

  (** Second projection *)
  Definition p_ (Lp : ptd_family_graphquotient) : L_ Lp (gq a0) := pr2 Lp.

  (** The arrows in this category is given by a tuple. The first component is a collection of functions between the fibers of the type families. The second component is the assertion that this collection respects the basepoint. *)

  Instance isgraph_ptd_family_graphquotient : IsGraph ptd_family_graphquotient.
  Proof.
    snrapply Build_IsGraph.
    intros Lp Lp'.
    exact {g : forall x : GraphQuotient R, L_ Lp x -> L_ Lp' x 
      & g _ (p_ Lp) = p_ Lp'}.
  Defined.

  (** Accessor functions for the homs of [ptd_family_graphquotient]. *)

  (** First projection *)
  Definition g_ {Lp Lp' : ptd_family_graphquotient} (f : Lp $-> Lp') (x : GraphQuotient R) 
    : L_ Lp x -> L_ Lp' x := pr1 f x.

  (** Second projection *)
  Definition epsilon_ {Lp Lp' : ptd_family_graphquotient} (f : Lp $-> Lp') 
    : g_ f _ (p_ Lp) = p_ Lp' := pr2 f.

  (** [ptd_family_graphquotient] defines a 1-category with morphism extensionality. *)

  Instance is01cat_ptd_family_graphquotient : Is01Cat ptd_family_graphquotient.
  Proof.
    snrapply Build_Is01Cat.
    - intros Lp. srefine (_ ; _).
      + intro x. exact idmap.
      + reflexivity.
    - intros Lp Lp' Lp'' g f. srefine (_ ; _).
      + intro x. exact ((g_ g x) o (g_ f x)).
      + cbn.
        lhs nrapply (ap _ (epsilon_ f)).
        nrapply (epsilon_ g).
  Defined.

  (* Likewise as above, these 2-cells does not seem to be the correct choice. We should only have the same problems of defnining homotopical versions for these 2-cells as before. *)
  Instance is2graph_ptd_family_graphquotient : Is2Graph ptd_family_graphquotient.
  Proof.
    intros Lp Lp'.
    snrapply Build_IsGraph.
    intros f g. exact (f = g).
  Defined.

  Instance is1cat_ptd_family_graphquotient : Is1Cat ptd_family_graphquotient.
  Proof.
    snrapply Build_Is1Cat'.
    - intros Lp Lp'.
      snrapply Build_Is01Cat.
      + intro p. reflexivity.
      + intros f g h [] []. reflexivity.
    - intros Lp Lp'.
      snrapply Build_Is0Gpd.
      intros f g []. reflexivity.
    - intros Lp Lp' Lp'' f.
      snrapply Build_Is0Functor.
      intros g h []. reflexivity.
    - intros Lp Lp' Lp'' f.
      snrapply Build_Is0Functor.
      intros g h []. reflexivity.
    - intros Lp Lp' Lp'' Lp''' f g h.
      snrapply path_sigma.
      + reflexivity.
      + cbn.
        lhs nrapply concat_p_pp.
        apply (ap (fun x => x @ epsilon_ h)).
        lhs nrapply (ap_compose _ _ _ @@ 1).
        nrapply (ap_pp _ _ _)^.
    - intros Lp Lp' f.
      snrapply path_sigma.
      + reflexivity.
      + cbn.
        lhs nrapply concat_p1.
        nrapply ap_idmap.
    - intros Lp Lp' f.
      snrapply path_sigma.
      + reflexivity.
      + cbn. nrapply concat_1p.
  Defined.

  Instance hasmorext_ptd_family_graphquotient : HasMorExt ptd_family_graphquotient.
  Proof.
    snrapply Build_HasMorExt.
    intros Lp Lp' f g.
    snrapply (Build_IsEquiv _ _ _ idmap).
    all: intros []; reflexivity.
  Defined.

  (** The initial object of [ptd_family_graphquotient]. *)
  Definition initLp : ptd_family_graphquotient.
  Proof.
    srefine (_ ; _).
    - intro x. exact (gq a0 = x).
    - exact (idpath (gq a0)).
  Defined.

  (* The choice of 2-cells makes this very difficult to prove, as funext gets in the way. Maybe there is a simple solution that I just don't know of ¯\_(ツ)_/¯*)
  Definition isinitial_initLp : IsInitial initLp.
  Proof.
    intro Lp.
    srefine (_ ; _).
    - srefine (_ ; _).
      + intros x []. exact (p_ Lp).
      + reflexivity.
    - intro f.
      snrapply path_sigma.
      + cbn.
        apply apD10^-1. intro x.
        apply apD10^-1. intros []. exact (epsilon_ f)^.
      + unfold transport. cbn.
  Abort.

End FamilyCat.
