Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.NatTrans.

(** ** Equivalences in wild categories *)

(** An equivalence of Wild 1-Categories is a split essentially surjective functor F, that is a groupoid equivalence on every hom-set.  *)

Class IsCatEquiv {A B : Type} (F : A -> B) `{Is1Functor A B F} `{!HasEquivs B} :=
  {
    spl_ess_surj (b : B) : {a : A & F a $<~> b};
    hom_spl_ess_surj {a b : A} (f : F a $-> F b) 
      : {g : a $-> b & fmap F g $== f}; (* Here we're using the groupoid structure to avoid equivalences. *)
    hom_surjinj {a b : A} {f g : a $-> b} 
      : fmap F f $== fmap F g -> f $== g
  }.

Arguments spl_ess_surj {A B} F {_ _ _ _ _ _ _ _ _ _ _ _} b : rename.
Arguments hom_spl_ess_surj {A B} F {_ _ _ _ _ _ _ _ _ _ _ _ _ _} f : rename.
Arguments hom_surjinj {A B} F {_ _ _ _ _ _ _ _ _ _ _ a b f g} p : rename.

(** If [F : A -> B] is an equivalence of categories, then we expect there to be a functor [G : B -> A] such that [F] and [G] are quasi-inverses. *)
Section CatEquivInverse.
  Context {A B : Type} (F : A -> B) `{IsCatEquiv A B F}.

  Definition G (b : B) : A := pr1 (spl_ess_surj F b).

  Definition approx_by_F {b b' : B} (f : b $-> b') : F (G b) $-> F (G b').
  Proof.
    pose (ab := pr2 (spl_ess_surj F b)).
    pose (ab' := pr2 (spl_ess_surj F b')).
    exact (ab'^-1$ $o f $o ab).
  Defined.

  Instance G_is0functor : Is0Functor G.
  Proof.
    snrapply Build_Is0Functor.
    intros b b' g.
    exact (pr1 (hom_spl_ess_surj F (approx_by_F g))).
  Defined.
End CatEquivInverse.

(** I don't think this type is contractlible under Univalence and probably HasMorExt. *)

Class IsCatQuasiInv {A B : Type} (F : A -> B) `{Is1Functor A B F, !HasEquivs A, !HasEquivs B} :=
  {
    cat_qinv : B -> A;
    cat_qinv_is0functor : Is0Functor cat_qinv;
    cat_qinv_is1functor : Is1Functor cat_qinv;
    is_cat_sect : NatEquiv (cat_qinv o F) idmap;
    is_cat_retr : NatEquiv (F o cat_qinv) idmap
  }.

(* I have no idea if this is more correct than the above type or not. *)

Class IsCatBiInv {A B : Type} (F : A -> B) 
  `{Is1Functor A B F, !HasEquivs A, !HasEquivs B} :=
  {
    cat_qlinv : B -> A;
    cat_qlinv_is0functor : Is0Functor cat_qlinv;
    cat_qlinv_is1functor : Is1Functor cat_qlinv;
    cat_qrinv : B -> A;
    cat_qrinv_is0functor : Is0Functor cat_qrinv;
    cat_qrinv_is1functor : Is1Functor cat_qrinv;
    is_cat_sect_l : NatEquiv (cat_qlinv o F) idmap;
    is_Cat_retr_r : NatEquiv (F o cat_qrinv) idmap
  }.

(* Observe that there is a map [IsCatQuasiInv F -> IsCatBiInv F]. These types should hopefully be logically equivalent. *)
