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
