Class EndoFunctor {C : Category} := {

EF_obj : @Obj C -> @Obj C;

EF_mor : forall {x y}, (Hom x y) -> (Hom (EF_obj x) (EF_obj y));

EF_id_ax : forall {x}, EF_mor (Id x) = Id (EF_obj x);

EF_comp_ax : forall {x y z : @Obj C} {f g},
      @EF_mor x z (f ∘ g) = (@EF_mor y z f) ∘ (@EF_mor x y g)
}.

Notation "⊥" := (Initial_obj) (at level 40, no
associativity) : type_scope.

Context {F : EndoFunctor}.


Definition isomorph x y := exists (i : x → y) (j : y → x), i ∘ j = Id y /\ j ∘ i = Id x.

Notation "x '≅' y" := (isomorph x y) (at level 40, left associativity) :
type_scope.


Class F_algebra {C : Category} (F : @EndoFunctor C) := {

Carr_F_alg : @Obj C;

Mor_F_alg : Hom ((@EF_obj C F) Carr_F_alg) Carr_F_alg
}.

Definition F_algebras_Obj {C : Category} (F : @EndoFunctor C) := (@sigT (@Obj C) (fun (x:@Obj C) => Hom (@EF_obj C F x) x) ) : Type.

Definition F_algebras_Hom {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) (y : F_algebras_Obj F) 
:= (sig (fun (f : @Hom C (projT1 x) (projT1 y) ) => (projT2 y) ∘ (EF_mor f )  = f ∘ (projT2 x)  )).

Definition F_algebras_Id {C : Category} (F : @EndoFunctor C) (x : F_algebras_Obj F) : @F_algebras_Hom C F x x.
unfold F_algebras_Hom.
exists (@Id C (projT1 x)).
rewrite EF_id_ax.
rewrite id_1.
rewrite id_2.
reflexivity.
Defined.

Definition F_algebras_Comp {C : Category} (F : @EndoFunctor C) (x y z : F_algebras_Obj F)
(h : F_algebras_Hom F y z ) (k : F_algebras_Hom F x y ) : F_algebras_Hom F x z.
unfold F_algebras_Hom.
unfold F_algebras_Hom in h, k.
exists ((proj1_sig h) ∘ (proj1_sig k)).
rewrite EF_comp_ax.
rewrite assoc.
rewrite (proj2_sig h).
rewrite <- assoc.
rewrite (proj2_sig k).
rewrite assoc.
reflexivity.
Defined.


Definition F_algebras_form_a_Cat {C : Category} (F : @EndoFunctor C) : Category.
Proof.
apply (cat_mk (@F_algebras_Obj C F) (@F_algebras_Hom C F) (@F_algebras_Id C F) (@F_algebras_Comp C F) ).
all: intros.
elim 
(* Eddig OK *)

Qed.

