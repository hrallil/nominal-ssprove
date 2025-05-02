Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

Module KEMScheme.

Record kem_scheme := {
    (* Public Key *)
    KEM_PKey : choice_type ;

    (* Secret Key *)
    KEM_SKey : choice_type ;

    (* Encapsulation *)
    KEM_EKey : choice_type ;

    (* Symmetric Key *)
    KEM_Key : choice_type ;

    KEM_kgen : code fset0 [interface] (KEM_PKey × KEM_SKey) ;
    KEM_encap : KEM_PKey → code fset0 [interface] (KEM_Key × KEM_EKey) ;
    KEM_decap : KEM_SKey → KEM_EKey → KEM_Key ;

    KEM_keypair : (KEM_PKey × KEM_SKey) → Prop ;
    KEM_kgen_spec: ⊢ₛ KEM_kgen ⦃ KEM_keypair ⦄ ;
    encap_spec (pk : KEM_PKey) (kek : chProd KEM_Key KEM_EKey) : Prop :=
      ∀ sk, KEM_keypair (pk, sk) → KEM_decap sk kek.2 = kek.1 ;
    KEM_encap_spec : ∀ (pk : KEM_PKey), ⊢ₛ KEM_encap pk ⦃ (encap_spec pk) ⦄
}.

Notation " 'kemPKey p " := (KEM_PKey p)
  (at level 3) : package_scope.
Notation " 'kemPKey p " := (KEM_PKey p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemSKey p " := (KEM_SKey p)
  (at level 3) : package_scope.
Notation " 'kemSKey p " := (KEM_SKey p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemKey p " := (KEM_Key p)
  (in custom pack_type at level 2, p constr at level 20).
Notation " 'kemKey p " := (KEM_Key p)
  (at level 3) : package_scope.

Notation " 'kemEKey p " := (KEM_EKey p)
  (in custom pack_type at level 2, p constr at level 20).
Notation " 'kemEKey p " := (KEM_EKey p)
  (at level 3) : package_scope.

Definition GET := 0%N.

Definition I_KEM (K : kem_scheme) :=
  [interface
    #val #[ GET ] : 'unit  → ('kemKey K × 'kemKey K)
  ].

Definition KEM_1 (K : kem_scheme) :
  game (I_KEM K) :=
  [module no_locs ;
    #def #[ GET ] (_ : 'unit) : ('kemKey K × 'kemKey K) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;
      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      ret (kemKey, kemKey)
    }
  ].

Definition KEM_0 (K : kem_scheme) :
  game (I_KEM K) :=
  [module no_locs ;
    #def #[ GET ] (_ : 'unit) : ('kemKey K × 'kemKey K) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;

      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      let kemKey' := K.(KEM_decap)(kemSKey)(kemEKey) in

      ret (kemKey, kemKey')
    }
  ].

Definition KEM (K : kem_scheme) b := if b then KEM_0 K else KEM_1 K.

End KEMScheme.