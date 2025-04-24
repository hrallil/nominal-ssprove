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

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.
Require Import Lia.

From NominalSSP Require Import DDH CKAScheme.

Module CKA_KEM (GP : GroupParam).

Module DDH' := DDH GP.
Import CKAScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

(* ------------ KEM START -------------- *)

(* Public and secret key *)
Context (chPKey chSKey : choice_type).

(* Plain text *)
Context (chPlain : choice_type).

(* Symmetric key *)
Context (keyD : Op).
Definition chKey := keyD.π1.

Context (ekeyD : Op).
Definition chEKey := ekeyD.π1.

(* Cipher text *)
Context (cipherD : Op).
Definition chCipher := cipherD.π1.

Notation "'smkey" := (chKey) (in custom pack_type at level 2).
Notation "'smkey" := (chKey) (at level 2) : package_scope.

Notation "'pkey" := (chPKey) (in custom pack_type at level 2).
Notation "'pkey" := (chPKey) (at level 2) : package_scope.

Notation "'skey" := (chSKey) (in custom pack_type at level 2).
Notation "'skey" := (chSKey) (at level 2) : package_scope.

Notation "'plain" := (chPlain) (in custom pack_type at level 2).
Notation "'plain" := (chPlain) (at level 2) : package_scope.

Notation "'ekey" := (chEKey) (in custom pack_type at level 2).
Notation "'ekey" := (chEKey) (at level 2) : package_scope.

Notation "'cipher" := (chCipher) (in custom pack_type at level 2).
Notation "'cipher" := (chCipher) (at level 2) : package_scope.

Record KEM_scheme := {
    KEM_kgen : code fset0 [interface] (chProd 'pkey 'skey) ;
    KEM_encap : 'pkey → code fset0 [interface] (chProd 'smkey 'ekey) ;
    KEM_decap : 'skey → 'ekey → 'smkey
}.

(* ------------ KEM END -------------- *)

Definition cka_kem (kem: KEM_scheme) : cka_scheme := {|
    Mes := chEKey × chPKey 
  ; Key := chKey
  ; StateS := chPKey
  ; StateR := chSKey

  ; sampleKey :=
    {code 
      '(kemPKey, _) ← kem.(KEM_kgen) ;;
      '(kemKey, _) ← kem.(KEM_encap)(kemPKey) ;;
      ret kemKey
    }

  ; sampleX := 
    {code 
      '(kemPKey, kemSKey) ← kem.(KEM_kgen) ;;
      ret (kemSKey)
    }

  ; keygen := 
    {code
      '(kemPKey, kemSKey) ← kem.(KEM_kgen) ;;
      ret (kemPKey, kemSKey)
    }

  ; ckaS := λ γ x,
    {code
      '(kemKey, kemEKey) ← kem.(KEM_encap)(γ) ;;
      '(kemPKey, kemSKey) ← kem.(KEM_kgen) ;;

      (* (sk, (c, pk), I) *)
      ret (kemSKey, (kemEKey, kemPKey), kemKey)
    }

  ; ckaR := λ γ m,
    {code
      let '(kemEKey, kemPKey) := m in
      let kemKey := kem.(KEM_decap)(γ)(kemEKey) in
      ret (kemPKey, kemKey)
    }
  |}.
  
Definition CKA_CORR_KEM := 0%N.

Definition I_CORR_KEM_simple (K : KEM_scheme) :=
  [interface #val #[ CKA_CORR_KEM ] : 'unit  → ('smkey × 'smkey)].

Definition CORR0_kem (K : KEM_scheme) :
  game (I_CORR_KEM_simple K) :=
  [module no_locs ;
    #def #[ CKA_CORR_KEM ] (_ : 'unit) : ('smkey × 'smkey) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;
      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      let kemKey' := K.(KEM_decap)(kemSKey)(kemEKey) in

      ret (kemKey, kemKey')
    }
  ].
  
Definition CORR1_kem (K : KEM_scheme) :
  game (I_CORR_KEM_simple K) :=
  [module no_locs ;
    #def #[ CKA_CORR_KEM ] (_ : 'unit) : ('smkey × 'smkey) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;
      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      ret (kemKey, kemKey)
    }
  ].

Definition CORR_KEM_RED (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    (* CKAKEY matches the oracle name from CORR_simple from the CKAScheme.v *)
    #def #[ CKAKEY ] (_ : 'unit) : 'unit {
      #import {sig #[ CKA_CORR_KEM ] : 'unit → ('smkey × 'smkey) } as GET_CORR_KEM ;;

      (*
        This throws an error
      
      '(kemKey, kemKey') ← GET_CORR_KEM tt ;;
      #assert (kemKey == kemKey') ;; *)

      @ret 'unit Datatypes.tt
    }
  ].

(*Theorem perfect (kem : KEM_scheme) : (CORR0_simple (cka_kem kem)) ≈₀ (CORR_KEM_RED (cka_kem kem) ∘ CORR0_kem kem).*)

(* This says that we have unfinished goal:

    All the remaining goals are on the shelf:

    {fset Location}
    ValidPackage ?L' Game_import (I_CORR_simple (cka_kem kem))
      (CORR_KEM_RED (cka_kem kem) ∘ CORR1_kem kem)%sep
  *)
Theorem perfect_1 (kem : KEM_scheme) :
  perfect (I_CORR_simple (cka_kem kem))(CORR1_simple (cka_kem kem))
          (CORR_KEM_RED (cka_kem kem) ∘ CORR1_kem kem).
Proof.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_ret.
  done.
Admitted.


(* Here we do now know how to unfold the KEMs such as (x ← KEM_kgen kem ;;) *)
Theorem perfect_0 (kem : KEM_scheme) :
  perfect (I_CORR_simple (cka_kem kem))(CORR0_simple (cka_kem kem))
          (CORR_KEM_RED (cka_kem kem) ∘ CORR0_kem kem).
Proof.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_simpl.
  admit.
Admitted.



(*Theorem perfect (I_CKA_PCS cka)(CORR1 (cka kem)) =0 (CORR_RED o CORR1_kem kem).

Theorem test kem: AdvFor (CORR (cka kem)) A <= AdvFor (CORR_kem kem) (A o CORR_RED).
Proof.

Qed.*)

End CKA_KEM.
