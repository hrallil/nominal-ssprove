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

Module FSAEADScheme.

Fixpoint repeat {A : choiceType} (n : nat) (x : A) (c : A → raw_code A) := 
  match n with
   | 0%N => ret x
   | n.+1 => 
      x' ← c x ;;
      repeat n x' c
  end.

Instance valid_repeat:
∀ {A : choiceType} (L : {fset Location}) (I : Interface) (c : A → raw_code A) (x : A) (N : nat),
    (∀ i : A, ValidCode L I (c i)) → ValidCode L I (repeat N x c).
    intros.
    generalize dependent x.
    induction N as [|N IH]; intros x0.
    - simpl. eapply valid_ret.
    - simpl. eapply valid_bind.
      + eapply H.
      + intros x'.
        apply IH.
Qed.


Record fasaead_scheme :=
  { Mes : choice_type
  ; Key: choice_type
  ; Index: choice_type
  ; Cip: choice_type
  ; AD: choice_type 

  ; fsS : ∀ (a: AD ) (m: Mes ),
      code fset0 [interface] (Index × Cip)

  ; fsR : ∀ (a: AD) (c : Cip),
      code fset0 [interface] (Index × Mes)
  }.

Notation " 'add p " := (AD p)
  (at level 3) : package_scope.

Notation " 'add p " := (AD p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'cip p " := (Cip p)
  (at level 3) : package_scope.

Notation " 'cip p " := (Cip p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'key p " := (Key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'key p " := (Key p)
  (at level 3) : package_scope.
  
Notation " 'index p " := (Index p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'index p " := (Index p)
  (at level 3) : package_scope.
  
Definition FSAEAD := 0%N.

Definition I_CORR (K : fasaead_scheme) :=
  [interface #val #[ FSAEAD] : ('nat)  → 'unit ].

Definition FSAEAD_loc (K : fasaead_scheme) :=
  no_locs.

Definition CORR0 (K : fasaead_scheme) : 
  game (I_CORR K) :=
  [module FSAEAD_loc K ;
    #def #[ FSAEAD ] ( m : 'mes K) (a : 'add K) : ('mes K) {
      '(i, c) ← K.(fsS) a m ;;
      '(i, m') ← K.(fsR) a c ;;

      @ret m'
    }
  ].
  
Definition CORR1 (K : fasaead_scheme) :
  game (I_CORR K) :=
  [module FSAEAD_loc K ;
    #def #[ FSAEAD ] (n : 'nat) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR K b := if b then CORR0 K else CORR1 K.

Definition epoch_loc : Location := ('nat; 11%N).
Definition send_loc (K: cka_scheme) : Location := ('stateS K; 13%N).
Definition rcv_loc (K: cka_scheme) : Location := ('stateR K; 16%N).

Definition init (K : cka_scheme) : raw_code ('unit) :=
  locked (epoch ← get epoch_loc ;;
  match epoch with
  | 0%N =>
    '(pk, x) ← K.(keygen) ;;
    #put (send_loc K) := pk ;;
    #put (rcv_loc K) := x ;;

    @ret 'unit Datatypes.tt
  | _.+1 =>
    @ret 'unit Datatypes.tt
  end).

#[export] Instance init_valid {K} {L : {fset Location}} {I : Interface}
  : epoch_loc \in L → send_loc K \in L → rcv_loc K \in L → ValidCode L I (init K).
Proof.
  intros epoch send rcv.
  rewrite /init -lock.
  ssprove_valid.
Qed.

Definition EPOCH := 3%N.

Definition I_CKA_PCS (K : cka_scheme) :=
  [interface
    #val #[ EPOCH ] : 'unit → (('mes K × 'key K) × 'option('stateR K))
  ].

Definition CKA_PCS (K : cka_scheme) bit t :
  game (I_CKA_PCS K) :=
  [module fset [:: epoch_loc ; send_loc K ; rcv_loc K] ;
    #def #[ EPOCH ] (_ : 'unit) : (('mes K × 'key K) × 'option('stateR K)) {
      _ ← init K ;;

      epoch ← get epoch_loc ;;
      let epoch_inc := epoch.+1 in
      #put epoch_loc := epoch_inc ;;

      (* Send *)
      stateS ← get send_loc K ;;
      '(stateR', m, k) ← K.(ckaS) stateS ;;

      (* Receive *)
      stateR ← get rcv_loc K ;;
      '(stateS', k) ← K.(ckaR) stateR m ;;
      
      #put (rcv_loc K) := stateR' ;;
      #put (send_loc K) := stateS' ;;

      (* Challenge Epoch *)
      if (epoch_inc == t) then
        if (bit) then
          @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k), None)
        else
          k' ← K.(sampleKey) ;;
          @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k'), None)

      (* Pre-challenge Epoch *)
      else if (epoch_inc.+1 == t) then
        (* Corruption is not allowed *)
        @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k), None)
      else
        @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k), Some(stateR'))
    }
 ].

End FSAEADScheme.