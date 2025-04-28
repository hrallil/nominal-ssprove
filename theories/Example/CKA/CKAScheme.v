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

Module CKAScheme.

Record cka_scheme :=
  { Mes : choice_type
  ; Key: choice_type
  ; StateS: choice_type
  ; StateR: choice_type

  ; sampleKey : code fset0 [interface] (Key)
  
  ; sampleX : code fset0 [interface] (StateR)
  
  ; keygen : code fset0 [interface] (StateS × StateR)

  ; ckaS : ∀ (state: StateS) (x: StateR),
      code fset0 [interface] (StateR × Mes × Key)

  ; ckaR : ∀ (state: StateR) (m : Mes),
      code fset0 [interface] (StateS × Key)
  }.

Notation " 'stateS p " := (StateS p)
  (at level 3) : package_scope.

Notation " 'stateS p " := (StateS p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'stateR p " := (StateR p)
  (at level 3) : package_scope.

Notation " 'stateR p " := (StateR p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'key p " := (Key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'key p " := (Key p)
  (at level 3) : package_scope.

Definition CKAKEY := 0%N.
Definition stater_loc (K: cka_scheme) : Location := ('option ('stateR K); 1%N).
Definition states_loc (K: cka_scheme) : Location := ('option ('stateS K); 2%N).

Definition CKA_loc (K : cka_scheme) :=
  fset [:: stater_loc K ; states_loc K ].

Definition I_CORR_simple (K : cka_scheme) :=
  [interface #val #[ CKAKEY ] : 'unit  → 'unit ].

Definition I_CORR (K : cka_scheme) :=
  [interface #val #[ CKAKEY] : ('nat)  → 'unit ].

Definition CORR0_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (_ : 'unit) : 'unit {
      '(pk, x) ← K.(keygen) ;;
      
      x' ← K.(sampleX) ;;
      '(stateA, m, kA) ← K.(ckaS) pk x' ;;
      '(stateB, kB) ← K.(ckaR) x m ;;

      #assert (kA == kB) ;;

      x'' ← K.(sampleX) ;;
      '(stateB', m', kB') ← K.(ckaS) stateB x'' ;;
      '(stateA', kA') ← K.(ckaR) stateA m' ;;

      #assert (kA' == kB') ;;

      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR1_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (_: 'unit) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

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

Definition CORR0 (K : cka_scheme) : 
  game (I_CORR K) :=
  [module CKA_loc K ;
    #def #[ CKAKEY ] (n : ('nat)) : 'unit {
      '(pk, x) ← K.(keygen) ;;
      
      repeat (n) ((pk, x) : ('stateS K × 'stateR K))  (fun state =>       
        let '(stateS, stateR) := state in
        
        x' ← K.(sampleX) ;;
        '(stateR', m, kS) ← K.(ckaS) stateS x' ;;
        '(stateS', kR) ← K.(ckaR) stateR m ;;

        #assert (kS == kR) ;;
        @ret ('stateS K × 'stateR K) (stateS', stateR')
      ) ;;
      @ret 'unit Datatypes.tt
    }
  ].
  
Definition CORR1 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (n : 'nat) : 'unit {
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

Definition I_CKA_SECURITY (K : cka_scheme) :=
  [interface
    #val #[ EPOCH ] : ('stateR K) → (('mes K × 'key K) × 'option('stateR K))
  ].

Definition CKA_SECURITY (K : cka_scheme) t bit :
  game (I_CKA_SECURITY K) :=
  [module fset [:: epoch_loc ; send_loc K ; rcv_loc K] ;
    #def #[ EPOCH ] (r : ('stateR K)) : (('mes K × 'key K) × 'option('stateR K)) {
      _ ← init K ;;

      epoch ← get epoch_loc ;;
      let epoch_inc := epoch.+1 in
      #put epoch_loc := epoch_inc ;;

      (* Send *)
      stateS ← get send_loc K ;;

      (* Cannot corrupt on t - 1 and t *)
      if ((epoch_inc.+1 == t) || (epoch_inc == t)) then
        x ← K.(sampleX) ;;
        '(stateR', m, k) ← K.(ckaS) stateS x ;;

        (* Receive *)
        stateR ← get rcv_loc K ;;
        '(stateS', k') ← K.(ckaR) stateR m ;;
        
        #assert (k == k') ;;
        
        #put (rcv_loc K) := stateR' ;;
        #put (send_loc K) := stateS' ;;
        
        (* Challenge Epoch *)
        if (epoch_inc == t) then
          if (bit) then
            @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k'), None)
          else
            k'' ← K.(sampleKey) ;;
            @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k''), None)

        (* Pre-challenge Epoch *)
        else
          @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k'), None)
      else
        '(stateR', m, k) ← K.(ckaS) stateS r ;;

        (* Receive *)
        stateR ← get rcv_loc K ;;
        '(stateS', k') ← K.(ckaR) stateR m ;;
        
        #assert (k == k') ;;
        
        #put (rcv_loc K) := stateR' ;;
        #put (send_loc K) := stateS' ;;

        @ret (('mes K × 'key K) × 'option('stateR K)) ((m, k'), Some(stateR'))
    }
 ].
  
End CKAScheme.