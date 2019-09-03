
Require Import Coq.Vectors.Vector.
        Import VectorNotations.
Require Import Coq.Sorting.Permutation.

Module Type PokerFunctions.

  (* Of Cards and Decks *)
  Parameter  Card              : Type.
  Parameter  standard_deck     : t Card 52.
  Parameter  shuffle           : forall n : nat, t Card n -> t Card n.
  Axiom      shuffle_changes   : forall n : nat, forall deck : t Card n,
                                        n > 1 -> shuffle n deck <> deck.
  Axiom      Shuffle_perumute  : forall n : nat, forall deck : t Card n,
                                 Permutation (to_list deck) (to_list (shuffle n deck)).
  Parameter  count_cards : Card -> nat.
  Axiom countable_cards : forall n : nat, 
      n < 14 -> exists c0 c1 c2 c3 : Card, 
            (count_cards c0 = count_cards c1) /\ 
            (count_cards c2 = count_cards c3) /\ 
            (count_cards c0 = count_cards c3).
  Definition hand              := option (prod Card Card).

  (* Of Players *)
  Definition Player           : Type := (nat * hand).
  Definition get_hand : Player -> hand    := snd .
  Definition get_money : Player -> nat := fst.
  Parameter  number_of_players : nat.
  Definition max_players       := 6.
  Axiom      multiple_players  : (number_of_players > 1) /\ (number_of_players <= max_players).
  Definition Players           := t Player number_of_players.
  Definition Active {n : nat} {c0 c1 : Card} (p: Player) : Prop := p = (n,Some (c0,c1)).

  (* Of Card Flops *)
  Definition flop : Type       := (Card * Card * Card).
  Definition turn              := prod Card flop.
  Definition river             := prod Card turn.
  Definition get_flop { n : nat } (deck : t Card (S ( S ( S ( S ( S n)))))) : 
                                 ((t Card (S (S n))) * flop ):=
      let c1 := hd deck                 in
      let c2 := hd (tl deck)            in
      let c3 := hd (tl (tl deck))       in
      let new_deck := tl (tl (tl deck)) in
      (new_deck, (c1,c2,c3)).
  Definition get_turn {n : nat} (deck : t Card (S (S n))) (fl : flop) : 
    ((t Card (S n)) * turn) :=
    (tl deck, (hd deck, fl)).
  Definition get_river {n : nat} (deck : t Card (S n)) (fl : flop) : 
    ((t Card n) * turn) :=
    (tl deck, (hd deck, fl)).

  (* Of Betting *)
  Definition bet (pl : Player) (pot : nat) (bet : nat) 
    : (Player * nat)  :=
    ( (get_money pl - bet, get_hand pl) , pot + bet).

End PokerFunctions.

Print All.

Module Type single_n.
  Parameter n : nat.
  Axiom    in_range : (n > 1) /\ n < 7.
End single_n.

Module impl (n' : single_n) <: PokerFunctions.
  
Inductive Name : Type :=
| Ace   : Name
| Two   : Name
| Three : Name
| Four  : Name
| Five  : Name
| Six   : Name
| Seven : Name
| Eight : Name
| Nine  : Name
| Ten   : Name
| Jack  : Name
| Queen : Name
| King  : Name
.

Definition Names : t Name 13  :=
  [
    Ace   ;
    Two   ;
    Three ;
    Four  ;
    Five  ;
    Six   ;
    Seven ;
    Eight ;
    Nine  ;
    Ten   ;
    Jack  ;
    Queen ;
    King  
  ]
.

Inductive Card' : Type :=
| Heart   : Name -> Card'
| Spade   : Name -> Card'
| Club    : Name -> Card'
| Diamond : Name -> Card'
.

Definition Card := Card'.

Definition standard_deck : t Card 52 := 
    map Heart   Names ++
    map Spade   Names ++
    map Club    Names ++
    map Diamond Names
.

Fixpoint isEven (n:nat) := 
match n with
| 0        => True
| S 0      => False
| S (S n') => isEven n'
end.

Definition split {n n' m' : nat} {A : Type} {p : (n' +  m') = n} 
                  (deck : t A n) : (t A n' , t A m') :=


Definition shuffle {n:nat} (deck : t Card n) := 
  match split deck with
  | (d1,d2) => merge (reverse d2) d1
  end.
End impl.