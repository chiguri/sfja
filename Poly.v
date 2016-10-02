(** * Poly:多相性と高階関数 *)
(* * Poly: Polymorphism and Higher-Order Functions *)

(** In this chapter we continue our development of basic 
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).
*)

Require Export Lists.   

(* ###################################################### *)
(* * Polymorphism *)
(** * ポリモルフィズム（多相性） *)
(* ###################################################### *)
(* ** Polymorphic Lists *)
(** ** 多相的なリスト *)

(* For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)
(** ここまでは、数値のリストについて学んできました。もちろん、数値以外の、文字列、ブール値、リストといったものを要素として持つリストを扱えるプログラムは、より興味深いものとなるでしょう。これまで学んできたことだけでも、実は新しい帰納的なデータ型を作ることはできるのです。例えば次のように... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(* ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.)  for each
    new datatype definition. *)
(** ... しかし、こんなことをやっていると、すぐに嫌になってしまうでしょう。その理由の一つは、データ型ごとに違ったコンストラクタの名前をつけなければならないことですが、もっと大変なのは、こういったリストを扱う関数（[length]、[rev]など）を、新しく対応した型ごとに作る必要が出てくることです。 *)

(** *** *)

(* To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)
(** この無駄な繰り返し作業を無くすため、Coqは多相的な帰納的データ型の定義をサポートしています。これを使うと、多相的なリストは以下のように書くことができます。 *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(* This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.) *)
(** これは、前の章にある[natlist]の定義とほとんどそっくりですが、コンストラクタ[cons]の引数の型が[nat]であったのに対し、任意の型を表す[X]がそれに変わっています。この[X]はヘッダに加えられた[X]と結びつけられ、さらに[natlist]であったものが[list X]に置き換わっています（ここで、コンストラクタに[nil]や[cons]といった名前を付けられるのは、最初に定義した[natlist]が[Module]の中で定義されていて、ここからはスコープの外になっているからです）。 *)

(* What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are things of type [X]. *)
(** それでは、[list]とはいったい何なのか、ということを正確に考えて見ましょう。これを考える一つの手がかりは、リストが「型を引数にとり、帰納的な定義を返す関数である」と考えることです。あるいは「型を引数にとり、型を返す関数」と考えてもいいかもしれません。任意の型[X]について、[list X]という型は、帰納的に定義されたリストの集合で、その要素の型が[X]となっているものと考えることもできます。
 *)

(* With this definition, when we use the constructors [nil] and
    [cons] to build lists, we need to tell Coq the type of the
    elements in the lists we are building -- that is, [nil] and [cons]
    are now _polymorphic constructors_.  Observe the types of these
    constructors: *)
(** この定義の下で、コンストラクタ[nil]や[cons]を使う際には、今作ろうとしているリストの要素の型を指定してやる必要があります。なぜなら、今や[nil]も[cons]も多相的なコンストラクタとなっているからです。 *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(* The "[forall X]" in these types can be read as an additional
    argument to the constructors that determines the expected types of
    the arguments that follow.  When [nil] and [cons] are used, these
    arguments are supplied in the same way as the others.  For
    example, the list containing [2] and [1] is written like this: *)
(** ここで出てきた"[forall X]"というのは、コンストラクタに追加された引数で、後に続く引数で型を特定させるものです。[nil]や[cons]が使われる際、例えば[2]と[1]を要素に持つリストは、以下のように表されます。  *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(* (We've gone back to writing [nil] and [cons] explicitly here
    because we haven't yet defined the [ [] ] and [::] notations for
    the new version of lists.  We'll do that in a bit.) *)
(** （ここでは[nil]や[cons]を明示的に記述していますが、それは我々がまだ[[]]や[::]の表記法（Notation）をまだ記述していないからです。この後でやります） *)

(* We can now go back and make polymorphic (or "generic")
    versions of all the list-processing functions that we wrote
    before.  Here is [length], for example: *)
(** それでは少し話を戻して、以前書いたリスト処理関数を多相版に作り直していきましょう。[length]関数は以下のようになります。 *)

(** *** *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(* Note that the uses of [nil] and [cons] in [match] patterns
    do not require any type annotations: Coq already knows that the list
    [l] contains elements of type [X], so there's no reason to include
    [X] in the pattern.  (More precisely, the type [X] is a parameter
    of the whole definition of [list], not of the individual
    constructors.  We'll come back to this point later.)

    As with [nil] and [cons], we can use [length] by applying it first
    to a type and then to its list argument: *)
(** ここで、[match]に使われている[nil]や[cons]に型修飾がついていないことに注意してください。我々はすでにリスト[l]が型[X]の要素を持っていることを知っていますが、それはパターンマッチに[X]を含める理由になりません。さらに形式的には、[X]はリスト定義全体での型であって、個々のコンストラクタの型ではないのです。

    [nil]や[cons]と同様に、[length]も与えるリストと同じ型を最初に適用すれば使えます。 *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(* To use our length with other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)
(** この[length]を別の型のリストに使いたい場合は、適切な型を与えるだけで済みます。 *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

(** *** *)
(* Let's close this subsection by re-implementing a few other
    standard list functions on our new polymorphic lists: *)
(** では、このサブセクションの終わりとして、他の標準的なリスト処理関数を多相的に書き直しましょう。 *)

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.



Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Module MumbleBaz.
(** **** Exercise: 2 stars (mumble_grumble)  *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c] 
(* FILL IN HERE *)
*)
(** [] *)


(** **** Exercise: 2 stars (baz_num_elts)  *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have? 
(* FILL IN HERE *)
*)
(** [] *)

End MumbleBaz.

(* ###################################################### *)
(* *** Type Annotation Inference *)
(** *** 型推論 *)

(* Let's write the definition of [app] again, but this time we won't
    specify the types of any of the arguments. Will Coq still accept
    it? *)
(** それでは、[app]関数の定義をもう一度書いてみましょう。ただし今回は、引数の型を指定しないでおきます。Coqはこれを受け入れてくれるでしょうか？ *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(* Indeed it will.  Let's see what type Coq has assigned to [app']: *)
(** うまくいったようです。Coqが[app']にどのような型を設定したのか確認してみましょう。 *)

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

(* It has exactly the same type type as [app].  Coq was able to
    use a process called _type inference_ to deduce what the types of
    [X], [l1], and [l2] must be, based on how they are used.  For
    example, since [X] is used as an argument to [cons], it must be a
    [Type], since [cons] expects a [Type] as its first argument;
    matching [l1] with [nil] and [cons] means it must be a [list]; and
    so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks.  You should try to find a balance in your own code between
    too many type annotations (so many that they clutter and distract)
    and too few (which forces readers to perform type inference in
    their heads in order to understand your code). *)
(** 両者は全く同じ型であることが分かります。Coqは型推論という機構を持っていて、これを使い、[X]と[l1]と[l2]の型が何であるべきかを、その使われ方から導き出します。例えば、[X]が[cons]の引数として使われたことがあれば、それは型に違いなく、さらに[cons]の最初に引数で型が指定されていて、[l1]が[nil]や[cons]とマッチされているなら、それは[list]に違いなかろう、といった具合です。

    このパワフルな機構の存在は、型情報を常にそこら中に書かなければならないわけではない、ということを意味します。とはいえ、型を明示的に書くことは、ドキュメント作成やプログラムの健全性をチェックする際に大いに意味はあるのですが。とにかく、これからは自分の書くコードで、型指定を書くところ、書かないところのバランスを考えていく必要があります（多すぎれば、コードが目障りな型指定で読みにくくなりますし、少なすぎると、プログラムを読む人に型推論の結果をいちいち推測させなければならなくなります）。
*)

(* ###################################################### *)
(* *** Type Argument Synthesis *)
(** *** 引数の同化（Synthesis） *)

(* Whenever we use a polymorphic function, we need to pass it
    one or more types in addition to its other arguments.  For
    example, the recursive call in the body of the [length] function
    above must pass along the type [X].  But just like providing
    explicit type annotations everywhere, this is heavy and verbose.
    Since the second argument to [length] is a list of [X]s, it seems
    entirely obvious that the first argument can only be [X] -- why
    should we have to write it explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please figure out for yourself what
    type belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- and,
    indeed, the two procedures rely on the same underlying mechanisms.
    Instead of simply omitting the types of some arguments to a
    function, like
      app' X l1 l2 : list X :=
    we can also replace the types with [_], like
      app' (X : _) (l1 l2 : _) : list X :=
    which tells Coq to attempt to infer the missing information, just
    as with argument synthesis.

    Using implicit arguments, the [length] function can be written
    like this: *)
(** 多相的な関数を使うときはいつも、通常の引数に加えて型を一つ以上渡さなければなりません。例えば、[length]関数で自分を再帰している部分には、型[X]として渡されたものをそのまま渡すことになります。しかしこのように、そこらじゅうに明示的に型を書かなければならないとなると、これはとても面倒で冗長な作業です。[length]の二つ目の引数が[X]型のリストなら、最初の引数は[X]以外になり得ないのは明らかなのではないか・・・・ならなぜわざわざそれを書く必要があるのでしょう。

    幸いなことに、Coqではこの種の冗長性を避けることができます。型を引数に渡すところではどこでも同化した引数"[_]"を書くことができるのです。これは「ここをあるべき型に解釈してください」という意味です。もう少し正確に言うと、Coqが[_]を見つけると、手近に集められる情報を集めます。それは、適用されている関数の型や、その適用が現れている文脈から予想される型などですが、それを使って[_]と置き換えるべき具体的な型を決定するのです。

    これを聞くと、型推論と同じじゃないかと思われるかもしれません。実際、この二つの機能は水面下にあるメカニズムではつながっています。次のように単に引数の型を省略する代わりに
      app' X l1 l2 : list X :=
    このように、型を[_]で書くことができるということです。
      app' (X : _) (l1 l2 : _) : list X :=
    いずれも、Coqに、欠落している情報を推論させるもので、これを引数の同化といいます。

    引数の同化を使うと、[length]関数は以下のように書けます。 *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(* In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference can be significant.  For
    example, suppose we want to write down a list containing the
    numbers [1], [2], and [3].  Instead of writing this... *)
(** この例では、[X]を[_]に省略することをあまりしていません。しかし多くの場合、この違いは重要です。例えば、[1],[2],[3]といった数値を保持するリストを書きたい場合、以下のように書く代わりに... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(* ...we can use argument synthesis to write this: *)
(** ...引数同化を使って以下のように書くこともできます。 *)

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(* *** Implicit Arguments *)
(** *** 暗黙の引数 *)

(* In fact, we can go further.  To avoid having to sprinkle [_]'s
    throughout our programs, we can tell Coq _always_ to infer the
    type argument(s) of a given function. The [Arguments] directive
    specifies the name of the function or constructor, and then lists
    its argument names, with curly braces around any arguments to be
    treated as implicit. 
    *)
(** さらに先に進みましょう。プログラム全体が[_]まみれになることを避けるため、特定の関数の引数については常に型推論するよう指定できます。 *)

Arguments nil {X}.
Arguments cons {X} _ _.  (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.

(* note: no _ arguments required... *)
(* 注）もはや引数に_は必要ありません... *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** *** *)

(* Alternatively, we can declare an argument to be implicit while
    defining the function itself, by surrounding the argument in curly
    braces.  For example: *)
(** また、関数定義の中で、引数を暗黙のものにすることもできます。その際は、次のように引数を中カッコで囲みます。 *)

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(* (Note that we didn't even have to provide a type argument to
    the recursive call to [length'']; indeed, it is invalid to provide
    one.)  We will use this style whenever possible, although we will
    continue to use use explicit [Argument] declarations for
    [Inductive] constructors. *)
(** （ここで注意してほしいのは、再帰呼び出しの[length'']ではもうすでに型を引数で指定していない、ということです）これからは、この書き方をできるだけ使っていくことにします。ただし、[Inductive]宣言のコンストラクタでは[Implicit Arguments]を明示的に書くようにします。 *)

(** *** *)

(* One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly this time, even though
    we've globally declared it to be [Implicit].  For example, suppose we
    write this: *)
(** 引数を暗黙的に宣言することには、小さな問題が一つあります。時折、Coqが型を特定するために必要な情報を十分に集められない時があるのです。そういう場合には、その時だけ明示してやります。たとえそれがグローバルには[Implicit]と宣言されていたとしてもです。例えば、もし次のように書きたかったとします。 *)

(* Definition mynil := nil.  *)
(** <<
(* Definition mynil := nil.  *)
>> *)

(* If we uncomment this definition, Coq will give us an error,
    because it doesn't know what type argument to supply to [nil].  We
    can help it by providing an explicit type declaration (so that Coq
    has more information available when it gets to the "application"
    of [nil]): *)
(** この定義のコメントをはずすと、Coqはエラーを出します。[nil]が何の型の[nil]なのか分からないからです。このようなときは、型宣言を明示的に行うことができます（これによって[nil]を何に適用できるか、という情報が与えられます）。 *)

Definition mynil : list nat := nil.

(* Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)
(** それとは別に、関数名の前に[@]を付けることで暗黙的に宣言された関数に対して型を明示的に与えることができます。 *)

Check @nil.

Definition mynil' := @nil nat.

(** *** *)
(* Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)
(** 引数同化と暗黙的な引数をつかうことで、リストのノーテーション（表記法）をより便利に記述できます。コンストラクタの型引数を暗黙的に記述すれば、Coqはその表記法を使ったときに型を自動的に推論してくれます。 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Now lists can be written just the way we'd hope: *)
(** これで、我々の望む書き方ができるようになりました。 *)

Definition list123''' := [1; 2; 3].


(* ###################################################### *)
(* *** Exercises: Polymorphic Lists *)
(** *** 練習問題:多相的なリスト *)

(* **** Exercise: 2 stars, optional (poly_exercises)  *)
(** **** 練習問題: ★★, optional (poly_exercises) *)
(* Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)
(** ここにあるいくつかの練習問題は、List.vにあったものと同じですが、多相性の練習になります。以下の定義を行い、証明を完成させなさい。 *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  (* FILL IN HERE *) admit.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
 (* FILL IN HERE *) Admitted.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
(* FILL IN HERE *) Admitted.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Polymorphic Pairs *)
(** ** 多相的なペア *)

(* Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_ (or _products_): *)
(** 次も同様に、前の章で作った数値のペアを多相的にすることを考えます。 *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(* As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)
(** リストと同様、型引数を暗黙にし、その表記法を定義します。 *)

Notation "( x , y )" := (pair x y).

(* We can also use the [Notation] mechanism to define the standard
    notation for pair _types_: *)
(** また、「ペア型」の、より標準的な表記法も登録しておきます。 *)

Notation "X * Y" := (prod X Y) : type_scope.

(* (The annotation [: type_scope] tells Coq that this abbreviation
    should be used when parsing types.  This avoids a clash with the
    multiplication symbol.) *)
(** （[type_scope]というアノテーションは、この省略形が、型を解析する際に使われるものであることを示しています。これによって、[*]が乗算の演算子と衝突することを避けています。*)

(** *** *)
(* A note of caution: it is easy at first to get [(x,y)] and
    [X*Y] confused.  Remember that [(x,y)] is a _value_ built from two
    other values; [X*Y] is a _type_ built from two other types.  If
    [x] has type [X] and [y] has type [Y], then [(x,y)] has type
    [X*Y]. *)
(** 注意：最初のうちは、[(x,y)]と[X*Y]の違いに混乱するかもしれません。覚えてほしいのは、[(x,y)]が値のペアを構成するもので、[X*Y]は型のペアを構成するものだということです。値[x]が[X]型で、値[y]が[Y]型なら、値[(x,y)]は[X*Y]型となります。 *)

(* The first and second projection functions now look pretty
    much as they would in any functional programming language. *)
(** ペアの最初の要素、２番目の要素を返す射影関数は他のプログラミング言語で書いたものと比べると若干長くなります。 *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

(* The following function takes two lists and combines them
    into a list of pairs.  In many functional programming languages,
    it is called [zip].  We call it [combine] for consistency with
    Coq's standard library. *)
(** 次の関数は二つのリストを引数にとり、一つの"ペアのリスト"を作成します。多くの関数型言語で[zip]関数と呼ばれているものです。Coqの標準ライブラリとぶつからないよう、ここでは[combine]と呼ぶことにします。 *)
(* Note that the pair notation can be used both in expressions and in
    patterns... *)
(** ペアの表記法は、式だけではなくパターンマッチにも使えることに注目してください。 *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.


(* **** Exercise: 1 star, optional (combine_checks)  *)
(** **** 練習問題: ★ (combine_checks) *)
(* Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does
        Eval compute in (combine [1;2] [false;false;true;true]).
      print?   []
*)
(** 次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。
    - 関数[combine]の型は何でしょう ([Check @combine]の出力結果は？
    - それでは
        Eval simpl in (combine [1,2] [false,false,true,true]).
      は何を出力する？   []
*)

(* **** Exercise: 2 stars (split)  *)
(** **** 練習問題: ★★, recommended (split) *)
(* The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)
(** [split]関数は[combine]と全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とで[unzip]と呼ばれているものです。次の段落のコメントをはずし、[split]関数の定義を完成させなさい。続くテストを通過することも確認しなさい。 *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
(* FILL IN HERE *) admit.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Polymorphic Options *)
(** ** 多相的なオプション *)

(* One last polymorphic type for now: _polymorphic options_.
    The type declaration generalizes the one for [natoption] in the
    previous chapter: *)
(** 最後に、多相的なオプションに取り組みます。この型は、前の章の[natoption]を多相化して定義することにします。 *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _. 
Arguments None {X}. 

(** *** *)
(* We can now rewrite the [index] function so that it works
    with any type of lists. *)
(** また、[index]関数も、色々な型のリストで使えるように定義し直しましょう。 *)

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1];[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(* **** Exercise: 1 star, optional (hd_opt_poly)  *)
(** **** 練習問題: ★, optional (hd_opt_poly) *)
(* Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)
(** 前の章に出てきた[hd_opt]関数の多相版を定義しなさい。次の単体テストでの確認も忘れずに。 *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  (* FILL IN HERE *) admit.

(* Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)
(** 再び、暗黙的に定義された引数を明示的に指定してみましょう。関数名の前に[@]をつければいいのでしたね。 *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* * Functions as Data *)
(** * データとしての関数 *)
(* ###################################################### *)
(* ** Higher-Order Functions *)
(** ** 高階関数 *)

(* Like many other modern programming languages -- including
    all _functional languages_ (ML, Haskell, Scheme, etc.) -- Coq
    treats functions as first-class citizens, allowing functions to be
    passed as arguments to other functions, returned as results,
    stored in data structures, etc.

    Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)
(** 他の多くの近代的なプログラミング言語（全ての関数型言語を含む）同様、Coqは関数をファーストクラスに属するものとして取り扱います。つまりそれは、関数を他の関数の引数として渡したり、結果として関数を返したり、データ構造の中に関数を含めたりすることができるということです。

    関数を操作する関数を、一般に「高階関数」と呼びます。例えば次のようなものです。 *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(* The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)
(** ここで引数[f]は関数です。[doit3times]の内容は、値[n]に対して関数[f]を3回適用するものです。 *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(* ** Partial Application *)
(** ** 部分適用 *)

(* In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)
(** 実は、我々がすでに見た、複数の引数を持つ関数は、関数を引数に渡すサンプルになっているのです。どういうことかは、[plus]関数の型を思い出せば分かります。それは[nat -> nat -> nat]でした。 *)

Check plus.
(* ==> nat -> nat -> nat *)

(* Each [->] in this expression is actually a _binary_ operator
    on types.  (This is the same as saying that Coq primitively
    supports only one-argument functions -- do you see why?)  This
    operator is _right-associative_, so the type of [plus] is really a
    shorthand for [nat -> (nat -> nat)] -- i.e., it can be read as
    saying that "[plus] is a one-argument function that takes a [nat]
    and returns a one-argument function that takes another [nat] and
    returns a [nat]."  In the examples above, we have always applied
    [plus] to both of its arguments at once, but if we like we can
    supply just the first.  This is called _partial application_. *)
(** [->]は、型同士の二項演算子ですが、このことはCoqが基本的に引数一つの関数しかサポートしていないことを意味します。さらに、この演算子は右結合であるため、[plus]関数の型は[nat -> (nat -> nat)]の省略であると言えます。これをよく読むと"[plus]は[nat]型の引数を一つ取り、引数が[nat]型一つで[nat]型を返す関数を返す"と読むことができます。以前の例では[plus]に二つの引数を一緒に与えていましたが、もし望むなら最初の一つだけを与えることもできます。これを部分適用といいます。 *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(* ** Digression: Currying *)
(** ** 余談： カリー化 *)

(* **** Exercise: 2 stars, advanced (currying)  *)
(** **** 練習問題: ★★, advanced (currying) *)
(* In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)
(** Coqでは、[f : A -> B -> C]という型の関数は[A -> (B -> C)]型と同じです。このことは、もし上の関数[f]に値[A]を与えると、[f' : B -> C]という型の関数が戻り値として返ってくるということです。これは部分適用の[plus3]でやりましたが、このように、複数の引数から戻り値の型のリストを、関数を返す関数として捉えなおすことを、論理学者ハスケル・カリーにちなんでカリー化、と呼んでいます。

    逆に、[A -> B -> C]型の関数を[(A * B) -> C]型の関数に変換することもできます。これをアンカリー化（非カリー化）といいます。アンカリー化された二項演算は、二つの引数を同時にペアの形で与える必要があり、部分適用はできません。 *)

(* We can define currying as follows: *)
(** カリー化は以下のように定義できます。 *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)
(** 練習問題として、その逆の[prod_uncurry]を定義し、二つの関数が互いに逆関数であることを証明しなさい。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* FILL IN HERE *) admit.

(* (Thought exercise: before running these commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]?) *)
(** (考える練習: 次のコマンドを実行する前に、[prod_curry]と[prod_uncurry]の型を考えなさい。) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Filter *)
(** ** フィルター (Filter)関数 *)

(* Here is a useful higher-order function, which takes a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filters" the list, returning a new list containing just those
    elements for which the predicate returns [true]. *)
(** 次に紹介するのは、とても有用な高階関数です。これは、[X]型のリストと、[X]についての述語（[X]を引数にとり、boolを返す関数）を引数にとり、リストの要素にフィルターをかけて、述語として与えられた関数の結果が[true]となった要素だけのリストを返す関数です。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(* For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)
(** 例えば、この[filter]関数に述語として[evenb]と数値のリスト[l]を与えると、リスト[l]の要素の中で偶数の要素だけがリストとなって帰ります。 *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

(** *** *)
Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** *** *)

(* We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)
(** この[filter]を使うことで、 [Lists.v]にある[countoddmembers]関数をもっと簡潔に書くことができます。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(* ** Anonymous Functions *)
(** ** 無名（匿名）関数 *)

(* It is a little annoying to be forced to define the function
    [length_is_1] and give it a name just to be able to pass it as an
    argument to [filter], since we will probably never use it again.
    Moreover, this is not an isolated example.  When using
    higher-order functions, we often want to pass as arguments
    "one-off" functions that we will never use again; having to give
    each of these functions a name would be tedious.

    Fortunately, there is a better way. It is also possible to
    construct a function "on the fly" without declaring it at the top
    level or giving it a name; this is analogous to the notation we've
    been using for writing down constant lists, natural numbers, and
    so on. *)
(** [filter]関数に渡すためだけに、二度と使われない[length_is_1]といった関数を定義して、それにわざわざ名前を付けるというのは、少しわずらわしく感じます。このようなことは、この例だけの問題ではありません。高階関数を使うときは、引数として"一度しか使わない関数"を渡すことがよくあります。こういう関数にいちいち名前を考えるのは、退屈以外の何物でもありません。

    幸いなことに、いい方法があります。一時的な関数を、名前を付けることも、トップレベルで宣言することもなく作成することができるのです。これは定数のリストや、数値定数と同じようなものだと考えられます。 *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(* Here is the motivating example from before, rewritten to use
    an anonymous function. *)
(** 次は無名関数を使った書き換えのもう少しいい例です。 *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(* **** Exercise: 2 stars (filter_even_gt7)  *)
(** **** 練習問題: ★★ (filter_even_gt7) *)

(* Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)
(** [filter]関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出す[filter_even_gt7]関数を書きなさい。 *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* FILL IN HERE *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (partition)  *)
(** **** 練習問題: ★★★ (partition) *)
(* Use [filter] to write a Coq function [partition]:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)
(** [filter]関数を使って、[partition]関数を書きなさい。:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   型[X]について、[X]型の値がある条件を満たすかを調べる述語[X -> bool]と[X]のリスト[list X]を引数に与えると、[partition]関数はリストのペアを返します。ペアの最初の要素は、与えられたリストのうち、条件を満たす要素だけのリストで、二番目の要素は、条件を満たさないもののリストです。二つのリストの要素の順番は、元のリストの順と同じでなければなりません。*)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
(* FILL IN HERE *) admit.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(* ** Map *)
(** ** マップ（Map）関数 *)

(* Another handy higher-order function is called [map]. *)
(** もう一つ、便利な高階関数として[map]を挙げます。 *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** *** *)
(* It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)
(** これは、関数[f]とリスト[ l = [n1, n2, n3, ...] ]を引数にとり、関数[f]を[l]の各要素に適用した[ [f n1, f n2, f n3,...] ]というリストを返します。例えばこのようなものです。 *)

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(* The element types of the input and output lists need not be
    the same ([map] takes _two_ type arguments, [X] and [Y]).  This
    version of [map] can thus be applied to a list of numbers and a
    function from numbers to booleans to yield a list of booleans: *)
(** 入力されるリストの要素の型と、出力されるリストの要素の型は同じである必要はありません（[map]は、[X]と[Y]二種類の型変数を取ります）。次の例は、数値のリストと、数値を受け取り[bool]値を返す関数から、bool型のリストを返します。 *)

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(* It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a list of lists of booleans: *)
(** 同じ関数が、数値のリストと、「数値から[bool]型のリストへの関数」を引数にとり、「[bool]型のリストのリスト」を返すような関数にも使えます。 *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.


(** ** Map for options *)
(* **** Exercise: 3 stars (map_rev)  *)
(** **** 練習問題: ★★★ (map_rev) *)
(* Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
(** [map]と[rev]が可換であることを示しなさい。補題をたてて証明する必要があるでしょう。 *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars (flat_map)  *)
(** **** 練習問題: ★★ (flat_map) *)
(* The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)
(** [map]関数は、[list X]から[list Y]へのマップを、型[X -> Y]の関数を使って実現しています。同じような関数[flat_map]を定義しましょう。これは[list X]から[list Y]へのマップですが、[X -> list Y]となる関数[f]を使用できます。このため、次のように要素ごとの関数[f]の結果を平坦化してやる必要があります。
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* FILL IN HERE *) admit.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)
(** リストは、[map]関数のような関数に渡すことができる、帰納的に定義された唯一の型、というわけではありません。次の定義は、[option]型のために[map]関数を定義したものです。 *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* **** Exercise: 2 stars, optional (implicit_args)  *)
(** **** 練習問題: ★★, optional (implicit_args) *)
(* The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)  [] *)
(** [filter]や[map]関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。暗黙の型引数定義に使われている中括弧を普通の括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかどうかをCoqでチェックしなさい。 [] *)

(* ###################################################### *)
(* ** Fold *)
(** ** 畳み込み（Fold）関数 *)

(* An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)
(** さらにパワフルな高階関数[fold]に話を移します。この関数はGoogleの分散フレームワーク"map/reduce"でいうところの"reduce"オペレーションに根ざしています。 *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** *** *)

(* Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,
   fold plus [1;2;3;4] 0
    yields
   1 + (2 + (3 + (4 + 0))).
    Here are some more examples:
*)
(** 直感的に[fold]は、与えられたリストの各要素の間に、与えられた二項演算子[f]を挟み込むように挿入していくような操作です。 例えば、[ fold plus [1,2,3,4] ]は、直感的に[1+2+3+4]と同じ意味です。ただし正確には、二番めの引数に、[f]に最初に与える"初期値"が必要になります。例えば
[[
   fold plus [1,2,3,4] 0
]]
    は、次のように解釈されます。
[[
   1 + (2 + (3 + (4 + 0))).
]]
    もう少しサンプルを見てください。
*)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* **** Exercise: 1 star, advanced (fold_types_different)  *)
(** **** 練習問題: ★, advanced (fold_types_different) *)
(* Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)
(** [fold]関数が[X]と[Y]二つの型引数をとっていて、関数[f]が型[X]を引数にとり型[Y]を返すようになっていることに注目してください。[X]と[Y]が別々の型となっていることで、どのような場合に便利であるかを考えてください。 *)

(* ###################################################### *)
(* ** Functions For Constructing Functions *)
(** ** 関数を作成する関数 *)

(* Most of the higher-order functions we have talked about so
    far take functions as _arguments_.  Now let's look at some
    examples involving _returning_ functions as the results of other
    functions.

    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)
(** これまで見てきた高階関数は、ほとんどが関数を引数にとるものでした。ここでは、関数が別の関数の戻り値になるような例を見ていきましょう。

    まず、値[x]（型[X]）を引数としてとり、「[nat]型の引数から[X]型の戻り値を返す関数」を返す関数を考えます。戻る関数は、引数に関係なく、生成時に与えられた値｢x｣を常に返すものです。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** *** *)
(* Similarly, but a bit more interestingly, here is a function
    that takes a function [f] from numbers to some type [X], a number
    [k], and a value [x], and constructs a function that behaves
    exactly like [f] except that, when called with the argument [k],
    it returns [x]. *)
(** もう少し面白い例を挙げます。次の関数は、数値から型[X]を戻す関数[f]と、数値[k]、型[X]の値[x]を引数にとり、[f]に[k]と同じ引数が与えられた場合だけ値[x]を返し、それ以外のときは[f]に[k]を渡した戻り値を返します。 *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(* For example, we can apply [override] twice to obtain a
    function from numbers to booleans that returns [false] on [1] and
    [3] and returns [true] on all other arguments. *)
(** たとえば、この[override]関数を数値から[bool]型への関数に以下のように２回適用すると、値が[1]と[3]のときだけ[false]を返し、それ以外はtrueを返すようにすることができます。 *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

(** *** *)

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** *** *)

(* **** Exercise: 1 star (override_example)  *)
(** **** 練習問題: ★ (override_example) *)
(* Before starting to work on the following proof, make sure you
    understand exactly what the theorem is saying and can paraphrase
    it in your own words.  The proof itself is straightforward. *)
(** 次の証明にとりかかる前に、あなたがこの証明の意味することを理解しているか確認するため、証明内容を別の言葉で言い換えてください。証明自体は単純なものです。 *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* We'll use function overriding heavily in parts of the rest of the
    course, and we will end up needing to know quite a bit about its
    properties.  To prove these properties, though, we need to know
    about a few more of Coq's tactics; developing these is the main
    topic of the next chapter.  For now, though, let's introduce just
    one very useful tactic that will also help us with proving
    properties of some of the other functions we have introduced in
    this chapter. *)
(** このコースでこれ以降、関数のオーバーライド（上書き）がよく登場しますが、この性質について多くを知る必要はありません。
    しかし、これらの性質を証明するには、さらにいくつかのCoqのタクティックを知らなければなりません。
    それが、次章の主なトピックになります。
    ここからは、あるタクティックを紹介します。
    本章で導入したいくつかの関数に関する性質の証明で非常に有用です。 *)

(* ###################################################### *)

(* ###################################################### *)
(* * The [unfold] Tactic *)
(** ** [unfold]タクティック *)

(* Sometimes, a proof will get stuck because Coq doesn't
    automatically expand a function call into its definition.  (This
    is a feature, not a bug: if Coq automatically expanded everything
    possible, our proof goals would quickly become enormous -- hard to
    read and slow for Coq to manipulate!) *)
(** 時折、Coqが関数を自動的に展開してくれないために証明が行き詰まってしまうことがあります（これは仕様であって、バグではありません。Coqがもし可能な展開を全て自動でやってしまったら、証明のゴールはたちまち巨大化して、読むこともCoqで操作することもできなくなってしまいます）。 *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
(* At this point, we'd like to do [rewrite -> H], since 
     [plus3 n] is definitionally equal to [3 + n].  However, 
     Coq doesn't automatically expand [plus3 n] to its 
     definition. *)
  (* ここでは[rewrite -> H]としたいところです。なぜなら、[plus3 n]はと同じ定義と言えるからです。しかしCoqは[plus3 n]をその定義に従って自動的に展開してくれません。 *)
  Abort.

(* The [unfold] tactic can be used to explicitly replace a
    defined name by the right-hand side of its definition.  *)
(** [unfold]タクティックは、定義された名前を、その定義の右側の記述に置き換えてくれるものです。  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(* Now we can prove a first property of [override]: If we
    override a function at some argument [k] and then look up [k], we
    get back the overridden value. *)
(** 今我々は、[override]の最初の性質を証明することができるようになりました。もしある関数の引数のある値[k]をオーバーライドしてから引数[k]を与えると、オーバーライドされた値が帰る、というものです。 *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(* This proof was straightforward, but note that it requires
    [unfold] to expand the definition of [override]. *)
(** この証明はストレートなものですが、[override]関数の展開に[unfold]を必要としている点だけ注意してください。 *)

(* **** Exercise: 2 stars (override_neq)  *)
(** **** 練習問題: ★★ (override_neq) *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* As the inverse of [unfold], Coq also provides a tactic
    [fold], which can be used to "unexpand" a definition.  It is used
    much less often. *)
(** [unfold]の逆の機能として、Coqには[fold]というタクティックも用意されています。これは、展開された定義を元に戻してくれますが、あまり使われることはありません。 *)

(* ##################################################### *)
(* * Additional Exercises *)
(** * さらなる練習問題 *)

(* **** Exercise: 2 stars (fold_length)  *)
(** **** 練習問題: ★★ (fold_length) *)
(* Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)
(** リストに関する多くの一般的な関数は[fold]を使って書きなおすることができます。例えば、次に示すのは[length]の別な実装です。 *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(* Prove the correctness of [fold_length]. *)
(** [fold_length]が正しいことを証明しなさい。 *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (fold_map)  *)
(** **** 練習問題: ★★★ (fold_map) *)
(* We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)
(** [map]関数も[fold]を使って書くことができます。以下の[fold_map]を完成させなさい。 *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* FILL IN HERE *) admit.

(* Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it. *)
(** [fold_map]の正しさを示す定理をCoqで書き、証明しなさい *)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 2 stars, advanced (index_informal)  *)
(** **** 練習問題: ★★, advanced (index_informal) *)
(* Recall the definition of the [index] function:
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None 
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
   Write an informal proof of the following theorem:
   forall X n l, length l = n -> @index X n l = None.
(* FILL IN HERE *)
*)
(** [index]関数の定義を思い出してください。
[[
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
]]
   次の定理の、非形式的な証明を書きなさい。
[[
   forall X n l, length l = n -> @index X (S n) l = None.
]]
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (church_numerals)  *)

Module Church.

(** In this exercise, we will explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church. We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. More formally, *)

Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Any
    function [f] iterated once shouldn't change. Thus, *)

Definition one : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** [zero] is somewhat trickier: how can we apply a function zero
    times? The answer is simple: just leave the argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] will be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f]. Notice in particular
    how the [doit3times] function we've defined previously is actually
    just the representation of [3]. *)

Definition three : nat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)    

(** Successor of a natural number *)

Definition succ (n : nat) : nat :=
  (* FILL IN HERE *) admit.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(** Addition of two natural numbers *)

Definition plus (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(** Multiplication *)

Definition mult (n m : nat) : nat := 
  (* FILL IN HERE *) admit.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(** Exponentiation *)

(** Hint: Polymorphism plays a crucial role here. However, choosing
    the right type to iterate over can be tricky. If you hit a
    "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic. *)

Definition exp (n m : nat) : nat :=
  (* FILL IN HERE *) admit.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

End Church.

(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

