(*
(** * Basics: Functional Programming in Coq *)
*)
(** * Basics: 関数プログラミングとプログラムの証明 *)
 
(*
   [Admitted] is Coq's "escape hatch" that says accept this definition
   without proof.  We use it to mark the 'holes' in the development
   that should be completed as part of your homework exercises.  In
   practice, [Admitted] is useful when you're incrementally developing
   large proofs. *)
(*
   [Admitted]はCoqにおける「脱出口」です。これにより、あらゆるものを証明なしに定義することができます。
   この資料ではこれを途中の空白部分として使い、これを埋めるという課題を出します。
   実際の記述では、大きな証明を作る場合に少しずつ証明を構築するのに有用です。 *)
Definition admit {T: Type} : T.  Admitted.

(* ###################################################################### *)
(*
(** * Introduction *)
*)
(** * 導入 *)

(*
(** The functional programming style brings programming closer to
    simple, everyday mathematics: If a procedure or method has no side
    effects, then pretty much all you need to understand about it is
    how it maps inputs to outputs -- that is, you can think of it as
    just a concrete method for computing a mathematical function.
    This is one sense of the word "functional" in "functional
    programming."  The direct connection between programs and simple
    mathematical objects supports both formal proofs of correctness
    and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, stored in data
    structures, etc.  The recognition that functions can be treated as
    data in this way enables a host of useful and powerful idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to construct
    and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ that support abstraction and code
    reuse.  Coq shares all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language.  The second
    half introduces some basic _tactics_ that can be used to prove
    simple properties of Coq programs.
*)
*)
(** 関数型プログラミングスタイルはプログラミングを単純で日用の数学に近いものにします。
    手続きやメソッドが副作用を持たなければ、理解に必要なのは入力をどの出力に割り当てるかだけです。
    つまり、これは数学的な関数を計算する手法として理解することとも考えられます。
    これが「関数型プログラミング(functional programming)」における「関数型(functional)」という語の本来の意味です。
    プログラムと数学的な対象を直接関係づけることは、正しさの形式的証明やプログラムの挙動の健全で非形式的な解釈の両面で役に立ちます。
 
    もう一つの関数型プログラミングが「関数型」であるという感覚は、関数（やメソッド）を「一級(_first class_)」値として扱うことから来ます。
    ここで、一級値であるとは、関数の引数にしたり、関数の結果として返したり、データ構造に格納したり、といったことができることを意味します。
    関数をデータとして取り扱えることで、有用かつ強力な表現が可能になります。
 
    このほかの関数型言語に存在する機能としては、「代数的データ型(_algebraic data type_)」や「パターンマッチ(_pattern matching_)」があります。
    これらは、データ構造の構成と操作を容易にしてくれます。
    また、「多相データ型(_polymorphic type system_)」という、抽象化やコードの再利用に有用な機能もあります。
    上に挙げた機能は全てCoqに含まれています。
 
    本章の最初半分はCoqの関数型プログラミング言語としての基本部分の紹介となります。
    後ろ半分は、Coqのプログラムの簡単な性質を示すために使う、基本的な「タクティック(_tactic_)」を説明します。
 *)

(* ###################################################################### *)
(*
(** * Enumerated Types *)
*)
(** * 列挙型 *)

(*
(** One unusual aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers an extremely powerful mechanism for
    defining new data types from scratch -- so powerful that all these
    familiar types arise as instances.  

    Naturally, the Coq distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions: they
    are ordinary user code.  To illustrate this, we will explicitly
    recapitulate all the definitions we need in this course, rather
    than just getting them implicitly from the library.

    To see how this mechanism works, let's start with a very simple
    example. *)
*)
(** プログラミング言語Coqには、ほとんど何もビルトインされていません。
    ブール値や自然数、文字列といった基本データ型を提供する代わりに、Coqには新しい型やそれを処理するための強力なツールが用意されています。
    これはとても強力で、よくあるデータ型は全てその仕組みで定義することができます。

    当然、配布されているCoqにはブール値や数値、リストやハッシュテーブルといったよく使われるデータ構造を定義した標準ライブラリが付属しています。
    しかし、このライブラリには魔法や基底型のようなものは使われておらず、全て普通のユーザーコードです。
    これを説明するために、この資料では、必要となる定義をライブラリから暗黙的に得るのではなく、明示的に再現します。

    機構がどのように動くかを知るために、簡単な例から始めましょう。 *)

(* ###################################################################### *)
(*
(** ** Days of the Week *)
*)
(** ** 曜日の表し方 *)

(*
(** The following declaration tells Coq that we are defining
    a new set of data values -- a _type_. *)
*)
(** 次の定義は、Coqに対して、新しいデータ型の集合である「型(_type_)」を定義しています。 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(*
(** The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Having defined [day], we can write functions that operate on
    days. *)
*)
(** 型の名前は[day]で、要素は[monday]、[tuesday]...などです。
    それ以降の各行は次のようにも読めます。「[monday]は[day]、[tuesday]は[day]、などなど」といった具合です。

    [day]が何かを定義できれば、それを利用した関数を書くこともできるでしょう。 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(*
(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it performs
    some _type inference_ -- but we'll always include them to make
    reading easier. *)
*)
(** 一つ注意しておかなければならないことがあります。
    この関数の定義では、引数の型と戻り値の型が明示されていることです。
    他の多くの関数型プログラミング言語と同様、Coqはこのように型を明示的に書かずともちゃんと動くようになっています。
    それはいわゆる「型推論(_type inference_)」という機構によって実現されていますが、この講義ではプログラムを読みやすいように、常に型を明示することにします。 *)

(*
(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  

    First, we can use the command [Eval compute] to evaluate a
    compound expression involving [next_weekday].  *)
*)
(** 関数の定義ができたら、いくつかの例を挙げてそれが正しいものであることをチェックしなければなりません。
    それを実現するために、Coqには三つの方法が用意されています。

    一つ目は [Eval compute] コマンドを使って、関数[next_weekday]を含んだ式を評価させることです。 *)

Eval compute in (next_weekday friday).
   (* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(*
(** If you have a computer handy, this would be an excellent
    moment to fire up the Coq interpreter under your favorite IDE --
    either CoqIde or Proof General -- and try this for yourself.  Load
    this file ([Basics.v]) from the book's accompanying Coq sources,
    find the above example, submit it to Coq, and observe the
    result. *)
*)
(** もし今手元にコンピュータがあるなら、CoqのIDEのうち好きなもの（CoqIDEやProofGeneralなどから）を選んで起動し、実際に上のコマンドを入力し動かしてみるといいでしょう。
    このファイル（[Basics.v]）から上のサンプルを探してCoqに読み込ませ、結果を観察してください。 *)

(*
(** The keyword [compute] tells Coq precisely how to
    evaluate the expression we give it.  For the moment, [compute] is
    the only one we'll need; later on we'll see some alternatives that
    are sometimes useful. *)
*)
(** [compute] というキーワードは、Coqに与えた式を評価する方法を指示します。
    しばらくの間、[compute]コマンドは我々にとって必要な唯一のコマンドになるでしょう。
    この後でもう少し使い出のある別のコマンドを覚えるまでの間ですが。 *)
(* 訳注：これ以後なぜかcomputeではなくsimplが使われている。以前はsimplの説明だったので、修正忘れの可能性？ *)

(*
(** Second, we can record what we _expect_ the result to be in
    the form of a Coq example: *)
*)
(** 二番目の方法は、評価の結果として我々が期待しているものをCoqに対してあらかじめ以下のような形で例示しておくというものです。 *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(*
(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later. *)
*)
(** この宣言は二つのことを行っています。
    ひとつは、[saturday]の次の次にあたる平日が、[tuesday]であるということを確認する必要があるということを示すこと。
    もう一つは、後で参照しやすいように、その確認事項に[test_next_weekday]という名前を与えていることです。 *)
(*
(** Having made the assertion, we can also ask Coq to verify it,
    like this: *)
*)
(** この確認事項を記述すれば、次のようなコマンドを流すだけで、Coqによって正しさを検証できます。 *)

Proof. simpl. reflexivity.  Qed.

(*
(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification." *)
*)
(** この文について細かいことは今は置いておきますが（じきに戻ってきます）、本質的には以下のような意味になります。
    「我々が作成した確認事項は等式の両辺が同じものに簡約されたことで証明できました。」 *)

(*
(** Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to construct _fully certified_ programs in mainstream
    languages.  Indeed, this is one of the main uses for which Coq was
    developed.  We'll come back to this topic in later chapters.  More
    information can also be found in the Coq'Art book by Bertot and
    Casteran, as well as the Coq reference manual. *)
*)
(** 三番目の方法は、Coqで（[Definition]を使って）定義したものから、もう少し普通の言語（OCamlやScheme、Haskell）のプログラムを抽出してしまうことです。
    この機能は今主流の言語で、完全に確認された(_fully certified_)プログラムを実現できる道を開いたという意味でとても興味深いものです。
    これはCoqの開発動機の一つです。
    後の章で詳しく見ますが、より深く知りたいという場合はCoq'Art book（Bertot and Casteran著）や、Coqリファレンスマニュアルを参照してください。 *)


(* ###################################################################### *)
(*
(** ** Booleans *)
*)
(** ** ブール型 *)

(*
(** In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)
*)
(** 同様にして、[true]と[false]を値とする[bool]型を定義することができます。 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(*
(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans in its standard
    library, together with a multitude of useful functions and
    lemmas.  (Take a look at [Coq.Init.Datatypes] in the Coq library
    documentation if you're interested.)  Whenever possible, we'll
    name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library. *)
*)
(** このように我々は独自のbool型を一から作っていますが、もちろんCoqには標準ライブラリとしてbool型が多くの有用な関数、補題と一緒に用意されています。
    （もし興味があるなら、Coqライブラリドキュメントの[Coq.Init.Datatypes]を参照してください。）
    ここでは可能な限り標準ライブラリと同じ機能をもつ関数や定理を、同じ名前で定義していくことにしましょう。 *)

(*
(** Functions over booleans can be defined in the same way as
    above: *)
*)
(** bool型を使用する関数は、Day型と同じように定義することができます。 *)

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

(*
(** The last two illustrate the syntax for multi-argument
    function definitions. *)
*)
(** 後ろ二つでは、引数を複数持つ関数を定義しています。 *)

(*
(** The following four "unit tests" constitute a complete
    specification -- a truth table -- for the [orb] function: *)
*)
(** 次の四つの単体テスト(unit test)は、関数[orb]が取り得るすべての引数についての完全な仕様（真理値表）となっています。 *)

Example test_orb1:  (orb true  false) = true. 
Proof. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. reflexivity.  Qed.

(*
(** (Note that we've dropped the [simpl] in the proofs.  It's not
    actually needed because [reflexivity] automatically performs
    simplification.) *)
*)
(** （ここでは[simpl]を使っていません。
    実際のところ、[reflexivity]は自動で簡約を行うため、[simpl]を使う必要はないのです。） *)

(*
(** _A note on notation_: In .v files, we use square brackets to
    delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font]. *)
*)
(** 記述方法について: .v ファイルのコメントの中に Coqのコード片を含める場合には、角括弧を使用してコメントと区切ります。
    この慣習は[coqdoc]というドキュメント作成ツールでも利用されているのですが、コード片を周囲のコメントから視覚的に分離することができます。
    CoqソースのHTML版では、ソースはコメントとは[別のフォント]で表示されます。 *)

(*
(** The values [Admitted] and [admit] can be used to fill
    a hole in an incomplete definition or proof.  We'll use them in the
    following exercises.  In general, your job in the exercises is 
    to replace [admit] or [Admitted] with real definitions or proofs. *)
*)
(** [Admitted]や[admit]により、定義や証明の不完全な箇所をひとまず埋めておくことができます。
    これらは以降の練習問題に使われます。
    この資料では、練習問題を解くということは[admit]や[Admitted]と書かれた部分をちゃんとした定義や証明に書き直す作業になります。 *)
(* 訳注：valuesとあるが、[admit]は値として定義されているものの、[Admitted]は相変わらずコマンドであり値ではない。一応[Admitted]を使って定義された値、というのが正確な訳だと思うが、ごちゃごちゃしていて分かりづらい。そのため訳では値というニュアンスをわざと外している。 *)

(*
(** **** Exercise: 1 star (nandb)  *)
*)
(** **** 練習問題: ★ (nandb) *)
(*
(** Complete the definition of the following function, then make
    sure that the [Example] assertions below can each be verified by
    Coq.  *)
*)
(** 次の定義を完成させ、[Example]で記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。  *)

(*
(** This function should return [true] if either or both of
    its inputs are [false]. *)
*)
(** この関数は引数のどちらか、もしくは両方が[false]だったときに[true]を返すものである。 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* FILL IN HERE *) admit.

(*
(** Remove "[Admitted.]" and fill in each proof with 
    "[Proof. reflexivity. Qed.]" *)
*)
(** 下の定義から[Admitted.]を取り去り、代わりに"[Proof. reflexivity. Qed.]"で検証できるようなコードを記述しなさい。 *)

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 1 star (andb3)  *)
*)
(** **** 練習問題: ★ (andb3) *)
(*
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)
*)
(** 同様のことを以下の [andb3] 関数についてしなさい。
    この関数は全ての入力が [true] である場合に [true]を返し、そうでない場合は [false] を返すものです。 *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(*
(** ** Function Types *)
*)
(** ** 関数の型 *)

(*
(** The [Check] command causes Coq to print the type of an
    expression.  For example, the type of [negb true] is [bool]. *)
*)
(** [Check]コマンドを使うと、Coqに、指定した式の型を表示させることができます。
    例えば、 [negb true] という式の全体の型は[bool]である、という具合です。 *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(*
(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)
*)
(** [negb] のような関数は、それ自身が [true] や [false] と同じように値であると考えることもできます。
    そのようにとらえた場合の値の型を「関数型(_function type_)」と呼び、以下のように矢印を使った型として表します。 *)

Check negb.
(* ===> negb : bool -> bool *)

(*
(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)
*)
(** [negb]の型は[bool -> bool]と書き、「[bool]から[bool]」と読み、「[bool]型の引数をとって[bool]型の戻り値を返す関数」と解釈します。
    同様に、[andb]の型は[bool -> bool -> bool]と書き、「二つの[bool]型の引数をとって[bool]型の戻り値を返す関数」と解釈します。 *)

(* ###################################################################### *)
(*
(** ** Numbers *)
*)
(** ** 数値 *)

(*
(** _Technical digression_: Coq provides a fairly sophisticated
    _module system_, to aid in organizing large developments.  In this
    course we won't need most of its features, but one is useful: If
    we enclose a collection of declarations between [Module X] and
    [End X] markers, then, in the remainder of the file after the
    [End], these definitions will be referred to by names like [X.foo]
    instead of just [foo].  Here, we use this feature to introduce the
    definition of the type [nat] in an inner module so that it does
    not shadow the one from the standard library. *)
*)
(** ちょっと技術的な話：Coqは大規模な開発を支援するためにちょっと大げさにも見えるモジュールシステムを提供しています。
    このコースではこれらはほとんど必要のないものですが、一つだけ有用な機能があります。
    プログラムの中のいくつかの要素を[Module X]と[End X]で囲んでおくと、[End X]以降の部分からは、囲まれた中で[foo]と定義したものを[foo]ではなく[X.foo]という形で呼び出すようになります。
    という訳で、今回はこの機能を使って[nat]という型を内部モジュールに定義します。
    そうすることで、標準ライブラリの同じ名前の定義を覆い隠してしまわずに済みます。 *)

Module Playground1.

(*
(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements.  A more interesting way of defining a type is to give a
    collection of "inductive rules" describing its elements.  For
    example, we can define the natural numbers as follows: *)
*)
(** 我々がここまでで定義してきた型は「列挙型」の型定義でした。
    このような型は、有限の要素をすべて列挙することによって定義されます。
    型を定義するもう一つの方法は、「帰納的な規則」を並べることで要素を記述する方法です。
    例えば、自然数以下のような方法で定義できます。 *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(*
(** The clauses of this definition can be read: 
      - [O] is a natural number (note that this is the letter "[O]," not
        the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
        another one -- that is, if [n] is a natural number, then [S n]
        is too.

    Let's look at this in a little more detail.  

    Every inductively defined set ([day], [nat], [bool], etc.) is
    actually a set of _expressions_.  The definition of [nat] says how
    expressions in the set [nat] can be constructed:

    - the expression [O] belongs to the set [nat]; 
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat].

    The same rules apply for our definitions of [day] and [bool]. The
    annotations we used for their constructors are analogous to the
    one for the [O] constructor, and indicate that each of those
    constructors doesn't take any arguments. *)
*)
(** この定義の各句は、以下のように解釈できます。
      - [O]は自然数である（[0]（数字のゼロ）ではなく[O]（アルファベットのオー）であることに注意）。
      - [S]は自然数を引数にとり、別の自然数を生成する「コンストラクタ」である。このことは、[n]が自然数なら[S n]も自然数であることを示している。
 
    この定義にして、もう少し詳しく見ていきましょう。
 
    これまでに定義してきた帰納的な型（[weekday]、[nat]、[bool]など）は、実際には「式(_expression_)」の集合とでも言うべきものです。
    [nat]の定義は、[nat]の要素となる式がどのように構築されるかを表しています。
 
    - 式[O]（オー）は、[nat]に属する。
    - もし[n]が[nat]に属するならば、[S n]もまた[nat]に属する。
    - これら二つの方法で表された式のみが[nat]に属するものの全てである。*)

(*
(** These three conditions are the precise force of the
    [Inductive] declaration.  They imply that the expression [O], the
    expression [S O], the expression [S (S O)], the expression
    [S (S (S O))], and so on all belong to the set [nat], while other
    expressions like [true], [andb true false], and [S (S false)] do
    not.

    We can write simple functions that pattern match on natural
    numbers just as we did above -- for example, the predecessor
    function: *)
*)
(** これら三つの条件によって、[nat]が帰納的([Inductive])な方法で厳格に定義されています。
    この定義によって、式 [O]、式 [S O]、式  [S (S O)]、式 [S (S (S O))]...が全て[nat]に属する式であることが表されています。
    また同時に、[true]や[andb true false]、[S (S false)]が[nat]に属さないことも明確にされています。
 
    こうして定義された自然数[nat]をマターンマッチにかけることで、簡単な関数を書いてみましょう。
    例えば、一つ前の[nat]を返す関数は以下のよう書けます。 *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(*
(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)
*)
(** この２番目の句は「もし[n]が何らかの[n']を用いて[S n']と表せるなら、[n']を返す」と読めます。 *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(*
(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)
*)
(** 自然数というのは非常に一般的な型なので、Coqは自然数を扱ったり表したりするときに若干特別な扱いをします。
    [S]や[O]を使った「1進数(_unary_)」表記の代わりに一般的に使われるアラビア数字を使うことができます。
    実際、Coqは数値を表示する際、デフォルトではアラビア数字を用います。 *)
(** 訳注：1進数は記号を並べた長さで数の大きさを表します。ここでは[S]の数がそれに当たります。 *)

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

(*
(** The constructor [S] has the type [nat -> nat], just like the
    functions [minustwo] and [pred]: *)
*)
(** [nat]のコンストラクタ[S]は[nat -> nat]型に属します。
    関数[minustwo]や[pred]と同じ型になっています。 *)

Check S.
Check pred.
Check minustwo.

(*
(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference: functions
    like [pred] and [minustwo] come with _computation rules_ -- e.g.,
    the definition of [pred] says that [pred 2] can be simplified to
    [1] -- while the definition of [S] has no such behavior attached.
    Although it is like a function in the sense that it can be applied
    to an argument, it does not _do_ anything at all! *)
*)
(** これらが表しているのは、いずれの関数も数を引数にとって数を生成できる、ということです。
    しかしながらこれらには根本的な違いがあります。
    [pred]や[minustwo]といった関数には「計算ルール(_computation rule_)」というものが定義されています。
    例えば、[pred]の定義は、[pred 2]が[1]に簡約されることを記述したものですが、一方[S]にはそのような定義がありません。
    コンストラクタは引数に適用するという面では関数と同様ではありますが、コンストラクタは「何も」しないのです！ *)

(*
(** For most function definitions over numbers, pure pattern
    matching is not enough: we also need recursion.  For example, to
    check that a number [n] is even, we may need to recursively check
    whether [n-2] is even.  To write such functions, we use the
    keyword [Fixpoint]. *)
*)
(** 数値を扱う多くの関数は、単なるパターンマッチだけでは記述できず、再帰が必要になってきます。
    例えば、[n]が偶数かどうかを調べて返す関数[evenb]は、[n-2]が偶数であるかどうかを調べる、という再帰的な定義を必要とします。
    そういう関数を定義する場合、[Fixpoint]というキーワードを使用します。 *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(*
(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition that will be a bit easier to work with: *)
*)
(** 同じように[Fixpoint]を使って関数[oddb]を定義することもできますが、ここでは次のようにもっとシンプルな方法で簡単に作ってみましょう。 *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. reflexivity.  Qed.

(*
(** Naturally, we can also define multi-argument functions by
    recursion.  (Once again, we use a module to avoid polluting the
    namespace.) *)
*)
(** 当然ながら、引数を複数持つ関数も再帰的に定義することができます。
    ネームスペースを汚さないようにするため、別のモジュールに定義することにしましょう。*)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(*
(** Adding three to two now gives us five, as we'd expect. *)
*)
(** 3に2を加えた結果は、5になるべきですね。 *)

Eval compute in (plus (S (S (S O))) (S (S O))).

(*
(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)
*)
(** Coqがこの計算をどう進めて（簡約して）結論を導くかは以下のように表現できます。 *)

(*  [plus (S (S (S O))) (S (S O))]    
==> [S (plus (S (S O)) (S (S O)))] by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))] by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))] by the second clause of the [match]
==> [S (S (S (S (S O))))]          by the first clause of the [match]
*)

(*
(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)
*)
(** 表記を簡便にするため、複数の引数が同じ型を持つときは、型の記述をまとめることができます。
    [(n m : nat)]は[(n : nat) (m : nat)]と書いたのとまったく同じ意味になります。 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity.  Qed.

(*
(** You can match two expressions at once by putting a comma
    between them: *)
*)
(** matchに引数を与える際、複数の引数を次のようにカンマで区切って一度に渡すことができます。 *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(*
(** The _ in the first line is a _wildcard pattern_.  Writing _ in a
    pattern is the same as writing some variable that doesn't get used
    on the right-hand side.  This avoids the need to invent a bogus
    variable name. *)
*)
(** [minus]の[match]の行に現れる「 _ 」は、ワイルドカードパターンと呼ばれるものです。
    パターンの中に _ を書くと、それはその部分が何であってもマッチし、その値が使用されないことを意味します。
    この _ は、このような場合に無意味な名前をつける必要をなくしてくれます。 *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(*
(** **** Exercise: 1 star (factorial)  *)
*)
(** **** 演習問題: ★ (factorial) *)
(*
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. *)
*)
(** 再帰を使用した、一般的なfactorical（階乗）の定義を思い出してください :
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    これをCoqでの定義に書き直しなさい。 *)

Fixpoint factorial (n:nat) : nat := 
(* FILL IN HERE *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.

(** [] *)

(*
(** We can make numerical expressions a little easier to read and
    write by introducing "notations" for addition, multiplication, and
    subtraction. *)
*)
(** ここで紹介する"notation"（表記法）という機能を使うことで、加算、減算、乗算のような数値を扱う式をずっと読みやすく、書きやすくすることができます。 *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

(*
(** (The [level], [associativity], and [nat_scope] annotations
   control how these notations are treated by Coq's parser.  The
   details are not important, but interested readers can refer to the
   "More on Notation" subsection in the "Advanced Material" section at
   the end of this chapter.) *)
*)
(** （[level]、[associativity]、[nat_scope]という記述は、Coqのパーザーにこれらの表記法をどう扱うかを指示するものです。
   詳細は重要ではないのですが、もし興味があれば本章の末尾にある「発展的な内容」にある「表記法をより詳しく」の項を読んでください。 *)

(*
(** Note that these do not change the definitions we've already
    made: they are simply instructions to the Coq parser to accept [x
    + y] in place of [plus x y] and, conversely, to the Coq
    pretty-printer to display [plus x y] as [x + y]. *)
*)
(** これらは、これまで我々が定義してきたものを何ら変えるわけではありません。
    NotationはCoqのパーサに対して[x + y]を[plus x y]と解釈させたり、逆に[plus x y]を[x + y]と表記させたりするためのものです。 *)

(*
(** When we say that Coq comes with nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation! *)
*)
(** 最初の方で、Coqにはほとんど何も用意されていない、という話をしましたが、本当のところ、数値を比較する関数すら自分で作らなければならないのです！! *)
(*
(** The [beq_nat] function tests [nat]ural numbers for [eq]uality,
    yielding a [b]oolean.  Note the use of nested [match]es (we could
    also have used a simultaneous match, as we did in [minus].)  *)
*)
(** [beq_nat]関数は自然数を比較して等しいかをbool値で返すものです。
    入れ子になった[match]に気をつけて、以下のソースを読んでください（二つの変数を一度に[match]させる場合の書き方は、[minus]のところですでに登場しています）。 *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(*
(** Similarly, the [ble_nat] function tests [nat]ural numbers for
    [l]ess-or-[e]qual, yielding a [b]oolean. *)
*)
(** 同様に、[ble_nat]関数は自然数を比較して小さいか等しい、ということをbool値で返します。 *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. reflexivity.  Qed.

(*
(** **** Exercise: 2 stars (blt_nat)  *)
*)
(** **** 練習問題: ★★ (blt_nat) *)
(*
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)
*)
(** [blt_nat]関数は、自然数を比較して小さい、ということをbool値で返します（ [nat]ural numbers for [l]ess-[t]han）。
    [Fixpoint]を使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。 *)

Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.

(** [] *)

(* ###################################################################### *)
(*
(** * Proof by Simplification *)
*)
(** * 簡約を用いた証明 *)

(*
(** Now that we've defined a few datatypes and functions, let's
    turn to the question of how to state and prove properties of their
    behavior.  Actually, in a sense, we've already started doing this:
    each [Example] in the previous sections makes a precise claim
    about the behavior of some function on some particular inputs.
    The proofs of these claims were always the same: use [reflexivity] 
    to check that both sides of the [=] simplify to identical values. 

    (By the way, it will be useful later to know that
    [reflexivity] actually does somewhat more simplification than [simpl] 
    does -- for example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    when reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    found; by contrast, [simpl] is used in situations where we may
    have to read and understand the new goal, so we would not want it
    blindly expanding definitions.) 

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved
    just by observing that [0 + n] reduces to [n] no matter what
    [n] is, a fact that can be read directly off the definition of [plus].*)
*)
(** ここまでに、いくつかの型や関数を定義してきました。
    が、ここからは少し目先を変えて、こういった型や関数の特性や振る舞いをどうやって知り、証明していくかを考えてみることにしましょう。
    実際には、すでにこれまでやってきたことでも、その一部に触れています。
    例えば、前のセクションの[Example]は、ある関数にある特定の値を入力した時の振る舞いについて、あらかじめ想定していたものと正確に一致していると主張してくれます。
    それらの主張が証明しているものは、以下のものと同じです。
    「[=]の両側の式を簡約した結果が一致しているかを調べるために、[reflexivity]を使いなさい。」
 
    （ところで、[reflexivity]は[simpl]より多くの簡約を行います。
    例えば、定義した項を定義の右辺に置き換える「展開(unfolding)」を行います。
    こう言った差が発生する理由は、[reflexivity]が成功するなら、簡約結果がどうなっているかを出す必要がないからです。
    [simpl]の場合はこうは行かず、簡約した結果を画面に出すため、定義をむやみに展開したりしません。）

    このような「簡約を用いた証明」は、関数のさらに興味深い性質をうまく証明することができます。
    例えば、[0]が自然数の加算における左単位元（左から加えても値が変わらない値）であることの証明は、[n]が何であっても[0 + n]を注意深く縮小（簡約）したものが[n]になることを、[+]という関数が「最初の引数を引き継いで再帰的に定義されている」ということを考慮した上で示せればいいということです。 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.


(*
(** (_Note_: You may notice that the above statement looks
    different in the original source file and the final html output. In Coq
    files, we write the [forall] universal quantifier using the
    "_forall_" reserved identifier. This gets printed as an
    upside-down "A", the familiar symbol used in logic.)  *)
*)
(* 訳注：いろいろ書いてあるが、makefileで有効にしていないので多分forallと見えていると思う。 *)

(*
(** The form of this theorem and proof are almost exactly the
    same as the examples above; there are just a few differences.

    First, we've used the keyword [Theorem] instead of
    [Example].  Indeed, the difference is purely a matter of
    style; the keywords [Example] and [Theorem] (and a few others,
    including [Lemma], [Fact], and [Remark]) mean exactly the same
    thing to Coq.

    Secondly, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  In order to prove
    theorems of this form, we need to to be able to reason by
    _assuming_ the existence of an arbitrary natural number [n].  This
    is achieved in the proof by [intros n], which moves the quantifier
    from the goal to a "context" of current assumptions. In effect, we
    start the proof by saying "OK, suppose [n] is some arbitrary number."

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to tell Coq how it should check the correctness of some
    claim we are making.  We will see several more tactics in the rest
    of this lecture, and yet more in future lectures. *)
*)
(** この定理と証明の様式は、以前示した例とほとんど同じですが、いくつか違いがあります。
 
    まず、[Example]の代わりに[Theorem]キーワードが使用されていることです。
    単なるスタイルの違いで、[Example]と[Theorem]（他にも[Lemma]、[Fact]、[Remark]など）はCoqから見るとすべて同じ意味を持ちます。
 
    他に、量化子が加えられている（[forall n:nat]）ことが挙げられます。
    これにより、定理は「全ての」自然数[n]について言及できます。
    証明では、勝手気ままな[n]が存在することを「仮定」できる必要があります。
    この動きは[intros n]によって実現できます。
    実際には、これは量化子をゴールから仮定の「文脈(context)」に移動しています。
    これにより、「[n]をある自然数とする」から証明を始められます。

    [intros]や[simpl]、[reflexivity]は「タクティック(_tactic_)」の例です。
    タクティックは、[Proof]と[Qed]の間に記述され、Coqに対して、我々がしようとしている主張の正当性をどのようにチェックすべきかを指示するためのコマンドです。
    この講義の残りでは、まだ出てきていないタクティックのうちのいくつかを紹介していきましょう。
    さらにその後の講義ではもっと色々出てくるのですが。 *)

(*
(** We could try to prove a similar theorem about [plus] *)
*)
(** 似ているこんな定理も示したくなるでしょう。 *)

Theorem plus_n_O : forall n, n + 0 = n.

(*
(** However, unlike the previous proof, [simpl] doesn't do anything in
    this case *)
*)
(** しかし、先ほどの証明と違い、今回[simpl]は何もしてくれません。 *)

Proof.
  simpl. (* Doesn't do anything! *)
Abort.

(*
(** (Can you explain why this happens?  Step through both proofs with
    Coq and notice how the goal and context change.) *)
*)
(** （どうしてこうなるか分かるでしょうか？
    それぞれの証明を1ステップずつ見て、ゴールと文脈がどのように変化していくかを見てください。） *)

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(*
(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)
*)
(** 定理の名前についている[_l]という接尾辞は、「左の」と読みます。 *)


(* ###################################################################### *)
(*
(** * Proof by Rewriting *)
*)
(** * 書き換え（[Rewriting]）による証明*)

(*
(** Here is a slightly more interesting theorem: *)
*)
(** もう少し面白い定理を見てみましょう。 *)

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.

(*
(** Instead of making a completely universal claim about all numbers
    [n] and [m], this theorem talks about a more specialized property
    that only holds when [n = m].  The arrow symbol is pronounced
    "implies."

    As before, we need to be able to reason by assuming the existence
    of some numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context. 

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)
*)
(** この定理は、あらゆる[n]や[m]について完全に成り立つと言っているわけではなく、[n = m]が成り立つときに限って成立する、というものです。
    この矢印は"ならば"と読みます。
 
    前と同じように、[n]と[m]の存在を仮定する必要があります。
    また、[n = m]という仮定を置く必要もあります。
    [intros]タクティックはこれら三つを全てゴールから仮定の文脈に移動します。
 
    [n]と[m]が両方とも任意の数なのですから、これまでの証明でやってきたように簡約することはできません。
    その代わりに、[n = m]ならば、イコールの両側の[n]を[m]に書き換えても等しさは変わらない、というところに注目します。
    このような書き換えをしてくれるのが[rewrite]タクティックです。 *)

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite -> H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

(*
(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the (arbitrary)
    name [H].  The third tells Coq to rewrite the current goal ([n + n
    = m + m]) by replacing the left side of the equality hypothesis
    [H] with the right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes in Coq's behavior.) *)
*)
(** 証明の1行目は、全称量化子（forall）がついた、つまり「あらゆる[n],[m]について」の部分をコンテキストに移しています。
    2行目は、[n = m]ならば、という仮定をコンテキストに写し、[H]という名前をこれに与えています。
    3行目は、ゴールになっている式([n + n = m + m])に仮定[H]の左側を右側にするような書き換えを施しています。
 
    （[rewrite]の矢印は特に論理に関与していません。
    単に左側を右側に置き換えているだけです。
    逆に右側を左側に置き換えたい場合は、[rewrite <-]と書きます。
    この逆の置き換えも上の証明で試して、Coqの振る舞いがどのように変わるかを観察してください。） *)

(*
(** **** Exercise: 1 star (plus_id_exercise)  *)
*)
(** **** 練習問題: ★ (plus_id_exercise) *)
(*
(** Remove "[Admitted.]" and fill in the proof. *)
*)
(** [Admitted.]を削除し、証明を完成させなさい。*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** As we've seen in earlier examples, the [Admitted] command
    tells Coq that we want to skip trying to prove this theorem and
    just accept it as a given.  This can be useful for developing
    longer proofs, since we can state subsidiary facts that we believe
    will be useful for making some larger argument, use [Admitted] to
    accept them on faith for the moment, and continue thinking about
    the larger argument until we are sure it makes sense; then we can
    go back and fill in the proofs we skipped.  Be careful, though:
    every time you say [Admitted] (or [admit]) you are leaving a door
    open for total nonsense to enter Coq's nice, rigorous, formally
    checked world! *)
*)
(** Admittedコマンドは、Coqに対して「この証明はあきらめたので、この定理はこれでいいことにしてください」と指示するものです。
    この機能は、より長い証明をする際に便利です。
    何か大きな論証をしようとする時、今のところ信用している補足的な命題を示したい時があります。
    そんな時、[Admitted]を使用すると、その命題を一時的に信用できることにして、それを踏み台にしてより大きな論証を進めることができるのです。
    そしてそれが完成したのち、あらためて保留していた命題の証明を埋めればいいのです。
    ただし注意して下さい。[admit]や[Admitted]を使用することは、一時的にドアを開けて、「全て形式的なチェックを受け証明済みの、信用するに足るCoqの世界」から、信用に値しない下界へ足を踏み出していることに他なりません。
    いつかは戻ってドアを閉めることがお約束です。*)

(*
(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. *)
*)
(** [rewrite]タクティックを使うときには、仮定の代わりに、前もって証明された定理も利用できます。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(*
(** **** Exercise: 2 stars (mult_S_1)  *)
*)
(** **** 練習問題: ★★ (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################################### *)
(*
(** * Proof by Case Analysis *) 
*)
(** * Case分析による証明 *)

(*
(** Of course, not everything can be proved by simple
    calculation: In general, unknown, hypothetical values (arbitrary
    numbers, booleans, lists, etc.) can block the calculation.  
    For example, if we try to prove the following fact using the 
    [simpl] tactic as above, we get stuck. *)
*)
(** もちろん、どんな命題でも簡単な計算だけで証明できるという訳ではありません。
    一般に、未知だったり仮定の値（任意の自然数、bool値、リストなど）は、簡約を止めてしまいます。
    例えば、下の命題を[simpl]タクティックだけで証明しようとすると、すぐに行き詰まってしまいます。 *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  simpl.  (* does nothing! *)
Abort.

(*
(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    What we need is to be able to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].
    And if [n = S n'] for some [n'], then, although we don't know
    exactly what number [n + 1] yields, we can calculate that, at
    least, it will begin with one [S], and this is enough to calculate
    that, again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)
*)
(** その原因は、beq_natと+の定義で、共に最初の引数が[match]に渡されていることです。
    つまり、[+]に渡す最初の引数は[n]という未知数な上に、[beq_nat]の引数は[n + 1]という複合式になっているため、そのまま簡約できないのです。
 
    今求められていることは、[n]を何らかの条件に分割できないかを検討することです。
    もし[n]が[O]なら、[beq_nat (n + 1) 0]の結果を得ることはできます。
    もちろん結果は[false]です。
    もし[n]が何かの[n']を使って[n = S n']と表せる場合、我々は[n + 1]の値を得ることはできません。
    ただ、少なくともその式が一つの[S]で始まることはわかります。
    これが分かれば、[beq_nat (n + 1) 0]の結果が[false]になることまでは計算できます。
 
    このことから、求められるタクティックはCoqに[n = O]の場合と[n = S n']の場合に分けて考えるように求めるようなもので、これを実現するのが[destruct]タクティックです。 *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

(*
(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem as
    proved.  (No special command is needed for moving from one subgoal
    to the other.  When the first subgoal has been proved, it just
    disappears and we are left with the other "in focus.")  In this
    proof, each of the subgoals is easily proved by a single use of
    [reflexivity].

    The annotation "[as [| n']]" is called an _intro pattern_.  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list_ of
    lists of names, separated by [|].  Here, the first component is
    empty, since the [O] constructor is nullary (it doesn't carry any
    data).  The second component gives a single name, [n'], since [S]
    is a unary constructor.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it here to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)
*)
(** この証明では、[destruct]タクティックは二つのサブゴールを作っています。
    その両方を別々に証明することで、全体が定理として認められます。
    一つのサブゴールからもう一つへ移動するための特別なコマンドは必要ありません。
    一つ目のサブゴールが証明されると、自動的にもう一つのサブゴールにフォーカスが移ります。
    この証明では、二つに分かれたサブゴールのいずれも[reflexivity]を1回使うだけで簡単に証明できます。
 
    [destruct]についている注釈"[as [| n']]"は、「イントロパターン(_intro pattern_)」と呼ばれるものです。
    これはCoqに対して、サブゴール毎に出てくる変数をどんな変数名で扱うかを指示するものです。
    一般的に[[]]の間にあるものは [|] によって区切った「名前のリスト」のリストです。
    今回のリストの最初の要素は空ですが、これは[nat]の最初のコンストラクタである[O]が引数をとらないからです。
    二つ目のコンストラクタ[S]は引数を一つ取りますので、二つ目の要素では変数名を一つ、[n']を指定しています。
 
    [destruct]タクティックは帰納的に定義された型に対して使用できます。
    例えば、bool値の否定が対合(_involutive_)であること、つまり否定の否定が元と同じになることを証明してみましょう。 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(*
(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  Although this is convenient, it is arguably bad
    style, since Coq often makes confusing choices of names when left
    to its own devices. *)
*)
(** ここで使われている[destruct]には[as]句がありませんが、ここで展開している[b]の型[bool]の二つのコンストラクタが両方とも引数をとらないため、名前を指定する必要がないのです。
    このような場合、"[as [|]]"や"[as []]"のように書くこともできます。
    実は、[destruct]の[as]句はどんなときでも省略可能です。
    その際はCoqの側で自動的に変数名をつけてくれます。
    これは確かに便利なのですが、よくない書き方とも言えます。
    Coqはしばしば混乱しやすい、望ましくない名前を付けることがあります。 *)

(*
(** **** Exercise: 1 star (zero_nbeq_plus_1)  *)
*)
(** **** 練習問題: ★ (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ###################################################################### *)
(*
(** * More Exercises *)
*)
(** * 発展課題 *)

(*
(** **** Exercise: 2 stars (boolean_functions)  *)
*)
(** **** 練習問題: ★★ (boolean_functions)  *)
(*
(** Use the tactics you have learned so far to prove the following 
    theorem about boolean functions. *)
*)
(** ここまでで学んだタクティックを使い、次のブール関数についての定理を証明しなさい。 *)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.

(*
(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)
*)
(** また、[negation_fn_applied_twice]という名前で、
    上の定理とほとんどが同じ、二つ目の[f]に関する仮定が[f x = negb x]になっている定理を記述し、証明しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*
(** **** Exercise: 2 stars (andb_eq_orb)  *)
*)
(** **** 練習問題: ★★ (andb_eq_orb)  *)
(*
(** Prove the following theorem.  (You may want to first prove a
    subsidiary lemma or two. Alternatively, remember that you do
    not have to introduce all hypotheses at the same time.) *)
*)
(** 次の定理を証明しなさい。
    （補題を先に一つか二つ示したくなるかもしれません。
    その代わりに、全ての仮定を同時に文脈に導入する必要はない、ということを覚えておいてください。） *)

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars (binary)  *)
*)
(** **** 練習問題: ★★★ (binary)  *)
(*
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers. 

    (Hint: Recall that the definition of [nat] from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function [incr] for binary numbers, 
        and a function [bin_to_nat] to convert binary numbers to unary numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions. Notice that 
        incrementing a binary number and then converting it to unary 
        should yield the same result as first converting it to unary and 
        then incrementing. 
*)
 *)
(** 自然数を1進数ではなくより効率的な2進数で扱う自然数の表現を考えます。
    これは「自然数は0かそれより1大きいものである」という表現をする代わりに、以下の3つの規則で表現します。
 
      - ゼロ
      - 2進数を2倍したもの
      - 2進数の2倍より1大きいもの
 
    (a) 上の規則で定義できる2進数に対応する[bin]という帰納型を定義しなさい。
 
    （ヒント：[nat]が以下のように定義されていたことを思い出しましょう。
[[
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
]]
    そして、この中では[O]や[S]が「何を意味しているか」は何も書かれていないことに注意してください。
    この定義は、単に「[O]は[nat]という集合に入っていて、また[n]がもし[nat]に入っていたら[S n]も[nat]に入っている」ということを言っているに過ぎません。
    [O]をゼロに、[S]を次の数のコンストラクタ（[+1]）に解釈することで、[nat]を「自然数として使って」関数を作ったり性質を証明したりしました。
    ここでの[bin]の定義は規則の数相応に簡単なものになるでしょう。
    これから作る[bin]に関する関数を書くことこそが、[bin]に数学的な意味づけをするのです。）
 
    (b) 次に、[incr]という名前でインクリメント関数を、[bin_to_nat]という名前で2進数を1進数に変換する関数を書きなさい。
 
    (c) [test_bin_incr1]や[test_bin_incr2]といった名前で[incr]や[bin_to_nat]に関する5つの単体テストを書きなさい。
        2進数をインクリメントして1進数に変換したものは、1進数に変換して1加えたものと一致するということに注意してください。 *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(*
(** * More on Notation (Advanced) *)
*)
(** * 発展：表記法をより詳しく *)

(*
(** In general, sections marked Advanced are not needed to follow the
    rest of the book, except possibly other Advanced sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference. *)
*)
(** 「発展」と付けた節は、同じく「発展」と付いている節以外には必須ではありません。
    初めて読むときは、今後のために軽く目を通すくらいにしておくと良いでしょう。 *)

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

(*
(** For each notation-symbol in Coq we can specify its _precedence level_
    and its _associativity_. The precedence level n can be specified by the
    keywords [at level n] and it is helpful to disambiguate
    expressions containing different symbols. The associativity is helpful
    to disambiguate expressions containing more occurrences of the same 
    symbol. For example, the parameters specified above for [+] and [*]
    say that the expression [1+2*3*4] is a shorthand for the expression
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and 
    _left_, _right_, or _no_ associativity.

    Each notation-symbol in Coq is also active in a _notation scope_.  
    Coq tries to guess what scope you mean, so when you write [S(O*O)] 
    it guesses [nat_scope], but when you write the cartesian
    product (tuple) type [bool*bool] it guesses [type_scope].
    Occasionally you have to help it out with percent-notation by
    writing [(x*y)%nat], and sometimes in Coq's feedback to you it
    will use [%nat] to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation (3,4,5, etc.), so you
    may sometimes see [0%nat] which means [O], or [0%Z] which means the
    Integer zero.
*)
 *)
(** Coqで表記法を定義する際、「優先度(_precedence level_)」と「結合性(_associativity_)」を定義できます。
    優先度に n を割り当てる際には[at level n]のように書きます。
    優先度は、複数の表記法が混じった際、表現している式の解釈を一意に定めるために付けます。
    結合性は同じ表記法が複数回現れたときの解釈を定めるために付けます。
    例えば、この章では[+]と[*]を定義しましたので、[1+2*3*4]を[(1+((2*3)*4))]の略記版として利用できます。
    Coqでは優先度として0から100のレベルを、また結合性として「左結合(left)」「右結合(right)」または「結合性なし(no)」を指定できます。
 
    Coqでの表記法は、それぞれ指定した「表記スコープ(_notation scope_)」の中でのみ利用できます。
    表記スコープが何で書いているかをCoqは自動で判定しようとします。
    例えば[S(O*O)]と書いていれば[nat_scope]だと判定し、デカルト積（タプル）型である[bool*bool]という記述からは[type_scope]と判定します。
    判定を誤ることもあるので、パーセント記号を使って、[(x*y)%nat]のように明示しないといけないこともあります。
    また、Coqが特定の表記スコープでの表記法であることを明示するために[%nat]という記法を使うこともあります。
 
    表記スコープは3,4,5などの数の表記法にも使われています。
    例えば[0%nat]と書くと[nat]の[O]を意味しますが、[0%Z]と書くと整数（[Z]）のゼロを意味します。 *)

(*
(** * [Fixpoint] and Structural Recursion (Advanced) *)
*)
(** * 発展：[Fixpoint]と構造的再帰 *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

(*
(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing".
    
    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)
*)
(** 上の定義をCoqが検査すると、[plus']が「第一引数が減少している（"decreasing on 1st argument"）」というメッセージを出します。
    これは引数[n]に関する「構造的再帰(_structural recursion_)」を行っていることを意味します。
    つまり、再帰呼び出しの際には、必ず[n]が厳密に小さくなっているということです。
    これにより、どんな引数でも[plus']の呼び出しが必ずいつか終了することを保証できます。
    Coqは[Fixpoint]での定義で、ある特定の引数が「減少している」ことを求めます。
 
    この要求はCoqの設計の基礎部分から来ています。
    この要求により、Coqで定義できる関数が、どんな入力に対しても終了することを保証できます。
    しかし、Coqの「減少性解析」はそれほど洗練されていないため、場合によっては関数を不自然な形で書かなければならないこともあります。 *)

(*
(** **** Exercise: 2 stars, optional (decreasing)  *)
*)
(** **** 練習問題: ★★, optional (decreasing) *)
(*
(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)
*)
(** これを具体的に感じるため、（自然数の単純な関数でかまわないので）全ての入力で停止するが、Coqが制限のため受け入れないような[Fixpoint]による定義の書き方を見つけなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)

