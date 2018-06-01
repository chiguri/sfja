(** * Induction: 帰納法による証明 *)
(* begin hide *)
(** * Induction: Proof by Induction *)
(* end hide *)

(* begin hide *)
(** Before getting started, we need to import all of our
    definitions from the previous chapter: *)
(* end hide *)
(** 始める前に、前の章の定義をここに持ってきます。 *)

Require Export Basics.

(* begin hide *)
(** For the [Require Export] to work, you first need to use
    [coqc] to compile [Basics.v] into [Basics.vo].  This is like
    making a [.class] file from a [.java] file, or a [.o] file from a
    [.c] file.  There are two ways to do it:

     - In CoqIDE:

         Open [Basics.v].  In the "Compile" menu, click on "Compile
         Buffer".

     - From the command line: Either

         [make Basics.vo]

       (assuming you've downloaded the whole LF directory and have a
       working [make] command) or

         [coqc Basics.v]

       (which should work from any terminal window).

    If you have trouble (e.g., if you get complaints about missing
    identifiers later in the file), it may be because the "load path"
    for Coq is not set up correctly.  The [Print LoadPath.] command may
    be helpful in sorting out such issues.

    In particular, if you see a message like

        [Compiled library Foo makes inconsistent assumptions over
        library Coq.Init.Bar]

    you should check whether you have multiple installations of Coq on
    your machine.  If so, it may be that commands (like [coqc]) that
    you execute in a terminal window are getting a different version of
    Coq than commands executed by Proof General or CoqIDE.

    One more tip for CoqIDE users: If you see messages like [Error:
    Unable to locate library Basics], a likely reason is
    inconsistencies between compiling things _within CoqIDE_ vs _using
    coqc_ from the command line.  This typically happens when there are
    two incompatible versions of [coqc] installed on your system (one
    associated with CoqIDE, and one associated with [coqc] from the
    terminal).  The workaround for this situation is compiling using
    CoqIDE only (i.e. choosing "make" from the menu), and avoiding
    using [coqc] directly at all. *)
(* end hide *)
(** [Require Export]を動かすには、[coqc]で[Basics.v]をコンパイルして[Basics.vo]を作る必要があります。
    ちょうど [.java] のファイルから [.class] を作ったり、 [.c] のファイルから [.o] を作ったりするのと同じです。
    コンパイルする方法を二つ紹介します。
 
     - CoqIDEを使って：
 
         CoqIDEで[Basics.v]を開き、メニューの"Compile"から"Compile Buffer"を選びます。
 
     - コマンドラインで：
 
         [make Basics.vo]を実行する（LFの中身全体をダウンロードしていて、かつ[make]が動く環境である場合）か、

         [coqc Basics.v]を実行してください（こちらは[coqc]がパスに存在すればどのターミナルからでも可能です）。
 
   もし識別子が見つからないなどのエラーが出たりしたら、Coqの"load path"が正しく設定されていないせいかもしれません。
   [Print LoadPath.]というコマンドで正しく設定されているか確認してみてください。

   特に、

        [Compiled library Foo makes inconsistent assumptions over
        library Coq.Init.Bar]

   というメッセージが表示される場合、Coqが複数インストールされていないか確認してください。
   入っていた場合、ターミナルからコマンドとして使っているCoq（[coqc]など）とProof GeneralやCoqIDEが使っているCoqが異なる可能性があります。

   もう一点CoqIDEユーザへ：
   もし[Error: Unable to locate library Basics] というメッセージが表示される場合、「CoqIDE内」のコンパイルと「ターミナル上の[coqc]」のコンパイルによる不整合が考えられます。
   よくある原因としては、互換性のない二つのバージョンの[coqc]（一方はCoqIDEから使われ、もう一方はターミナルから使用されている）が存在するというものです。
   この場合、常にコンパイルをCoqIDEからのみ（例えば"make"をメニューから選んで）コンパイルし、ターミナルから呼び出さないようにしましょう。 *)

(* ################################################################# *)
(* begin hide *)
(** * Proof by Induction *)
(* end hide *)
(** * 帰納法による証明 *)

(* begin hide *)
(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left, using an easy argument based on
    simplification.  We also observed that proving the fact that it is
    also a neutral element on the _right_... *)
(* end hide *)
(** 前の章では、[0]が[+]に対する左単位元であることを証明しました。
    実際には、[0]は「右(_right_)」単位元でもあるのですが... *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

(* begin hide *)
(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)
(* end hide *)
(** ... しかし、これは左単位元ほど簡単には示せません。
  [reflexivity]を使ってもうまくいきません。
  というのも、[n + 0]にある[n]はよく分からない数なので、[+]の定義における[match]は簡約されないのです。 *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(* begin hide *)
(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)
(* end hide *)
(** [destruct n]を使った場合分けもやはり先には進められません。
    [n = 0]のときはいいのですが、[n = S n']のときは同じ理由で詰まってしまいます。 *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(* begin hide *)
(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, if we just go on like this
    we'll never finish. *)
(* end hide *)
(** [destruct n']を使って進められますが、[n]がいくらでも大きくなりうるので、このやり方ではいつまで経っても終わりません。 *)

(* begin hide *)
(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we usually need a more powerful
    reasoning principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)
(* end hide *)
(** これらの、大体の数やリストなどの帰納的に定義された集合に関する性質を示すには、より強力な道具、「帰納法(_induction_)」が必要になります。
 
    高校や離散数学の講義などで習ったと思いますが、「自然数に関する帰納法（数学的帰納法）の原理」をおさらいしておきましょう。
    もし[P(n)]が自然数[n]に関する命題だったとすると、任意の数[n]に対し[P]が成り立つことを、次のように示すのでした。
         - [P(O)]が成り立つことを示す。
         - どんな[n']についても、[P(n')]が成り立つならば、[P(S n')]が成り立つことを示す。
         - 以上から、任意の[n]について[P(n)]が成り立つと言える。
 
    Coqではこれを同じようにします。
    任意の[n]で[P(n)]が成り立つことをゴールとして示すときに、それを（[induction]タクティックを使うことで）、二つのサブゴールに分けます。
    一つ目は[P(O)]の証明、そして次は[P(n') -> P(S n')]の証明です。
    どのようになるのかを例を使って見ていきましょう。 *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(* begin hide *)
(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].  (Strictly speaking, we can omit
    the [as...] clause and Coq will choose names for us.  In practice,
    this is a bad idea, as Coq's automatic choices tend to be
    confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)
(* end hide *)
(** [destruct]タクティックと同様に、[induction]タクティックには、サブゴールで使う変数を指定する[as...]節を使うことができます。
    二つに分かれているので、[as...]節も[|]で二つに分かれています。
    （厳密に言うと、ここでは[as...]節は省略できて、その場合Coqが名前を付けてくれます。
    ただし、実際には、これはあまりいい方法ではありません。
    というのも、Coqが自動で付ける名前では混乱しがちだからです。）
 
    一つ目のサブゴールでは、[n]は[0]に置き換えられています。
    新しい変数は特に導入されていません（そのため[as...]の一つ目は空になっています）。
    ゴールは[0 = 0 + 0]となっていて、これは簡約すれば示せます。
 
    二つ目のサブゴールでは、[n]は[S n']に置き換えられ、仮定として[IHn']という名前（つまり[n']に関する帰納法の仮定(Induction Hypothesis)）で[n' = n' + 0]が文脈に追加されます。
    [n']と[IHn']という二つの名前は[as...]節の二つ目で指定しています。
    ゴールは[S n' = (S n') + 0]となっていますが、簡約すると[S n' = S (n' + 0)]になります。
    これは帰納法の仮定である[IHn']から示せます。 *)


Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(* begin hide *)
(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)
(* end hide *)
(** （実のところ、上の証明では[intros]タクティクは冗長です。
    量化変数を持つゴールに対して[induction]タクティクを適用すると、これらの変数は必要に応じて文脈に移動されます。） *)

(* begin hide *)
(** **** Exercise: 2 stars, recommended (basic_induction)  *)
(* end hide *)
(** **** 練習問題: ★★, recommended (basic_induction)  *)
(* begin hide *)
(** Prove the following using induction. You might need previously
    proven results. *)
(* end hide *)
(** 以下の定理を帰納法で証明しなさい。
    証明には、前に示した内容を使う必要があるかもしれません。 *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.5: mult_0_r *)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.5: plus_n_Sm *)


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.5: plus_comm *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(* GRADE_THEOREM 0.5: plus_assoc *)
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars (double_plus)  *)
(* end hide *)
(** **** 練習問題: ★★ (double_plus)  *)
(* begin hide *)
(** Consider the following function, which doubles its argument: *)
(* end hide *)
(** 次のように、引数を二倍にする関数を定義します。 *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* begin hide *)
(** Use induction to prove this simple fact about [double]: *)
(* end hide *)
(** 帰納法を使って、[double]に関する以下の性質を証明しなさい。 *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, optional (evenb_S)  *)
(* end hide *)
(** **** 練習問題: ★★, optional (evenb_S)  *)
(* begin hide *)
(** One inconvenient aspect of our definition of [evenb n] is the
    recursive call on [n - 2]. This makes proofs about [evenb n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [evenb (S n)] that works better
    with induction: *)
(* end hide *)
(** [evenb n]の定義の不便な点は、再帰呼び出しが[n - 2]に対して行われているというものです。
    これにより、[evenb n]に関する性質の証明を[n]に基づく帰納法で行う場合に、再帰呼び出しに関する性質を得るには[n - 2]に対する仮定が必要となります。
    このため、そのままでは帰納法で示すことが難しくなっています。
    次の補題は[evenb (S n)]の特徴付けを行っています。
    これを用いることで、帰納法での扱いが容易になります。 *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star (destruct_induction)  *)
(* end hide *)
(** **** 練習問題: ★ (destruct_induction)  *)
(* begin hide *)
(** Briefly explain the difference between the tactics [destruct]
    and [induction].

(* FILL IN HERE *)
*)
(* end hide *)
(** [destruct]と[induction]の違いについて大まかに説明しなさい。
 
(* FILL IN HERE *)
 *)
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Proofs Within Proofs *)
(* end hide *)
(** * 証明の中の証明 *)

(* begin hide *)
(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this.  For example, our earlier
    proof of the [mult_0_plus] theorem referred to a previous theorem
    named [plus_O_n].  We could instead use [assert] to state and
    prove [plus_O_n] in-line: *)
(* end hide *)
(** Coqでは、通常の数学のように、大きな証明を複数の定理の列に分割して、後ろの証明で前の定理を利用する、ということをします。
    しかし、このように分割した定理の中には、内容が自明だったり全く一般的でなかったりするため、全体に見える名前を付けるのが面倒になるものも現れます。
    こういう場合、その場所でだけ使うように「副定理」を記述、証明できると便利です。
    これを可能にするのが[assert]タクティックです。
    例えば、前に証明した[mult_0_plus]という定理では[plus_O_n]という名前の定理を使っていました。
    これを[assert]を使い、[plus_O_n]の記述と証明を書くと次のようになります。 *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(* begin hide *)
(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)
(* end hide *)
(** [assert]タクティックは二つのサブゴールを作ります。
    一つ目は表明したものそのものです。
    [H:]という記述は、表明したものを[H]と名付けることを意味します。
    （[destruct]や[induction]同様に、[as]を使って[assert (0 + n = n) as H]と書くこともできます。）
    ここで、表明の証明を波括弧[{ ... }]で囲ったのは、可読性のためという理由の他に、Coqの対話環境では、この部分の証明が終わったことがわかりやすくなるという理由もあります。
    二つ目のゴールは[assert]を実行したものと同じですが、文脈に[H]という名前で[0 + n = n]の仮定が入っています。
    つまり、[assert]は一つのサブゴールで表明した内容を証明させ、二つ目のサブゴールで元の場所に戻り、表明した内容を使って証明を進めさせるのです。 *)

(* begin hide *)
(** Another example of [assert]... *)
(* end hide *)
(** [assert]の他の使用例です。 *)

(* begin hide *)
(** For example, suppose we want to prove that [(n + m) + (p + q)
    = (m + n) + (p + q)]. The only difference between the two sides of
    the [=] is that the arguments [m] and [n] to the first inner [+]
    are swapped, so it seems we should be able to use the
    commutativity of addition ([plus_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> plus_comm] will affect
    only the _outer_ one... *)
(* end hide *)
(** 例えば、[(n + m) + (p + q) = (m + n) + (p + q)]を示す必要があったとします。
    [=]の左右での差は[m]と[n]の位置が[+]の間で入れ替わっているだけですから、加算の可換律（[plus_comm]）で書き換えれば簡単に示せるはずです。
    ただ、[rewrite]タクティックは「どこを」書き換えるかに関してはあまり賢くないので、今回は[rewrite -> plus_comm]を実行しても、3箇所存在する[+]のうち「外側」のものを書き換えてしまいます。 *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

(* begin hide *)
(** To use [plus_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the particular [m]
    and [n] that we are talking about here), prove this lemma using
    [plus_comm], and then use it to do the desired rewrite. *)
(* end hide *)
(** [plus_comm]を必要な場所に使うために、[n + m = m + n]（ただし[m]と[n]は今の文脈にある変数）を[assert]を使って補題として作る方法があります。
    この補題を[plus_comm]で示し、それを使って意図通りに式を書き換えるのです。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(* begin hide *)
(** * Formal vs. Informal Proof *)
(* end hide *)
(** * 形式的証明　対　非形式的証明 *)

(* begin hide *)
(** "_Informal proofs are algorithms; formal proofs are code_." *)
(* end hide *)
(** 「非形式的証明はアルゴリズムで、形式的証明はコードだ。」 *)

(* begin hide *)
(** What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true --
    an unassailable argument for the truth of [P].  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)
(* end hide *)
(** 数学的な言明に対して「よい証明」とは一体何でしょうか？この
    問いは、数千年に渡り議論されていますが、大まかに合意されている定義は次のようになります。
    「数学的命題[P]に対する証明とは、読み手（聞き手）が確かに[P]は正しいと信じるに足るような記述（発言）、すなわち[P]の正しさを否定できないような議論である。」
    つまり、証明とはコミュニケーションであるということです。
 
    コミュニケーションは、様々な「読み手」と行われます。
    あるときには、この「読み手」はCoqのようなプログラムでしょう。
    この場合、信じさせるための「信条」は[P]が形式的に定義された論理規則から導出できるということであり、証明はこれを確かめるためにプログラムを案内するレシピということになります。
    このレシピを「形式的(_formal_)」証明といいます。
 
    また別のときには、「読み手」が人間であることもあるでしょう。
    この場合、証明は英語や日本語などの自然言語で書かれることになり、結果として「非形式的(_informal_)」になります。
    こちらは、コミュニケーション時の戦略はそこまではっきりとはしません。
    「妥当な」証明ならば、読み手が[P]を信じるでしょう。
    しかし、読み手には、ある特定の書き方でないと信じない人もいれば、その書き方では信じられない人もいます。
    もしその読み手が、特別融通が利かなかったり、過度に未熟だったり、頭の回転が非常に鈍い人だったりすると、信じさせるには綿密に詳細を記述しなければならないでしょう。
    一方で、その分野に詳しい人がその証明を読んだ場合、あまりの詳細の記述に全体の流れを追えなくなってしまうでしょう。
    そのような読み手が知りたいのは証明における主なアイディアです。
    なぜなら、その人にとっては、ひたすら書かれた記述を理解するよりも、細部を自分で埋める方が楽なのです。
    究極的には、証明の記述方法の普遍的標準などありません。
    あり得る読み手全員が信じるに足るような非形式的証明の記述方法が存在しないからです。
 
    ただし実際には、複雑な内容を記述するための、多彩な慣習や慣用表現が作られています。
    これらを用いることで、少なくとも特定のコミュニティの中では、コミュニケーションをかなり円滑に進めることができます。
    こう言った慣習は、かなり明確に証明の良し悪しを判定する基準があります。
 
    この講義ではCoqを使っていますので、かなり形式的証明を扱うことになります。
    しかし、だからといって非形式的証明を忘れていいわけではありません！
    形式的証明は様々な点で有用なのですが、他の人とアイディアを交わしたりといったことには全くもって非効率的です。 *)

(* begin hide *)
(** For example, here is a proof that addition is associative: *)
(* end hide *)
(** 例えば、次の証明は加算が結合的であることを示しています。 *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(* begin hide *)
(** Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)
(* end hide *)
(** この証明はCoqにとっては完璧です。
    しかし人間からすると、直観的に理解することは難しいものです。
    コメントやbulletを使って証明の構成を記述すれば、少し読みやすくなります。 *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(* begin hide *)
(** ... and if you're used to Coq you may be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)
(* end hide *)
(** Coqに慣れている人なら、タクティックを一つずつ進めるように文脈とゴールを頭の中に作ることも可能かもしれません。
    しかし、ほんの少し証明が複雑になるだけでほぼ不可能になります。
 
    （こと細かな）数学者がこの証明を書くとしたら、大体次のようになるでしょう。 *)

(* begin hide *)
(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must show

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)
(* end hide *)
(** - 定理： 任意の[n]、[m]、[p]について、以下が成立する。
[[
      n + (m + p) = (n + m) + p.
]]
    証明： [n]に関する帰納法による。

    - [n = 0]の場合、示す命題は
[[
        0 + (m + p) = (0 + m) + p
]]
      である。これは[+]の定義から明らかである。
 
    - [n = S n']の場合で、帰納法の仮定として
[[
        n' + (m + p) = (n' + m) + p
]]
      が成り立つとする。示す命題は
[[
        (S n') + (m + p) = ((S n') + m) + p
]]
      である。[+]の定義より、次の形に変形される。
[[
        S (n' + (m + p)) = S ((n' + m) + p)
]]
      これは帰納法の仮定から明らかである。
      証明終了 *)
(* begin hide *)
(** The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)
(* end hide *)
(** 証明の大まかな形式は似ていますが、当然これは偶然ではありません。
    Coqの[induction]は、数学者版の箇条書きされたものと同じサブゴールを、同じ順で作るように設定されています。
    しかし、細部は大きく違います。
    形式的証明ではいくつかの手順がより明示的になっています（例えば[reflexivity]の使用など）が、逆に明示されていない箇所もあります（特に「証明する命題」はCoqの証明上には全く現れませんが、非形式的証明では現状確認のために明示されています）。 *)

(* begin hide *)
(** **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(* end hide *)
(** **** 練習問題: ★★, advanced, recommended (plus_comm_informal)  *)
(* begin hide *)
(** Translate your solution for [plus_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
*)
(* end hide *)
(** [plus_comm]の（課題として解いた）証明を非形式的証明で書きなさい。
 
    定理： 加算は可換律を満たす。
  
    証明： (* FILL IN HERE *)
 *)
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(* end hide *)
(** **** 練習問題: ★★, optional (beq_nat_refl_informal)  *)
(* begin hide *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [true = beq_nat n n] for any [n].

    Proof: (* FILL IN HERE *)
*)
(* end hide *)
(** [plus_assoc]の非形式的証明を参考に、次の定理の非形式的証明を書きなさい。
    Coqのタクティックを日本語に変換するだけではだめです！
  
    定理： 任意の[n]について、[true = beq_nat n n]が成立する。
     
    証明： (* FILL IN HERE *) 
 *)
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * More Exercises *)
(* end hide *)
(** * 発展課題 *)

(* begin hide *)
(** **** Exercise: 3 stars, recommended (mult_comm)  *)
(* end hide *)
(** **** 練習問題: ★★★, recommended (mult_comm)  *)
(* begin hide *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap]. *)
(* end hide *)
(** [assert]を使い、次の定理を示しなさい。
    ここでは[plus_swap]に対して[induction]を使ってはいけません。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(* begin hide *)
(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.  You may find that [plus_swap] comes in
    handy.) *)
(* end hide *)
(** 次に乗算の可換律を示しなさい。
    （補助定理を一つ示す必要があるでしょう。
    [plus_swap]を使うといいかもしれません。） *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, optional (more_exercises)  *)
(* end hide *)
(** **** 練習問題: ★★★, optional (more_exercises)  *)
(* begin hide *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)
(* end hide *)
(** 紙を準備し、以下の定理のそれぞれに対して、
    (a)簡約と書き換えだけで示せるか、
    (b)場合分け（[destruct]）が必要か、
    (c)帰納法が必要か、
    を考え、その予想を書きなさい。
    それが終わったら、実際に証明しなさい。
    （紙に書いた予想をコード中に書いたりしなくて構いません。
    手を動かす前に一度考えてもらうために使ったのです。） *)
(* 訳注：最後の括弧書きは「提出しなくて構いません」なのだが、web公開のテキストに提出も何もないので意訳。 *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(* end hide *)
(** **** 練習問題: ★★, optional (beq_nat_refl)  *)
(* begin hide *)
(** Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)
(* end hide *)
(** 次の定理を示しなさい。
    （[true]を統合の左辺に置くのは奇妙に見えるかもしれませんが、これは標準ライブラリにある定理に合わせたためです。
    書き換えは両方向で可能なので、どちらで記述しても問題はありません。） *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, optional (plus_swap')  *)
(* end hide *)
(** **** 練習問題: ★★, optional (plus_swap')  *)
(* begin hide *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. *)
(* end hide *)
(** [replace]タクティックは、特定の部分式を指定した別の式に書き換えるのに使います。
   [replace (t) with (u)]の形で、ゴールに存在する[t]を全て[u]に書き換え、サブゴールとして[t = u]を作ります。
   [rewrite]での書き換えが意図通りに行えないときに便利です。
 
   [replace]を使って次の[plus_swap']を証明しなさい。
   証明はほとんど[plus_swap]と同じですが、[assert (n + m = m + n)]を書かないようにしなさい。 *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, recommended (binary_commute)  *)
(* end hide *)
(** **** 練習問題: ★★★, recommended (binary_commute)  *)
(* begin hide *)
(** Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions
    from your solution to the [binary] exercise here so that this file
    can be graded on its own.  If you want to change your original
    definitions to make the property easier to prove, feel free to
    do so! *)
(* end hide *)
(** [Basics]の章の[binary]という課題で書いた、[increment]と[bin_to_nat]関数に関してです。
    以下の図が可換であることを示しなさい。
<<
                            incr 
              bin ----------------------> bin 
               |                           | 
    bin_to_nat |                           |  bin_to_nat 
               |                           | 
               v                           v 
              nat ----------------------> nat 
                             S 
>>
    つまり、2進数を1増やしてから（1進の）自然数に変換した結果と、変換を先にしてから1増やした結果が一致するということです。
    名前は[bin_to_nat_pres_incr]とします（presは保存(preserve)です）。
 
    始める前に、[binary]に書いた定義から証明しやすい形に変更しても構いません。 *)
(* 訳注：括弧書きに「このファイル単体で評価できるようにコピーしてください」と書いてあるが無関係なので消去 *)

(* FILL IN HERE *)
(** [] *)

(* begin hide *)
(** **** Exercise: 5 stars, advanced (binary_inverse)  *)
(* end hide *)
(** **** 練習問題: ★★★★★, advanced (binary_inverse)  *)
(* begin hide *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    there to complete this one; please copy them to this file to make
    it self contained for grading.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. *)
(* end hide *)
(** この課題は一つ前の続きになります。
    したがって、一つ前の課題で使った定義や定理が必要です。
 
    (a) まず、自然数から2進数へ変換する関数を書きなさい。
        そして、自然数を2進数に変換し、逆に変換した結果が元の自然数となることを示しなさい。
 
    (b) 逆方向も示した方がいいのでは？と思うでしょう。
        逆とはつまり、2進数を自然数に変換し、それをまた2進数に戻すと、元の2進数になる、というものです。
        しかし、これは正しくありません。
        なぜそうなるのかを説明しなさい。
 
    (c) 2進数を「直接」正規化する関数を定義しなさい（訳注：ここでいう「直接」とは、自然数に変換などせずに2進数のデータのまま計算を行うことです）。
        この関数[normalize]は2進数から2進数への関数であり、2進数を自然数に変換してそれを2進数に逆変換すると、[normalize]を適用した結果に一致するという性質があります。
        これを示しなさい。
        （注意：証明はトリッキーです。）
 
    ここでも、もし定義を変更したければして構いません。 *)

(* FILL IN HERE *)
(** [] *)


