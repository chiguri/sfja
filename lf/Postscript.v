(** * Postscript: あとがき *)
(*
(** * Postscript *)
*)

(** Congratulations: We've made it to the end! *)

(* ################################################################# *)
(*
(** * Looking Back *)
*)
(** * ふりかえり *)

(*
(** We've covered quite a bit of ground so far.  Here's a quick review...  

   - _Functional programming_:
          - "declarative" programming style (recursion over persistent
            data structures, rather than looping over mutable arrays
            or pointer structures)
          - higher-order functions
          - polymorphism *)
*)
(** ここまでとても多くのことを学んできました。
    簡単に振り返ってみましょう。
 
    - 関数プログラミング
          - 「宣言的」プログラミング（変更可能な配列やポインタなどによるループではなく、永続データ構造上の再帰）
          - 高階関数
          - 多相性 *)

(*
(**
     - _Logic_, the mathematical basis for software engineering:

               logic                        calculus
        --------------------   ~   ----------------------------
        software engineering       mechanical/civil engineering


          - inductively defined sets and relations
          - inductive proofs
          - proof objects *)
*)
(** 
     - 論理、ソフトウェア工学の数学的基盤:
<<
                論理                        微積分
        --------------------   ~   ---------------------------- 
            ソフトウェア工学               機械/土木工学
>>
 
          - 帰納的に定義された集合と関係
          - 帰納的証明
          - 証明オブジェクト *)

(*
(**
     - _Coq_, an industrial-strength proof assistant
          - functional core language
          - core tactics
          - automation
*)
 *)
(** 
     - _Coq_、産業用途に耐え得る証明支援器
          - 関数型のコア言語
          - 基礎となるタクティック
          - 自動化
 *)

(* ################################################################# *)
(*
(** * Looking Forward *)
*)
(** * これからの指針 *)

(*
(** If what you've seen so far has whetted your interest, you have two
    choices for further reading in the _Software Foundations_ series:

           - _Programming Language Foundations_ (volume 2, by a set of
             authors similar to this book's) covers material that
             might be found in a graduate course on the theory of
             programming languages, including Hoare logic, operational
             semantics, and type systems.

           - _Verified Functional Algorithms_ (volume 3, by Andrew
             Appel) builds on the themes of functional programming and
             program verification in Coq, addressing a range of topics
             that might be found in a standard data structures course,
             with an eye to formal verification. *)
*)
(** もしここまでの内容に興味を抱いたなら、続きとして「ソフトウェアの基礎」のシリーズに二つの選択肢があります。
 
           - 「プログラミング言語の基礎(_Programming Language Foundations_)」（この本とほとんど同じ著者たちに寄って書かれた第二巻）では、院生向けのプログラミング言語理論が説明されています。
             例えばホーア論理や操作的意味論、型システムなどについてです。
 
           - 「検証済み関数型アルゴリズム(_Verified Functional Algorithms_)」（Andrew Appelによる第三巻）では、Coqによる関数型プログラミングとプログラム検証について説明されています。
             一般的なデータ構造に関して広く、検証という視点を交えて述べられています。 *)

(* ################################################################# *)
(*
(** * Other sources *)
*)
(** * その他の資料 *)

(*
(** Here are some other good places to learn more...

       - This book includes some optional chapters covering topics
         that you may find useful.  Take a look at the table of contents and the chapter dependency diagram to find
         them.

       - If you're interested in real-world applications of formal
         verification to critical software, see the Postscript chapter
         of _Programming Language Foundations_.

       - Here are some great books on functional programming
            - Learn You a Haskell for Great Good, by Miran Lipovaca
              [Lipovaca 2011].
            - Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart [O'Sullivan 2008]
            - ...and many other excellent books on Haskell, OCaml,
              Scheme, Racket, Scala, F sharp, etc., etc.

       - And some further resources for Coq:
           - Certified Programming with Dependent Types, by Adam
             Chlipala [Chlipala 2013].
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran [Bertot 2004].

       - For applications of Coq in building verified systems, the
         lectures and course materials for the 2017 DeepSpec Summer
         School are a great resource.
         https://deepspec.org/event/dsss17/index.html
*)
 *)
(** その他に先に進む資料としてよいものをいくつか...
 
       - この本のオプションの章。
         目次と依存関係のページを眺めてみてください。
 
       - 実際の重要なソフトウェアに対する検証の適用について、第二巻「プログラミング言語の基礎」のあとがきの章に挙げています。
 
       - 関数型プログラミングについてよい本をいくつか:
            - Learn You a Haskell for Great Good, by Miran Lipovaca [Lipovaca 2011]
              （和訳：すごいHaskell たのしく学ぼう！）
            - Real World Haskell, by Bryan O'Sullivan, John Goerzen, and Don Stewart [O'Sullivan 2008]
              （和訳：Real World Haskell ―― 実戦で学ぶ関数型言語プログラミング）
            - その他、Haskell、OCaml、Scheme、Racket、Scala、F sharpなどなどでの素晴らしい本
 
       - Coqについての資料:
           - Certified Programming with Dependent Types, by Adam Chlipala [Chlipala 2013]
           - Interactive Theorem Proving and Program Development: Coq'Art: The Calculus of Inductive Constructions,
             by Yves Bertot and Pierre Casteran [Bertot 2004]

       - Coqを用いて検証済みシステムを構築するという話については、2017年のDeepSpec Summer Schoolの講義資料が有用でしょう。
         https://deepspec.org/event/dsss17/index.html 
 *)

(** $Date: 2017-08-24 17:13:02 -0400 (Thu, 24 Aug 2017) $ *)
