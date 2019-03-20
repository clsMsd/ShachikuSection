# プログラミング言語Dylanの紹介

## Dylanとは?
> Dylan is a multi-paradigm functional and object-oriented programming language.  
It is dynamic while providing a programming model designed to support efficient machine code generation,  
including fine-grained control over dynamic and static behaviors.
(https://opendylan.org/ より引用)

1990年台のはじめにAppleにより開発されたプログラミング言語。  
NewtonというPDA向けのプログラミング言語として採用される予定だったが、開発が間に合わずNewtonには別の言語(NewtonScript)の処理系が乗ることになった。  
その後もMac向けのプログラミング言語として開発が進められたが、1995年に開発チームごと解散させれられ Apple による開発は終了。  
その後は開発チームの元メンバーが別会社や大学でほそぼそと開発を続け、Open Source化して今に至る。  

## 特徴
- 漸近的型付け
- 識別子に自由に記号が使える
- オブジェクト指向と関数型言語の融合(Scheme + CLOS)
- 多重継承
- 多重ディスパッチ
- マクロあり
- TIOBE Index Top 50 圏外

## インストール
https://opendylan.org/download/index.html から各OS向けのコンパイラをダウンロードできる。

奇跡的にvscodeにvscode-dylanというプラグインがあるのでそれを使うとよい。

## CLIツールの使い方
`make-dylan-app` でプロジェクトの作成。  
`dylan-compiler -Build` でコンパイル。  
コンパイル後に `./_build/bin/` に実行ファイルが生成される。  

## 基礎文法

### Hello World

```dylan
Module: sample

define function main(name :: <string>, arguments :: <vector>)
  format-out("Hello, world!\n");
  exit-application(0);
end function main;

main(application-name(), application-arguments());
```

`format-out` や `exit-application` のように、識別子にハイフンを使うことができる。  
引き算の演算子と区別するために、2項演算子を適用するときは演算子の前後にスペースを開けなければならない。  

```dylan
a-b   // まちがい: a-b という識別子として解釈される
a - b // せいかい
```

型名(クラス名)は `<>` で囲む。  
関数の終わりには `end function 関数名;` と書いてあるが、これは省略できて単に `end;` でよい。 
型注釈は `変数名 :: 型名` のように書く。  

### グローバル変数

```dylan
define variable hoge :: <integer> = 1; // 変数

define constant pi :: <number> = 3.14; // 定数
```

### ローカル変数
`let` でローカル変数を宣言する。
再代入にするには `:=` を使う。

### 制御構造
`if`、`for`、`while` 等が使える。
`if` は式である。
`break` が無いのでそのままではループを途中で抜けることができない(ので違う書き方をする)。

### 関数定義
`define method 関数名(引数:: 型) => (なんか :: 戻り値の型)` または、  
`define function 関数名(引数:: 型) => (なんか :: 戻り値の型)` で関数定義。`なんか` は必須(謎だ…)。  
`return` は無く、関数の最後で評価された式が戻り値になる。

```dylan
// add だと組み込みの関数と名前がかぶるので名前を変えている
define function addo(a :: <integer>, b :: <integer>) => (result :: <integer>)
  a + b // 単一の式のときはセミコロンを省略できる(省略しなくてもよい)
end;
```

前述したように、型を省略することもできる。
```dylan
define function addo(a, b)
  a + b
end;
```

階乗を求める関数
```dylan
define function fact(n :: <integer>) => (result :: <integer>)
  if (n == 0) // if は式である。
    1
  else
    fact(n - 1) * n
  end
end;

define function fact2(n :: <integer>) => (result :: <integer>)
  if (n == 0) 1 else fact(n - 1) * n end // 一行で書いてもよい
end;

// 破壊的なやつ
define function fact3(n :: <integer>) => (result :: <integer>)
  let total = 1; // ローカル変数は let で宣言する。
  let a = 1;
  while(a <= n) // whileもある
    total := total * a;
    a := a + 1; // 再代入は := 
  end;
  total
end;
```

関数型言語なので末尾再帰の最適化も保証される。

### FizzBuzz

```dylan
define function fizzbuzz(n :: <integer>)
  for(i from 0 to n) // forもある
    if (modulo(i, 15) == 0)    // 割り算のあまりは modulo 関数で求める
      format-out("FizzBuzz\n");
    elseif (modulo(i, 5) == 0) // elseif で１キーワード
      format-out("Fizz\n");
    elseif (modulo(i, 3) == 0)
      format-out("Buzz\n");
    else
      format-out("%d\n", i);
    end;
  end;
end;
```

### クロージャ
関数型言語なので関数は第一級の値であり、クロージャも使える。
`method () 本体 end` でクロージャを作る。

```dylan
define function create-counter(n :: <integer>) => (res :: <function>)
  let count :: <integer> = n;
  method ()
    format-out("%d\n", n);
    n := n + 1;
  end;
end;

define function main(name :: <string>, arguments :: <vector>)
  let counter = create-counter(3);
  counter(); // => 3
  counter(); // => 4
  counter(); // => 5
  exit-application(0);
end function main;

main(application-name(), application-arguments());
```

### Block
`block` をつくることで、ループを途中で抜けることができる。

```dylan
// 非常に単純な block の例
let a = block(break) // 意味的に分かりやすいのでbreakにしているが、名前は何でも良い
   break(3) // break の引数が block を評価した値になる
end;
format-out("%d\n", a); // => 3
```
`break` は値付きgotoというか、関数化したretrunというか、そんなようなものだと考えてよい。
`break` 関数が呼び出されると`block`の先頭の行まで制御が戻ってきて、`break`の引数が`block`を評価した値になる。

```dylan
// 配列の中から指定された要素を探し、見つかったらその場でループを打ち切る関数
define function find(arr :: <array>, target :: <integer>) => (res :: <boolean>)
  block(break)
    for (elem in arr)
      if (elem = target)
        break(#t) 
      end;
    end;
    break(#f)
  end;
end;

let arr = #[1, 2, 3, 4, 5];
let exist? = find(arr, 6);
format-out("%s\n", exist?);
```

`break`が呼ばれると他の関数の中を実行中であろうと強制的に`block`まで戻ってくる。

```dylan
define function find2(arr :: <array>, target :: <integer>, break :: <function>)
  for (elem in arr)
    print(elem);
    if (elem = target)
      break(#t)
    end;
  end;
  break(#f)
end;

let arr = #[1, 2, 3, 4, 5];
let exist? = block(break)
  find2(arr, 3, break);
end;
format-out("%s\n", exist?);
```

こういうもの(`break`関数)のことを継続(Continuation)という。
`block`は、JavaScriptでいうと`Promise`に近い(ただし、`Promise`の実行は非同期だが、`block`は同期的である)。

```javascript
const find = (arr, target, breakf) => {
   for(let elem of arr) {
      if (target === elem) {
         breakf(true);
         return;
      }
   }
   breakf(false)
}

// JavaScriptでは、「breakf を実行したら制御を戻して引数を取り出す」処理が存在しないので、次のようには書けない。
// const result = block(breakf) { 
//    find([1,2,3,4,5], 3, breakf)
// }
// console.log(result);

// breakf を実行したあとの処理をすべてコールバック関数として渡す必要がある。
find([1,2,3,4,5], 3, (result) => { console.log(result) });

// Promiseとawaitを使えば(見かけ上)似たようなことができるが、実行は非同期になる。
(async () => {
   let result = await new Promise(res => {
      find([1,2,3,4,5], 3, res)
   });
   console.log(result);
})()
```

`block`と`break`は、「クロージャの中から(`break`の引数として)値を取り出して、クロージャの外に値を持っていく」ものと考えられるが、逆に、
「クロージャの外にある残りの計算をすべて取り出して、(`break`として)クロージャの中に持っていく」ものと考えることもできる。

```dylan
let arr = #[1, 2, 3, 4, 5];
let exist? = block(break)  // find2 の中で break が呼ばれるとここまで戻ってくると考えてもよいし、
  find2(arr, 3, break);
end;
format-out("%s\n", exist?);
```

```dylan
let arr = #[1, 2, 3, 4, 5];
let rest_calc = method(result) 
   let exist? = result;
   format-out("%s\n", exist?);
end;
find2(arr, 3, rest_calc); // block が現れた瞬間、残りの全ての計算を含んだクロージャが生成され、そのクロージャが find2 の引数に渡されていると考えることもできる。
```

継続とは、厳密にはこの「プログラムを実行した際の、ある時点での残りの計算」を表す概念であり、他の言語にも同様の概念自体は存在する。  
ただし、この継続を陽に取り出して操作する機能がある(継続がファーストクラスオブジェクトである、という)言語は限られている(Scheme, Ruby, Haskell など)。  
継続がファーストクラスオブジェクトである言語では、ある時点での継続を変数に代入して、あとでその継続を再実行するということもできる。  

```dylan
define variable cont :: <function> = method() end;
define variable counter :: <integer> = 0;

define function main(name :: <string>, arguments :: <vector>)
   let a = block(break)
      cont := break;
      break(counter)
   end;
   print(a);
   counter := counter + 1;
   if (counter < 5) 
      cont(counter);
   end;
end function main;
```

## クラス

### 定義
`define class <クラス名> (<親クラス>)` でクラスを定義する。
`slot` というのがインスタンス変数に相当する。 
メソッドはクラスとは別に定義する。  
`make`という組み込み関数でインスタンスを作成する。  

```dylan
define class <point-2d> (<object>)
  slot x :: <integer>,
    required-init-keyword: x:;
  slot y :: <integer>,
    required-init-keyword: y:;
end;

define function main(name :: <string>, arguments :: <vector>)
  let p = make(<point-2d>, x: 1, y: 1);
end function main;

main(application-name(), application-arguments());
```

### メソッド
メソッドはクラスとは別に関数として定義する。

```dylan
define function distanceFromOrigin(point :: <point-2d>) => (res :: <number>)
  (point.x * point.x + point.y * point.y) ^ 0.5
end;
```

メソッドを呼び出すときは普通に関数として呼び出す。  
メソッドの引数が一つのときに限り、いわゆるメソッド形式の呼び出しができる。
```dylan
let p = make(<point-2d>, x: 1, y: 1);
format-out("%d\n", distanceFromOrigin(p));
format-out("%d\n", p.distanceFromOrigin);
```

引数が複数あるメソッドは、メソッド形式で呼び出すことはできない。
```dylan
define function move(point :: <point-2d>, dx :: <integer>, dy :: <integer>)
  point.x := point.x + dx;
  point.y := point.y + dy;
end;

let p = make(<point-2d>, x: 1, y: 1);
move(p, 1, 1)
p.move(1, 1) // <- このようには書けない
```

この制約は不便ではあるが、複数のレシーバーに対してメソッド呼び出しを行う多重ディスパッチができるという利点もある(詳細は後述)。

### Todo: 継承と多重継承と総称関数と多重ディスパッチについて書く

## とりあえず作ってみた
Brainfucnkインタープリター
```dylan
Module: sample

define function brainfuck(prog :: <string>) => ()
  let prog-ptr = 0;
  let data-arr = make(<array>, size: 30000, fill:  0);
  let data-ptr = 0;

  while(prog.size > prog-ptr)
    select (prog[prog-ptr])
      '+' => data-arr[data-ptr] := data-arr[data-ptr] + 1;
      '-' => data-arr[data-ptr] := data-arr[data-ptr] - 1;
      '>' => data-ptr := data-ptr + 1;
      '<' => data-ptr := data-ptr - 1;
      '.' => format-out("%c", as(<character>, data-arr[data-ptr]));
      ',' => data-arr[data-ptr] := as(<integer>, read-element(*standard-input*));
      '[' =>
        if (data-arr[data-ptr] = 0)
          let bracket-count = 0;
          while(bracket-count >= 0)
            prog-ptr := prog-ptr + 1;
            if (prog[prog-ptr] == '[')
              bracket-count := bracket-count + 1;
            elseif (prog[prog-ptr] == ']')
              bracket-count := bracket-count - 1;
            end;
          end;
        end;
      ']' =>
        if (data-arr[data-ptr] ~= 0)
          let bracket-count = 0;
          while(bracket-count >= 0)
            prog-ptr := prog-ptr - 1;
            if (prog[prog-ptr] == ']')
              bracket-count := bracket-count + 1;
            elseif (prog[prog-ptr] == '[')
              bracket-count := bracket-count - 1;
            end;
          end;
        end;
      otherwise => #f
    end;
    prog-ptr := prog-ptr + 1;
  end;
  format-out("\n");
end;

define function main(name :: <string>, arguments :: <vector>)
  brainfuck(arguments[0]);
  exit-application(0);
end function main;

main(application-name(), application-arguments());
```

```dylan:library.dylan
Module: dylan-user

define library sample
  use common-dylan;
  use io;
end library sample;

define module sample
  use common-dylan;
  use format-out;
  use standard-io;
  use streams;
end module sample;
```

## 感想
- 1992年というかなり古い言語ながら漸近的型付けを採用しているのはすごい
- リストやベクタやクロージャに型がつかないのは辛いが時代を考えるとやむなしという感じか?
- Web上の情報はかなり少ない上に日本語の資料はほとんど無い。公式のドキュメントが充実してのが救い。
- いろいろなところでシンタックスハイライトが使えないのは辛い…(vscodeに拡張機能があるのが奇跡に近い)
- コンパイル時のメッセージが多すぎるのが困る
- Apple は Objective-C よりもこっちを採用して開発を続けた方が良かったのでは...?
  (Objective-CはC言語のクソさと動的型付け言語のクソさを併せ持った最悪のクソ言語では?という思いがある)
  (まあ、ある意味ではC言語のガバガバな型付けと動的型付けは相性がいいかもしれない(ほんまか?))

総評としては、いろいろな意味で実用には全く適さないが遊んでみる分には面白い言語である。  

## 参考資料
An Introduction to Dylan [https://opendylan.org/documentation/intro-dylan/index.html]  
リファレンスマニュアル [https://opendylan.org/books/drm/]  
Scheme使い向けのチートシート [https://opendylan.org/documentation/cheatsheets/scheme.html]
Dylan Programming　[https://opendylan.org/books/dpg/index.html]  
Rubyist のための他言語探訪【第 6 回】Dylan [https://magazine.rubyist.net/articles/0013/0013-Legwork.html]  
