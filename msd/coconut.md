# coconut

# Coconutとは？

Coconut is a functional programming language that compiles to Python. Since all valid Python is valid Coconut, using Coconut will only extend and enhance what you're already capable of in Python. (http://coconut-lang.org/より引用)

pythonのスーパーセットでpythonに関数型言語によくある機能(パターンマッチ、部分適用、パイプライン演算子  などなど)を加えた言語。coconutで書かれたプログラムはpythonのコードにトランスパイルされる。
JavaScriptに対するTypeScript的なもの？
pythonの豊富なライブラリをそのまま使いながら関数型的な機能を使いたいという場合におすすめ？

# 使い方

## インストール
``` bash
pip install coconut
```

## トランスパイル
``` bash
coconut hoge.coco # hoge.py が出力される
python hoge.py
```
トランスパイル後すぐに実行したい場合は --run オプションをつける
``` bash
coconut hoge.coco --run
```

# 機能

## 関数定義
単一の式で表せる関数は `return` を省略できる

``` python
# pythonでの定義
def add(x, y):
    return x + y    

# coconutでの定義
def add(x, y)=
    x + y
```

## パイプライン演算子
``` python
“Hello World” |> print #=> Hello World
```
左オペランドが右オペランドの関数の第一引数に渡される。

``` python
h(g(f(x))) # pythonでこうなってしまうコードが
x |> f |> g |> h # こう書ける

result = x |> f |> g |> h # 戻り値を変数に代入することもできる

(1, 2) |*> add |> print # 複数の引数をとる関数には |*> を使う
```

## ラムダ式

pythonのラムダ式は式しか書けない、わざわざ lambda とタイプする必要があるなどの理由で評判が悪い。

``` python
add = lambda x, y: x + y
add(1, 2) #=> 3
add = lambda x, y: print(x, y); x + y # このようには書けない
```

coconutでは lambda の代わりに -> が使える

``` 
add = (x, y) -> x + y
add(1, 2) #=> 3
```

ラムダ式の中に文を書きたい場合には 先頭に def をつけ、文はセミコロンで区切り、全体を括弧で囲む

```
add = (def (x, y) -> print(x, y); x + y)
add(1, 2)
``` 

## パターンマッチ

階乗を求める
``` python
def fact(n):
    match 0 in n:
        return 1
    else:
        return n * fact(n - 1)
```

リストの長さを求める
``` python
def length(lst):
    match [head] + tail in lst:
        return 1 + length(tail)
    else:
        return 0
```

## 部分適用（カリー化）

複数の引数を取る関数に対して、関数名の後に `$` を付けて関数を呼び出すと

``` python
add = (a, b, c) -> a + b + c
add1 = add$(1)   # add1 = (b, c) -> 1 + b + c としたのと同じ
add2 = add1$(2) # add2 = c -> 1 + 2 + c としたのと同じ
add2(3) #=> 6
```

例えば、pythonの `map` は第一にリストの各要素に適用する関数を、第二引数にリストを取るので、
パイプライン演算子と組み合わせるとfizzbuzzは次のように書ける。

```
range(100)
|> map$( x ->
    “fizzbuzz” if x % 15 == 0 else
    “fizz” if x % 5 == 0 else
    “buzz” if x % 3 == 0 else
    x)
|> list
|> print
```

## 演算子の関数化
演算子を括弧で囲むと関数化できる。

```
(+)(1, 2) 
```

## 関数の中位演算子化

関数をバッククオートで囲むことで中位演算子化することができる。

``` python
add = (x, y) -> x + y
1 `add` 2
```

# 代数的データ型

`data` キーワードでイミュータブルなフィールドを持つクラスのようなものを定義できる

``` python
data Point(x, y)
p = Point(x=1, y=3)
p.x #=> 1
p.y #=> 3

p.x = 2  #=> Error
```

メソッドを定義することもできる

``` python
data Person(name, age):
    def greet(self):
        print(“I’m %s. %d old.”, self.name, self.age)

p = Person(name=“tanaka”, age=25)
p.greet()
```

`@addpattern` で関数に対してパターンを追加することができる

例
``` python
data Blue()
data Green()
data Red()

def color_to_rgb(Blue()) = (0, 0, 255)

@addpattern(color_to_rgb)
def color_to_rgb(Red()) = (255, 0, 0)

@addpattern(color_to_rgb)
def color_to_rgb(Green()) = (0, 255, 0)

# 上と同じ
def color_to_rgb(color):
    case color:
        match Blue():
            return (0, 0, 255)
        match Red():
            return (255, 0, 0)
	match Green():
            return (0, 255, 0)
    else:
	raise MatchError
```

# vim-quickrun で使う際の設定

vimでquickrunを使っている場合、.vimrc(neovimの場合はinit.vim)に以下を追記するとquickrunでcoconutのコードを実行できる。

``` vimrc
autocmd BufRead,BufNewFile *.coco setfiletype coco
let g:quickrun_config = {}
let g:quickrun_config.coco = {
\ 'command': 'coconut',
\ 'exec': '%c %o %s %a',
\ 'cmdopt': '--run',
\ }
```
