# 型のあるPythonによる安全な開発

## はじめに
みんな知っての通りpythonはもともと動的型付け言語である。  
しかしPythonの中の人も動的型付けのクソさに気づいたのか、Python3.5からオプショナルな型ヒントの機能が追加された。  

TypeScriptと違って、標準実装の処理系(CPython)の機能として組み込まれているのでトランスパイルのような余計な処理なしに
型ヒントありのコードがそのまま標準の処理系で実行できる。  
Pythonには明文化された仕様が存在せず、標準実装の処理系の動作を仕様としている(実装による仕様)ので、  
要するにPythonの言語仕様として型ヒントをサポートしていると考えてよい。  

文法として型ヒントの文法は定められているが、処理系は型ヒントを単なるコメントとして解釈するので実行時にはなんの影響も及ぼさない。  
型チェックはプログラムの実行とは別にサードパーティによる静的型チェッカを使って行う。  
型チェッカにはいろいろあるが、今回はよく使われているmypyというツールを使う。  
(mypy以外にもGoogleが開発しているpytypeやMicrosoftが開発しているpyright(vscodeのプラグインとして使える)等がある)。  
場合によって同じコードでも使用する型チェッカ(あるいは型チェッカのオプション)によってエラーとなったりならなかったりすることがあるので、注意が必要である。

また、今回は詳しく調べていないのでどの程度実用性があるかは不明だが、dropboxがPythonのコードを静的解析して  
自動的に型アノテーションを生成するpyannotateというツールを公開している。

## mypyの使い方
pipで一発でインストールできる。
```
pip3 install mypy
```

型チェックの実行は次のように行う。
```
mypy sample.py
```

毎回コマンドで型チェックするのではなく、mypyのデーモンを起動して編集中のファイルに対して  
リアルタイムでチェックを行うこともできるらしいが、未調査。

今回はmypyの最新版である v0.701 を使う。

## 型ヒントの書き方

### 変数
```python
a: int = 1
b: bool = True
c: str = "hoge"
f: float = 1.5
```

型推論もあるので、右辺値から型が明らかな場合は型を省略できる。
```python
a = 1
a = "hoge" # mypyによるエラー
```

型チェックを回避したい場合は`typing`モジュールに定義されている`Any`型を使う。
```python
import typing

a: typing.Any = 1 
a = "hoge"
```

#### 変数のスコープと未定義変数の問題

pythonはif文やfor文がブロックスコープを持たないので、次のようなコードが動作する。
```python
if random.random() > 0.5:
   a = 1
print(a)
```
このコードは1/2の確率でエラーを起こす。  
つまり、pythonでは実行時の分岐によって同じスコープでも変数があったり無かったりするのである。  
この特徴は静的解析の敵と言っても過言ではない。  

mypyでは上のようなコードは正しいものとみなされ、エラーにならない。
そうでないと恐らくfalse negativeが多すぎて使い物にならないと判断したのだろうが、正直に言ってこの挙動はかなり痛い。

例えばありそうな例として下のようなコードは`some_func_maybe_throw_exception`の実行中に例外が発生した場合に、`a`は未定義となる(`None`にすらならない)
ので、普通の静的型付けの言語ではコンパイルエラーとなるが、mypyはこのコードを正しいものとする。
```python
try:
   result = some_func_maybe_throw_exception()
except:
   # Error Handling

print(result) # 実行時エラー
```
したがって、プログラマ側がこのようなコードを書かないように気をつける必要がある。  
(`except`節の中で必ず`return`するとか、予め`Optional`型として`try`節の外側で`result`という変数を宣言しておく、など)

```python
result: typing.Optional[SomeClass] = None
try:
   result = some_func_maybe_throw_exception()
except:
   # エラーハンドリングとか

if result is not None:
   print(result)
```

### 関数
```python
def add(a: int, b: int) -> int:
   return a + b
```

戻り値が無い関数は`None`を返すとする。
```python
def log(a: str) -> None:
   print(a)
```

戻り値の型を省略した場合は、戻り値の型は`Any`型であると解釈される。

ラムダ式に型を付ける場合には、`typing.Callable`を使う。  
```python
add: typing.Callable[[int, int], int] = lambda a, b: a + b
```

### クラス

TypeScriptと異なりクラス間のSubtypingはいわゆるNominal Subtyping(公証的部分型?)となっており、  
継承関係がそのままSubtypingの関係になっている(要するに普通のオブジェクト指向言語と同じと考えて良い)。  
```python
class Animal:
   pass

class Cat(Animal):
   pass 

ani: Animal = Cat() # Cat <: Animal なので問題なし
cat: Cat = Animal() # mypyによるエラー
```

イニシャライザの戻り値の型には必ず`None`を指定する。
```python
class Person:
   def __init__(self, name: str, age: int) -> None:
      self.name = name
      self.age = age
   
   def greet(self) -> None:
      print(f"I'm {self.name}")
```

PythonではJavaScriptのようにオブジェクトに後付でインスタンス変数を付け足すことができるが、  
mypyではそのようなコードはエラーとされる。  
```python
p = Person("masuda", 28)

p.foo = "foo" # 実行するとちゃんと動くが、mypyではエラー
print(p.foo)
```
これはPythonとしては正当なコードであるが、Pythonの習慣としてはこのようなコードはあまり書かない[要出典]ので、  
このように厳しくチェックしてもfalse negativeは十分少なく実用に耐えると判断したものと思われる。  

#### インスタンス変数の問題
Pythonではイニシャライザ以外のメソッドで新しくインスタンス変数を付け足すことができる。  
こちらは上の例と違い、mypyではエラーとならず、そのメソッドで付け足されるインスタンス変数は始めから存在するものとして扱われる。

```python
class Foo:
   def __init__(self) -> None:
      self.a = 1
      self.b = 2

   def define_c(self) -> None:
      self.c = 3

f = Foo()
print(f.c) # mypyではエラーにならないが、実行時にはエラー
```

この動作も変数のスコープの問題と並んで静的解析にとって痛手である。  
が、これを許さないと制約が強くなりすぎて使い物にならないことになるので止む終えない妥協である。  

Pythonではこのようにインスタンス変数はメソッド内で定義するので、逆に言うとメソッドの定義を見ないと  
クラスがどのようなインスタンス変数を持っているのかが分からない。

そこで、クラス定義の直下にインスタンス変数の定義を書くこともできる
```python
class Foo:
   a: int
   b: int

   def __init__(self) -> None:
      self.a = 1
      self.b = 2
```
ただし、これは型チェックのためのものというよりも人間のためのドキュメントとしての型という意味合いが大きい。   
このように定義したインスタンス変数に実際に値の割り当てを行わなくともmypyはエラーとしない。  

```python
class Foo:
   a: int
   b: int

   def __init__(self) -> None:
      self.a = 1

f = Foo()
print(f.b)  # mypyはエラーを報告しないが、実行時エラー
```

一応クラス直下の定義と実際に割り当てた値の型が違うとmypyはエラーを報告する。  
```python
class Foo:
   a: int
   b: int

   def __init__(self) -> None:
      self.a = 1
      self.b = "hoge" # mypyによるエラー
```

### ジェネリクス

```python
T = typing.TypeVar("T") # 型変数としてTを宣言

def id(a: T) -> T:
   return a

U = typing.TypeVar("U")

def apply(f: typing.Callable[[T], U], a: T) -> U:
   return f(a)

print(apply(lambda a: str(a), 1))
```

`typing.TypeVar`の第一引数の文字列は、型変数の文字と同じである必要がある。
```python
T = typing.TypeVar("U") # mypyによるエラー (error: String argument 1 'U' to TypeVar(...) does not match variable name 'T')
```

ジェネリッククラスを作りたいときは、`typing.Generic`を継承する。  
```python
class Stack(typing.Generic[T]):
   def __init__(self) -> None:
      self.__items: typing.List[T] = []

   def push(self, item: T) -> None:
      self.__items.append(item)

   def peek(self) -> T:
      return self.__items[len(self.__items) - 1]
   
   def pop(self) -> T:
      return self.__items.pop()

stack: Stack[int] = Stack()
stack.push(1)
stack.push("hoge") # mypyによるエラー
```

### 組み込みの型

```python
lst: typing.List[int] = [1,2,3]

dct: typing.Dict[str, int] = { "foo": 1, "bar": 2 }

tpl: typing.Tuple[int, int, int] = (1, 2, 3)

uni: typing.Union[int, str] = 1

opt: typing.Optional[int] = None

func: typing.Callable[[int, int], int] = lambda a, b: a + b

# 型エイリアスを作ることもできる
IntList = typing.List[int]

```

#### Union
pythonの`Union`はTypeScriptの直和型とかなり近い。  
変数の型によって分岐したい場合は、`isinstance`を使って変数の型を調べる。

```python
IntOrStr = typing.Union[int, str] 

def foo(a: IntOrStr) -> None:
   if isinstance(a, int):
      print(f"{a} is int")
   elif isinstance(a, str):
      print(f"{a} is str")
```

`isinstance`を条件式にもつif文の中では型が分かっているので、その型特有の操作ができる。
```python
def foo(a: IntOrStr) -> None:
   if isinstance(a, int):
      print(a - 1) # 問題なし
   elif isinstance(a, str):
      print(a - 1) # error: Unsupported operand types for - ("str" and "int")
```

網羅性のチェックをしたい場合は、`typing.NoReturn`型を使う(TypeScriptでいうところの`Never`型)
```python
def foo(a: IntOrStr) -> None:
   if isinstance(a, int):
      print(f"{a} is int")
   elif isinstance(a, str):
      print(f"{a} is str")
   else:
      b: typing.NoReturn = a # 漏れがあるとここでエラー
```

### variance

関数の型はちゃんと引数に対して反変、戻り値に対して共変になっているので安全である。
```python
class Animal: pass
class Cat(Animal): pass 

def f1(a: Animal) -> None: pass
def f2(c: Cat) -> None: pass

f4: typing.Callable[[Cat], None] = f1    # 問題なし
f3: typing.Callable[[Animal], None] = f2 # mypyによるエラー
                                         # (error: Incompatible types in assignment (expression has type "Callable[[Cat], None]", variable has type "Callable[[Animal], None]"))
```

メソッドのオーバーライドについても同様である。  
```python
class Parent:
   def f(self) -> Animal:
      return Animal()

   def g(self) -> Cat:
      return Cat()

class Child(Parent):
   def f(self) -> Cat: # 問題なし
      return Cat()

   def g(self) -> Animal: # error: Return type of "g" incompatible with supertype "Parent"
      return Animal()
```

ユーザー定義クラスについても、デフォルトでは不変になっている。
```python
# さっき定義したStackクラスの動作

s1: Stack[Cat] = Stack()
s2: Stack[Animal] = s1 # mypyによるエラー
```

型引数に対して共変にしたい場合は、型変数を作るときに`typing.TypeVar`の引数に`covariant=True`と指定する。
```python
CoT = typing.TypeVar("CoT", covariant=True)

class CoStack(typing.Generic[CoT]):
   def __init__(self, initial_values: typing.List[CoT] = []) -> None:
      self.__items: typing.List[CoT] = initial_values

   # def push(self, item: CoT) -> None:
   #    self.__items.append(item)

   def peek(self) -> CoT:
      return self.__items[len(self.__items) - 1]
   
   def pop(self) -> CoT:
      return self.__items.pop()

s1: CoStack[Animal] = CoStack()
s2: CoStack[Cat] = s1 # 問題なし
```

上のコードで`push`がコメントアウトされているが、これは共変の型変数をメソッドの引数の型に使っているためで、  
このコメントアウトを外すとエラーになる(それはそう)。  

同様に、`contravariant=True`と指定すると型変数が反変になる。

covariantとcontravariantを両方Trueにすることはできない。
```python
V = typing.TypeVar("V", covariant=True, contravariant=True) # error: TypeVar cannot be both covariant and contravariant
```

### 構造的部分型とprotocol
構造的部分型を使いたい場合は、`typing_extensions.Protocol`を使うと、  
継承関係にないクラスについてもサブタイピングの関係を作ることができる。  

```python
import typing_extensions

class Hogerable(typing_extensions.Protocol):
   def hoge(self) -> str: ... # strを返すhogeメソッドを持つクラスは全てHogerableになる

class Hoge1:
   def hoge(self) -> str:
      return "HOGE"

class Hoge2:
   def hoge(self) -> str:
      return "HOGEHOGE"

lst: typing.List[Hogerable] = [Hoge1(), Hoge2()] # Hoge1, Hoge2のどちらもhogeメソッドを持つので問題なし
```

Pythonはもともとダックタイピングでやっていたのでこの機能はなかなか有用そうである。

### アノテーションの遅延評価と再帰型
python3.6以前では型ヒントで使える型は既にそのスコープで使える型である必要があった。
これは

```python
class C:
   @staticmethod
   def create() -> C:
      return C()
```

python3.7からは型アノテーションが遅延評価されるようになり、上のコードが正当なものとして扱われるようになった。
これにより
しかし、現時点のmypyでは一部の型で再帰型が使えない。
```python
# 2分木を表すデータ構造

# こちらはエラーが出る
# (error: Recursive types not fully supported yet, nested types replaced with "Any")
Node = typing.NamedTuple("Node", (
            ("left", typing.Optional[Node]),
            ("right", typing.Optional[Node]),
            ("value", int)))

# こちらはエラーが出ない
class CNode:
   def __init__(self, left: CNode, right: CNode, value: int) -> None:
      self.left = left
      self.right = right
      self.value = value
```

## まとめ
pythonの静的型付けについて見てきたが、やはりというかなんというかもともと動的型付けなところに後付で型を付けるということに対する苦労が見て取れる。  
また、TypeScriptと比較すると標準実装が文法として型ヒントとサポートしているのでもっと流行っても良さそうであるが、  
実のところTypeScriptと比べると流行っているとは言い難い上に流行る気配すらないという感じである:sob:。
Python用の型定義ファイルを集めたtypeshedというリポジトリがあるが、TypeScriptと比べると型定義ファイルの充実度はかなり低い。
ただやはり公式のサポートのおかげで型チェックの導入のハードル自体はTypeScriptよりも低い  
(なにせ型ヒントを付けるだけならランタイムの変更どころか外部ツールの一つもいらない)ので、  
ちゃんとしたプログラムを書きたいがドウシテモPythonを使わざるおえないという人は積極的に使うといいと思う。  

## 参考資料
公式ドキュメント [https://mypy.readthedocs.io/en/latest/index.html]  
mypyやっていくぞ [https://qiita.com/k-saka/items/8f05c89f675af219e081]  
mypyやっていったぞ [https://qiita.com/k-saka/items/9d7111e82cd06e5419db]  
[https://github.com/python/typeshed]  
