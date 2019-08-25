# Lua 入門

## はじめに
> Lua is a powerful, efficient, lightweight, embeddable scripting language. It supports procedural programming, object-oriented programming, functional programming, data-driven programming, and data description. 
(Cited from [https://www.lua.org/about.html])

Luaとはリオデジャネイロ・カトリカ大学で開発されたスクリプト言語で
- コンパクトな処理系
- MITライセンス
- マルチパラダイム
- C/C++との相互運用性の高さ
などの特徴を持つ。  
主にゲーム開発においてよく使われる他、プラグインの記述等によく使われる。  
[https://en.wikipedia.org/wiki/Category:Lua-scripted_video_games]

## インストール
```
sudo apt install lua5.3 liblua5.3-dev
```
## 基本文法

### Hello World
```lua
print("Hello World!!!")

-- 引数が１つの場合は括弧を省略できる
print "Hello World!!!"

-- [[ ]] で囲うことで複数行の文字列を表すことができる 
print [[
   Hello
   World!!!
]]
```

### FizzBuzz
```lua
for i = 1, 20 do
   if i % 15 == 0 then
      print("FizzBuzz")
   elseif i % 5 == 0 then
      print("Fizz")
   elseif i % 3 == 0 then
      print("Buzz")
   else
      print(i)
   end
end
```

### 関数定義
```lua
function fact(n)
   if n == 0 then
      return 1
   else
      return n * fact(n - 1)
   end
end

function fact2(n)
   local result = 1 --ローカルスコープの変数を宣言する際は local を付ける
   for i = 1, n do
      result = result * i
   end
   return result
end
```

### 匿名関数
```lua
add = function (a, b) return a + b end
```

### クロージャ
```lua
function createCounter(n)
   return function()
      print(n)
      n = n + 1
   end
end

c1 = createCounter(1)
c1() --=> 1
c1() --=> 2
c1() --=> 3
```

### コレクション
```lua
tbl = { a = 1, b = 2, c = "C" }

-- 配列(実装は整数をキーとした連想配列)
arr = {1, 2, 3}
print(arr[1]) -- indexは1からスタート
print(arr[4]) -- 未定義の要素にアクセスするとnilが返る 

arr[4] = 4 -- 現在の要素数よりも多いindexにアクセスすると勝手に拡張される

print
```

### 多値
```lua
a, b, c = 1, 2, 3 -- 分割代入として使う
print(a, b, c) --=> 1 2 3

-- 第1級の値ではないので、変数に代入することはできない
a = 1, 2, 3
print(a) --> 1

-- 関数の戻り値として返すことができる
function foo()
   return 1, 2, 3
end

function bar(a, b, c)
   print(a + b + c)
end

bar(foo()) --=> 6
```

### エラー処理
Luaには例外は無いが、失敗するかもしれない関数呼び出しを安全に行う `pcall` (protected call) という機能がある。  

```lua
function add(a, b)
   return a + b
end

-- 第1引数に実行する関数を、第2引数以降に第1引数の関数にわたす引数を渡す
-- 1つ目の戻り値には真偽値で関数の実行の成否が、2つ目の戻り値には関数の結果が返ってくる
result, value = pcall(add, 1, 2) 
print(result, value) --> true    3

result, value = pcall(add, "a", "b")
print(result, value) --> false   pcall.lua:2: attempt to perform arithmetic on a string value (local 'a') 
```

### Brainfuck
```lua
if arg[1] == nil then
   print("No input")
   os.exit(1)
end

prog = arg[1]
prog_ptr = 1
data = {}
for i = 1, 30000 do
   data[i] = 0
end
data_ptr = 1

while prog_ptr <= #prog do
   op = string.sub(prog, prog_ptr, prog_ptr)
   
   if op == "+" then
      data[data_ptr] = data[data_ptr] + 1
   elseif op == "-" then
      data[data_ptr] = data[data_ptr] - 1
   elseif op == ">" then
      data_ptr = data_ptr + 1
   elseif op == "<" then
      data_ptr = data_ptr - 1
   elseif op == "." then
      io.write(string.char(data[data_ptr]))
   elseif op == "," then
      data[data_ptr] = string.byte(io.read())
   elseif op == "[" then
      if data[data_ptr] == 0 then
         prog_ptr = prog_ptr + 1
         brace_count = 0
         while true do
            if string.sub(prog, prog_ptr, prog_ptr) == "[" then
               brace_count = brace_count + 1
            elseif string.sub(prog, prog_ptr, prog_ptr) == "]" then
               brace_count = brace_count - 1
            end
            if brace_count == -1 then
               break
            end
            prog_ptr = prog_ptr + 1
         end
      end
   elseif op == "]" then
      if data[data_ptr] ~= 0 then
         prog_ptr = prog_ptr - 1
         brace_count = 0
         while true do
            if string.sub(prog, prog_ptr, prog_ptr) == "]" then
               brace_count = brace_count + 1
            elseif string.sub(prog, prog_ptr, prog_ptr) == "[" then
               brace_count = brace_count - 1
            end
            if brace_count == -1 then
               break
            end
            prog_ptr = prog_ptr - 1
         end
      end
   end

   prog_ptr = prog_ptr + 1
end
```

## オブジェクト指向
Luaではプロトタイプベースのオブジェクト指向がサポートされている。  

非常に素朴なオブジェクト指向の実現方法として、テーブルにデータとメソッドをそのまま持たせるという方法がある。  
```lua
function createPoint(_x, _y)
   return {
      x = _x,
      y = _y,
      print = function(self)
         print(string.format("x=%d, y=%d", self.x, self.y))
      end,
      move = function(self, dx, dy)
         self.x = self.x + dx --テーブルは共有渡しされるので、これで引数のテーブルを書き換えることができる
         self.y = self.y + dy
      end
   }
end

p1 = createPoint(1, 1)
p1.print(p1) --> x=1, y=1
p1.move(p1, 1, 2)
p1.print(p1) --> x=2, y=3
```

このままではあんまりという感じだが、`:`記法を使うとメソッドの第一引数を省略することができる。  
```lua
p1 = createPoint(1, 1)
p1:print() --> x=1, y=1
p1:move(1, 2)
p1:print() --> x=2, y=3
```

これだけでも結構オブジェクト指向って感じだが(ほんまか?)、このままではオブジェクト毎に異なる実体のメソッドが生成されて無駄である。  
そこで、データはオブジェクト毎に変えたいがメソッドは使いまわしたいということになる。  
Luaではこれを実現するためにJavaScriptのプロトタイプチェーンに似たメタテーブルという仕組みがある。  

```lua
Point = {}
function Point.print(self)
   print(string.format("x=%d, y=%d", self.x, self.y))
end
function Point.move(self, dx, dy)
   self.x = self.x + dx
   self.y = self.y + dy
end
function Point.new(_x, _y)
   local obj = { x = _x, y = _y }
   return setmetatable(obj, { __index = Point })
end
-- メソッドだけでなくクラス変数のようなものも持てる
Point.origin = Point.new(0, 0)

p1 = Point.new(1, 1)
p1:print() --> x=1, y=1
p1:move(1, 2)
p1:print() --> x=2, y=3

Point.origin:print() --> x=0, y=0
p1.origin:print() --> x=0, y=0
```

メソッドの定義時にも、`:`記法を使うと第一引数を省略することができる。  
```lua
Point = {}
function Point:print()
   print(string.format("x=%d, y=%d", self.x, self.y))
end
function Point:move(dx, dy)
   self.x = self.x + dx
   self.y = self.y + dy
end
function Point.new(_x, _y)
   local obj = { x = _x, y = _y }
   return setmetatable(obj, { __index = Point })
end
```

継承もメタテーブルを使って実現できる。  
```lua
ColoredPoint = {}
setmetatable(ColoredPoint, { __index = Point })
function Point:print()
   print(string.format("x=%d, y=%d, color=%s", self.x, self.y, self.color))
end
function Point.new(_x, _y, _color)
   local obj = { x = _x, y = _y, color = _color }
   return setmetatable(obj, { __index = ColoredPoint })
end
p2 = ColoredPoint.new(1, 1, "red")
p2:print() --> x=1, y=1, color=red
p2:move(1, 2)
p2:print() --> x=2, y=3, color=red
```

演算子の実体はメソッドなので、演算子オーバーロードもメタテーブルで実現できる。  
```lua
Complex = {}
Complex.__index = Complex
function Complex.__add(c1, c2)
   return Complex.new(c1.re + c2.re, c1.im + c2.im)
end
function Complex.__sub(c1, c2)
   return Complex.new(c1.re - c2.re, c1.im - c2.im)
end
function Complex:print()
   print(string.format("re=%d, im=%d", self.re, self.im))
end
function Complex.new(_re, _im)
   local obj = { re=_re, im=_im }
   return setmetatable(obj, Complex)
end

c1 = Complex.new(1, 1)
c2 = Complex.new(1, -1)
(c1 + c2):print() --> re=2, im=0
```
ただし、文字列等の組み込み型のメタテーブルは書き換えられないので、組み込み型に対する演算子オーバーロードはできない。  

## C言語との連携
Luaの最大の特徴は、C/C++で作られたプログラムとの相互運用性が高いことである。  
RubyやPythonといったインタプリタ型言語がC言語と連携する場合、RubyやPythonからC言語のライブラリを呼び出すことは原理的には比較的簡単だが、  
C言語からRubyやPythonのライブラリを呼び出すことは難しい。  
というのもインタプリタ型言語は実行のためのインタプリタが必要なので、ライブラリとしてRubyやPythonのコードを利用するプログラムがあった場合、  
プログラムを単体で動作させようとした場合、プログラムの配布の際にインタプリタも一緒に配布する必要がある。  

Luaもインタプリタ型言語なので、Luaを使ったプログラムを単体で動作できるようにして配布する場合はインタプリタを一緒に配布する必要があるが、  
LuaのインタプリタはRubyやPythonといった他の言語と比べて非常に小さい(64bit Linux向けバイナリで247KB)ので、  
プログラム本体と一緒にインタプリタを配布しても邪魔になりにくい  
(まあ実のところ今どきのPC向けに配布するプログラムのサイズが数十~数百MB増えたところであまり問題無いかもしれないが...)。

Luaはこの特徴のおかげで、主にゲーム開発でC/C++のメインプログラムと連携する形で利用されることが多い。  
ゲーム開発においてコードの修正→動作の確認のサイクルを素早く行うことは極めて重要であるが、一方でC++はコンパイルに時間がかかる言語として有名である。  
そこで、プログラムのうち頻繁に変更が必要な部分をLuaで、あまり変更が必要でない部分をC++で記述することで、効率的に開発を行うことができると言われている。  

### CからLuaを呼び出す
```c
#include "lua.hpp"
#include "lauxlib.h"
#include "lualib.h"

int main() {
    lua_State *L = luaL_newstate();
    luaL_openlibs(L);
    luaL_loadfile(L, "lib.lua");
    lua_pcall(L, 0, 0, 0);
    lua_close(L);

    return 0;
}
```

### LuaからCを呼び出す

## LuaJIT
Luaのオリジナルの実装のインタプリタはJITを使っていないが、LuaにはLuaJITと呼ばれる別実装のインタプリタが存在する。  
こちらはその名の通りLuaのプログラムをネイティブコードにJITコンパイルして実行するものである  
(これ本家のLua処理系がJITし始めたら名称がめちゃくちゃ紛らわしくなるがどうするのだろう…？)。  
オリジナルのLuaもスクリプト言語としてはそこそこの速さ(CPythonより少し速い程度)であるが、  
LuaJITは動的型付け言語のインタプリタの中では非常に高速であることが知られている  
(V8と同じかそれ以上。場合によってはJavaよりも速くなるということもあるらしい)。  

### インストール

#### Windows
公式からはソースしか配布していないらしい。  
野良ビルドのバイナリも探せばどこかに落ちてるかもしれないが、探すのが面倒なのでビルドする。  
1. [http://luajit.org/download.html]からソースをダウンロード
1. MSVC or MinGW or Cygwin でビルドできるのでビルド(自分はMSYS2 + MinGWでビルドした)
1. srcディレクトリに `luajit.exe` と `lua51.dll` というファイルが生成されるので、それらを使いたい場所にコピーするなりpathを通すなりする(この2つのファイルは同じディレクトリに入れておく必要がある)
1. `luajit ファイル名` でプログラムを実行

### ベンチマーク

## まとめ
プロトタイプベースオブジェクト指向、初めて見たときは何だこれは…(ドン引き)という感じだったが、
最近になってどうせ動的型付けでガバガバなんだからこんなもんでいいのではと思い始めた(KONAMI感)。
